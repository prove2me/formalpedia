-- Prove2me | Definitions.Def_LatticeHamSim_CommLR_Setting
-- name    : LatticeHamSim_CommLR_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:07.873994+00:00
-- url     : https://prove2.me/theorems/731a0bf9-cb00-4e60-a595-dbbc2d7b7fa5
-- title:
--   Appendix C.1–C.2 — local operators, Hamiltonian, Heisenberg evolution, C_B, D_B and linked weights
-- statement:
--   Let $\Lambda$ be a finite metric space of sites, with a common local dimension $q$. The product basis of the system is indexed by configurations $\sigma:\Lambda\to\{0,\ldots,q-1\}$. An operator is **supported on** $X\subseteq\Lambda$ when it is $m_X\otimes I_{\Lambda\setminus X}$: its matrix entry is the entry of $m_X$ on the restrictions of the two configurations to $X$ if those configurations agree outside $X$, and zero otherwise. The Hamiltonian and Heisenberg evolution are
--
--   $$H=\sum_{X\subseteq\Lambda}h_X,\qquad O(t;J)=e^{iJt}Oe^{-iJt}. $$
--
--   The set distance is the minimum of site distances over pairs, and $X\sim Y$ means $X\cap Y\ne\varnothing$. For a fixed $B$, $C_B(X,t)$ is the supremum of $\|[A(t),B]\|$ over all operators $A$ supported on $X$ with $\|A\|\le1$; $D_B(X,t)=\|[h_X(t),B]\|$. The linked weight sums products of interaction norms over the overlap patterns of equation (32). These definitions are the common interface for every milestone.
--
--   **Formalization Note** Matrices use the L2 operator norm. The set distance is zero if either set is empty, as are Mathlib's point-to-empty distance and empty-set diameter. $C_B$ is a real supremum of a nonempty, bounded set under the Hermitian Hamiltonian hypotheses used by the theorems. The linked weight's zero-based index $j$ represents the paper's $Z_{j+1}$; its endpoint is constrained to meet $Y$.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, pp. 21–24, Appendix C.1–C.2, (14)–(15), (18)–(19), (32)

import Mathlib
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.CommLR

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}

/-- An operator acting as the identity outside the sites in `X`. -/
def SupportedOn (X : Finset Λ)
    (M : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) : Prop :=
  ∃ m : Matrix (X → Fin q) (X → Fin q) ℂ,
    ∀ σ τ : Λ → Fin q,
      M σ τ = if (∀ x, x ∉ X → σ x = τ x)
        then m (fun x => σ x) (fun x => τ x) else 0

/-- Heisenberg evolution `O(t; J) = exp(i J t) O exp(-i J t)`. -/
noncomputable def evolve (J : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (t : ℝ)
    (O : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) : Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
  NormedSpace.exp ((Complex.I * (t : ℂ)) • J) * O *
    NormedSpace.exp ((-(Complex.I * (t : ℂ))) • J)

/-- The full Hamiltonian, summed over every subset of the finite site set. -/
def H (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    Matrix (Λ → Fin q) (Λ → Fin q) ℂ :=
  ∑ X : Finset Λ, h X

/-- Minimum distance between two nonempty finite sets; zero when either is empty. -/
noncomputable def setDist (X Y : Finset Λ) : ℝ :=
  if h : (X ×ˢ Y).Nonempty then
    (X ×ˢ Y).inf' h (fun p => dist p.1 p.2)
  else 0

/-- `X ∼ Y`: the two site sets overlap. -/
def meets (X Y : Finset Λ) : Prop := (X ∩ Y).Nonempty

/-- The indicator of an overlap condition. -/
noncomputable def indicator (P : Prop) : ℝ := by
  classical
  exact if P then 1 else 0

/-- The supremum `C_B(X,t)` in (18). -/
noncomputable def CB (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
    SupportedOn X A ∧ ‖A‖ ≤ 1 ∧
    r = ‖evolve (H h) t A * B - B * evolve (H h) t A‖}

/-- The commutator norm `D_B(X,t)` in (19). -/
noncomputable def DB (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) : ℝ :=
  ‖evolve (H h) t (h X) * B - B * evolve (H h) t (h X)‖

/-- The `j`th set in a finite linked sequence, extended by the empty set. -/
def linkedGet {k : ℕ} (Z : Fin k → Finset Λ) (j : ℕ) : Finset Λ :=
  if hj : j < k then Z ⟨j, hj⟩ else ∅

/-- The overlap required at the `j`th link of (32), with zero-based `j`. -/
def linkedCondition {k : ℕ} (X : Finset Λ) (Z : Fin k → Finset Λ)
    (j : ℕ) : Prop :=
  if j = 0 then meets X (linkedGet Z j)
  else if j % 2 = 0 then
    meets (linkedGet Z (j - 2) ∪ linkedGet Z (j - 1)) (linkedGet Z j)
  else meets (linkedGet Z (j - 1)) (linkedGet Z j)

/-- The inner linked-set sum of (32), without its time and commutator factors. -/
noncomputable def linkedWeight
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (X Y : Finset Λ) (k : ℕ) : ℝ :=
  ∑ Z : Fin k → Finset Λ,
    (∏ j : Fin k, ‖h (Z j)‖ * indicator (linkedCondition X Z j.val)) *
      indicator (meets (linkedGet Z (k - 1)) Y)

end LatticeHamSim.CommLR


