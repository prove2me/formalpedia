-- Prove2me | Definitions.Def_StabPauli1264_Grouped_Domain
-- name    : StabPauli1264_Grouped_Domain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:23:41.443319+00:00
-- url     : https://prove2.me/theorems/d1c5ba95-b82c-4bce-94d8-5a8cd80ffb4e
-- title:
--   Pauli windows, mixed inputs and stabilizer prediction risk
-- statement:
--   Let $n$ be a number of qubits, with computational basis indexed by $\{0,1\}^n$. A density matrix is any complex positive semidefinite matrix of trace one. A window $M=(P_1,\ldots,P_m)$ is nonempty and contains signed Hermitian Pauli operators, none proportional to the identity, with distinct unsigned labels. A known real probability law $p$ on the window permits zero masses. Write $p(C)=\sum_{i\in C}p_i$. A context is a pairwise commuting subset of the window.
--
--   For a valid signed stabilizer tableau $T$, let $\sigma_T$ be its rank-one projector and $f_T(i)=\operatorname{tr}(\sigma_TP_i)$. For any matrix $\rho$ write $b_i=\operatorname{Re}\operatorname{tr}(\rho P_i)$, and define
--
--   $$R_{p,\rho}(h)=\frac12-\frac12\sum_i p_i b_i h_i,\qquad R^*_{p,\rho}=\min_{T\text{ valid}}R_{p,\rho}(f_T).$$
--
--   Excess risk is $R_{p,\rho}(h)-R^*_{p,\rho}$. Stabilizer mixtures are convex combinations of the actual valid tableau projectors, with arbitrary nonnegative real coefficients summing to one. The benchmark includes every pure stabilizer, independently of which contexts are measured.
--
--   **Formalization Note** The existing signed I,X,Y,Z Pauli model, tableau validity, density predicate and finite-law model are imported. Window coordinates use `Fin m`; distinct operator words express distinct labels up to sign. The real part changes no physical expectation. The risk minimum is represented by the infimum of its finite nonempty range. `pointLaw` is a deterministic probability law.
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), §1.1 pp. 3–4; §5, Definitions 5.1–5.2 and Eqs. (12)–(13), p. 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Mathlib
import Definitions.Def_ClonableQMASep_Main_Channels
import Definitions.Def_QAlgorithms_Defs_Stabilizer
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
set_option autoImplicit false

namespace StabPauli1264.Grouped

open QAlgorithms.Stabilizer
open scoped BigOperators Classical ComplexOrder

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev Mat (n : ℕ) := Matrix (Bits n) (Bits n) ℂ
abbrev EvalLaw (m : ℕ) := OAI.ThorpCompatibility.Law (Fin m)

/-- All complex positive semidefinite trace-one matrices; no purity promise. -/
structure Density (n : ℕ) where
  matrix : Mat n
  physical : ClonableQMASep.Main.IsDensity matrix

instance pauliFintype : Fintype Pauli :=
  ⟨{.I, .X, .Y, .Z}, by intro p; cases p <;> simp⟩

noncomputable instance pauliStringFintype (n : ℕ) : Fintype (PauliString n) :=
  Fintype.ofEquiv (ZMod 4 × (Fin n → Pauli))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun p => (p.phase, p.ops)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Distinct unsigned labels are the `ops` components in the I,X,Y,Z basis.
This basis includes the integer-overlap phase in Y = iXZ. -/
structure Window (n m : ℕ) where
  observable : Fin m → PauliString n
  hermitian : ∀ i, (observable i).phase = 0 ∨ (observable i).phase = 2
  nonidentity : ∀ i, ∃ q, (observable i).ops q ≠ .I
  distinct : Function.Injective (fun i => (observable i).ops)
  nonempty : 0 < m

noncomputable def operator {n m : ℕ} (M : Window n m) (i : Fin m) : Mat n :=
  (M.observable i).toMatrix

noncomputable def mass {m : ℕ} (p : EvalLaw m) (C : Finset (Fin m)) : ℝ :=
  ∑ i ∈ C, p.mass i

def IsContext {n m : ℕ} (M : Window n m) (C : Finset (Fin m)) : Prop :=
  ∀ i ∈ C, ∀ j ∈ C, (M.observable i).Commute (M.observable j)

noncomputable def bias {n m : ℕ} (M : Window n m) (ρ : Mat n) (i : Fin m) : ℝ :=
  (Matrix.trace (ρ * operator M i)).re

noncomputable def response {n m : ℕ} (M : Window n m) (T : Tableau n) : Fin m → ℝ :=
  bias M (tableauProjector T)

noncomputable def risk {n m : ℕ} (M : Window n m) (p : EvalLaw m)
    (ρ : Mat n) (h : Fin m → ℝ) : ℝ :=
  1 / 2 - (∑ i, p.mass i * bias M ρ i * h i) / 2

/-- Minimum over all valid tableaux, identifying duplicate generator descriptions by their
projector. This is a finite nonempty set, not a measured-context benchmark. -/
noncomputable def optimalRisk {n m : ℕ} (M : Window n m) (p : EvalLaw m) (ρ : Mat n) : ℝ :=
  sInf {r : ℝ | ∃ T : Tableau n, IsValidTableau T ∧ r = risk M p ρ (response M T)}

/-- Physical stabilizer mixtures with arbitrary real convex weights. -/
def IsStabilizerMixture {n : ℕ} (ρ : Mat n) : Prop :=
  ∃ w : Tableau n → ℝ, (∀ T, 0 ≤ w T) ∧ (∑ T, w T = 1) ∧
    (∀ T, ¬ IsValidTableau T → w T = 0) ∧
    ρ = ∑ T, (w T : ℂ) • tableauProjector T

noncomputable def excess {n m : ℕ} (M : Window n m) (p : EvalLaw m)
    (ρ : Mat n) (h : Fin m → ℝ) : ℝ :=
  risk M p ρ h - optimalRisk M p ρ

/-- A point mass with real weights, used for deterministic choices. -/
noncomputable def pointLaw {α : Type} [Fintype α] (a : α) : OAI.ThorpCompatibility.Law α where
  mass b := if b = a then 1 else 0
  nonneg b := by split_ifs <;> norm_num
  total := by simp

end StabPauli1264.Grouped


