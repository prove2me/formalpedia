-- Prove2me | Definitions.Def_UhlmannRoof_RankTwo_Model
-- name    : UhlmannRoof_RankTwo_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:33:39.661001+00:00
-- url     : https://prove2.me/theorems/4128b506-a941-424e-bc5d-ba907f5c228b
-- title:
--   Equations (3)–(11), pp. 4–8 — states, diagonal entropy, convex roof, supporting contact sets, and transpositions
-- statement:
--   Fix the standard basis of a finite dimensional complex Hilbert space and its diagonal maximal commutative algebra. A **state** is a positive semidefinite matrix of trace one; a **pure state** is a rank one matrix $|\psi\rangle\langle\psi|$ with $\|\psi\|=1$. The minimal diagonal projections are $P_j=|j\rangle\langle j|$.
--
--   For a state $\nu$, its diagonal entropy and its convex roof are
--   $$
--   \widetilde S(\nu)=\sum_j -\nu_{jj}\ln\nu_{jj},\qquad
--   R(\omega)=\inf_{\omega=\sum_k p_k\rho_k}\sum_k p_k\widetilde S(\rho_k),
--   $$
--   where the infimum is over finite decompositions into pure states with strictly positive weights summing to one. An **optimal decomposition** attains this infimum. The entropy of the diagonal algebra at $\omega$ is $H_\omega=\widetilde S(\omega)-R(\omega)$.
--
--   An **$R$-set** is a convex set of states in which every member has an optimal decomposition using pure states of the same set. A Hermitian matrix $A$ represents the affine functional $l_A(\nu)=\operatorname{Re}\operatorname{Tr}(\nu A)$. It supports $R$ when $l_A\le R$ on all states and equality holds somewhere. Its contact set is $\Omega(A)=\{\nu:R(\nu)=l_A(\nu)\}$. The set $\Omega_\omega$ is the intersection of all such contact sets for which $l_A(\omega)=R(\omega)$. A **transposition** is a unitary that exchanges two diagonal minimal projections and fixes the rest.
--
--   These definitions supply the common state space, convex roof, and contact set used by the paper's rank two symmetry theorem.
--
--   **Formalization Note** The basis is indexed by `Fin d`, so the paper's indices start at zero here. `Real.negMulLog` gives the convention $0\ln0=0$. The real `sInf` defining $R$ is used only on states, where pure state decompositions exist and the costs are bounded below. The density matrix predicate is reused from `QAlgorithms.IsDensityMatrix`.
-- source:
--   Uhlmann, arXiv:quant-ph/9704017v2, pp. 4–8, eqs. (3)–(11), Lemma 1 preamble, Remark p. 7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information

namespace UhlmannRoof.RankTwo

open Matrix
open scoped ComplexOrder

abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- A state is a positive density operator of unit trace. -/
def IsState {d : ℕ} (ρ : Mat d) : Prop := QAlgorithms.IsDensityMatrix ρ

/-- The minimal projection of the distinguished diagonal algebra. -/
def P {d : ℕ} (j : Fin d) : Mat d := Matrix.single j j 1

/-- A rank-one density operator associated to a unit vector. -/
def IsPure {d : ℕ} (ρ : Mat d) : Prop :=
  ∃ ψ : Fin d → ℂ, (∑ i, ‖ψ i‖ ^ 2) = (1 : ℝ) ∧
    ρ = Matrix.vecMulVec ψ (star ψ)

/-- Entropy of the restriction to the diagonal algebra, in natural units. -/
noncomputable def Stilde {d : ℕ} (ν : Mat d) : ℝ :=
  ∑ j, Real.negMulLog (ν j j).re

/-- An extremal finite convex decomposition with strictly positive coefficients. -/
def IsPureDecomp {d m : ℕ} (ω : Mat d) (p : Fin m → ℝ) (ρ : Fin m → Mat d) : Prop :=
  (∀ k, 0 < p k) ∧ (∑ k, p k) = 1 ∧
  (∀ k, IsPure (ρ k)) ∧ (∑ k, (p k : ℂ) • ρ k) = ω

/-- The convex roof of the diagonal entropy, equation (6). -/
noncomputable def R {d : ℕ} (ω : Mat d) : ℝ :=
  sInf {x : ℝ | ∃ (m : ℕ) (p : Fin m → ℝ) (ρ : Fin m → Mat d),
    IsPureDecomp ω p ρ ∧ x = ∑ k, p k * Stilde (ρ k)}

/-- Entropy of the diagonal algebra relative to the state, equation (4). -/
noncomputable def H {d : ℕ} (ω : Mat d) : ℝ := Stilde ω - R ω

/-- An extremal decomposition attaining the convex roof, equation (7). -/
def IsOptimalDecomp {d m : ℕ} (ω : Mat d) (p : Fin m → ℝ) (ρ : Fin m → Mat d) : Prop :=
  IsPureDecomp ω p ρ ∧ R ω = ∑ k, p k * Stilde (ρ k)

/-- A convex subset of states in which every state has an internal optimal pure decomposition. -/
def IsRSet {d : ℕ} (S : Set (Mat d)) : Prop :=
  Convex ℝ S ∧ (∀ ν ∈ S, IsState ν) ∧
  ∀ ω ∈ S, ∃ (m : ℕ) (p : Fin m → ℝ) (ρ : Fin m → Mat d),
    IsOptimalDecomp ω p ρ ∧ ∀ k, ρ k ∈ S

/-- The affine functional represented by a Hermitian matrix, equation (9). -/
noncomputable def lA {d : ℕ} (A ν : Mat d) : ℝ := (Matrix.trace (ν * A)).re

/-- A Hermitian affine functional below `R` and touching it on at least one state. -/
def SupportsR {d : ℕ} (A : Mat d) : Prop :=
  A.IsHermitian ∧ (∀ ν, IsState ν → lA A ν ≤ R ν) ∧
  ∃ ν, IsState ν ∧ lA A ν = R ν

/-- The contact set of a supporting affine functional, equation (8). -/
def OmegaL {d : ℕ} (A : Mat d) : Set (Mat d) :=
  {ν | IsState ν ∧ R ν = lA A ν}

/-- The intersection of all supporting contact sets touching `ω`, equation (10). -/
def OmegaOf {d : ℕ} (ω : Mat d) : Set (Mat d) :=
  {ν | IsState ν ∧ ∀ A, SupportsR A → lA A ω = R ω → R ν = lA A ν}

/-- A unitary that swaps two minimal projections and fixes the others. -/
def IsTransposition {d : ℕ} (U : Mat d) (i j : Fin d) : Prop :=
  Matrix.conjTranspose U * U = 1 ∧ U * Matrix.conjTranspose U = 1 ∧
  i ≠ j ∧ ∀ k, U * P k * Matrix.conjTranspose U = P (Equiv.swap i j k)

end UhlmannRoof.RankTwo


