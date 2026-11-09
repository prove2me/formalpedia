-- Prove2me | Definitions.Def_CliffordCert_Optimal_matrix_model
-- name    : CliffordCert_Optimal_matrix_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:28:50.348112+00:00
-- url     : https://prove2.me/theorems/017b0ff2-f3bb-44e3-a5ad-54a648721598
-- title:
--   Density matrices, Born probabilities and the private-coin model
-- statement:
--   For a finite computational basis $I$, a density matrix is a complex matrix $\rho\succeq0$ with $\operatorname{Tr}\rho=1$. Define
--   $$\|X\|_2^2=\operatorname{Tr}(X^\dagger X),\qquad p_\rho(E)=\operatorname{Tr}(\rho E),\qquad 0\preceq E\preceq I.$$
--   The operator norm uses Euclidean vectors, and the full trace norm is the published Schatten 1 norm. Independent tensor states are entrywise Kronecker products.
--
--   An $m$-sender protocol consists of a fixed labelled list of complex-linear CPTP maps $\Phi_j$ and a collective acceptance effect. Its received state and acceptance probability are
--   $$\bigotimes_{j=1}^m\Phi_j(\rho),\qquad p(\rho)=\operatorname{Tr}\!\left(E\bigotimes_{j=1}^m\Phi_j(\rho)\right).$$
--   Certification requires $p(\sigma)\ge2/3$ and $p(\rho)\le1/3$ for every state with $\|\rho-\sigma\|_1\ge\varepsilon$. A feasible uniform budget means every known reference admits such a protocol with the same integer budget; the protocol may depend on that reference. No success condition is a field of the physical protocol. Private encoder randomization is averaged independently sender by sender, as in §A.2. There is no common seed, entanglement resource, feedback or auxiliary classical transcript.
--
--   This unbundles the general quantum model from the Clifford construction. The Euclidean operator-norm supremum has a nonempty bounded defining set, including the zero vector.
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 9, §A, Eqs. (11)–(15), §A.2 p. 10 (PDF p. 11) (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel
import Definitions.Def_WildeQIT_traceNorm
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal
abbrev Mat (I : Type) := Matrix I I ℂ

abbrev IsState {I : Type} [Fintype I] (ρ : Mat I) : Prop :=
  WildeQIT.IsDensityOperator ρ

def hsSq {I : Type} [Fintype I] (X : Mat I) : ℝ := (Matrix.trace (Xᴴ * X)).re

def hsNorm {I : Type} [Fintype I] (X : Mat I) : ℝ := Real.sqrt (hsSq X)

/-- The Euclidean operator norm; the unit ball is always nonempty and bounded. -/
def opNorm {I : Type} [Fintype I] (X : Mat I) : ℝ :=
  sSup {t | ∃ v : EuclideanSpace ℂ I, ‖v‖ ≤ 1 ∧
    t = ‖WithLp.toLp 2 (Matrix.mulVec X (WithLp.ofLp v))‖}

def born {I : Type} [Fintype I] (ρ E : Mat I) : ℝ := (Matrix.trace (ρ * E)).re

def IsEffect {I : Type} [Fintype I] [DecidableEq I] (E : Mat I) : Prop :=
  E.PosSemidef ∧ (1 - E).PosSemidef

def tensorStates {I : Type} [Fintype I] {m : ℕ} (ρ : Fin m → Mat I) :
    Mat (Fin m → I) := fun a b => ∏ j, ρ j (a j) (b j)

def tensorPower {I : Type} [Fintype I] (ρ : Mat I) (s : ℕ) : Mat (Fin s → I) :=
  tensorStates (fun _ => ρ)

/-- Eq. (15): fixed labelled CPTP encoders and an arbitrary collective binary effect.
    There is no common random seed or transcript in this data. -/
structure Protocol (I J : Type) [Fintype I] [Fintype J] [DecidableEq J] (m : ℕ) where
  encoder : Fin m → (Mat I →ₗ[ℂ] Mat J)
  channel : ∀ j, WildeQIT.EntBreaking.IsQuantumChannel (encoder j)
  effect : Mat (Fin m → J)
  effect_valid : IsEffect effect

def output {I J : Type} [Fintype I] [Fintype J] [DecidableEq J] {m : ℕ}
    (P : Protocol I J m) (ρ : Mat I) : Mat (Fin m → J) :=
  tensorStates (fun j => P.encoder j ρ)

def acceptance {I J : Type} [Fintype I] [Fintype J] [DecidableEq J] {m : ℕ}
    (P : Protocol I J m) (ρ : Mat I) : ℝ := born (output P ρ) P.effect

def Certifies {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {m : ℕ} (P : Protocol I J m) (σ : Mat I) (ε : ℝ) : Prop :=
  (2 / 3 : ℝ) ≤ acceptance P σ ∧
  ∀ ρ, IsState ρ → ε ≤ WildeQIT.traceNorm (ρ - σ) → acceptance P ρ ≤ 1 / 3

/-- A feasible uniform budget allows the schedule and referee to depend on the known reference. -/
def FeasibleBudget (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (ε : ℝ) (m : ℕ) : Prop :=
  ∀ σ : Mat I, IsState σ → ∃ P : Protocol I J m, Certifies P σ ε

/-- A linear superoperator from its matrix-unit coefficients. -/
def fromCoefficients {I J : Type} [Fintype I]
    (K : J → J → I → I → ℂ) : Mat I →ₗ[ℂ] Mat J where
  toFun X u v := ∑ a, ∑ b, K u v a b * X a b
  map_add' X Y := by
    ext u v
    change (∑ a, ∑ b, K u v a b * (X a b + Y a b)) =
      (∑ a, ∑ b, K u v a b * X a b) + (∑ a, ∑ b, K u v a b * Y a b)
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    ext u v
    change (∑ a, ∑ b, K u v a b * (c * X a b)) = c * (∑ a, ∑ b, K u v a b * X a b)
    simp [Finset.mul_sum, mul_left_comm]
end CliffordCert.Optimal


