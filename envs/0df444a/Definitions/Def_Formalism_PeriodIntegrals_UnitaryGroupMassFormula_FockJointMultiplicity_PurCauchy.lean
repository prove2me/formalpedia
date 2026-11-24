-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurCauchy
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:17.141475+00:00
-- url     : https://prove2.me/theorems/8a84d9ac-d91c-4043-87ec-07418599da39
-- title:
--   Pur Cauchy
-- statement:
--   Definitions and structural lemmas for Pur Cauchy, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/PurCauchy.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
namespace PI.FJMB
def HypAnti : Prop := ∀ (σ : Type) (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι →
  ∀ (α : Fin m → ℕ) (P : MvPolynomial σ ℂ), P ≠ 0 → (∀ a b : Fin m, a < b → PI.FJM.bRow ι a b P = 0) →
  (∀ e ∈ P.support, ∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) → Antitone α
def HypShape : Prop := ∀ (σ : Type) (m : ℕ) (ι : Fin m × Fin m → σ), Function.Injective ι →
  ∀ (α : Fin m → ℕ), Antitone α →
  HWB ι (PI.FJM.shapeProd (Matrix.of fun (i : Fin m) (k : Fin m) => (X (ι (i, k)) : MvPolynomial σ ℂ))
    (List.ofFn α)) ∧
  aeval (killS (offD ι)) (PI.FJM.shapeProd (Matrix.of fun (i : Fin m) (k : Fin m) =>
    (X (ι (i, k)) : MvPolynomial σ ℂ)) (List.ofFn α)) = ∏ i, X (ι (i, i)) ^ α i
def diagOne' {σ : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) : σ → MvPolynomial σ ℂ := fun v =>
  if v ∈ offD ι then 0 else if ∃ i k, ι (i, k) = v ∧ (i : ℕ) = k then 1 else X v
def HypDiag : Prop := ∀ (σ : Type) (m : ℕ) (ι : Fin m × Fin m → σ), Function.Injective ι →
  ∀ (α : Fin m → ℕ) (P : MvPolynomial σ ℂ), (∀ e ∈ P.support, ∀ i, ∑ k : Fin m, e (ι (i, k)) = α i) →
  aeval (killS (offD ι)) P = (∏ i, X (ι (i, i)) ^ α i) * aeval (diagOne' ι) P
def HypFree : Prop := ∀ (σ : Type) (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι →
  ∀ P : MvPolynomial σ ℂ, ∀ e ∈ (aeval (diagOne' ι) P).support, ∀ x, e (ι x) = 0
variable {σ : Type*}
end PI.FJMB


