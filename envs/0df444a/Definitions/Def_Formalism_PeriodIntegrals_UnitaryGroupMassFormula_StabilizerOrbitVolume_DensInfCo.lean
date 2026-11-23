-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfCo
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfCo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:06:39.253838+00:00
-- url     : https://prove2.me/theorems/98113ab3-0634-4625-83c4-f8d7cc8439f4
-- title:
--   Dens Inf Co
-- statement:
--   Definitions and structural lemmas for Dens Inf Co, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DensInfCo.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensInfTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW Topology
open scoped TensorProduct
open PI.AdicCompletionValuation
def QuadCoord : Prop :=
  ∀ (V H : Type) [AddCommGroup V] [TopologicalSpace V] [AddCommGroup H] [TopologicalSpace H]
    (n m : ℕ) (eV : V ≃ₜ (Fin n → ℝ)) (eH : H ≃ₜ (Fin m → ℝ)) (Q : V → H) (β : V → V → H),
    (∀ x y, eV (x + y) = eV x + eV y) → (∀ x y, eH (x + y) = eH x + eH y) →
    Continuous (fun p : V × V => β p.1 p.2) → (∀ x y z, β (x + y) z = β x z + β y z) →
    (∀ x y, β x y = β y x) → (∀ x, β x x = Q x + Q x) →
    ContDiff ℝ 1 (fun y => eH (Q (eV.symm y))) ∧
      ∀ x y, fderiv ℝ (fun y => eH (Q (eV.symm y))) (eV x) (eV y) = eH (β x y)
section B
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
def gramB (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X Y : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin n) (Fin n) (R ⊗[F] E) :=
  fun i j => hR R σ J (X i) (Y j) + hR R σ J (Y i) (X j)
end B
section BTop
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]
end BTop
def TensR : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∃ (n m : ℕ) (eV : (Fin a → Fin M → Ainf F ⊗[F] E) ≃ₜ (Fin n → ℝ))
    (eH : HermR (Ainf F) σ a ≃ₜ (Fin m → ℝ)),
    (∀ x y, eV (x + y) = eV x + eV y) ∧ ∀ x y, eH (x + y) = eH x + eH y
def FreeSurj : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ X : Fin a → Fin M → Ainf F ⊗[F] E, LinearIndependent (Ainf F ⊗[F] E) X →
    ∀ S : HermR (Ainf F) σ a, ∃ Y, gramB (Ainf F) σ J X Y = S
end PI.VolStabSW


