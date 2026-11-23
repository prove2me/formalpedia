-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_DSurjDef
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_DSurjDef
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:40.310489+00:00
-- url     : https://prove2.me/theorems/7cae66db-563c-4d21-93bd-a93af5e3bb1f
-- title:
--   DSurj Def
-- statement:
--   Definitions and structural lemmas for DSurj Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountNonIntegrality/DSurjDef.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.CntNotIntW
open scoped TensorProduct
def piMap (K : Type) [Field K] [CharZero K] (ℓ : ℕ) [Fact ℓ.Prime] (Fp : Type) [Field Fp] [CharZero Fp] [Algebra ℚ_[ℓ] Fp] (ι : K →+* Fp) :
    ℚ_[ℓ] ⊗[ℚ] K →ₐ[ℚ_[ℓ]] Fp :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ_[ℓ] Fp) ι.toRatAlgHom (fun _ _ => Commute.all _ _)
def PiSurj : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime] (Fp : Type) [Field Fp] [CharZero Fp] [ValuativeRel Fp]
    [TopologicalSpace Fp] [IsNonarchimedeanLocalField Fp] [Algebra ℚ_[ℓ] Fp],
    Continuous (algebraMap ℚ_[ℓ] Fp) → FiniteDimensional ℚ_[ℓ] Fp → ∀ (ι : K →+* Fp), DenseRange ι →
      Function.Surjective (piMap K ℓ Fp ι)
end PI.CntNotIntW


