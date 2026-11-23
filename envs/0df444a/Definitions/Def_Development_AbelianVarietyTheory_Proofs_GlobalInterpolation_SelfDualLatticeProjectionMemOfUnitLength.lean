-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
-- name    : Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SelfDualLatticeProjectionMemOfUnitLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:44.264144+00:00
-- url     : https://prove2.me/theorems/5b6019c7-1572-4f13-9f5e-cb3133e9e545
-- title:
--   Self Dual Lattice Projection Mem Of Unit Length
-- statement:
--   Definitions and structural lemmas for Self Dual Lattice Projection Mem Of Unit Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SelfDualLatticeProjectionMemOfUnitLength.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Theorems.Thm_GlobalTheory_SelfDualLatticeCompare_hR_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal
namespace GlobalTheory.SelfDualLatticeSplit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F))
open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.SelfDualLatticeSplit.hR_add_right (x y z : Fin M → _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.Ev F E v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x (y + z) =
      _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x y + _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ J x z := by
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.hR _root_.Formalism.UG.hform
  simp [mul_add, Finset.sum_add_distrib]
def formAt (x : Fin M → Ev F E v) : (Fin M → Ev F E v) →ₗ[Ev F E v] Ev F E v where
  toFun y := hR (Fv F v) σ J x y
  map_add' := hR_add_right σ J v x
  map_smul' c y := GlobalTheory.SelfDualLatticeCompare.hR_smul_right _ J x y c
def proj (x : Fin M → Ev F E v) (b : Ev F E v) :
    (Fin M → Ev F E v) →ₗ[Ev F E v] (Fin M → Ev F E v) :=
  LinearMap.id - (b • formAt σ J v x).smulRight x
end GlobalTheory.SelfDualLatticeSplit


