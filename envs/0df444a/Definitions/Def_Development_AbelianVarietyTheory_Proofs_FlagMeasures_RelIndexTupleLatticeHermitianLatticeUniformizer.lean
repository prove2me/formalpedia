-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizer
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizer
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:53:04.501425+00:00
-- url     : https://prove2.me/theorems/690dfbd9-5a64-469f-9626-f4bda68bd610
-- title:
--   Rel Index Tuple Lattice Hermitian Lattice Uniformizer
-- statement:
--   Definitions and structural lemmas for Rel Index Tuple Lattice Hermitian Lattice Uniformizer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/RelIndexTupleLatticeHermitianLatticeUniformizer.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.LatCard
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
noncomputable def hermOf (L : LocE F E) (m : ℕ) :
    ((Fin m → 𝒪[F]) × ({p : Fin m × Fin m // p.1 < p.2} → L.O)) →+ Matrix (Fin m) (Fin m) E where
  toFun x := Matrix.of fun a b =>
    if h : a < b then (x.2 ⟨(a, b), h⟩ : E)
    else if h' : b < a then L.cj (x.2 ⟨(b, a), h'⟩ : E) else algebraMap F E (x.1 a : F)
  map_zero' := by
    ext a b
    simp
  map_add' x y := by
    ext a b
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp
noncomputable def tupOf (L : LocE F E) {n : ℕ} (b : Fin n → Fin n → E) (m : ℕ) :
    (Fin m → Fin n → L.O) →+ (Fin m → Fin n → E) where
  toFun x := fun a => ∑ i, (x a i : E) • b i
  map_zero' := by
    ext a
    simp
  map_add' x y := by
    funext a
    simp [add_smul, Finset.sum_add_distrib]
end GlobalTheory.HL.LatCard


