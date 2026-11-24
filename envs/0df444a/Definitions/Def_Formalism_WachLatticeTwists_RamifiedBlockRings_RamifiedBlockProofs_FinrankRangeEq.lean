-- Prove2me | Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
-- name    : Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:12.145623+00:00
-- url     : https://prove2.me/theorems/65f7e4e2-7e27-4fdb-8c00-d4c21dac28e9
-- title:
--   Finrank Range Eq
-- statement:
--   Definitions and structural lemmas for Finrank Range Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/WachLatticeTwists/RamifiedBlockRings/RamifiedBlockProofs/FinrankRangeEq.lean

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_RankDiagIte
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_TruncatedSeriesCounting_TruncatedSeriesProofs_BridgeDet
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
section Build
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type}
  (T' : Subalgebra O (X' → O)) {d : Type} [Fintype d] [DecidableEq d] {G : Type} [Group G]
  (rK : G →* (X' → Matrix d d (FractionRing O)))
def scal : T' →+* spanSub T' rK where
  toFun f := ⟨term rK f.1 1, term_mem T' rK f.2 1⟩
  map_one' := Subtype.ext (by funext y; simp [term])
  map_mul' f g := Subtype.ext (by
    show term rK (f.1 * g.1) 1 = term rK f.1 1 * term rK g.1 1
    rw [term_mul, mul_one])
  map_zero' := Subtype.ext (term_zero rK 1)
  map_add' f g := Subtype.ext (term_add rK f.1 g.1 1)
theorem scal_apply (f : T') (y : X') :
    (scal T' rK f).1 y = algebraMap O (FractionRing O) (f.1 y) • (1 : Matrix d d (FractionRing O)) := by
  simp [scal, term]
@[instance_reducible] def algRp : Algebra T' (spanSub T' rK) :=
  RingHom.toAlgebra' (scal T' rK) (fun f a => Subtype.ext (by
    funext y
    show (scal T' rK f).1 y * a.1 y = a.1 y * (scal T' rK f).1 y
    rw [scal_apply]; simp))
@[instance_reducible] def modEvRp (x' : X') : Module T' (EvalSp O d (spanSub T' rK) x') :=
  Module.compHom _ ((algebraMap O (FractionRing O)).comp
    ((Pi.evalRingHom (fun _ : X' => O) x').comp T'.val.toRingHom))
end Build
end Formalism.RepresentationBoundsCohomology.ringDataObjects


