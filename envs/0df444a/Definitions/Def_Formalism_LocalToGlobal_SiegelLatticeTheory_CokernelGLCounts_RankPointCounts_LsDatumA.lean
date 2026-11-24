-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_LsDatumA
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_LsDatumA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:13:10.881409+00:00
-- url     : https://prove2.me/theorems/7bfa079f-99b2-41fa-8f9c-803fb2d2e5f1
-- title:
--   Ls Datum A
-- statement:
--   Definitions and structural lemmas for Ls Datum A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/LsDatumA.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_LinQRawRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel
namespace Formalism.L2.SG.LsDatumA
open Formalism.MainNotions.S.Loc
section Basic
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
theorem perp_anti {S T : Submodule E V} (h : S ≤ T) : H.perp T ≤ H.perp S :=
  fun _ hv x hx => hv x (h hx)
theorem X_le_Xp {r : ℕ} (f : Fin (r + 1) → V) : H.X f ≤ H.Xp f :=
  Submodule.span_mono (Set.range_subset_iff.mpr fun a => ⟨a.castSucc, rfl⟩)
theorem mem_perp_isotropicSpan_of_mem_framePerp {r : ℕ} {f f' : Fin (r + 1) → V} {w : V} (hw : w ∈ H.W0 f f') :
    w ∈ H.perp (H.X f) :=
  perp_anti H ((X_le_Xp H f).trans le_sup_left) hw
theorem mem_perp_isotropicSpan_of_mem_framePerp' {r : ℕ} {f f' : Fin (r + 1) → V} {w : V} (hw : w ∈ H.W0 f f') :
    w ∈ H.perp (H.X f') :=
  perp_anti H ((X_le_Xp H f').trans le_sup_right) hw
end Basic
section Stmt
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
def Lemma0L (M : Model F E) (r : ℕ) : Prop :=
  M.split = none → ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r),
    H.IsGeneric t → ∀ (w : V) (hw : w ∈ H.W0 t.f t.f'),
      (w ∈ t.abelian₂ ↔ (H.mkW t.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩ ∈ H.Lset t.abelian₂ t.f ∧
        H.mkW t.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩ ∈ H.Lset t.abelian₂ t.f'))
end Stmt
end Formalism.L2.SG.LsDatumA


