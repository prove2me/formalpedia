-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLattices
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramePairCoordinatesTransportInnerLattices
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T13:01:03.311872+00:00
-- url     : https://prove2.me/theorems/e4270196-12ae-4571-aaf5-34ccf8c9b08a
-- title:
--   Frame Pair Coordinates Transport Inner Lattices
-- statement:
--   Definitions and structural lemmas for Frame Pair Coordinates Transport Inner Lattices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/FramePairCoordinatesTransportInnerLattices.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
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
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.CoordInnerSnd
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}
def hl (H : HermSp M V) (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' a b := H.h_add_left a b y
  map_smul' a x := H.h_smul_left a x y
lemma hl_apply (y x : V) : hl H y x = H.h x y := rfl
lemma h_swap_zero {x y : V} (h : H.h x y = 0) : H.h y x = 0 := by
  rw [H.h_herm, h, map_zero]
lemma mem_perp_span (s : Set V) (v : V) :
    v ∈ H.perp (Submodule.span E s) ↔ ∀ x ∈ s, H.h v x = 0 := by
  constructor
  · intro hv x hx; exact hv x (Submodule.subset_span hx)
  · intro hv x hx
    have : Submodule.span E s ≤ LinearMap.ker (hl H v) :=
      Submodule.span_le.2 fun y hy => h_swap_zero (hv y hy)
    exact h_swap_zero (this hx)
variable (Fr : LocNG.FrameD H r)
lemma mem_perpX (v : V) : v ∈ H.perp (H.X Fr.f) ↔ ∀ a, H.h v (Fr.e a) = 0 := by
  unfold HermSp.X
  rw [mem_perp_span]
  simp [LocNG.FrameD.e]
lemma h_ee (a b : Fin r) : H.h (Fr.e a) (Fr.e b) = 0 :=
  Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
lemma h_e_es (a b : Fin r) : H.h (Fr.e a) (Fr.es b) = if a = b then 1 else 0 := Fr.h_es a b
lemma h_es_e (a b : Fin r) : H.h (Fr.es a) (Fr.e b) = if a = b then 1 else 0 := by
  rw [H.h_herm, h_e_es]
  by_cases h : a = b
  · simp [h]
  · simp [h, Ne.symm h]
lemma z_perp : Fr.z ∈ H.perp (H.X Fr.f) :=
  (mem_perpX Fr _).2 fun a => Fr.h_iso _ _ (Or.inr (Fin.castSucc_lt_last a).ne)
noncomputable def prL : V →ₗ[E] V :=
  LinearMap.id - ∑ a, (hl H (Fr.es a)).smulRight (Fr.e a) - ∑ a, (hl H (Fr.e a)).smulRight (Fr.es a)
lemma prL_apply (v : V) : prL Fr v = Fr.prF v := by
  simp [prL, LocNG.FrameD.prF, hl_apply]
lemma h_prF_e (v : V) (b : Fin r) : H.h (Fr.prF v) (Fr.e b) = 0 := by
  rw [← hl_apply]
  simp only [LocNG.FrameD.prF, map_sub, map_sum, map_smul, hl_apply, h_ee, h_es_e]
  simp
lemma prF_perp (v : V) : Fr.prF v ∈ H.perp (H.X Fr.f) := (mem_perpX Fr _).2 (h_prF_e Fr v)
lemma prF_e (a : Fin r) : Fr.prF (Fr.e a) = 0 := by
  simp [LocNG.FrameD.prF, h_ee, h_e_es]
lemma prF_X {v : V} (hv : v ∈ H.X Fr.f) : Fr.prF v = 0 := by
  have : H.X Fr.f ≤ LinearMap.ker (prL Fr) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact (prL_apply Fr _).trans (prF_e Fr a)
  exact (prL_apply Fr v).symm.trans (this hv)
noncomputable def sec : H.Wb Fr.f →ₗ[E] V :=
  Submodule.liftQ _ ((prL Fr).comp (H.perp (H.X Fr.f)).subtype) fun x hx =>
    (prL_apply Fr _).trans (prF_X Fr hx)
noncomputable def pre (L : Submodule M.L.O (H.Wb Fr.f)) : Submodule M.L.O V :=
  (L.comap ((H.mkW Fr.f).restrictScalars M.L.O)).map ((H.perp (H.X Fr.f)).subtype.restrictScalars M.L.O)
section Transport
variable {P : LocNG.FPair H r} {S : Frames M.L r k} (c : Coord P S)
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V)
end Transport
end GlobalTheory.HL.CoordInnerSnd


