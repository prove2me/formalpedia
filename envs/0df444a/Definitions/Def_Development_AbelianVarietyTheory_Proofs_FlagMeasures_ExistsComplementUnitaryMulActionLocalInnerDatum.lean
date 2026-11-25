-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsComplementUnitaryMulActionLocalInnerDatum
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsComplementUnitaryMulActionLocalInnerDatum
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:52:20.187867+00:00
-- url     : https://prove2.me/theorems/bf297518-bc9a-512e-b4e8-e6b2bca6b623
-- title:
--   Exists Complement Unitary Mul Action Local Inner Datum
-- statement:
--   Definitions and structural lemmas for Exists Complement Unitary Mul Action Local Inner Datum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsComplementUnitaryMulActionLocalInnerDatum.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
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
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
noncomputable section
namespace GlobalTheory.InnerDatumAct
open Formalism.MainNotions.S.LocNG
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
def FixesFrame (H : HermSp M V) (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V) : Prop :=
  IsUnitary H g ∧ ∀ b, g (f b) = f b
lemma FixesFrame.symm {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g) :
    FixesFrame H f g.symm := by
  refine ⟨fun x y => ?_, fun b => ?_⟩
  · have := hg.1 (g.symm x) (g.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · rw [LinearEquiv.symm_apply_eq, hg.2 b]
lemma FixesFrame.mem_X {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {v : V} (hv : v ∈ H.X f) : g v ∈ H.X f := by
  have hle : H.X f ≤ (H.X f).comap (g : V →ₗ[E] V) := by
    unfold HermSp.X
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe, hg.2]
    exact Submodule.subset_span ⟨a, rfl⟩
  exact hle hv
lemma FixesFrame.mem_perp {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {v : V} (hv : v ∈ H.perp (H.X f)) : g v ∈ H.perp (H.X f) := by
  show ∀ x ∈ H.X f, H.h (g v) x = 0
  intro x hx
  have hx' := hg.symm.mem_X hx
  have h1 := hg.1 v (g.symm x)
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [h1]
  exact (hv : ∀ x ∈ H.X f, H.h v x = 0) _ hx'
def perpMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g) :
    ↥(H.perp (H.X f)) →ₗ[E] ↥(H.perp (H.X f)) :=
  (g : V →ₗ[E] V).restrict (fun _ hv => hg.mem_perp hv)
def wMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g) : H.Wb f →ₗ[E] H.Wb f :=
  Submodule.mapQ _ _ (perpMap hg) (fun x hx => by
    show ((perpMap hg x : ↥(H.perp (H.X f))) : V) ∈ H.X f
    exact hg.mem_X hx)
lemma wMap_mk {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (x : ↥(H.perp (H.X f))) : wMap hg (H.mkW f x) = H.mkW f ⟨g x, hg.mem_perp x.2⟩ := rfl
lemma mkW_congr {f : Fin (r + 1) → V} {x y : ↥(H.perp (H.X f))} (h : (x : V) = y) :
    H.mkW f x = H.mkW f y := by
  rw [Subtype.ext h]
lemma wMap_of_eq {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {x y : ↥(H.perp (H.X f))} (h : (y : V) = g x) : wMap hg (H.mkW f x) = H.mkW f y := by
  rw [wMap_mk]; exact mkW_congr h.symm
lemma wMap_symm_of_eq {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    {x y : ↥(H.perp (H.X f))} (h : (y : V) = g x) : wMap hg.symm (H.mkW f y) = H.mkW f x := by
  rw [wMap_mk]; apply mkW_congr; simp [h]
lemma wMap_symm_wMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (w : H.Wb f) : wMap hg.symm (wMap hg w) = w := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
  exact (congrArg (wMap hg.symm) (wMap_of_eq hg (y := ⟨g x, hg.mem_perp x.2⟩) rfl)).trans
    (wMap_symm_of_eq hg rfl)
lemma wMap_wMap_symm {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (w : H.Wb f) : wMap hg (wMap hg.symm w) = w := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ w
  have e : (x : V) = g (g.symm x) := by simp
  exact (congrArg (wMap hg) (wMap_symm_of_eq hg (x := ⟨g.symm x, hg.symm.mem_perp x.2⟩) e)).trans
    (wMap_of_eq hg e)
lemma mem_map_wMap {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : FixesFrame H f g)
    (L : Submodule M.L.O (H.Wb f)) (w : H.Wb f) :
    w ∈ L.map ((wMap hg).restrictScalars M.L.O) ↔ wMap hg.symm w ∈ L := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    show wMap hg.symm (wMap hg u) ∈ L
    rw [wMap_symm_wMap]; exact hu
  · intro h
    exact ⟨_, h, wMap_wMap_symm hg w⟩
def InU (P : FPair H r) (g : V ≃ₗ[E] V) : Prop := FixesFrame H P.A.f g ∧ FixesFrame H P.B.f g
lemma isInner_map (Fr : FrameD H r) {g : V ≃ₗ[E] V} (hg : FixesFrame H Fr.f g)
    {L : Submodule M.L.O (H.Wb Fr.f)} (hL : Fr.IsInner L) :
    Fr.IsInner (L.map ((wMap hg).restrictScalars M.L.O)) := by
  obtain ⟨hfg, hdual, xz, hxz, hxzL, hprim⟩ := hL
  have hz : g.symm xz = xz := by
    rw [hxz]; exact hg.symm.2 (Fin.last r)
  refine ⟨hfg.map _, fun x => ?_, xz, hxz, ?_, fun c y hy heq => ?_⟩
  · rw [mem_map_wMap, wMap_mk, hdual]
    constructor
    · intro h y hy
      rw [mem_map_wMap, wMap_mk] at hy
      have h1 := h _ hy
      have h2 := hg.symm.1 x y
      simp only at h1
      rw [h2] at h1
      exact h1
    · intro h y hy
      have hy' : H.mkW Fr.f ⟨g y, hg.mem_perp y.2⟩ ∈ L.map ((wMap hg).restrictScalars M.L.O) := by
        rw [mem_map_wMap, wMap_symm_of_eq hg rfl]; exact hy
      have h1 := h _ hy'
      have h2 := hg.symm.1 x (g y)
      simp only [LinearEquiv.symm_apply_apply] at h2
      show H.h (g.symm x) y ∈ M.L.O
      rw [h2]; exact h1
  · rw [mem_map_wMap, wMap_mk]
    rw [mkW_congr (y := xz) hz]; exact hxzL
  · rw [mem_map_wMap] at hy
    refine hprim c ⟨g.symm y, hg.symm.mem_perp y.2⟩ ?_ ?_
    · rw [← wMap_mk]; exact hy
    · have h3 := congrArg (wMap hg.symm) heq
      rw [LinearMap.map_smul, wMap_mk, wMap_mk, mkW_congr (y := xz) hz] at h3
      exact h3
def act {P : FPair H r} {g : V ≃ₗ[E] V} (hg : InU P g) (d : Datum P) : Datum P where
  L := d.L.map ((wMap hg.1).restrictScalars M.L.O)
  L' := d.L'.map ((wMap hg.2).restrictScalars M.L.O)
  hL := isInner_map P.A hg.1 d.hL
  hL' := isInner_map P.B hg.2 d.hL'
  io := {p | (wMap hg.2.symm p.1, wMap hg.1.symm p.2) ∈ d.io}
  io_L := fun h => by
    ext p
    simp [d.io_L h]
end GlobalTheory.InnerDatumAct


