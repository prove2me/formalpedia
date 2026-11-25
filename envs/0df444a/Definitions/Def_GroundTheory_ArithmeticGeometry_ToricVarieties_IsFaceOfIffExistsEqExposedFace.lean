-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
-- name    : GroundTheory_ArithmeticGeometry_ToricVarieties_IsFaceOfIffExistsEqExposedFace
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:14.421841+00:00
-- url     : https://prove2.me/theorems/f89ff8a6-b37d-4ed6-a958-d14b03560969
-- title:
--   Is Face Of Iff Exists Eq Exposed Face
-- statement:
--   Definitions and structural lemmas for Is Face Of Iff Exists Eq Exposed Face, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/ToricVarieties/IsFaceOfIffExistsEqExposedFace.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_ExistsDualNegOfNotMemHullFinset
import Theorems.Thm_GroundTheory_Arith_Toric_exists_dual_neg_of_not_mem
import Theorems.Thm_GroundTheory_Arith_Toric_exists_dual_neg_of_not_mem_hull_finset
import Theorems.Thm_GroundTheory_Arith_Toric_exists_of_mem_hull_image
import Theorems.Thm_GroundTheory_Arith_Toric_fg_dual
import Theorems.Thm_GroundTheory_Arith_Toric_fg_dual_finset
import Theorems.Thm_GroundTheory_Arith_Toric_mem_hull_insert
import Theorems.Thm_GroundTheory_Arith_Toric_nonneg_of_mem_hull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Arith.Toric
open Module PointedCone
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
def exposedFace (σ : PointedCone 𝕜 V) (u : Dual 𝕜 V) : PointedCone 𝕜 V :=
  σ ⊓ ofSubmodule (LinearMap.ker (u : V →ₗ[𝕜] 𝕜))
@[simp] theorem mem_exposedFace {σ : PointedCone 𝕜 V} {u : Dual 𝕜 V} {x : V} :
    x ∈ exposedFace σ u ↔ x ∈ σ ∧ u x = 0 := by
  simp [exposedFace]
theorem exposedFace_isFaceOf {σ : PointedCone 𝕜 V} {u : Dual 𝕜 V} (hu : ∀ x ∈ σ, 0 ≤ u x) :
    (exposedFace σ u).IsFaceOf σ where
  le := inf_le_left
  mem_of_smul_add_mem := by
    intro x y a hx hy ha h
    rw [mem_exposedFace] at h ⊢
    refine ⟨hx, ?_⟩
    have h2 : a * u x + u y = 0 := by simpa using h.2
    have h3 : a * u x = 0 := by nlinarith [mul_nonneg ha.le (hu x hx), hu y hy]
    exact (mul_eq_zero.1 h3).resolve_left ha.ne'
theorem isFaceOf_eq_hull_filter {F : PointedCone 𝕜 V} (S : Finset V) [DecidablePred (· ∈ F)]
    (hF : F.IsFaceOf (hull 𝕜 (S : Set V))) :
    F = hull 𝕜 ((S.filter (· ∈ F) : Finset V) : Set V) := by
  classical
  apply le_antisymm
  · intro x hxF
    have key : ∀ T : Finset V, T ⊆ S → ∀ x ∈ hull 𝕜 (T : Set V), x ∈ F →
        x ∈ hull 𝕜 ((T.filter (· ∈ F) : Finset V) : Set V) := by
      intro T
      induction T using Finset.induction_on with
      | empty => intro _ x hx _; simpa using hx
      | insert a T haT ih =>
        intro hTS x hx hxF
        have haS : a ∈ S := hTS (Finset.mem_insert_self a T)
        have hTS' : T ⊆ S := (Finset.subset_insert a T).trans hTS
        rw [Finset.coe_insert, mem_hull_insert] at hx
        obtain ⟨c, hc, y, hy, rfl⟩ := hx
        have hyS : y ∈ hull 𝕜 (S : Set V) := Submodule.span_mono (Finset.coe_subset.2 hTS') hy
        have haS' : a ∈ hull 𝕜 (S : Set V) := subset_hull haS
        have hyF : y ∈ F := hF.mem_of_add_mem_right (smul_mem _ hc haS') hyS hxF
        have hmono : hull 𝕜 ((T.filter (· ∈ F) : Finset V) : Set V) ≤
            hull 𝕜 (((insert a T).filter (· ∈ F) : Finset V) : Set V) :=
          Submodule.span_mono
            (Finset.coe_subset.2 (Finset.filter_subset_filter _ (Finset.subset_insert _ _)))
        rcases hc.eq_or_lt with rfl | hc
        · simpa using hmono (ih hTS' y hy hyF)
        · have haF : a ∈ F := hF.mem_of_smul_add_mem haS' hyS hc hxF
          exact add_mem (smul_mem _ hc.le (subset_hull (by simp [haF])))
            (hmono (ih hTS' y hy hyF))
    exact key S le_rfl x (hF.le hxF) hxF
  · rw [Submodule.span_le]
    intro y hy
    exact (Finset.mem_filter.1 hy).2
theorem fg_of_isFaceOf {σ F : PointedCone 𝕜 V} (hσ : σ.FG) (hF : F.IsFaceOf σ) : F.FG := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  exact ⟨_, (isFaceOf_eq_hull_filter S hF).symm⟩
theorem forall_hull_iff (S S' : Finset V) [DecidableEq V] (u : Dual 𝕜 V) :
    (∀ y ∈ ((S ∪ S'.image Neg.neg : Finset V) : Set V), 0 ≤ u y) ↔
      (∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ u x) ∧ (∀ x ∈ hull 𝕜 (S' : Set V), u x ≤ 0) := by
  constructor
  · intro h
    refine ⟨fun x hx => nonneg_of_mem_hull (fun y hy => h y (by simp [hy])) hx, fun x hx => ?_⟩
    have := nonneg_of_mem_hull (f := -u) (s := (S' : Set V))
      (fun y hy => by simpa using h (-y) (by simp [hy])) hx
    simpa using this
  · rintro ⟨h1, h2⟩ y hy
    simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Finset.mem_coe,
      Set.mem_image] at hy
    rcases hy with hy | ⟨z, hz, rfl⟩
    · exact h1 y (subset_hull hy)
    · simpa using h2 z (subset_hull hz)
theorem exists_sub_of_mem_hull_union_neg (S S' : Finset V) [DecidableEq V] {x : V}
    (hx : x ∈ hull 𝕜 ((S ∪ S'.image Neg.neg : Finset V) : Set V)) :
    ∃ a ∈ hull 𝕜 (S : Set V), ∃ b ∈ hull 𝕜 (S' : Set V), x = a - b := by
  rw [Finset.coe_union] at hx
  obtain ⟨a, ha, b', hb', rfl⟩ := Submodule.mem_sup.1 ((Submodule.span_union _ _).le hx)
  have e : ((S'.image Neg.neg : Finset V) : Set V) = (-LinearMap.id : V →ₗ[𝕜] V) '' (S' : Set V) := by
    ext; simp
  rw [e] at hb'
  obtain ⟨b, hb, rfl⟩ := exists_of_mem_hull_image (-LinearMap.id : V →ₗ[𝕜] V) hb'
  exact ⟨a, ha, b, hb, by simp [sub_eq_add_neg]⟩
theorem separation_of_generators (S S' : Finset V) (T : Finset (Dual 𝕜 V))
    (hT : ∀ u : Dual 𝕜 V, u ∈ hull 𝕜 (T : Set (Dual 𝕜 V)) ↔
      (∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ u x) ∧ (∀ x ∈ hull 𝕜 (S' : Set V), u x ≤ 0))
    (h : (hull 𝕜 (S : Set V) ⊓ hull 𝕜 (S' : Set V)).IsFaceOf (hull 𝕜 (S : Set V)))
    (h' : (hull 𝕜 (S : Set V) ⊓ hull 𝕜 (S' : Set V)).IsFaceOf (hull 𝕜 (S' : Set V))) :
    (∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ (∑ t ∈ T, t) x) ∧
      (∀ x ∈ hull 𝕜 (S' : Set V), (∑ t ∈ T, t) x ≤ 0) ∧
      exposedFace (hull 𝕜 (S : Set V)) (∑ t ∈ T, t) = hull 𝕜 (S : Set V) ⊓ hull 𝕜 (S' : Set V) ∧
      exposedFace (hull 𝕜 (S' : Set V)) (∑ t ∈ T, t) =
        hull 𝕜 (S : Set V) ⊓ hull 𝕜 (S' : Set V) := by
  classical
  set σ := hull 𝕜 (S : Set V)
  set σ' := hull 𝕜 (S' : Set V)
  set u : Dual 𝕜 V := ∑ t ∈ T, t with hu_def
  have hTmem : ∀ t ∈ T, (∀ x ∈ σ, 0 ≤ t x) ∧ (∀ x ∈ σ', t x ≤ 0) :=
    fun t ht => (hT t).1 (subset_hull ht)
  have hu : (∀ x ∈ σ, 0 ≤ u x) ∧ (∀ x ∈ σ', u x ≤ 0) :=
    (hT u).1 (Submodule.sum_mem _ fun t ht => subset_hull ht)
  have hu_apply : ∀ x, u x = ∑ t ∈ T, t x := fun x => by simp [hu_def]

  have key : ∀ z : V, z ∉ hull 𝕜 ((S ∪ S'.image Neg.neg : Finset V) : Set V) →
      ∃ t ∈ T, t z < 0 := by
    intro z hz
    obtain ⟨f, hf, hfz⟩ := exists_dual_neg_of_not_mem_hull_finset _ hz
    have hfT : f ∈ hull 𝕜 (T : Set (Dual 𝕜 V)) :=
      (hT f).2 ((forall_hull_iff S S' f).1 (fun y hy => hf y hy))
    by_contra hne
    push Not at hne
    have := nonneg_of_mem_hull (f := Dual.eval 𝕜 V z) (s := (T : Set (Dual 𝕜 V)))
      (fun t ht => by simpa using hne t ht) hfT
    simp at this
    linarith
  have hface : ∀ (C : PointedCone 𝕜 V) (R : Finset V) (u : Dual 𝕜 V), C = hull 𝕜 (R : Set V) →
      (∀ s ∈ R, u s = 0 → s ∈ σ ⊓ σ') → (∀ x ∈ C, 0 ≤ u x) →
      exposedFace C u ≤ σ ⊓ σ' := by
    intro C R u hC hR hCu
    have hE := exposedFace_isFaceOf hCu
    rw [hC] at hE
    rw [hC, isFaceOf_eq_hull_filter R hE, Submodule.span_le]
    intro s hs
    obtain ⟨hsR, hsE⟩ := Finset.mem_filter.1 hs
    exact hR s hsR (mem_exposedFace.1 hsE).2
  have hle : σ ⊓ σ' ≤ exposedFace σ u ⊓ exposedFace σ' u := by
    rintro x ⟨hx, hx'⟩
    have h0 : u x = 0 := le_antisymm (hu.2 x hx') (hu.1 x hx)
    exact ⟨mem_exposedFace.2 ⟨hx, h0⟩, mem_exposedFace.2 ⟨hx', h0⟩⟩
  refine ⟨hu.1, hu.2, le_antisymm ?_ (fun x hx => (hle hx).1),
    le_antisymm ?_ (fun x hx => (hle hx).2)⟩
  · refine hface σ S u rfl (fun s hs hus => ?_) hu.1
    by_contra hsτ
    have hsσ : s ∈ σ := subset_hull hs
    obtain ⟨t, ht, hts⟩ := key (-s) (fun hmem => by
      obtain ⟨a, ha, b, hb, hab⟩ := exists_sub_of_mem_hull_union_neg S S' hmem
      have hb' : b = s + a := by linear_combination (norm := module) hab
      have hbσ : b ∈ σ := hb' ▸ add_mem hsσ ha
      exact hsτ (h.mem_of_add_mem_left hsσ ha (hb' ▸ ⟨hbσ, hb⟩)))
    have hts' : 0 < t s := by simpa using hts
    have : t s ≤ u s := by
      rw [hu_apply]
      exact Finset.single_le_sum (f := fun t : Dual 𝕜 V => t s)
        (fun t ht => (hTmem t ht).1 s hsσ) ht
    linarith
  · have e : exposedFace σ' u = exposedFace σ' (-u) := by ext x; simp
    rw [e]
    refine hface σ' S' (-u) rfl (fun s hs hus => ?_) (fun x hx => by simpa using hu.2 x hx)
    · have hus : u s = 0 := by simpa using hus
      by_contra hsτ
      have hsσ' : s ∈ σ' := subset_hull hs
      obtain ⟨t, ht, hts⟩ := key s (fun hmem => by
        obtain ⟨a, ha, b, hb, hab⟩ := exists_sub_of_mem_hull_union_neg S S' hmem
        have ha' : a = s + b := by linear_combination (norm := module) -hab
        have haσ' : a ∈ σ' := ha' ▸ add_mem hsσ' hb
        exact hsτ (h'.mem_of_add_mem_left hsσ' hb (ha' ▸ ⟨ha, haσ'⟩)))
      have : u s ≤ t s := by
        rw [hu_apply]
        have := Finset.single_le_sum (f := fun t : Dual 𝕜 V => -t s)
          (fun t ht => by simpa using (hTmem t ht).2 s hsσ') ht
        simp only [Finset.sum_neg_distrib] at this
        linarith
      linarith
section FiniteDimensional
variable [FiniteDimensional 𝕜 V]
theorem exists_finset_hull_eq_separating (S S' : Finset V) :
    ∃ T : Finset (Dual 𝕜 V), ∀ u : Dual 𝕜 V, u ∈ hull 𝕜 (T : Set (Dual 𝕜 V)) ↔
      (∀ x ∈ hull 𝕜 (S : Set V), 0 ≤ u x) ∧ (∀ x ∈ hull 𝕜 (S' : Set V), u x ≤ 0) := by
  classical
  obtain ⟨T, hT⟩ := fg_dual_finset (Dual.eval 𝕜 V) (S ∪ S'.image Neg.neg)
  refine ⟨T, fun u => ?_⟩
  rw [← forall_hull_iff S S' u]
  constructor
  · intro h y hy
    have h' : u ∈ dual (Dual.eval 𝕜 V) ((S ∪ S'.image Neg.neg : Finset V) : Set V) := by
      rw [← hT]; exact h
    simpa using h' hy
  · intro h
    have h' : u ∈ dual (Dual.eval 𝕜 V) ((S ∪ S'.image Neg.neg : Finset V) : Set V) :=
      fun y hy => by simpa using h y hy
    rw [← hT] at h'
    exact h'
theorem exists_separating {σ σ' : PointedCone 𝕜 V} (hσ : σ.FG) (hσ' : σ'.FG)
    (h : (σ ⊓ σ').IsFaceOf σ) (h' : (σ ⊓ σ').IsFaceOf σ') :
    ∃ u : Dual 𝕜 V, (∀ x ∈ σ, 0 ≤ u x) ∧ (∀ x ∈ σ', u x ≤ 0) ∧
      exposedFace σ u = σ ⊓ σ' ∧ exposedFace σ' u = σ ⊓ σ' := by
  obtain ⟨S, rfl⟩ := hσ
  obtain ⟨S', rfl⟩ := hσ'
  obtain ⟨T, hT⟩ := exists_finset_hull_eq_separating (𝕜 := 𝕜) S S'
  exact ⟨_, separation_of_generators S S' T hT h h'⟩
theorem isFaceOf_iff_exists_eq_exposedFace {σ F : PointedCone 𝕜 V} (hσ : σ.FG) :
    F.IsFaceOf σ ↔ ∃ u : Dual 𝕜 V, (∀ x ∈ σ, 0 ≤ u x) ∧ F = exposedFace σ u := by
  constructor
  · intro hF
    have hFσ : σ ⊓ F = F := inf_eq_right.2 hF.le
    obtain ⟨u, hu, -, hue, -⟩ := exists_separating hσ (fg_of_isFaceOf hσ hF)
      (by rw [hFσ]; exact hF) (by rw [hFσ])
    exact ⟨u, hu, by rw [hue, hFσ]⟩
  · rintro ⟨u, hu, rfl⟩
    exact exposedFace_isFaceOf hu
omit [FiniteDimensional 𝕜 V] in

theorem dual_id_dual_eval_of_fg {σ : PointedCone 𝕜 V} (hσ : σ.FG) :
    dual (LinearMap.id : Dual 𝕜 V →ₗ[𝕜] Dual 𝕜 V) (dual (Dual.eval 𝕜 V) (σ : Set V) : Set (Dual 𝕜 V))
      = σ := by
  refine le_antisymm (fun x hx => ?_) (fun x hx u hu => by simpa using hu hx)
  by_contra hxσ
  obtain ⟨f, hf, hfx⟩ := exists_dual_neg_of_not_mem hσ hxσ
  have hfd : f ∈ dual (Dual.eval 𝕜 V) (σ : Set V) := fun y hy => by simpa using hf y hy
  have := hx hfd
  simp only [LinearMap.id_apply] at this
  exact this.not_gt hfx
end FiniteDimensional
def dualFace (σ τ : PointedCone 𝕜 V) : PointedCone 𝕜 (Dual 𝕜 V) where
  carrier := {u | (∀ x ∈ σ, 0 ≤ u x) ∧ ∀ x ∈ τ, u x = 0}
  add_mem' := fun {u v} hu hv =>
    ⟨fun x hx => by simpa using add_nonneg (hu.1 x hx) (hv.1 x hx),
      fun x hx => by simp [hu.2 x hx, hv.2 x hx]⟩
  zero_mem' := ⟨fun _ _ => le_rfl, fun _ _ => rfl⟩
  smul_mem' := fun c u hu =>
    ⟨fun x hx => by
        have e : (c • u) x = (c : 𝕜) * u x := rfl
        rw [e]
        exact mul_nonneg c.2 (hu.1 x hx),
      fun x hx => by
        have e : (c • u) x = (c : 𝕜) * u x := rfl
        rw [e, hu.2 x hx, mul_zero]⟩
@[simp] theorem mem_dualFace {σ τ : PointedCone 𝕜 V} {u : Dual 𝕜 V} :
    u ∈ dualFace σ τ ↔ (∀ x ∈ σ, 0 ≤ u x) ∧ ∀ x ∈ τ, u x = 0 := Iff.rfl
def predualFace (σ : PointedCone 𝕜 V) (ν : PointedCone 𝕜 (Dual 𝕜 V)) : PointedCone 𝕜 V where
  carrier := {x | x ∈ σ ∧ ∀ u ∈ ν, u x = 0}
  add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, fun u hu => by simp [hx.2 u hu, hy.2 u hu]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ => map_zero _⟩
  smul_mem' := fun c x hx =>
    ⟨Submodule.smul_mem _ c hx.1, fun u hu => by
      have e : u (c • x) = (c : 𝕜) * u x := by
        change u ((c : 𝕜) • x) = _
        rw [map_smul, smul_eq_mul]
      rw [e, hx.2 u hu, mul_zero]⟩
@[simp] theorem mem_predualFace {σ : PointedCone 𝕜 V} {ν : PointedCone 𝕜 (Dual 𝕜 V)} {x : V} :
    x ∈ predualFace σ ν ↔ x ∈ σ ∧ ∀ u ∈ ν, u x = 0 := Iff.rfl
theorem dualFace_isFaceOf {σ τ : PointedCone 𝕜 V} (hτ : τ ≤ σ) :
    (dualFace σ τ).IsFaceOf (dual (Dual.eval 𝕜 V) (σ : Set V)) where
  le := fun u hu x hx => by simpa using hu.1 x hx
  mem_of_smul_add_mem := by
    intro u v a hu hv ha h
    refine ⟨fun x hx => by simpa using hu hx, fun x hx => ?_⟩
    have h1 : 0 ≤ u x := by simpa using hu (hτ hx)
    have h2 : 0 ≤ v x := by simpa using hv (hτ hx)
    have h3 : a * u x + v x = 0 := by simpa using h.2 x hx
    have h4 : a * u x = 0 := by nlinarith [mul_nonneg ha.le h1]
    exact (mul_eq_zero.1 h4).resolve_left ha.ne'
theorem predualFace_isFaceOf {σ : PointedCone 𝕜 V} {ν : PointedCone 𝕜 (Dual 𝕜 V)}
    (hν : ν ≤ dual (Dual.eval 𝕜 V) (σ : Set V)) : (predualFace σ ν).IsFaceOf σ where
  le := fun x hx => hx.1
  mem_of_smul_add_mem := by
    intro x y a hx hy ha h
    refine ⟨hx, fun u hu => ?_⟩
    have h1 : 0 ≤ u x := by simpa using hν hu hx
    have h2 : 0 ≤ u y := by simpa using hν hu hy
    have h3 : a * u x + u y = 0 := by simpa using h.2 u hu
    have h4 : a * u x = 0 := by nlinarith [mul_nonneg ha.le h1]
    exact (mul_eq_zero.1 h4).resolve_left ha.ne'
theorem dualFace_anti {σ τ₁ τ₂ : PointedCone 𝕜 V} (h : τ₁ ≤ τ₂) :
    dualFace σ τ₂ ≤ dualFace σ τ₁ :=
  fun _ hu => ⟨hu.1, fun x hx => hu.2 x (h hx)⟩
theorem predualFace_anti {σ : PointedCone 𝕜 V} {ν₁ ν₂ : PointedCone 𝕜 (Dual 𝕜 V)} (h : ν₁ ≤ ν₂) :
    predualFace σ ν₂ ≤ predualFace σ ν₁ :=
  fun _ hx => ⟨hx.1, fun u hu => hx.2 u (h hu)⟩
section FiniteDimensional
variable [FiniteDimensional 𝕜 V]
theorem predualFace_dualFace {σ τ : PointedCone 𝕜 V} (hσ : σ.FG) (hτ : τ.IsFaceOf σ) :
    predualFace σ (dualFace σ τ) = τ := by
  obtain ⟨u, hu, rfl⟩ := (isFaceOf_iff_exists_eq_exposedFace hσ).1 hτ
  apply le_antisymm
  · intro x hx
    exact mem_exposedFace.2 ⟨hx.1, hx.2 u ⟨hu, fun y hy => (mem_exposedFace.1 hy).2⟩⟩
  · intro x hx
    exact ⟨(mem_exposedFace.1 hx).1, fun v hv => hv.2 x hx⟩
theorem dualFace_predualFace {σ : PointedCone 𝕜 V} {ν : PointedCone 𝕜 (Dual 𝕜 V)} (hσ : σ.FG)
    (hν : ν.IsFaceOf (dual (Dual.eval 𝕜 V) (σ : Set V))) :
    dualFace σ (predualFace σ ν) = ν := by
  have hσd : (dual (Dual.eval 𝕜 V) (σ : Set V)).FG := fg_dual _ hσ
  obtain ⟨φ, hφ, rfl⟩ := (isFaceOf_iff_exists_eq_exposedFace hσd).1 hν
  set x := (Module.evalEquiv 𝕜 V).symm φ with hx
  have hφx : ∀ u : Dual 𝕜 V, φ u = u x := fun u => by
    rw [hx, Module.apply_evalEquiv_symm_apply]
  have hxσ : x ∈ σ := by
    rw [← dual_id_dual_eval_of_fg hσ]
    intro u hu
    simpa [hφx] using hφ u hu
  apply le_antisymm
  · intro u hu
    refine mem_exposedFace.2 ⟨fun y hy => by simpa using hu.1 y hy, ?_⟩
    rw [hφx]
    exact hu.2 x ⟨hxσ, fun v hv => by simpa [hφx] using (mem_exposedFace.1 hv).2⟩
  · intro u hu
    obtain ⟨hu1, -⟩ := mem_exposedFace.1 hu
    exact ⟨fun y hy => by simpa using hu1 hy, fun y hy => hy.2 u hu⟩
def faceOrderIso {σ : PointedCone 𝕜 V} (hσ : σ.FG) :
    {τ : PointedCone 𝕜 V // τ.IsFaceOf σ} ≃o
      OrderDual {ν : PointedCone 𝕜 (Dual 𝕜 V) // ν.IsFaceOf (dual (Dual.eval 𝕜 V) (σ : Set V))} where
  toFun τ := OrderDual.toDual ⟨dualFace σ τ.1, dualFace_isFaceOf τ.2.le⟩
  invFun ν := ⟨predualFace σ (OrderDual.ofDual ν).1, predualFace_isFaceOf (OrderDual.ofDual ν).2.le⟩
  left_inv τ := Subtype.ext (predualFace_dualFace hσ τ.2)
  right_inv ν := Subtype.ext (dualFace_predualFace hσ (OrderDual.ofDual ν).2)
  map_rel_iff' := by
    intro τ₁ τ₂
    change dualFace σ τ₂.1 ≤ dualFace σ τ₁.1 ↔ τ₁.1 ≤ τ₂.1
    constructor
    · intro h
      have := predualFace_anti (σ := σ) h
      rwa [predualFace_dualFace hσ τ₁.2, predualFace_dualFace hσ τ₂.2] at this
    · exact dualFace_anti
end FiniteDimensional
end GroundTheory.Arith.Toric


