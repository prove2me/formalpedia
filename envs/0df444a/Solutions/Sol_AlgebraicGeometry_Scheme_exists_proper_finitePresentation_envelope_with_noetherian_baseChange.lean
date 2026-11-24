-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_proper_finitePresentation_envelope_with_noetherian_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T19:50:59.323838+00:00
-- url     : https://prove2.me/submissions/eba08a07-cf13-4adc-9e7b-622ea1a8d5f2

import Definitions.Def_AlgebraicGeometry_SchematicImageLimitIdeal
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_proper_finitePresentation_envelope
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_noetherian_affineModels_of_isProper

noncomputable section

section

section

set_option autoImplicit false

open AlgebraicGeometry

namespace PhilipponNoetherianIdealSheafStabilization

/-- A nonempty directed family of ideal sheaves on a Noetherian scheme attains its supremum. -/
theorem exists_eq_iSup {X : Scheme} [IsNoetherian X] {J : Type*} [Nonempty J]
    (K : J → X.IdealSheafData) (hK : Directed (· ≤ ·) K) :
    ∃ j, (⨆ i, K i) = K j := by
  classical
  let j₀ : J := Classical.choice inferInstance
  have locally (U : X.affineOpens) : ∃ j, ∀ i, (K i).ideal U ≤ (K j).ideal U := by
    let := IsLocallyNoetherian.component_noetherian U
    let I : J → Ideal Γ(X, U) := fun j => (K j).ideal U
    obtain ⟨m, ⟨j, rfl⟩, hm⟩ := (wellFounded_gt (α := Ideal Γ(X, U))).has_min
      (Set.range I) ⟨I j₀, ⟨j₀, rfl⟩⟩
    refine ⟨j, fun i => ?_⟩
    obtain ⟨k, hik, hjk⟩ := hK i j
    have hji : I k ≤ I j := by
      by_contra h
      exact hm (I k) ⟨k, rfl⟩ (lt_of_le_not_ge (hjk U) h)
    exact (hik U).trans hji
  choose j hj using locally
  obtain ⟨s, hs, hcover⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : X.Opens))).mp isCompact_univ
  have bound (t : Finset X.affineOpens) : ∃ i, ∀ U ∈ t, K (j U) ≤ K i := by
    induction t using Finset.induction_on with
    | empty => exact ⟨j₀, by simp⟩
    | @insert U t _ ih =>
        obtain ⟨i, hi⟩ := ih
        obtain ⟨k, hUk, hik⟩ := hK (j U) i
        refine ⟨k, fun V hV => ?_⟩
        rcases Finset.mem_insert.mp hV with rfl | hV
        · exact hUk
        · exact (hi V hV).trans hik
  obtain ⟨i, hi⟩ := bound hs.toFinset
  refine ⟨i, le_antisymm ?_ (le_iSup K i)⟩
  apply Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : s => U.1)
  · rw [iSup_subtype]
    exact hcover.symm
  · intro U
    rw [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    exact iSup_le fun k => (hj U.1 k).trans (hi U.1 (hs.mem_toFinset.mpr U.2) U.1)

end PhilipponNoetherianIdealSheafStabilization

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.IdealSheafData


namespace PhilipponProperSameFiberEnvelope

universe u

private lemma ker_of_isPullback {T S X Y : Scheme.{u}}
    {a : T ⟶ S} {b : T ⟶ X} {c : S ⟶ Y} {d : X ⟶ Y} [IsClosedImmersion d]
    (h : IsPullback a b c d) : a.ker = d.ker.comap c := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso, ker_fst_of_isClosedImmersion]

private lemma directed_stageIdeal {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) {X : Scheme.{u}} (a : X ⟶ c.pt) [QuasiCompact a]
    [∀ {i j : I} (v : i ⟶ j), IsAffineHom (D.map v)] :
    Directed (· ≤ ·) (fun i => (a ≫ c.π.app i).ker.comap (c.π.app i)) := by
  have step {i j : I} (v : i ⟶ j) :
      (a ≫ c.π.app j).ker.comap (c.π.app j) ≤ (a ≫ c.π.app i).ker.comap (c.π.app i) := by
    have he := c.w v
    change c.π.app i ≫ D.map v = c.π.app j at he
    rw [← he, ← Category.assoc, Scheme.Hom.ker_comp, comap_comp]
    exact comap_mono _ (comap_map_le _ _)
  intro i j
  exact ⟨IsCofiltered.min i j, step (IsCofiltered.minToLeft i j), step (IsCofiltered.minToRight i j)⟩

/-- Over a Noetherian test base, a proper scheme agrees with a proper
finitely presented closed envelope on the entire base change. -/
theorem exists_envelope {A : Type u} [CommRing A] {X S T : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (r : S ⟶ Spec (.of A)) [IsNoetherian S]
    (s : T ⟶ S) (j : T ⟶ X) (h : IsPullback s j r f) :
    ∃ (P : Scheme.{u}) (g : P ⟶ Spec (.of A)) (a : X ⟶ P),
      IsProper g ∧ LocallyOfFinitePresentation g ∧ IsClosedImmersion a ∧
        a ≫ g = f ∧ IsPullback s (j ≫ a) r g := by
  obtain ⟨Y, q, b, hq, hfp, hb, hcomp⟩ := Scheme.exists_proper_finitePresentation_envelope f
  let _ := hq
  let _ := hfp
  let _ := hb
  obtain ⟨M⟩ := AlgebraicGeometry.Scheme.nonempty_noetherian_affineModels_of_isProper q
  let : Category.{u} M.index := M.category
  let : IsCofiltered M.index := M.cofiltered
  let : Nonempty M.index := IsCofiltered.nonempty
  let : ∀ i, IsNoetherianRing (M.rings.obj i) := M.noetherian
  let : ∀ i, IsProper (M.maps.app i) := M.proper
  let : ∀ {i k : M.index} (v : i ⟶ k), IsAffineHom (M.ambient.map v) := fun v => M.affine v
  let : ∀ i, QuasiSeparatedSpace (M.ambient.obj i) := fun i => by
    let : QuasiSeparatedSpace ((M.rings.rightOp ⋙ Scheme.Spec).obj i) :=
      inferInstanceAs (QuasiSeparatedSpace (Spec (M.rings.obj (Opposite.op i))))
    exact quasiSeparatedSpace_of_quasiSeparated (M.maps.app i)
  let : ∀ i, IsLocallyNoetherian (M.ambient.obj i) := fun i => by
    let : IsLocallyNoetherian ((M.rings.rightOp ⋙ Scheme.Spec).obj i) :=
      inferInstanceAs (IsLocallyNoetherian (Spec (M.rings.obj (Opposite.op i))))
    exact LocallyOfFiniteType.isLocallyNoetherian (M.maps.app i)
  let c : Cone M.ambient := ⟨Y, M.projection⟩
  let K : M.index → Y.IdealSheafData := fun i => (b ≫ c.π.app i).ker.comap (c.π.app i)
  have hK : (⨆ i, K i) = b.ker := PhilipponImageLimitIdeal.iSup_kernels_eq M.ambientLimit b
  let p : pullback r q ⟶ Y := pullback.snd r q
  let : IsNoetherian (pullback r q) :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (pullback.fst r q) }
  have hdir : Directed (· ≤ ·) (fun i => (K i).comap p) := by
    intro i k
    obtain ⟨l, hi, hk⟩ := directed_stageIdeal M.ambient c b i k
    exact ⟨l, comap_mono _ hi, comap_mono _ hk⟩
  obtain ⟨i, hi⟩ := PhilipponNoetherianIdealSheafStabilization.exists_eq_iSup _ hdir
  have hi' : b.ker.comap p = (K i).comap p := by
    rw [← hK, (map_gc p).l_iSup]
    exact hi
  let I := (b ≫ c.π.app i).ker
  let k := (K i).subschemeι
  let a := IsClosedImmersion.lift k b (by rw [ker_subschemeι, ← hK]; exact le_iSup K i)
  have hak : a ≫ k = b := IsClosedImmersion.lift_fac _ _ _
  let : LocallyOfFinitePresentation k := by
    have hfp' : LocallyOfFinitePresentation ((I.comapIso (c.π.app i)).hom ≫
        pullback.fst (c.π.app i) I.subschemeι) := by
      let : LocallyOfFinitePresentation I.subschemeι := inferInstance
      infer_instance
    rw [comapIso_hom_fst] at hfp'
    exact hfp'
  let : IsClosedImmersion (a ≫ k) := hak.symm ▸ hb
  let : IsClosedImmersion a := IsClosedImmersion.of_comp_isClosedImmersion a k
  let g := k ≫ q
  have hag : a ≫ g = f := by dsimp [g]; rw [← Category.assoc, hak, hcomp]
  let t : T ⟶ pullback r q := pullback.lift s (j ≫ b) (by rw [Category.assoc, hcomp]; exact h.w)
  let t' : T ⟶ pullback r g := pullback.lift s (j ≫ a) (by rw [Category.assoc, hag]; exact h.w)
  let l : pullback r g ⟶ pullback r q := pullback.lift (pullback.fst r g)
    (pullback.snd r g ≫ k) (by rw [Category.assoc]; exact pullback.condition)
  have ht : IsPullback t j p b := by
    apply IsPullback.of_right (h₁₂ := pullback.fst r q) (h₂₂ := q) (v₁₃ := r)
      _ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback r q)
    rw [show t ≫ pullback.fst r q = s from pullback.lift_fst _ _ _, hcomp]
    exact h
  have hl : IsPullback l (pullback.snd r g) p k := by
    apply IsPullback.of_right (h₁₂ := pullback.fst r q) (h₂₂ := q) (v₁₃ := r)
      _ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback r q)
    rw [show l ≫ pullback.fst r q = pullback.fst r g from pullback.lift_fst _ _ _]
    exact IsPullback.of_hasPullback r g
  let : IsClosedImmersion t := MorphismProperty.of_isPullback ht.flip hb
  let : IsClosedImmersion l := MorphismProperty.of_isPullback hl.flip inferInstance
  have htl : t' ≫ l = t := by
    apply pullback.hom_ext
    · simp [l, t', t]
    · simp [l, t', t, hak]
  let : IsIso t' := IsClosedImmersion.isIso_of_ker_eq t l t' htl (by
    rw [ker_of_isPullback ht, ker_of_isPullback hl, ker_subschemeι]
    exact hi')
  refine ⟨_, g, a, inferInstance, inferInstance, inferInstance, hag, ?_⟩
  exact (IsPullback.of_hasPullback r g).of_iso' (asIso t') (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [t']) (by simp [t']) (by simp) (by simp)

end PhilipponProperSameFiberEnvelope

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution {A : Type u} [CommRing A] {X S T : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (r : S ⟶ Spec (.of A)) [IsNoetherian S]
    (s : T ⟶ S) (j : T ⟶ X) (h : IsPullback s j r f) :
    ∃ (P : Scheme.{u}) (g : P ⟶ Spec (.of A)) (a : X ⟶ P),
      IsProper g ∧ LocallyOfFinitePresentation g ∧ IsClosedImmersion a ∧
        a ≫ g = f ∧ IsPullback s (j ≫ a) r g := by
  exact PhilipponProperSameFiberEnvelope.exists_envelope f r s j h

end

end
