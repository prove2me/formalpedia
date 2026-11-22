-- Prove2me | Definitions.Def_AlgebraicGeometry_Scheme_ProperClosedFiberModels
-- name    : AlgebraicGeometry_Scheme_ProperClosedFiberModels
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T23:18:20.129446+00:00
-- url     : https://prove2.me/theorems/2f0e5f42-dee2-453c-8392-09cb63fa85a3
-- title:
--   Proper Noetherian models of a closed fiber
-- statement:
--   An affine-transition diagram of models of a closed fiber, with the comparison on global idempotents and the lifts to infinitesimal thickenings.

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

noncomputable section

section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace PhilipponSchemeIdempotents

universe u

/-- The characteristic section of a clopen subset is a global idempotent. -/
theorem exists_idempotent_of_clopen (X : Scheme.{u}) {s : Set X} (hs : IsClopen s) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧
      (∀ x ∈ s, X.presheaf.Γgerm x e = 1) ∧
      (∀ x ∉ s, X.presheaf.Γgerm x e = 0) := by
  classical
  let U : Bool → X.Opens := fun i => if i then ⟨s, hs.2⟩ else ⟨sᶜ, hs.1.isOpen_compl⟩
  let a (i : Bool) : Γ(X, U i) := if i then 1 else 0
  let k (i : Bool) : U i ⟶ ⊤ := homOfLE le_top
  have hDisj : ∀ i j : Bool, i ≠ j → U i ⊓ U j = ⊥ := by
    intro i j hij
    cases i <;> cases j <;> simp_all [U]
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    rw [Opens.mem_iSup]
    by_cases hx : x ∈ s
    · exact ⟨true, by simpa [U] using hx⟩
    · exact ⟨false, by simpa [U] using hx⟩
  have hCompatible : TopCat.Presheaf.IsCompatible X.presheaf U a := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · exact (CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty (hDisj i j hij))).elim _ _
  obtain ⟨e, hRes, hUnique⟩ := X.sheaf.existsUnique_gluing' U ⊤ k hcover a hCompatible
  have hRes' (i : Bool) : (X.presheaf.map (k i).op).hom e = a i := hRes i
  have he : IsIdempotentElem e := by
    change e * e = e
    apply hUnique
    intro i
    let g := (X.presheaf.map (k i).op).hom
    calc
      g (e * e) = g e * g e := map_mul g e e
      _ = a i * a i := congrArg (fun z : Γ(X, U i) => z * z) (hRes' i)
      _ = a i := by cases i <;> simp [a]
  have hg (i : Bool) (x : X) (hx : x ∈ U i) :
      X.presheaf.Γgerm x e = X.presheaf.germ (U i) x hx (a i) := by
    rw [← hRes' i]
    exact (X.presheaf.germ_res_apply (k i) x hx e).symm
  refine ⟨e, he, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ U true := by simpa [U] using hx
    simpa only [a, if_true, map_one] using hg true x hx'
  · intro x hx
    have hx' : x ∈ U false := by simpa [U] using hx
    simpa only [a, Bool.false_eq_true, if_false, map_zero] using hg false x hx'

/-- A scheme whose global functions have only trivial idempotents has
preconnected underlying space. -/
theorem preconnectedSpace_of_trivial_idempotents (X : Scheme.{u})
    (h : ∀ e : Γ(X, ⊤), IsIdempotentElem e → e = 0 ∨ e = 1) : PreconnectedSpace X := by
  apply preconnectedSpace_iff_clopen.2
  intro s hs
  obtain ⟨e, he, h1, h0⟩ := exists_idempotent_of_clopen X hs
  rcases h e he with he₀ | he₁
  · left
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    exact zero_ne_one (by simpa only [he₀, map_zero] using h1 x hx)
  · right
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    exact one_ne_zero (by simpa only [he₁, map_one] using h0 x hx)

end PhilipponSchemeIdempotents

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite

namespace PhilipponSchemeIdempotentPullback

universe u

private theorem isOpen_eq_germ {X : Scheme.{u}} (a b : Γ(X, ⊤)) :
    IsOpen {x : X | X.presheaf.Γgerm x a = X.presheaf.Γgerm x b} := by
  apply isOpen_iff_forall_mem_open.2
  intro x hx
  obtain ⟨U, hxU, i, j, he⟩ := X.presheaf.germ_eq x (U := ⊤) (V := ⊤) trivial trivial a b hx
  have hij : j = i := Subsingleton.elim _ _
  subst j
  refine ⟨U, ?_, U.2, hxU⟩
  intro y hy
  exact (X.presheaf.germ_res_apply i y hy a).symm.trans
    ((congrArg (X.presheaf.germ U y hy) he).trans (X.presheaf.germ_res_apply i y hy b))

private theorem germ_eq_zero_or_one {X : Scheme.{u}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e)
    (x : X) : X.presheaf.Γgerm x e = 0 ∨ X.presheaf.Γgerm x e = 1 := by
  let a := X.presheaf.Γgerm x e
  have ha : IsIdempotentElem a := he.map (X.presheaf.Γgerm x).hom
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha)
  · exact Or.inl (sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha.one_sub))

private theorem isClopen_germ_eq_one {X : Scheme.{u}} {e : Γ(X, ⊤)} (he : IsIdempotentElem e) :
    IsClopen {x : X | X.presheaf.Γgerm x e = 1} := by
  refine ⟨?_, by simpa only [map_one] using isOpen_eq_germ e 1⟩
  apply isOpen_compl_iff.mp
  have hCompl : {x : X | X.presheaf.Γgerm x e = 1}ᶜ = {x : X | X.presheaf.Γgerm x e = 0} := by
    ext x
    change X.presheaf.Γgerm x e ≠ 1 ↔ X.presheaf.Γgerm x e = 0
    exact ⟨fun h => (germ_eq_zero_or_one he x).resolve_right h, fun h => h.trans_ne zero_ne_one⟩
  rw [hCompl]
  simpa only [map_zero] using isOpen_eq_germ e 0

private theorem germ_appTop {X Y : Scheme.{u}} (i : X ⟶ Y) (x : X) (a : Γ(Y, ⊤)) :
    X.presheaf.Γgerm x (i.appTop.hom a) = i.stalkMap x (Y.presheaf.Γgerm (i x) a) :=
  (i.germ_stalkMap_apply ⊤ x trivial a).symm

/-- Lifting clopen subsets along a morphism suffices to lift global idempotents. -/
theorem exists_idempotent_lift_of_clopens {X Y : Scheme.{u}} (i : X ⟶ Y)
    (lift : ∀ s : Set X, IsClopen s → ∃ t : Set Y, IsClopen t ∧ i ⁻¹' t = s)
    (e : Γ(X, ⊤)) (he : IsIdempotentElem e) :
    ∃ a : Γ(Y, ⊤), IsIdempotentElem a ∧ i.appTop.hom a = e := by
  let s : Set X := {x | X.presheaf.Γgerm x e = 1}
  obtain ⟨t, ht, hPreimage⟩ := lift s (isClopen_germ_eq_one he)
  obtain ⟨a, ha, h1, h0⟩ := PhilipponSchemeIdempotents.exists_idempotent_of_clopen Y ht
  refine ⟨a, ha, ?_⟩
  apply TopCat.Presheaf.section_ext X.sheaf ⊤
  intro x _
  change X.presheaf.Γgerm x (i.appTop.hom a) = X.presheaf.Γgerm x e
  rw [germ_appTop]
  have hx : i x ∈ t ↔ x ∈ s := by
    change x ∈ i ⁻¹' t ↔ x ∈ s
    rw [hPreimage]
  by_cases hs : x ∈ s
  · rw [h1 _ (hx.mpr hs), map_one]
    exact hs.symm
  · rw [h0 _ (hx.not.mpr hs), map_zero]
    exact ((germ_eq_zero_or_one he x).resolve_right hs).symm

/-- A surjective closed immersion induces a bijection on global idempotents. -/
theorem existsUnique_idempotent_lift {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    [Surjective i] (e : Γ(X, ⊤)) (he : IsIdempotentElem e) :
    ∃! a : Γ(Y, ⊤), IsIdempotentElem a ∧ i.appTop.hom a = e := by
  obtain ⟨a, ha, hl⟩ := exists_idempotent_lift_of_clopens i (fun s hs => by
    let h := i.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective i.surjective
    refine ⟨h.symm ⁻¹' s, hs.preimage h.symm.continuous, ?_⟩
    ext x
    change h.symm (h x) ∈ s ↔ x ∈ s
    rw [h.symm_apply_apply]) e he
  refine ⟨a, ⟨ha, hl⟩, ?_⟩
  intro b ⟨hb, hbRes⟩
  apply TopCat.Presheaf.section_ext Y.sheaf ⊤
  intro y _
  obtain ⟨x, rfl⟩ := i.surjective y
  change Y.presheaf.Γgerm (i x) b = Y.presheaf.Γgerm (i x) a
  have hEq : i.stalkMap x (Y.presheaf.Γgerm (i x) b) = i.stalkMap x (Y.presheaf.Γgerm (i x) a) := by
    rw [← germ_appTop, ← germ_appTop, hbRes, hl]
  rcases germ_eq_zero_or_one hb (i x) with hB | hB <;>
    rcases germ_eq_zero_or_one ha (i x) with hA | hA <;>
    simp_all only [map_zero, map_one, zero_ne_one, one_ne_zero]

end PhilipponSchemeIdempotentPullback

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponClosedFiberThickenings

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

private abbrev q (I : Ideal R) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- The base change of a scheme to a quotient of its affine base. -/
abbrev Fiber (I : Ideal R) := pullback (q I) f

private abbrev factorMap {I J : Ideal R} (h : I ≤ J) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h))

private theorem factorMap_comp {I J : Ideal R} (h : I ≤ J) : factorMap h ≫ q I = q J := by
  rw [← Spec.map_comp]
  congr 1

/-- Transition from the base change along a larger ideal to that along a smaller one. -/
def transition {I J : Ideal R} (h : I ≤ J) : Fiber f J ⟶ Fiber f I :=
  pullback.lift (pullback.fst (q J) f ≫ factorMap h) (pullback.snd (q J) f) (by
    rw [Category.assoc, factorMap_comp, pullback.condition])

@[reassoc (attr := simp)]
theorem transition_fst {I J : Ideal R} (h : I ≤ J) :
    transition f h ≫ pullback.fst (q I) f = pullback.fst (q J) f ≫ factorMap h := by
  simp only [transition, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem transition_snd {I J : Ideal R} (h : I ≤ J) :
    transition f h ≫ pullback.snd (q I) f = pullback.snd (q J) f := by
  simp only [transition, pullback.lift_snd]

theorem transition_comp {I J K : Ideal R} (h : I ≤ J) (k : J ≤ K) :
    transition f k ≫ transition f h = transition f (h.trans k) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, transition_fst, transition_fst_assoc]
    rw [← Category.assoc, Category.assoc (pullback.fst (q K) f)]
    congr 1
    rw [← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (Ideal.Quotient.factor_comp h k)
  · simp only [Category.assoc, transition_snd]

private theorem transition_isPullback {I J : Ideal R} (h : I ≤ J) :
    IsPullback (pullback.fst (q J) f) (transition f h) (factorMap h) (pullback.fst (q I) f) := by
  have hOuter : IsPullback (pullback.fst (q J) f) (transition f h ≫ pullback.snd (q I) f)
      (factorMap h ≫ q I) f := by
    rw [transition_snd, factorMap_comp]
    exact IsPullback.of_hasPullback (q J) f
  exact IsPullback.of_bot hOuter (transition_fst f h).symm (IsPullback.of_hasPullback (q I) f)

instance {I J : Ideal R} (h : I ≤ J) : IsClosedImmersion (transition f h) := by
  apply MorphismProperty.of_isPullback (transition_isPullback f h)
  exact IsClosedImmersion.spec_of_surjective _ (Ideal.Quotient.factor_surjective h)

private theorem surjective_factorMap (I : Ideal R) (n : ℕ) :
    Surjective (factorMap (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n))) := by
  let h : I ^ (n + 1) ≤ I := Ideal.pow_le_self (Nat.succ_ne_zero n)
  constructor
  change Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.factor h))
  rw [← Set.range_eq_univ, range_comap_of_surjective _ _
    (Ideal.Quotient.factor_surjective h), PrimeSpectrum.zeroLocus_eq_univ_iff]
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.factor h (Ideal.Quotient.mk _ a) = 0 at hx
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  exact mem_nilradical.mpr ⟨n + 1, by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hx _⟩

private theorem surjective_thickening (I : Ideal R) (n : ℕ) :
    Surjective (transition f (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n))) :=
  MorphismProperty.of_isPullback (transition_isPullback f _) (surjective_factorMap I n)

theorem surjective_transition_pow (I : Ideal R) {n : ℕ} (hn : n ≠ 0) :
    Surjective (transition f (Ideal.pow_le_self (I := I) hn)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  exact surjective_thickening f I k

/-- Idempotents on the special fiber lift to a compatible system on its infinitesimal thickenings. -/
theorem exists_compatible_idempotents (I : Ideal R) (e : Γ(Fiber f I, ⊤)) (he : IsIdempotentElem e) :
    ∃ a : ∀ n : ℕ, Γ(Fiber f (I ^ (n + 1)), ⊤),
      (∀ n, IsIdempotentElem (a n)) ∧
      (∀ n, (transition f (Ideal.pow_le_self (Nat.succ_ne_zero n))).appTop.hom (a n) = e) ∧
      (∀ {m n : ℕ} (h : m ≤ n),
        (transition f (Ideal.pow_le_pow_right (Nat.succ_le_succ h))).appTop.hom (a n) = a m) := by
  classical
  let i (n : ℕ) := transition f (Ideal.pow_le_self (I := I) (Nat.succ_ne_zero n))
  have hLift (n : ℕ) : ∃! b : Γ(Fiber f (I ^ (n + 1)), ⊤),
      IsIdempotentElem b ∧ (i n).appTop.hom b = e := by
    let : Surjective (i n) := surjective_thickening f I n
    exact PhilipponSchemeIdempotentPullback.existsUnique_idempotent_lift (i n) e he
  choose a ha hu using hLift
  refine ⟨a, fun n => (ha n).1, fun n => (ha n).2, ?_⟩
  intro m n h
  let t := transition f (Ideal.pow_le_pow_right (I := I) (Nat.succ_le_succ h))
  apply hu m _ ⟨(ha n).1.map t.appTop.hom, ?_⟩
  have hComp : i m ≫ t = i n := transition_comp f _ _
  exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop (i m) t).symm (a n)).trans
    ((ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop hComp) (a n)).trans (ha n).2)

end PhilipponClosedFiberThickenings

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponIdempotentLimit

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  (c : Cone D) (hc : IsLimit c)

include hc in
/-- A global idempotent on a cofiltered limit with affine transitions
comes from a global idempotent at a finite stage. -/
theorem exists_appTop_idempotent_eq_of_isLimit (e : Γ(c.pt, ⊤)) (he : IsIdempotentElem e) :
    ∃ (j : I) (b : Γ(D.obj j, ⊤)), IsIdempotentElem b ∧ (c.π.app j).appTop.hom b = e := by
  obtain ⟨i, a, ha⟩ := exists_appTop_π_eq_of_isLimit D c hc e
  have hZero : (c.π.app i).appTop (a * a - a) = 0 := by
    change (c.π.app i).appTop.hom (a * a - a) = 0
    rw [map_sub, map_mul, ← ha, he.eq, sub_self]
  obtain ⟨j, g, hg⟩ := exists_appTop_map_eq_zero_of_isLimit D c hc (a * a - a) hZero
  let b := (D.map g).appTop.hom a
  refine ⟨j, b, ?_, ?_⟩
  · change b * b = b
    change (D.map g).appTop.hom (a * a - a) = 0 at hg
    exact sub_eq_zero.mp (by simpa only [map_sub, map_mul] using hg)
  · have h := congrArg Scheme.Hom.appTop (Cone.w c g)
    rw [Scheme.Hom.comp_appTop] at h
    exact (ConcreteCategory.congr_hom h a).trans ha.symm

include hc in
/-- Idempotent lifting on finite stages gives lifting to the ambient scheme
when each stage of the limit has a compatible ambient model. -/
theorem exists_lift_of_stage_lifts {X : Scheme.{u}} (i : c.pt ⟶ X)
    (Y : I → Scheme.{u}) (j : ∀ k, D.obj k ⟶ Y k) (p : ∀ k, X ⟶ Y k)
    (hp : ∀ k, c.π.app k ≫ j k = i ≫ p k)
    (lift : ∀ (k : I) (b : Γ(D.obj k, ⊤)), IsIdempotentElem b →
      ∃ a : Γ(Y k, ⊤), (j k).appTop.hom a = b)
    (e : Γ(c.pt, ⊤)) (he : IsIdempotentElem e) :
    ∃ a : Γ(X, ⊤), i.appTop.hom a = e := by
  obtain ⟨k, b, hb, hRes⟩ := exists_appTop_idempotent_eq_of_isLimit D c hc e he
  obtain ⟨a, ha⟩ := lift k b hb
  refine ⟨(p k).appTop.hom a, ?_⟩
  have h := congrArg Scheme.Hom.appTop (hp k)
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  exact (ConcreteCategory.congr_hom h a).symm.trans (by rw [CommRingCat.comp_apply, ha, hRes])

end PhilipponIdempotentLimit

end

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponClosedFiberThickenings (Fiber)


namespace PhilipponProperClosedFiberApproximation

universe u

private abbrev closed {A : Type u} [CommRing A] [IsLocalRing A] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A)) :
    Fiber g (IsLocalRing.maximalIdeal A) ⟶ Y :=
  pullback.snd (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g

/-- A model of one stage of a closed-fiber approximation over a Noetherian local ring. -/
structure NoetherianStage {T X Z : Scheme.{u}} (i : T ⟶ X) (π : T ⟶ Z) where
  A : Type u
  [ring : CommRing A]
  [localRing : IsLocalRing A]
  [noetherian : IsNoetherianRing A]
  Y : Scheme.{u}
  g : Y ⟶ Spec (.of A)
  [proper : IsProper g]
  fiber : Z ≅ Fiber g (IsLocalRing.maximalIdeal A)
  ambient : X ⟶ Y
  commutes : π ≫ fiber.hom ≫ closed g = i ≫ ambient

/-- A limit diagram of closed fibers with their proper Noetherian ambient models. -/
structure ClosedFiberModels {T X : Scheme.{u}} (i : T ⟶ X) where
  index : Type u
  [category : Category.{u} index]
  [cofiltered : IsCofiltered index]
  stages : index ⥤ Scheme.{u}
  affine : ∀ {j k : index} (v : j ⟶ k), IsAffineHom (stages.map v)
  compact : ∀ k, CompactSpace (stages.obj k)
  quasiSeparated : ∀ k, QuasiSeparatedSpace (stages.obj k)
  projection : (Functor.const index).obj T ⟶ stages
  limit : IsLimit ⟨T, projection⟩
  model : ∀ k, NoetherianStage i (projection.app k)

/-- Idempotent lifting for proper schemes over Noetherian local rings
extends along a closed-fiber approximation. -/
theorem exists_idempotent_lift {T X : Scheme.{u}} (i : T ⟶ X) (D : ClosedFiberModels i)
    (noetherianLift : ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A)) [IsProper g]
      (e : Γ(Fiber g (IsLocalRing.maximalIdeal A), ⊤)), IsIdempotentElem e →
      ∃ a : Γ(Y, ⊤), (closed g).appTop.hom a = e)
    (e : Γ(T, ⊤)) (he : IsIdempotentElem e) : ∃ b : Γ(X, ⊤), i.appTop.hom b = e := by
  let : Category.{u} D.index := D.category
  let : IsCofiltered D.index := D.cofiltered
  let : ∀ {j k : D.index} (v : j ⟶ k), IsAffineHom (D.stages.map v) := fun v => D.affine v
  let : ∀ k, CompactSpace (D.stages.obj k) := D.compact
  let : ∀ k, QuasiSeparatedSpace (D.stages.obj k) := D.quasiSeparated
  let c : Cone D.stages := ⟨T, D.projection⟩
  apply PhilipponIdempotentLimit.exists_lift_of_stage_lifts D.stages c D.limit i
    (fun k => (D.model k).Y)
    (fun k => (D.model k).fiber.hom ≫ @closed _ (D.model k).ring (D.model k).localRing _ (D.model k).g)
    (fun k => (D.model k).ambient) (fun k => (D.model k).commutes) ?_ e he
  intro k b hb
  let M := D.model k
  let : CommRing M.A := M.ring
  let : IsLocalRing M.A := M.localRing
  let : IsNoetherianRing M.A := M.noetherian
  let : IsProper M.g := M.proper
  obtain ⟨a, ha⟩ := noetherianLift M.g (M.fiber.inv.appTop.hom b) (hb.map M.fiber.inv.appTop.hom)
  refine ⟨a, ?_⟩
  change (M.fiber.hom ≫ closed M.g).appTop.hom a = b
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ha]
  have h : M.fiber.inv.appTop ≫ M.fiber.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  exact ConcreteCategory.congr_hom h b

end PhilipponProperClosedFiberApproximation

end

end


