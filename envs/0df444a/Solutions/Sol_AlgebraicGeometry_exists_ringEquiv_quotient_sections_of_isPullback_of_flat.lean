-- Prove2me | solution 1 for AlgebraicGeometry.exists_ringEquiv_quotient_sections_of_isPullback_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/fb4772c0-f221-5e28-99e1-1c1ba018763d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_quotient_sections_of_isPullback_of_flat

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace W2C2

section LimSys

variable {M : ℕ → Type} [∀ n : ℕ, CommRing (M n)] (r : ∀ n : ℕ, M (n + 1) →+* M n)

def limSubring : Subring (∀ n : ℕ, M n) where
  carrier := {f | ∀ n : ℕ, r n (f (n + 1)) = f n}
  mul_mem' {f g} hf hg n := by simp only [Pi.mul_apply, map_mul, hf n, hg n]
  one_mem' n := by simp only [Pi.one_apply, map_one]
  add_mem' {f g} hf hg n := by simp only [Pi.add_apply, map_add, hf n, hg n]
  zero_mem' n := by simp only [Pi.zero_apply, map_zero]
  neg_mem' {f} hf n := by simp only [Pi.neg_apply, map_neg, hf n]

variable {r}

theorem limSubring_pow_mul_apply (x f : ↥(limSubring r)) (e i : ℕ) : (x ^ e * f).1 i = (x.1 i) ^ e * f.1 i := rfl

theorem limSubring_map_pow_mul (x : ↥(limSubring r)) (i e : ℕ) (y : M (i + 1)) :
    r i ((x.1 (i + 1)) ^ e * y) = (x.1 i) ^ e * r i y := by
  rw [map_mul, map_pow, x.2 i]

theorem limSubring_apply_eq_zero_of_le (h : ↥(limSubring r)) :
    ∀ (i j : ℕ), j ≤ i → h.1 i = 0 → h.1 j = 0 := by
  intro i
  induction i with
  | zero => intro j hj hi; obtain rfl := Nat.le_zero.1 hj; exact hi
  | succ i ih =>
    intro j hj hi
    rcases Nat.le_or_eq_of_le_succ hj with hle | rfl
    · exact ih j hle (by rw [← h.2 i, hi, map_zero])
    · exact hi

theorem limSubring_dvd_apply_of_le (x h : ↥(limSubring r)) (e : ℕ) :
    ∀ (i j : ℕ), j ≤ i → (∃ t, h.1 i = (x.1 i) ^ e * t) → ∃ t, h.1 j = (x.1 j) ^ e * t := by
  intro i
  induction i with
  | zero => intro j hj hi; obtain rfl := Nat.le_zero.1 hj; exact hi
  | succ i ih =>
    intro j hj hi
    rcases Nat.le_or_eq_of_le_succ hj with hle | rfl
    · obtain ⟨t, ht⟩ := hi
      exact ih j hle ⟨r i t, by rw [← h.2 i, ht, limSubring_map_pow_mul]⟩
    · exact hi

theorem limSubring_exists_apply_zero_eq (surj : ∀ n : ℕ, Function.Surjective (r n)) (y : M 0) :
    ∃ f : ↥(limSubring r), f.1 0 = y := by
  classical
  let lam : ∀ m : ℕ, M m → M (m + 1) := fun m => Function.surjInv (surj m)
  refine ⟨⟨fun m => Nat.rec (motive := fun m => M m) y (fun m z => lam m z) m, fun m => ?_⟩, rfl⟩
  exact Function.surjInv_eq (surj m) _

theorem limSubring_exists_apply_sub_eq_mul (x : ↥(limSubring r)) (surj : ∀ n : ℕ, Function.Surjective (r n))
    (ker : ∀ (n : ℕ) (y : M (n + 1)), r n y = 0 → ∃ z, y = (x.1 (n + 1)) ^ (n + 1) * z) :
    ∀ (N : ℕ) (y : M N), ∃ f : ↥(limSubring r), ∃ t : M N, f.1 N - y = x.1 N * t := by
  intro N
  induction N with
  | zero =>
    intro y; obtain ⟨f, hf⟩ := limSubring_exists_apply_zero_eq surj y; exact ⟨f, 0, by rw [hf, sub_self, mul_zero]⟩
  | succ N ih =>
    intro y
    obtain ⟨f, w, hw⟩ := ih (r N y)
    obtain ⟨w', rfl⟩ := surj N w
    obtain ⟨t, ht⟩ := ker N (f.1 (N + 1) - y - x.1 (N + 1) * w') (by
      rw [map_sub, map_sub, map_mul, x.2 N, f.2 N, hw, sub_self])
    refine ⟨f, w' + (x.1 (N + 1)) ^ N * t, ?_⟩
    linear_combination ht

theorem limSubring_exists_apply_eq (x : ↥(limSubring r)) (surj : ∀ n : ℕ, Function.Surjective (r n))
    (ker : ∀ (n : ℕ) (y : M (n + 1)), r n y = 0 → ∃ z, y = (x.1 (n + 1)) ^ (n + 1) * z)
    (nil : ∀ n : ℕ, (x.1 n) ^ (n + 1) = 0) :
    ∀ (N : ℕ) (y : M N), ∃ f : ↥(limSubring r), f.1 N = y := by
  intro N
  induction N with
  | zero => exact limSubring_exists_apply_zero_eq surj
  | succ N ih =>
    intro y
    obtain ⟨f, hf⟩ := ih (r N y)
    obtain ⟨z, hz⟩ := ker N (y - f.1 (N + 1)) (by rw [map_sub, f.2 N, hf, sub_self])
    obtain ⟨g, t, hg⟩ := limSubring_exists_apply_sub_eq_mul x surj ker (N + 1) z
    refine ⟨f + x ^ (N + 1) * g, ?_⟩
    show f.1 (N + 1) + (x ^ (N + 1) * g).1 (N + 1) = y
    rw [limSubring_pow_mul_apply]
    linear_combination (-1 : M (N + 1)) * hz + (x.1 (N + 1)) ^ (N + 1) * hg + t * nil (N + 1)

theorem limSubring_exists_eq_pow_mul (x : ↥(limSubring r)) (surj : ∀ n : ℕ, Function.Surjective (r n))
    (ker : ∀ (n : ℕ) (y : M (n + 1)), r n y = 0 → ∃ z, y = (x.1 (n + 1)) ^ (n + 1) * z)
    (nil : ∀ n : ℕ, (x.1 n) ^ (n + 1) = 0)
    (tors : ∀ (m j : ℕ), j ≤ m + 1 → ∀ y : M m, (x.1 m) ^ j * y = 0 → ∃ z, y = (x.1 m) ^ (m + 1 - j) * z)
    (n : ℕ) (f : ↥(limSubring r)) (hfn : f.1 n = 0) : ∃ g : ↥(limSubring r), f = x ^ (n + 1) * g := by
  classical

  have hZ : ∀ i : ℕ, ∃ w : M i, f.1 i = (x.1 i) ^ (n + 1) * w := by
    intro i
    induction i with
    | zero => exact ⟨0, by rw [limSubring_apply_eq_zero_of_le f n 0 (Nat.zero_le n) hfn, mul_zero]⟩
    | succ i ih =>
      by_cases hi : i + 1 ≤ n
      · exact ⟨0, by rw [limSubring_apply_eq_zero_of_le f n (i + 1) hi hfn, mul_zero]⟩
      · obtain ⟨w, hw⟩ := ih
        obtain ⟨w', rfl⟩ := surj i w
        obtain ⟨t, ht⟩ := ker i (f.1 (i + 1) - (x.1 (i + 1)) ^ (n + 1) * w') (by
          rw [map_sub, limSubring_map_pow_mul, f.2 i, hw, sub_self])
        refine ⟨w' + (x.1 (i + 1)) ^ (i - n) * t, ?_⟩
        have hpow : (x.1 (i + 1)) ^ (i + 1) = (x.1 (i + 1)) ^ (n + 1) * (x.1 (i + 1)) ^ (i - n) := by
          rw [← pow_add]; congr 1; omega
        linear_combination ht + t * hpow
  choose w hw using hZ
  choose Gf hGf using fun i => limSubring_exists_apply_eq x surj ker nil i (w i)

  have hvan : ∀ (i j : ℕ), j ≤ i → (x ^ (n + 1) * Gf i - f).1 j = 0 := by
    intro i j hij
    refine limSubring_apply_eq_zero_of_le _ i j hij ?_
    show (x ^ (n + 1) * Gf i).1 i - f.1 i = 0
    rw [limSubring_pow_mul_apply, hGf, ← hw, sub_self]

  have hgcomp : ∀ m : ℕ, (Gf (m + 1 + n + 1)).1 m = (Gf (m + n + 1)).1 m := by
    intro m
    have e1 : (x ^ (n + 1) * Gf (m + 1 + n + 1)).1 (m + n + 1) - f.1 (m + n + 1) = 0 :=
      hvan (m + 1 + n + 1) (m + n + 1) (by omega)
    have e2 : (x ^ (n + 1) * Gf (m + n + 1)).1 (m + n + 1) - f.1 (m + n + 1) = 0 :=
      hvan (m + n + 1) (m + n + 1) le_rfl
    rw [limSubring_pow_mul_apply] at e1 e2
    have hdiff : (x.1 (m + n + 1)) ^ (n + 1) * ((Gf (m + 1 + n + 1)).1 (m + n + 1) - (Gf (m + n + 1)).1 (m + n + 1)) = 0 := by
      linear_combination e1 - e2
    obtain ⟨t, ht⟩ := tors (m + n + 1) (n + 1) (by omega) _ hdiff
    rw [show m + n + 1 + 1 - (n + 1) = m + 1 by omega] at ht
    have ht0 : (Gf (m + 1 + n + 1) - Gf (m + n + 1)).1 (m + n + 1) = (x.1 (m + n + 1)) ^ (m + 1) * t := ht
    obtain ⟨t', ht'⟩ := limSubring_dvd_apply_of_le x (Gf (m + 1 + n + 1) - Gf (m + n + 1)) (m + 1) (m + n + 1) m (by omega) ⟨t, ht0⟩
    rw [nil, zero_mul] at ht'
    have : (Gf (m + 1 + n + 1)).1 m - (Gf (m + n + 1)).1 m = 0 := ht'
    exact sub_eq_zero.1 this
  let g : ↥(limSubring r) := ⟨fun m => (Gf (m + n + 1)).1 m, fun m => by
    show r m ((Gf (m + 1 + n + 1)).1 (m + 1)) = (Gf (m + n + 1)).1 m
    rw [(Gf (m + 1 + n + 1)).2 m, hgcomp]⟩
  refine ⟨g, Subtype.ext (funext fun m => ?_)⟩
  show f.1 m = (x ^ (n + 1) * g).1 m
  rw [limSubring_pow_mul_apply]
  have e : (x ^ (n + 1) * Gf (m + n + 1)).1 m - f.1 m = 0 := hvan (m + n + 1) m (by omega)
  rw [limSubring_pow_mul_apply] at e
  exact (sub_eq_zero.1 e).symm

theorem limSubring_exists_levelEquiv (x : ↥(limSubring r)) (surj : ∀ n : ℕ, Function.Surjective (r n))
    (ker : ∀ (n : ℕ) (y : M (n + 1)), r n y = 0 → ∃ z, y = (x.1 (n + 1)) ^ (n + 1) * z)
    (nil : ∀ n : ℕ, (x.1 n) ^ (n + 1) = 0)
    (tors : ∀ (m j : ℕ), j ≤ m + 1 → ∀ y : M m, (x.1 m) ^ j * y = 0 → ∃ z, y = (x.1 m) ^ (m + 1 - j) * z)
    (n : ℕ) : ∃ e : (↥(limSubring r) ⧸ Ideal.span {x ^ (n + 1)}) ≃+* M n,
      ∀ f : ↥(limSubring r), e (Ideal.Quotient.mk _ f) = f.1 n := by
  classical
  let p : ↥(limSubring r) →+* M n := (Pi.evalRingHom M n).comp (limSubring r).subtype
  have hp : ∀ f : ↥(limSubring r), p f = f.1 n := fun f => rfl
  have hpsurj : Function.Surjective p := fun y => by
    obtain ⟨f, hf⟩ := limSubring_exists_apply_eq x surj ker nil n y; exact ⟨f, hf⟩
  have hpker : RingHom.ker p = Ideal.span {x ^ (n + 1)} := by
    ext f
    rw [RingHom.mem_ker, hp, Ideal.mem_span_singleton]
    constructor
    · intro hf; obtain ⟨g, hg⟩ := limSubring_exists_eq_pow_mul x surj ker nil tors n f hf; exact ⟨g, hg⟩
    · rintro ⟨g, rfl⟩; rw [limSubring_pow_mul_apply, nil, zero_mul]
  refine ⟨(Ideal.quotEquivOfEq hpker.symm).trans (RingHom.quotientKerEquivOfSurjective hpsurj), fun f => ?_⟩
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk, hp]

theorem limSubring_mem_pow_smul_top_iff (x : ↥(limSubring r)) (k : ℕ) (f : ↥(limSubring r)) :
    f ∈ (Ideal.span {x} ^ k • ⊤ : Submodule ↥(limSubring r) ↥(limSubring r)) ↔ ∃ g : ↥(limSubring r), f = x ^ k * g := by
  rw [Ideal.span_singleton_pow, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]; rfl

theorem limSubring_isAdicComplete (x : ↥(limSubring r)) (surj : ∀ n : ℕ, Function.Surjective (r n))
    (ker : ∀ (n : ℕ) (y : M (n + 1)), r n y = 0 → ∃ z, y = (x.1 (n + 1)) ^ (n + 1) * z)
    (nil : ∀ n : ℕ, (x.1 n) ^ (n + 1) = 0)
    (tors : ∀ (m j : ℕ), j ≤ m + 1 → ∀ y : M m, (x.1 m) ^ j * y = 0 → ∃ z, y = (x.1 m) ^ (m + 1 - j) * z) :
    IsAdicComplete (Ideal.span {x}) ↥(limSubring r) := by
  refine { haus' := fun f hf => ?_, prec' := fun f hf => ?_ }
  ·
    apply Subtype.ext; funext m
    obtain ⟨g, hg⟩ := (limSubring_mem_pow_smul_top_iff x (m + 1) f).1 (by simpa only [SModEq.sub_mem, sub_zero] using hf (m + 1))
    show f.1 m = 0
    rw [hg, limSubring_pow_mul_apply, nil, zero_mul]
  ·
    have hdf : ∀ m : ℕ, ∃ g : ↥(limSubring r), f m - f (m + 1) = x ^ m * g :=
      fun m => (limSubring_mem_pow_smul_top_iff x m _).1 (SModEq.sub_mem.1 (hf (Nat.le_succ m)))
    let L : ↥(limSubring r) := ⟨fun m => (f (m + 1)).1 m, fun m => by
      show r m ((f (m + 1 + 1)).1 (m + 1)) = (f (m + 1)).1 m
      rw [(f (m + 1 + 1)).2 m]
      obtain ⟨g, hg⟩ := hdf (m + 1)
      have e : (f (m + 1)).1 m - (f (m + 1 + 1)).1 m = (x ^ (m + 1) * g).1 m := congrArg (fun q : ↥(limSubring r) => q.1 m) hg
      rw [limSubring_pow_mul_apply, nil, zero_mul, sub_eq_zero] at e
      exact e.symm⟩
    refine ⟨L, fun k => ?_⟩
    rw [SModEq.sub_mem, limSubring_mem_pow_smul_top_iff]
    cases k with
    | zero => exact ⟨f 0 - L, by rw [pow_zero, one_mul]⟩
    | succ n =>
      exact limSubring_exists_eq_pow_mul x surj ker nil tors n (f (n + 1) - L)
        (show (f (n + 1)).1 n - (f (n + 1)).1 n = 0 from sub_self _)

end LimSys

section L1

open CategoryTheory.Limits

universe u

theorem isPushout_appTop_of_isPullback {P X Y Z : Scheme.{u}} [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine Z]
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (H : IsPullback fst snd f g) :
    IsPushout g.appTop f.appTop snd.appTop fst.appTop := by
  haveI : ∀ i : WalkingCospan, IsAffine ((cospan f g).obj i) := fun i => by
    rcases i with _ | _ | _
    · change IsAffine Z; infer_instance
    · change IsAffine X; infer_instance
    · change IsAffine Y; infer_instance
  have H' := H.map Scheme.Γ.rightOp
  exact H'.unop

theorem isPushout_appLE_of_isPullback {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
    (H : IsPullback g iY iX f)
    {US : S.Opens} (hUS : IsAffineOpen US) {UT : T.Opens} (hUT : IsAffineOpen UT)
    {UX : X.Opens} (hUX : IsAffineOpen UX) {UY : Y.Opens} (hUY' : IsAffineOpen UY)
    (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US) (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT)
    (eg : UY ≤ g ⁻¹ᵁ UX) (eY : UY ≤ iY ⁻¹ᵁ UT) :
    IsPushout (f.appLE US UT hUST) (iX.appLE US UX hUSX) (iY.appLE UT UY eY) (g.appLE UX UY eg) := by
  have H1 := Scheme.Hom.isPullback_resLE H hUST hUSX hUY
  haveI : IsAffine (US : Scheme.{u}) := hUS
  haveI : IsAffine (UT : Scheme.{u}) := hUT
  haveI : IsAffine (UX : Scheme.{u}) := hUX
  haveI : IsAffine (UY : Scheme.{u}) := hUY'
  have H2 := isPushout_appTop_of_isPullback H1
  refine H2.of_iso US.topIso UT.topIso UX.topIso UY.topIso ?_ ?_ ?_ ?_
  all_goals
    dsimp only [Scheme.Hom.appTop]
    rw [Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem surjective_and_ker_eq_of_isPushout {R S A B : CommRingCat.{u}} {f : R ⟶ S} {g : R ⟶ A} {inl : S ⟶ B} {inr : A ⟶ B}
    (h : IsPushout f g inl inr) (hf : Function.Surjective f.hom) :
    Function.Surjective inr.hom ∧ RingHom.ker inr.hom = (RingHom.ker f.hom).map g.hom := by
  classical
  set I : Ideal A := (RingHom.ker f.hom).map g.hom with hIdef
  have hw : ∀ r : R, inl.hom (f.hom r) = inr.hom (g.hom r) := fun r => by
    have := congrArg (fun k => k.hom r) h.w
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have hI : ∀ a ∈ I, inr.hom a = 0 := by
    have : I ≤ RingHom.ker inr.hom := by
      rw [hIdef, Ideal.map_le_iff_le_comap]
      intro r hr
      rw [RingHom.mem_ker] at hr
      rw [Ideal.mem_comap, RingHom.mem_ker, ← hw, hr, map_zero]
    exact fun a ha => this ha

  let v : A ⧸ I →+* B := Ideal.Quotient.lift I inr.hom hI

  let r₀ : R →+* A ⧸ I := (Ideal.Quotient.mk I).comp g.hom
  have hr₀ : ∀ x ∈ RingHom.ker f.hom, r₀ x = 0 := fun x hx => by
    show Ideal.Quotient.mk I (g.hom x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hIdef]
    exact Ideal.mem_map_of_mem _ hx
  let r : S →+* A ⧸ I :=
    (Ideal.Quotient.lift (RingHom.ker f.hom) r₀ hr₀).comp (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom
  have hr : ∀ x : R, r (f.hom x) = Ideal.Quotient.mk I (g.hom x) := fun x => by
    show Ideal.Quotient.lift (RingHom.ker f.hom) r₀ hr₀ ((RingHom.quotientKerEquivOfSurjective hf).symm (f.hom x)) = _
    rw [RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.Quotient.lift_mk]
    rfl

  have hcomm : f ≫ CommRingCat.ofHom r = g ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    ext x
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using hr x
  let u : B ⟶ CommRingCat.of (A ⧸ I) := h.desc (CommRingCat.ofHom r) (CommRingCat.ofHom (Ideal.Quotient.mk I)) hcomm
  have hu_inr : ∀ a : A, u.hom (inr.hom a) = Ideal.Quotient.mk I a := fun a => by
    have := congrArg (fun k => k.hom a) (h.inr_desc (CommRingCat.ofHom r) (CommRingCat.ofHom (Ideal.Quotient.mk I)) hcomm)
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using this
  have hu_inl : ∀ s : S, u.hom (inl.hom s) = r s := fun s => by
    have := congrArg (fun k => k.hom s) (h.inl_desc (CommRingCat.ofHom r) (CommRingCat.ofHom (Ideal.Quotient.mk I)) hcomm)
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using this

  have hvu : u ≫ CommRingCat.ofHom v = 𝟙 B := by
    apply h.hom_ext
    · ext s
      obtain ⟨x, rfl⟩ := hf s
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Category.comp_id]
      rw [hu_inl, hr, Ideal.Quotient.lift_mk, ← hw]
    · ext a
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Category.comp_id]
      rw [hu_inr, Ideal.Quotient.lift_mk]
  have hvu' : ∀ b : B, v (u.hom b) = b := fun b => by
    have := congrArg (fun k => k.hom b) hvu
    simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] using this
  refine ⟨fun b => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u.hom b)
    refine ⟨a, ?_⟩
    rw [← hvu' b, ← ha, Ideal.Quotient.lift_mk]
  · apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      have : Ideal.Quotient.mk I x = 0 := by rw [← hu_inr, hx, map_zero]
      rwa [Ideal.Quotient.eq_zero_iff_mem] at this
    · exact fun a ha => (RingHom.mem_ker).2 (hI a ha)

theorem level_surjective_and_ker (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (n : ℕ)
    (X X' : Scheme.{0}) (xb : X ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xb' : X' ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)})))
    (xt : X ⟶ X')
    (hcart : IsPullback xt xb xb'
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (W : X.Opens) (hW : IsAffineOpen W) (W' : X'.Opens) (hW' : IsAffineOpen W') (hWW : xt ⁻¹ᵁ W' = W)
    (e : W ≤ xt ⁻¹ᵁ W') :
    Function.Surjective (xt.appLE W' W e).hom ∧
    ∀ x : Γ(X', W'), (xt.appLE W' W e).hom x = 0 ↔ ∃ y : Γ(X', W'),
      x = (xb'.appLE ⊤ W' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)}))).inv.hom
        (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1 + 1)}) π)) ^ (n + 1) * y := by
  classical
  have hle : Ideal.span {π ^ (n + 1 + 1)} ≤ Ideal.span {π ^ (n + 1)} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))
  let R' : CommRingCat.{0} := CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)})
  let R : CommRingCat.{0} := CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})
  let φ : R' ⟶ R := CommRingCat.ofHom (Ideal.Quotient.factor hle)

  have H1 : IsPushout ((Spec.map φ).appLE ⊤ ⊤ le_top) (xb'.appLE ⊤ W' le_top) (xb.appLE ⊤ W le_top) (xt.appLE W' W e) :=
    isPushout_appLE_of_isPullback hcart (isAffineOpen_top _) (isAffineOpen_top _) hW' hW le_top le_top
      (by rw [hWW]; simp) e le_top

  have H2 : IsPushout φ ((Scheme.ΓSpecIso R').inv ≫ xb'.appLE ⊤ W' le_top)
      ((Scheme.ΓSpecIso R).inv ≫ xb.appLE ⊤ W le_top) (xt.appLE W' W e) := by
    refine H1.of_iso (Scheme.ΓSpecIso R') (Scheme.ΓSpecIso R) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · have htop : (Spec.map φ).appLE ⊤ ⊤ le_top = (Spec.map φ).appTop := by
        rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; congr 1
      rw [htop, Scheme.ΓSpecIso_naturality]
    · simp
    · simp
    · simp

  obtain ⟨hsurj, hker⟩ := surjective_and_ker_eq_of_isPushout H2 (Ideal.Quotient.factor_surjective hle)
  refine ⟨hsurj, fun x => ?_⟩
  have hkerφ : RingHom.ker φ.hom = Ideal.span {Ideal.Quotient.mk (Ideal.span {π ^ (n + 1 + 1)}) (π ^ (n + 1))} := by
    apply le_antisymm
    · intro z hz
      obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hz' : Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)}) o = 0 := by
        rw [RingHom.mem_ker] at hz
        rw [← hz]
        exact (Ideal.Quotient.factor_mk hle o).symm
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hz'
      obtain ⟨c, hc⟩ := hz'
      rw [← hc, map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      show Ideal.Quotient.factor hle (Ideal.Quotient.mk _ (π ^ (n + 1))) = 0
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span rfl
  rw [← RingHom.mem_ker, hker, hkerφ, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, map_pow]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [← ha, mul_comm]⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [hy, mul_comm]⟩

end L1

theorem appLE_congr_hom {X' Y' : Scheme.{0}} {f g : X' ⟶ Y'} (h : f = g) (U : Y'.Opens) (V : X'.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

section FlatTorsion

open scoped TensorProduct in

theorem smul_pow_eq_zero_imp_of_flat'
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hπ : ∀ s : 𝒪, π * s = 0 → s = 0) (k : ℕ)
    (M : Type) [AddCommGroup M] [Module (𝒪 ⧸ Ideal.span {π ^ k}) M] [Module.Flat (𝒪 ⧸ Ideal.span {π ^ k}) M]
    (j : ℕ) (hj : j ≤ k) (y : M) (hy : (Ideal.Quotient.mk (Ideal.span {π ^ k}) π) ^ j • y = 0) :
    ∃ z : M, y = (Ideal.Quotient.mk (Ideal.span {π ^ k}) π) ^ (k - j) • z := by
  classical
  have hreg : ∀ (i : ℕ) (u v : 𝒪), π ^ i * u = π ^ i * v → u = v := by
    intro i
    induction i with
    | zero => intro u v h; simpa using h
    | succ i ih =>
      intro u v h
      apply ih
      have h' : π * (π ^ i * u - π ^ i * v) = 0 := by
        rw [mul_sub, ← mul_assoc, ← mul_assoc, ← pow_succ', h, sub_self]
      exact sub_eq_zero.1 (hπ _ h')
  set A := 𝒪 ⧸ Ideal.span {π ^ k} with hA
  set ϖ : A := Ideal.Quotient.mk (Ideal.span {π ^ k}) π with hϖ
  let f : A →ₗ[A] A := LinearMap.lsmul A A (ϖ ^ (k - j))
  let g : A →ₗ[A] A := LinearMap.lsmul A A (ϖ ^ j)
  have hfg : Function.Exact f g := by
    intro x
    constructor
    · intro hx
      obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hx' : Ideal.Quotient.mk (Ideal.span {π ^ k}) (π ^ j * x₀) = 0 := by
        have : g (Ideal.Quotient.mk _ x₀) = ϖ ^ j * Ideal.Quotient.mk _ x₀ := rfl
        rw [← map_pow, ← map_mul] at this; rw [← this]; exact hx
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx'
      obtain ⟨c, hc⟩ := hx'
      have hx₀ : x₀ = c * π ^ (k - j) := by
        have : π ^ j * x₀ = π ^ j * (c * π ^ (k - j)) := by
          rw [← hc, mul_comm c, mul_comm c, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]
        exact hreg j _ _ this
      refine ⟨Ideal.Quotient.mk (Ideal.span {π ^ k}) c, ?_⟩
      show ϖ ^ (k - j) • Ideal.Quotient.mk (Ideal.span {π ^ k}) c = Ideal.Quotient.mk (Ideal.span {π ^ k}) x₀
      rw [hx₀, smul_eq_mul, hϖ, ← map_pow, ← map_mul, mul_comm]
    · rintro ⟨w, rfl⟩
      show ϖ ^ j • (ϖ ^ (k - j) • w) = 0
      rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj, hϖ, ← map_pow,
        show Ideal.Quotient.mk (Ideal.span {π ^ k}) (π ^ k) = 0 from Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl),
        zero_mul]
  have hex := Module.Flat.lTensor_exact M hfg
  have h1 : LinearMap.lTensor M g (y ⊗ₜ[A] (1 : A)) = 0 := by
    rw [LinearMap.lTensor_tmul]
    show y ⊗ₜ[A] (ϖ ^ j • (1 : A)) = 0
    rw [← TensorProduct.smul_tmul, hy, TensorProduct.zero_tmul]
  obtain ⟨t, ht⟩ := (hex _).1 h1
  refine ⟨TensorProduct.rid A M t, ?_⟩
  have key : ∀ u : M ⊗[A] A, TensorProduct.rid A M (LinearMap.lTensor M f u) = ϖ ^ (k - j) • TensorProduct.rid A M u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul m b =>
      rw [LinearMap.lTensor_tmul]
      show TensorProduct.rid A M (m ⊗ₜ[A] (ϖ ^ (k - j) • b)) = ϖ ^ (k - j) • TensorProduct.rid A M (m ⊗ₜ[A] b)
      rw [TensorProduct.rid_tmul, TensorProduct.rid_tmul, smul_smul, smul_eq_mul]
    | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, smul_add]
  rw [← key, ht, TensorProduct.rid_tmul, one_smul]

end FlatTorsion

section CSide

variable {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {X : ℕ → Scheme.{0}}
  (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
  (xt : ∀ n : ℕ, X n ⟶ X (n + 1)) {G : Type} [Group G] (a : ∀ n : ℕ, G →* Aut (X n))
  (W : ∀ n : ℕ, (X n).Opens) (hWc : ∀ n : ℕ, (xt n) ⁻¹ᵁ (W (n + 1)) = W n)
  (hWs : ∀ (n : ℕ) (g : G), (a n g).hom ⁻¹ᵁ (W n) = W n)

noncomputable def ρC (n : ℕ) : Γ(X (n + 1), W (n + 1)) →+* Γ(X n, W n) :=
  ((xt n).appLE (W (n + 1)) (W n) (by rw [hWc])).hom

noncomputable def sC (n : ℕ) : 𝒪 →+* Γ(X n, W n) :=
  ((xb n).appLE ⊤ (W n) le_top).hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv.hom.comp
      (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)})))

theorem ρC_sC
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (n : ℕ) (o : 𝒪) : ρC xt W hWc n (sC xb W (n + 1) o) = sC xb W n o := by
  let φ : CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)}) ⟶ CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) :=
    CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))
  have hw : xt n ≫ xb (n + 1) = xb n ≫ Spec.map φ := (hcart n).w
  show ((xb (n + 1)).appLE ⊤ (W (n + 1)) le_top ≫ (xt n).appLE (W (n + 1)) (W n) (by rw [hWc]))
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)}))).inv (Ideal.Quotient.mk _ o)) =
    ((xb n).appLE ⊤ (W n) le_top) ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hw ⊤ (W n) _ le_top,
    ← Scheme.Hom.appLE_comp_appLE (xb n) (Spec.map φ) ⊤ ⊤ (W n) le_top le_top]
  show ((xb n).appLE ⊤ (W n) le_top) (((Spec.map φ).appLE ⊤ ⊤ le_top)
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)}))).inv (Ideal.Quotient.mk _ o))) = _
  congr 1
  have htop : (Spec.map φ).appLE ⊤ ⊤ le_top = (Spec.map φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; congr 1
  rw [htop]
  have hnat := Scheme.ΓSpecIso_inv_naturality φ
  have := congrArg (fun k => k.hom (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1 + 1)}) o)) hnat
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  erw [← this]
  show (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv
      (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))
        (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1 + 1)}) o)) = _
  rw [Ideal.Quotient.factor_mk]

noncomputable def RC : Subring (∀ n : ℕ, (Γ(X n, W n) : Type)) :=
  limSubring (M := fun n => (Γ(X n, W n) : Type)) (ρC xt W hWc)

noncomputable def sRC
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))))) :
    𝒪 →+* ↥(RC xt W hWc) where
  toFun o := ⟨fun n => sC xb W n o, fun n => ρC_sC xb xt W hWc hcart n o⟩
  map_one' := Subtype.ext (funext fun n => by simp)
  map_mul' o o' := Subtype.ext (funext fun n => by simp)
  map_zero' := Subtype.ext (funext fun n => by simp)
  map_add' o o' := Subtype.ext (funext fun n => by simp)

noncomputable def τC (n : ℕ) (g : G) : Γ(X n, W n) →+* Γ(X n, W n) :=
  ((a n g⁻¹).hom.appLE (W n) (W n) (by rw [hWs])).hom

theorem τC_apply (n : ℕ) (g : G) (y : Γ(X n, W n)) :
    τC a W hWs n g y = (a n g⁻¹).hom.appLE (W n) (W n) (by rw [hWs]) y := rfl

theorem ρC_τC (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (n : ℕ) (g : G) (y : Γ(X (n + 1), W (n + 1))) :
    ρC xt W hWc n (τC a W hWs (n + 1) g y) = τC a W hWs n g (ρC xt W hWc n y) := by
  show ((a (n + 1) g⁻¹).hom.appLE (W (n + 1)) (W (n + 1)) (by rw [hWs]) ≫ (xt n).appLE (W (n + 1)) (W n) (by rw [hWc])) y =
    ((xt n).appLE (W (n + 1)) (W n) (by rw [hWc]) ≫ (a n g⁻¹).hom.appLE (W n) (W n) (by rw [hWs])) y
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (ha_xt n g⁻¹).symm]

theorem τC_one (n : ℕ) (y : Γ(X n, W n)) : τC a W hWs n 1 y = y := by
  have h1 : (a n 1⁻¹).hom = 𝟙 (X n) := by rw [inv_one, map_one]; rfl
  have key : ∀ (e : W n ≤ (𝟙 (X n)) ⁻¹ᵁ (W n)), (𝟙 (X n) : X n ⟶ X n).appLE (W n) (W n) e = 𝟙 _ := by
    intro e
    rw [Scheme.Hom.appLE, show homOfLE e = 𝟙 (W n) from Subsingleton.elim _ _]
    erw [CategoryTheory.op_id, CategoryTheory.Functor.map_id, Category.comp_id]
    simp
  have e1 : W n ≤ (𝟙 (X n)) ⁻¹ᵁ (W n) := le_of_eq (by simp)
  have : (a n 1⁻¹).hom.appLE (W n) (W n) (by rw [hWs]) = 𝟙 _ := (appLE_congr_hom h1 _ _ _ e1).trans (key e1)
  rw [τC_apply, this]; rfl

theorem τC_mul (n : ℕ) (g h : G) (y : Γ(X n, W n)) : τC a W hWs n (g * h) y = τC a W hWs n g (τC a W hWs n h y) := by
  have hm : (a n (g * h)⁻¹).hom = (a n g⁻¹).hom ≫ (a n h⁻¹).hom := by
    rw [mul_inv_rev, map_mul, Aut.Aut_mul_def]; rfl
  show ((a n (g * h)⁻¹).hom.appLE (W n) (W n) (by rw [hWs])) y =
    ((a n h⁻¹).hom.appLE (W n) (W n) (by rw [hWs]) ≫ (a n g⁻¹).hom.appLE (W n) (W n) (by rw [hWs])) y
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hm]

theorem τC_sC (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n) (n : ℕ) (g : G) (o : 𝒪) :
    τC a W hWs n g (sC xb W n o) = sC xb W n o := by
  show ((xb n).appLE ⊤ (W n) le_top ≫ (a n g⁻¹).hom.appLE (W n) (W n) (by rw [hWs]))
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)) =
    ((xb n).appLE ⊤ (W n) le_top) ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (ha_over n g⁻¹)]

@[reducible] noncomputable def actC (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom) :
    MulSemiringAction G ↥(RC xt W hWc) where
  smul g f := ⟨fun n => τC a W hWs n g (f.1 n), fun n => by
    show ρC xt W hWc n (τC a W hWs (n + 1) g (f.1 (n + 1))) = τC a W hWs n g (f.1 n)
    rw [ρC_τC xt a W hWc hWs ha_xt, f.2 n]⟩
  one_smul f := Subtype.ext (funext fun n => τC_one a W hWs n (f.1 n))
  mul_smul g h f := Subtype.ext (funext fun n => τC_mul a W hWs n g h (f.1 n))
  smul_zero g := Subtype.ext (funext fun n => by show τC a W hWs n g 0 = 0; exact map_zero _)
  smul_add g f f' := Subtype.ext (funext fun n => by show τC a W hWs n g (f.1 n + f'.1 n) = _; exact map_add _ _ _)
  smul_one g := Subtype.ext (funext fun n => by show τC a W hWs n g 1 = 1; exact map_one _)
  smul_mul g f f' := Subtype.ext (funext fun n => by show τC a W hWs n g (f.1 n * f'.1 n) = _; exact map_mul _ _ _)

theorem sC_pow_eq_zero (m : ℕ) : (sC xb W m π) ^ (m + 1) = 0 := by
  rw [← map_pow, sC, RingHom.comp_apply, RingHom.comp_apply,
    show Ideal.Quotient.mk (Ideal.span {π ^ (m + 1)}) (π ^ (m + 1)) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl), map_zero, map_zero]

theorem ρC_surjective
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hWa : ∀ n : ℕ, IsAffineOpen (W n)) (m : ℕ) : Function.Surjective (ρC xt W hWc m) :=
  (level_surjective_and_ker 𝒪 π m (X m) (X (m + 1)) (xb m) (xb (m + 1)) (xt m) (hcart m)
    _ (hWa m) _ (hWa (m + 1)) (hWc m) (by rw [hWc])).1

theorem ρC_ker
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hWa : ∀ n : ℕ, IsAffineOpen (W n)) (m : ℕ) (y : Γ(X (m + 1), W (m + 1)))
    (hy : ρC xt W hWc m y = 0) : ∃ z, y = (sC xb W (m + 1) π) ^ (m + 1) * z :=
  ((level_surjective_and_ker 𝒪 π m (X m) (X (m + 1)) (xb m) (xb (m + 1)) (xt m) (hcart m)
    _ (hWa m) _ (hWa (m + 1)) (hWc m) (by rw [hWc])).2 y).1 hy

theorem sC_tors (hπ : ∀ s : 𝒪, π * s = 0 → s = 0) (hflat : ∀ n : ℕ, Flat (xb n)) (hWa : ∀ n : ℕ, IsAffineOpen (W n))
    (m j : ℕ) (hj : j ≤ m + 1) (y : Γ(X m, W m)) (hy : (sC xb W m π) ^ j * y = 0) :
    ∃ z : Γ(X m, W m), y = (sC xb W m π) ^ (m + 1 - j) * z := by
  let sq : (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) →+* Γ(X m, W m) :=
    ((xb m).appLE ⊤ (W m) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (m + 1)}))).inv.hom
  have hsq : ∀ o : 𝒪, sq (Ideal.Quotient.mk _ o) = sC xb W m o := fun o => rfl
  have hsqflat : sq.Flat := by
    have h1 : ((xb m).appLE ⊤ (W m) le_top).hom.Flat :=
      HasRingHomProperty.appLE @Flat (xb m) (hflat m) ⟨⊤, isAffineOpen_top _⟩ ⟨_, hWa m⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (m + 1)}))).inv.hom.Flat :=
      RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (m + 1)}))).commRingCatIsoToRingEquiv.symm.bijective
    exact RingHom.Flat.comp h2 h1
  letI : Algebra (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) Γ(X m, W m) := sq.toAlgebra
  haveI : Module.Flat (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) Γ(X m, W m) := hsqflat
  obtain ⟨z, hz⟩ := smul_pow_eq_zero_imp_of_flat' 𝒪 π hπ (m + 1) Γ(X m, W m) j hj y (by
    rw [Algebra.smul_def, map_pow]; show (sq (Ideal.Quotient.mk _ π)) ^ j * y = 0; rw [hsq]; exact hy)
  refine ⟨z, ?_⟩
  rw [hz, Algebra.smul_def, map_pow]; show (sq (Ideal.Quotient.mk _ π)) ^ (m + 1 - j) * z = _; rw [hsq]

end CSide

end W2C2

open W2C2 in

theorem solution
    (S : Type) [CommRing S] (ϖ : S) (hϖ : ∀ s : S, ϖ * s = 0 → s = 0)
    (X' : ℕ → Scheme.{0}) (xb' : ∀ n : ℕ, X' n ⟶ Spec (CommRingCat.of (S ⧸ Ideal.span {ϖ ^ (n + 1)})))
    (xt' : ∀ n : ℕ, X' n ⟶ X' (n + 1))
    (hcart' : ∀ n : ℕ, IsPullback (xt' n) (xb' n) (xb' (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ (n + 1))))))))
    (hflat' : ∀ n : ℕ, Flat (xb' n))
    (G : Type) [Group G] [Finite G] (a' : ∀ n : ℕ, G →* Aut (X' n))
    (ha'_over : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ xb' n = xb' n)
    (ha'_xt : ∀ (n : ℕ) (g : G), (a' n g).hom ≫ xt' n = xt' n ≫ (a' (n + 1) g).hom)
    (W' : ∀ n : ℕ, (X' n).Opens) (hW'a : ∀ n : ℕ, IsAffineOpen (W' n))
    (hW'c : ∀ n : ℕ, (xt' n) ⁻¹ᵁ (W' (n + 1)) = W' n)
    (hW's : ∀ (n : ℕ) (g : G), (a' n g).hom ⁻¹ᵁ (W' n) = W' n) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra S R') (_ : MulSemiringAction G R') (_ : SMulCommClass G S R'),
      IsAdicComplete (Ideal.span {algebraMap S R' ϖ}) R' ∧
      (∀ x : R', algebraMap S R' ϖ * x = 0 → x = 0) ∧
      ∃ (lvl' : ∀ n : ℕ, (R' ⧸ Ideal.span {algebraMap S R' ϖ ^ (n + 1)}) ≃+* Γ(X' n, W' n)),
        (∀ (n : ℕ) (x : R'), (xt' n).appLE (W' (n + 1)) (W' n) (by rw [hW'c])
            (lvl' (n + 1) (Ideal.Quotient.mk _ x)) = lvl' n (Ideal.Quotient.mk _ x)) ∧
        (∀ (n : ℕ) (g : G) (x : R'), (a' n g⁻¹).hom.appLE (W' n) (W' n) (by rw [hW's])
            (lvl' n (Ideal.Quotient.mk _ x)) = lvl' n (Ideal.Quotient.mk _ (g • x))) ∧
        (∀ (n : ℕ) (s : S), lvl' n (Ideal.Quotient.mk _ (algebraMap S R' s)) =
            (xb' n).appLE ⊤ (W' n) le_top
              ((Scheme.ΓSpecIso (CommRingCat.of (S ⧸ Ideal.span {ϖ ^ (n + 1)}))).inv (Ideal.Quotient.mk _ s))) := by
  classical
  letI algR : Algebra S ↥(RC xt' W' hW'c) := (sRC xb' xt' W' hW'c hcart').toAlgebra
  letI actR' : MulSemiringAction G ↥(RC xt' W' hW'c) := actC xt' a' W' hW'c hW's ha'_xt
  haveI hsmc : SMulCommClass G S ↥(RC xt' W' hW'c) :=
    ⟨fun g o f => Subtype.ext (funext fun n => by
      show τC a' W' hW's n g (sC xb' W' n o * f.1 n) = sC xb' W' n o * τC a' W' hW's n g (f.1 n)
      rw [map_mul, τC_sC xb' a' W' hW's ha'_over])⟩
  have hlvl : ∀ n : ℕ, ∃ e : (↥(RC xt' W' hW'c) ⧸ Ideal.span {algebraMap S (↥(RC xt' W' hW'c)) ϖ ^ (n + 1)}) ≃+* Γ(X' n, W' n),
      (∀ f : ↥(RC xt' W' hW'c), e (Ideal.Quotient.mk _ f) = f.1 n) := fun n =>
    limSubring_exists_levelEquiv (algebraMap S (↥(RC xt' W' hW'c)) ϖ) (ρC_surjective xb' xt' W' hW'c hcart' hW'a)
      (ρC_ker xb' xt' W' hW'c hcart' hW'a) (sC_pow_eq_zero xb' W') (sC_tors xb' W' hϖ hflat' hW'a) n
  choose lvl hlvl' using hlvl
  have hcompleteR : IsAdicComplete (Ideal.span {algebraMap S (↥(RC xt' W' hW'c)) ϖ}) ↥(RC xt' W' hW'c) :=
    limSubring_isAdicComplete (algebraMap S (↥(RC xt' W' hW'c)) ϖ) (ρC_surjective xb' xt' W' hW'c hcart' hW'a)
      (ρC_ker xb' xt' W' hW'c hcart' hW'a) (sC_pow_eq_zero xb' W') (sC_tors xb' W' hϖ hflat' hW'a)
  have htf : ∀ x : ↥(RC xt' W' hW'c), algebraMap S (↥(RC xt' W' hW'c)) ϖ * x = 0 → x = 0 := by
    intro x hx
    apply Subtype.ext; funext m
    have hm : sC xb' W' (m + 1) ϖ * x.1 (m + 1) = 0 := congrArg (fun f : ↥(RC xt' W' hW'c) => f.1 (m + 1)) hx
    obtain ⟨z, hz⟩ := sC_tors xb' W' hϖ hflat' hW'a (m + 1) 1 (by omega) (x.1 (m + 1)) (by simpa using hm)
    show x.1 m = 0
    rw [← x.2 m, hz, map_mul, map_pow]
    show (ρC xt' W' hW'c m (sC xb' W' (m + 1) ϖ)) ^ (m + 1 + 1 - 1) * _ = 0
    rw [ρC_sC xb' xt' W' hW'c hcart', Nat.add_sub_cancel, sC_pow_eq_zero, zero_mul]
  refine ⟨↥(RC xt' W' hW'c), inferInstance, algR, actR', hsmc, hcompleteR, htf, lvl, ?_, ?_, ?_⟩
  · intro n x; rw [hlvl', hlvl']; exact x.2 n
  · intro n g x; rw [hlvl', hlvl']; rfl
  · intro n s; rw [hlvl']; rfl

end S_AlgebraicGeometry_exists_ringEquiv_quotient_sections_of_isPullback_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ringEquiv_quotient_sections_of_isPullback_of_flat (solution)
