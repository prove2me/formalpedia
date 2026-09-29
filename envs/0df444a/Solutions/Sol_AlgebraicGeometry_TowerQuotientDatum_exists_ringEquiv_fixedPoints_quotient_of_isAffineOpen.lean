-- Prove2me | solution 1 for AlgebraicGeometry.TowerQuotientDatum.exists_ringEquiv_fixedPoints_quotient_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/dfa5f6e3-c834-51ce-b116-4257e5fa473c

import Mathlib
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_fixedPoints_quotient_of_isAffineOpen

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace W2L15

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

theorem finiteType_quotient_of_level
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (k : ℕ)
    (X0 : Scheme.{0}) (xb0 : X0 ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (k + 1)}))) [LocallyOfFiniteType xb0]
    (W : X0.Opens) (hW : IsAffineOpen W)
    (R : Type) [CommRing R] [Algebra 𝒪 R]
    (e : (R ⧸ Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) ≃+* Γ(X0, W))
    (he : ∀ o : 𝒪, e (Ideal.Quotient.mk _ (algebraMap 𝒪 R o)) =
      xb0.appLE ⊤ W le_top ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (k + 1)}))).inv (Ideal.Quotient.mk _ o))) :
    Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}) := by
  classical

  have h1 : (xb0.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType xb0 inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top

  let q : 𝒪 →+* Γ(Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (k + 1)})), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (k + 1)}))).inv.hom.comp (Ideal.Quotient.mk (Ideal.span {π ^ (k + 1)}))
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨o, ho⟩ := Ideal.Quotient.mk_surjective ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (k + 1)}))).hom y)
    refine ⟨o, ?_⟩
    show (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (k + 1)}))).inv (Ideal.Quotient.mk _ o) = y
    rw [ho]
    exact CategoryTheory.Iso.hom_inv_id_apply _ y

  have h3 : ((xb0.appLE ⊤ W le_top).hom.comp q).FiniteType := h1.comp (RingHom.FiniteType.of_surjective q hq)
  have h4 : (e.symm.toRingHom.comp ((xb0.appLE ⊤ W le_top).hom.comp q)).FiniteType :=
    (RingHom.FiniteType.of_surjective e.symm.toRingHom e.symm.surjective).comp h3
  have h5 : e.symm.toRingHom.comp ((xb0.appLE ⊤ W le_top).hom.comp q) =
      algebraMap 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π ^ (k + 1)}) := by
    ext o
    show e.symm ((xb0.appLE ⊤ W le_top) ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (k + 1)}))).inv
      (Ideal.Quotient.mk _ o))) = Ideal.Quotient.mk _ (algebraMap 𝒪 R o)
    rw [← he, RingEquiv.symm_apply_apply]
  rw [h5, RingHom.finiteType_algebraMap] at h4

  have hle : Ideal.span {algebraMap 𝒪 R π ^ (k + 1)} ≤ Ideal.span {algebraMap 𝒪 R π} :=
    Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self _ (Nat.succ_ne_zero k))
  exact Algebra.FiniteType.of_surjective (Ideal.Quotient.factorₐ 𝒪 hle) (Ideal.Quotient.factor_surjective hle)

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

section Helpers

open scoped TensorProduct in

theorem smul_pow_eq_zero_imp_of_flat
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (π : 𝒪) (hπ : π ≠ 0) (k : ℕ)
    (M : Type) [AddCommGroup M] [Module (𝒪 ⧸ Ideal.span {π ^ k}) M] [Module.Flat (𝒪 ⧸ Ideal.span {π ^ k}) M]
    (j : ℕ) (hj : j ≤ k) (y : M) (hy : (Ideal.Quotient.mk (Ideal.span {π ^ k}) π) ^ j • y = 0) :
    ∃ z : M, y = (Ideal.Quotient.mk (Ideal.span {π ^ k}) π) ^ (k - j) • z := by
  classical
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
        exact mul_left_cancel₀ (pow_ne_zero j hπ) this
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

theorem appLE_congr_hom {X' Y' : Scheme.{0}} {f g : X' ⟶ Y'} (h : f = g) (U : Y'.Opens) (V : X'.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

end Helpers

theorem injective_of_injective_comp {R S T : CommRingCat.{0}} (f : R ⟶ S) (g : S ⟶ T)
    (h : Function.Injective (f ≫ g)) : Function.Injective f := by
  intro a b hab
  apply h
  simp only [CommRingCat.comp_apply, hab]

theorem injective_app_of_forall_epi_morphismRestrict
    {X Y : Scheme.{0}} (p : X ⟶ Y) (hp : ∀ U : Y.Opens, Epi (p ∣_ U)) (V : Y.Opens) :
    Function.Injective (p.app V) := by
  have h1 : Mono (p ∣_ V).appTop := by
    haveI := Functor.preservesEpimorphisms_of_adjunction ΓSpec.adjunction
    haveI := hp V
    have h : Epi (Scheme.Γ.rightOp.map (p ∣_ V)) := inferInstance
    have h' : Mono (Scheme.Γ.map (p ∣_ V).op) := (op_epi_iff _).mp h
    rwa [Scheme.Γ_map_op] at h'
  have h2 : Function.Injective (p ∣_ V).appTop :=
    ConcreteCategory.injective_of_mono_of_preservesPullback _
  rw [morphismRestrict_appTop] at h2
  have h3 : Function.Injective (p.app (V.ι ''ᵁ ⊤)) := injective_of_injective_comp _ _ h2
  rwa [Scheme.Opens.ι_image_top] at h3

noncomputable def secHom {W : Scheme.{0}} (V : W.Opens) (s : Γ(W, V)) :
    (↑V : Scheme.{0}) ⟶ Spec (CommRingCat.of (MvPolynomial Unit (ULift.{0} ℤ))) :=
  (AffineSpace.toSpecMvPolyIntEquiv Unit).symm (fun _ => V.topIso.inv s)

theorem toSpecMvPolyIntEquiv_secHom {W : Scheme.{0}} (V : W.Opens) (s : Γ(W, V)) (i : Unit) :
    AffineSpace.toSpecMvPolyIntEquiv Unit (secHom V s) i = V.topIso.inv s := by
  rw [secHom, Equiv.apply_symm_apply]

theorem topIso_inv_injective {W : Scheme.{0}} (V : W.Opens) : Function.Injective V.topIso.inv :=
  ConcreteCategory.injective_of_mono_of_preservesPullback _

theorem resLE_comp_secHom {W W' : Scheme.{0}} (q : W ⟶ W') (V' : W'.Opens) (V : W.Opens) (e : V ≤ q ⁻¹ᵁ V')
    (s : Γ(W', V')) : q.resLE V' V e ≫ secHom V' s = secHom V (q.appLE V' V e s) := by
  apply (AffineSpace.toSpecMvPolyIntEquiv Unit).injective
  funext i
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp, toSpecMvPolyIntEquiv_secHom, toSpecMvPolyIntEquiv_secHom,
    Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  change V.topIso.inv (q.appLE V' V e (V'.topIso.hom (V'.topIso.inv s))) = _
  rw [← CommRingCat.comp_apply V'.topIso.inv, Iso.inv_hom_id, CommRingCat.id_apply]

theorem exists_app_eq_of_invariant
    {𝒪 : Type} [CommRing 𝒪] {π : 𝒪}
    {X : ℕ → Scheme.{0}} {xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))}
    {xt : ∀ n : ℕ, X n ⟶ X (n + 1)} {G : Type} [Group G] {a : ∀ n : ℕ, G →* Aut (X n)}
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)
    (U : ∀ n : ℕ, (D.Y n).Opens) (hU : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (U (n + 1)) = U n)
    (f : ∀ n : ℕ, Γ(X n, (D.p n) ⁻¹ᵁ (U n)))
    (hinv : ∀ (n : ℕ) (g : G), (a n g).hom.appLE ((D.p n) ⁻¹ᵁ (U n)) ((D.p n) ⁻¹ᵁ (U n))
      (by rw [← Scheme.Hom.comp_preimage, D.p_inv]) (f n) = f n)
    (hcompat : ∀ n : ℕ, (xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (U (n + 1))) ((D.p n) ⁻¹ᵁ (U n))
      (by rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hU]) (f (n + 1)) = f n) :
    ∃ b : ∀ n : ℕ, Γ(D.Y n, U n), ∀ n : ℕ, (D.p n).app (U n) (b n) = f n := by
  obtain ⟨v, hv⟩ := D.univ_loc (Spec (CommRingCat.of (MvPolynomial Unit (ULift.{0} ℤ)))) U hU
    (fun n => secHom ((D.p n) ⁻¹ᵁ (U n)) (f n))
    (fun n g => by rw [resLE_comp_secHom, hinv])
    (fun n => by rw [resLE_comp_secHom, hcompat])
  refine ⟨fun n => (U n).topIso.hom (AffineSpace.toSpecMvPolyIntEquiv Unit (v n) ()), fun n => ?_⟩
  have e := congrArg (fun φ => AffineSpace.toSpecMvPolyIntEquiv Unit φ ()) (hv n)
  simp only [AffineSpace.toSpecMvPolyIntEquiv_comp, toSpecMvPolyIntEquiv_secHom] at e

  rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top] at e
  apply topIso_inv_injective ((D.p n) ⁻¹ᵁ (U n))
  rw [Scheme.Hom.app_eq_appLE]
  exact e

section YSide

variable {𝒪 : Type} [CommRing 𝒪] {π : 𝒪}
  {X : ℕ → Scheme.{0}} {xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))}
  {xt : ∀ n : ℕ, X n ⟶ X (n + 1)} {G : Type} [Group G] {a : ∀ n : ℕ, G →* Aut (X n)}
  (D : TowerQuotientDatum 𝒪 π X xb xt G a)
  (V : ∀ n : ℕ, (D.Y n).Opens) (hV : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (V (n + 1)) = V n)

noncomputable def ρY (n : ℕ) : Γ(D.Y (n + 1), V (n + 1)) →+* Γ(D.Y n, V n) :=
  ((D.yt n).appLE (V (n + 1)) (V n) (by rw [hV])).hom

noncomputable def sY (n : ℕ) : 𝒪 →+* Γ(D.Y n, V n) :=
  ((D.yb n).appLE ⊤ (V n) le_top).hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv.hom.comp
      (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)})))

theorem sY_apply (n : ℕ) (o : 𝒪) : sY D V n o =
    (D.yb n).appLE ⊤ (V n) le_top ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)) := rfl

theorem ρY_sY (n : ℕ) (o : 𝒪) : ρY D V hV n (sY D V (n + 1) o) = sY D V n o := by
  let φ : CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)}) ⟶ CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) :=
    CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))
  have hw : D.yt n ≫ D.yb (n + 1) = D.yb n ≫ Spec.map φ := (D.yt_isPullback n).w
  show ((D.yb (n + 1)).appLE ⊤ (V (n + 1)) le_top ≫ (D.yt n).appLE (V (n + 1)) (V n) (by rw [hV]))
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)}))).inv (Ideal.Quotient.mk _ o)) =
    ((D.yb n).appLE ⊤ (V n) le_top) ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hw ⊤ (V n) _ le_top,
    ← Scheme.Hom.appLE_comp_appLE (D.yb n) (Spec.map φ) ⊤ ⊤ (V n) le_top le_top]
  show ((D.yb n).appLE ⊤ (V n) le_top) (((Spec.map φ).appLE ⊤ ⊤ le_top)
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

noncomputable def Bsub : Subring (∀ n : ℕ, (Γ(D.Y n, V n) : Type)) :=
  limSubring (M := fun n => (Γ(D.Y n, V n) : Type)) (ρY D V hV)

noncomputable def sB : 𝒪 →+* ↥(Bsub D V hV) where
  toFun o := ⟨fun n => sY D V n o, fun n => ρY_sY D V hV n o⟩
  map_one' := Subtype.ext (funext fun n => by simp)
  map_mul' o o' := Subtype.ext (funext fun n => by simp)
  map_zero' := Subtype.ext (funext fun n => by simp)
  map_add' o o' := Subtype.ext (funext fun n => by simp)

theorem sB_apply (o : 𝒪) (n : ℕ) : (sB D V hV o).1 n = sY D V n o := rfl

theorem sY_pow_eq_zero (m : ℕ) : (sY D V m π) ^ (m + 1) = 0 := by
  rw [← map_pow, sY, RingHom.comp_apply, RingHom.comp_apply,
    show Ideal.Quotient.mk (Ideal.span {π ^ (m + 1)}) (π ^ (m + 1)) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl), map_zero, map_zero]

theorem ρY_surjective (hVa : ∀ n : ℕ, IsAffineOpen (V n)) (m : ℕ) : Function.Surjective (ρY D V hV m) :=
  (level_surjective_and_ker 𝒪 π m (D.Y m) (D.Y (m + 1)) (D.yb m) (D.yb (m + 1)) (D.yt m) (D.yt_isPullback m)
    (V m) (hVa m) (V (m + 1)) (hVa (m + 1)) (hV m) (by rw [hV])).1

theorem ρY_ker (hVa : ∀ n : ℕ, IsAffineOpen (V n)) (m : ℕ) (y : Γ(D.Y (m + 1), V (m + 1))) (hy : ρY D V hV m y = 0) :
    ∃ z : Γ(D.Y (m + 1), V (m + 1)), y = (sY D V (m + 1) π) ^ (m + 1) * z :=
  ((level_surjective_and_ker 𝒪 π m (D.Y m) (D.Y (m + 1)) (D.yb m) (D.yb (m + 1)) (D.yt m) (D.yt_isPullback m)
    (V m) (hVa m) (V (m + 1)) (hVa (m + 1)) (hV m) (by rw [hV])).2 y).1 hy

theorem sY_tors [IsDomain 𝒪] (hπ : π ≠ 0) (hVa : ∀ n : ℕ, IsAffineOpen (V n))
    (m j : ℕ) (hj : j ≤ m + 1) (y : Γ(D.Y m, V m)) (hy : (sY D V m π) ^ j * y = 0) :
    ∃ z : Γ(D.Y m, V m), y = (sY D V m π) ^ (m + 1 - j) * z := by
  let sq : (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) →+* Γ(D.Y m, V m) :=
    ((D.yb m).appLE ⊤ (V m) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (m + 1)}))).inv.hom
  have hsq : ∀ o : 𝒪, sq (Ideal.Quotient.mk _ o) = sY D V m o := fun o => rfl
  have hsqflat : sq.Flat := by
    have h1 : ((D.yb m).appLE ⊤ (V m) le_top).hom.Flat :=
      HasRingHomProperty.appLE @Flat (D.yb m) (D.yb_flat m) ⟨⊤, isAffineOpen_top _⟩ ⟨V m, hVa m⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (m + 1)}))).inv.hom.Flat :=
      RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (m + 1)}))).commRingCatIsoToRingEquiv.symm.bijective
    exact RingHom.Flat.comp h2 h1
  letI : Algebra (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) Γ(D.Y m, V m) := sq.toAlgebra
  haveI : Module.Flat (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) Γ(D.Y m, V m) := hsqflat
  obtain ⟨z, hz⟩ := smul_pow_eq_zero_imp_of_flat 𝒪 π hπ (m + 1) Γ(D.Y m, V m) j hj y (by
    rw [Algebra.smul_def, map_pow]; show (sq (Ideal.Quotient.mk _ π)) ^ j * y = 0; rw [hsq]; exact hy)
  refine ⟨z, ?_⟩
  rw [hz, Algebra.smul_def, map_pow]; show (sq (Ideal.Quotient.mk _ π)) ^ (m + 1 - j) * z = _; rw [hsq]

end YSide

section XSide

variable {𝒪 : Type} [CommRing 𝒪] {π : 𝒪}
  {X : ℕ → Scheme.{0}} {xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))}
  {xt : ∀ n : ℕ, X n ⟶ X (n + 1)} {G : Type} [Group G] {a : ∀ n : ℕ, G →* Aut (X n)}
  (D : TowerQuotientDatum 𝒪 π X xb xt G a)
  (V : ∀ n : ℕ, (D.Y n).Opens) (hV : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (V (n + 1)) = V n)

include hV in
theorem preimage_xt_preimage_p (n : ℕ) : (xt n) ⁻¹ᵁ ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) = (D.p n) ⁻¹ᵁ (V n) := by
  rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hV]

theorem preimage_a_preimage_p (n : ℕ) (g : G) : (a n g).hom ⁻¹ᵁ ((D.p n) ⁻¹ᵁ (V n)) = (D.p n) ⁻¹ᵁ (V n) := by
  rw [← Scheme.Hom.comp_preimage, D.p_inv]

theorem isAffineOpen_preimage_p (hVa : ∀ n : ℕ, IsAffineOpen (V n)) (n : ℕ) : IsAffineOpen ((D.p n) ⁻¹ᵁ (V n)) := by
  haveI := D.p_isFinite n
  exact (hVa n).preimage (D.p n)

noncomputable def ρX (n : ℕ) : Γ(X (n + 1), (D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) →+* Γ(X n, (D.p n) ⁻¹ᵁ (V n)) :=
  ((xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((D.p n) ⁻¹ᵁ (V n)) (by rw [preimage_xt_preimage_p D V hV])).hom

noncomputable def sX (n : ℕ) : 𝒪 →+* Γ(X n, (D.p n) ⁻¹ᵁ (V n)) :=
  ((xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top).hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv.hom.comp
      (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)})))

theorem sX_apply (n : ℕ) (o : 𝒪) : sX D V n o =
    (xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)) := rfl

theorem ρX_sX
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (n : ℕ) (o : 𝒪) : ρX D V hV n (sX D V (n + 1) o) = sX D V n o := by
  let φ : CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)}) ⟶ CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) :=
    CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))
  have hw : xt n ≫ xb (n + 1) = xb n ≫ Spec.map φ := (hcart n).w
  show ((xb (n + 1)).appLE ⊤ ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) le_top ≫
      (xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((D.p n) ⁻¹ᵁ (V n)) (by rw [preimage_xt_preimage_p D V hV]))
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)}))).inv (Ideal.Quotient.mk _ o)) =
    ((xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top)
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hw ⊤ ((D.p n) ⁻¹ᵁ (V n)) _ le_top,
    ← Scheme.Hom.appLE_comp_appLE (xb n) (Spec.map φ) ⊤ ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top le_top]
  show ((xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top) (((Spec.map φ).appLE ⊤ ⊤ le_top)
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

noncomputable def Rsub : Subring (∀ n : ℕ, (Γ(X n, (D.p n) ⁻¹ᵁ (V n)) : Type)) :=
  limSubring (M := fun n => (Γ(X n, (D.p n) ⁻¹ᵁ (V n)) : Type)) (ρX D V hV)

noncomputable def sR
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))))) :
    𝒪 →+* ↥(Rsub D V hV) where
  toFun o := ⟨fun n => sX D V n o, fun n => ρX_sX D V hV hcart n o⟩
  map_one' := Subtype.ext (funext fun n => by simp)
  map_mul' o o' := Subtype.ext (funext fun n => by simp)
  map_zero' := Subtype.ext (funext fun n => by simp)
  map_add' o o' := Subtype.ext (funext fun n => by simp)

noncomputable def τX (n : ℕ) (g : G) : Γ(X n, (D.p n) ⁻¹ᵁ (V n)) →+* Γ(X n, (D.p n) ⁻¹ᵁ (V n)) :=
  ((a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n)) (by rw [preimage_a_preimage_p D V])).hom

theorem τX_apply (n : ℕ) (g : G) (y : Γ(X n, (D.p n) ⁻¹ᵁ (V n))) : τX D V n g y =
    (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n)) (by rw [preimage_a_preimage_p D V]) y := rfl

theorem ρX_τX (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (n : ℕ) (g : G) (y : Γ(X (n + 1), (D.p (n + 1)) ⁻¹ᵁ (V (n + 1)))) :
    ρX D V hV n (τX D V (n + 1) g y) = τX D V n g (ρX D V hV n y) := by
  show ((a (n + 1) g⁻¹).hom.appLE _ _ (by rw [preimage_a_preimage_p D V]) ≫
      (xt n).appLE _ _ (by rw [preimage_xt_preimage_p D V hV])) y =
    ((xt n).appLE _ _ (by rw [preimage_xt_preimage_p D V hV]) ≫
      (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n)) (by rw [preimage_a_preimage_p D V])) y
  rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (ha_xt n g⁻¹).symm]

theorem τX_one (n : ℕ) (y : Γ(X n, (D.p n) ⁻¹ᵁ (V n))) : τX D V n 1 y = y := by
  have h1 : (a n 1⁻¹).hom = 𝟙 (X n) := by rw [inv_one, map_one]; rfl
  have key : ∀ (e : (D.p n) ⁻¹ᵁ (V n) ≤ (𝟙 (X n)) ⁻¹ᵁ ((D.p n) ⁻¹ᵁ (V n))),
      (𝟙 (X n) : X n ⟶ X n).appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n)) e = 𝟙 _ := by
    intro e
    rw [Scheme.Hom.appLE, show homOfLE e = 𝟙 ((D.p n) ⁻¹ᵁ (V n)) from Subsingleton.elim _ _]
    erw [CategoryTheory.op_id, CategoryTheory.Functor.map_id, Category.comp_id]
    simp
  have e1 : (D.p n) ⁻¹ᵁ (V n) ≤ (𝟙 (X n)) ⁻¹ᵁ ((D.p n) ⁻¹ᵁ (V n)) := le_of_eq (by simp)
  have : (a n 1⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n)) (by rw [preimage_a_preimage_p D V]) = 𝟙 _ :=
    (appLE_congr_hom h1 _ _ _ e1).trans (key e1)
  rw [τX_apply, this]; rfl

theorem τX_mul (n : ℕ) (g h : G) (y : Γ(X n, (D.p n) ⁻¹ᵁ (V n))) : τX D V n (g * h) y = τX D V n g (τX D V n h y) := by
  have hm : (a n (g * h)⁻¹).hom = (a n g⁻¹).hom ≫ (a n h⁻¹).hom := by
    rw [mul_inv_rev, map_mul, Aut.Aut_mul_def]; rfl
  show ((a n (g * h)⁻¹).hom.appLE _ _ (by rw [preimage_a_preimage_p D V])) y =
    ((a n h⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n)) (by rw [preimage_a_preimage_p D V]) ≫
      (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n)) (by rw [preimage_a_preimage_p D V])) y
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hm]

theorem τX_sX (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n) (n : ℕ) (g : G) (o : 𝒪) :
    τX D V n g (sX D V n o) = sX D V n o := by
  show ((xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top ≫
      (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n)) (by rw [preimage_a_preimage_p D V]))
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)) =
    ((xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top)
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))
  rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (ha_over n g⁻¹)]

@[reducible] noncomputable def actR (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom) :
    MulSemiringAction G ↥(Rsub D V hV) where
  smul g f := ⟨fun n => τX D V n g (f.1 n), fun n => by
    show ρX D V hV n (τX D V (n + 1) g (f.1 (n + 1))) = τX D V n g (f.1 n)
    rw [ρX_τX D V hV ha_xt, f.2 n]⟩
  one_smul f := Subtype.ext (funext fun n => τX_one D V n (f.1 n))
  mul_smul g h f := Subtype.ext (funext fun n => τX_mul D V n g h (f.1 n))
  smul_zero g := Subtype.ext (funext fun n => by show τX D V n g 0 = 0; exact map_zero _)
  smul_add g f f' := Subtype.ext (funext fun n => by show τX D V n g (f.1 n + f'.1 n) = _; exact map_add _ _ _)
  smul_one g := Subtype.ext (funext fun n => by show τX D V n g 1 = 1; exact map_one _)
  smul_mul g f f' := Subtype.ext (funext fun n => by show τX D V n g (f.1 n * f'.1 n) = _; exact map_mul _ _ _)

theorem actR_smul_apply (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (g : G) (f : ↥(Rsub D V hV)) (n : ℕ) :
    letI := actR D V hV ha_xt
    (g • f).1 n = τX D V n g (f.1 n) := rfl

theorem sX_pow_eq_zero (m : ℕ) : (sX D V m π) ^ (m + 1) = 0 := by
  rw [← map_pow, sX, RingHom.comp_apply, RingHom.comp_apply,
    show Ideal.Quotient.mk (Ideal.span {π ^ (m + 1)}) (π ^ (m + 1)) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl), map_zero, map_zero]

theorem ρX_surjective
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hVa : ∀ n : ℕ, IsAffineOpen (V n)) (m : ℕ) : Function.Surjective (ρX D V hV m) :=
  (level_surjective_and_ker 𝒪 π m (X m) (X (m + 1)) (xb m) (xb (m + 1)) (xt m) (hcart m)
    _ (isAffineOpen_preimage_p D V hVa m) _ (isAffineOpen_preimage_p D V hVa (m + 1))
    (preimage_xt_preimage_p D V hV m) (by rw [preimage_xt_preimage_p D V hV])).1

theorem ρX_ker
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hVa : ∀ n : ℕ, IsAffineOpen (V n)) (m : ℕ) (y : Γ(X (m + 1), (D.p (m + 1)) ⁻¹ᵁ (V (m + 1))))
    (hy : ρX D V hV m y = 0) : ∃ z, y = (sX D V (m + 1) π) ^ (m + 1) * z :=
  ((level_surjective_and_ker 𝒪 π m (X m) (X (m + 1)) (xb m) (xb (m + 1)) (xt m) (hcart m)
    _ (isAffineOpen_preimage_p D V hVa m) _ (isAffineOpen_preimage_p D V hVa (m + 1))
    (preimage_xt_preimage_p D V hV m) (by rw [preimage_xt_preimage_p D V hV])).2 y).1 hy

theorem sX_tors [IsDomain 𝒪] (hπ : π ≠ 0) (hflat : ∀ n : ℕ, Flat (xb n)) (hVa : ∀ n : ℕ, IsAffineOpen (V n))
    (m j : ℕ) (hj : j ≤ m + 1) (y : Γ(X m, (D.p m) ⁻¹ᵁ (V m))) (hy : (sX D V m π) ^ j * y = 0) :
    ∃ z : Γ(X m, (D.p m) ⁻¹ᵁ (V m)), y = (sX D V m π) ^ (m + 1 - j) * z := by
  let sq : (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) →+* Γ(X m, (D.p m) ⁻¹ᵁ (V m)) :=
    ((xb m).appLE ⊤ ((D.p m) ⁻¹ᵁ (V m)) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (m + 1)}))).inv.hom
  have hsq : ∀ o : 𝒪, sq (Ideal.Quotient.mk _ o) = sX D V m o := fun o => rfl
  have hsqflat : sq.Flat := by
    have h1 : ((xb m).appLE ⊤ ((D.p m) ⁻¹ᵁ (V m)) le_top).hom.Flat :=
      HasRingHomProperty.appLE @Flat (xb m) (hflat m) ⟨⊤, isAffineOpen_top _⟩ ⟨_, isAffineOpen_preimage_p D V hVa m⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (m + 1)}))).inv.hom.Flat :=
      RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (m + 1)}))).commRingCatIsoToRingEquiv.symm.bijective
    exact RingHom.Flat.comp h2 h1
  letI : Algebra (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) Γ(X m, (D.p m) ⁻¹ᵁ (V m)) := sq.toAlgebra
  haveI : Module.Flat (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) Γ(X m, (D.p m) ⁻¹ᵁ (V m)) := hsqflat
  obtain ⟨z, hz⟩ := smul_pow_eq_zero_imp_of_flat 𝒪 π hπ (m + 1) Γ(X m, (D.p m) ⁻¹ᵁ (V m)) j hj y (by
    rw [Algebra.smul_def, map_pow]; show (sq (Ideal.Quotient.mk _ π)) ^ j * y = 0; rw [hsq]; exact hy)
  refine ⟨z, ?_⟩
  rw [hz, Algebra.smul_def, map_pow]; show (sq (Ideal.Quotient.mk _ π)) ^ (m + 1 - j) * z = _; rw [hsq]

end XSide

section Glue

variable {𝒪 : Type} [CommRing 𝒪] {π : 𝒪}
  {X : ℕ → Scheme.{0}} {xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))}
  {xt : ∀ n : ℕ, X n ⟶ X (n + 1)} {G : Type} [Group G] {a : ∀ n : ℕ, G →* Aut (X n)}
  (D : TowerQuotientDatum 𝒪 π X xb xt G a)
  (V : ∀ n : ℕ, (D.Y n).Opens) (hV : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (V (n + 1)) = V n)

noncomputable def pa (n : ℕ) : Γ(D.Y n, V n) →+* Γ(X n, (D.p n) ⁻¹ᵁ (V n)) := ((D.p n).app (V n)).hom

theorem pa_apply (n : ℕ) (y : Γ(D.Y n, V n)) : pa D V n y = (D.p n).app (V n) y := rfl

theorem pa_injective (n : ℕ) : Function.Injective (pa D V n) :=
  injective_app_of_forall_epi_morphismRestrict (D.p n) (D.p_epi_loc n) (V n)

theorem ρX_pa (n : ℕ) (y : Γ(D.Y (n + 1), V (n + 1))) : ρX D V hV n (pa D V (n + 1) y) = pa D V n (ρY D V hV n y) := by
  show ((D.p (n + 1)).app (V (n + 1)) ≫ (xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((D.p n) ⁻¹ᵁ (V n))
      (by rw [preimage_xt_preimage_p D V hV])) y =
    ((D.yt n).appLE (V (n + 1)) (V n) (by rw [hV]) ≫ (D.p n).app (V n)) y
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom (D.p_xt n)]

theorem pa_sY (n : ℕ) (o : 𝒪) : pa D V n (sY D V n o) = sX D V n o := by
  show ((D.yb n).appLE ⊤ (V n) le_top ≫ (D.p n).app (V n))
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)) =
    ((xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top)
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (D.p_over n)]

theorem τX_pa (n : ℕ) (g : G) (y : Γ(D.Y n, V n)) : τX D V n g (pa D V n y) = pa D V n y := by
  show ((D.p n).app (V n) ≫ (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n))
      (by rw [preimage_a_preimage_p D V])) y = (D.p n).app (V n) y
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (D.p_inv n g⁻¹)]

noncomputable def θ : ↥(Bsub D V hV) →+* ↥(Rsub D V hV) where
  toFun b := ⟨fun n => pa D V n (b.1 n), fun n => by
    show ρX D V hV n (pa D V (n + 1) (b.1 (n + 1))) = pa D V n (b.1 n)
    rw [ρX_pa, b.2 n]⟩
  map_one' := Subtype.ext (funext fun n => map_one (pa D V n))
  map_mul' b b' := Subtype.ext (funext fun n => map_mul (pa D V n) (b.1 n) (b'.1 n))
  map_zero' := Subtype.ext (funext fun n => map_zero (pa D V n))
  map_add' b b' := Subtype.ext (funext fun n => map_add (pa D V n) (b.1 n) (b'.1 n))

theorem θ_apply (b : ↥(Bsub D V hV)) (n : ℕ) : (θ D V hV b).1 n = pa D V n (b.1 n) := rfl

theorem θ_injective : Function.Injective (θ D V hV) := by
  intro b b' h
  apply Subtype.ext; funext n
  exact pa_injective D V n (by rw [← θ_apply, ← θ_apply, h])

theorem θ_sB
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (o : 𝒪) : θ D V hV (sB D V hV o) = sR D V hV hcart o :=
  Subtype.ext (funext fun n => pa_sY D V n o)

theorem τX_θ (g : G) (b : ↥(Bsub D V hV)) (n : ℕ) : τX D V n g ((θ D V hV b).1 n) = (θ D V hV b).1 n :=
  τX_pa D V n g (b.1 n)

theorem exists_θ_eq (r : ↥(Rsub D V hV)) (hr : ∀ (n : ℕ) (g : G), τX D V n g (r.1 n) = r.1 n) :
    ∃ b : ↥(Bsub D V hV), θ D V hV b = r := by
  have hinv : ∀ (n : ℕ) (g : G), (a n g).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n))
      (by rw [← Scheme.Hom.comp_preimage, D.p_inv]) (r.1 n) = r.1 n := by
    intro n g
    have := hr n g⁻¹
    rw [τX_apply] at this
    rw [← appLE_congr_hom (show (a n (g⁻¹)⁻¹).hom = (a n g).hom by rw [inv_inv]) _ _
      (by rw [preimage_a_preimage_p D V]) (by rw [← Scheme.Hom.comp_preimage, D.p_inv])]
    exact this
  obtain ⟨b, hb⟩ := exists_app_eq_of_invariant D V hV (fun n => r.1 n) hinv (fun n => r.2 n)
  have hbc : ∀ n : ℕ, ρY D V hV n (b (n + 1)) = b n := by
    intro n
    apply pa_injective D V n
    rw [← ρX_pa, pa_apply, pa_apply, hb, hb]
    exact r.2 n
  exact ⟨⟨b, hbc⟩, Subtype.ext (funext fun n => hb n)⟩

end Glue

section Packages

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] {π : 𝒪}
  {X : ℕ → Scheme.{0}} {xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))}
  {xt : ∀ n : ℕ, X n ⟶ X (n + 1)} {G : Type} [Group G] {a : ∀ n : ℕ, G →* Aut (X n)}
  (D : TowerQuotientDatum 𝒪 π X xb xt G a)
  (V : ∀ n : ℕ, (D.Y n).Opens) (hV : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (V (n + 1)) = V n)

theorem rPackage (hπ : π ≠ 0) (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hproper : ∀ n : ℕ, IsProper (xb n)) (hflat : ∀ n : ℕ, Flat (xb n))
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (hVa : ∀ n : ℕ, IsAffineOpen (V n)) :
    letI : Algebra 𝒪 ↥(Rsub D V hV) := (sR D V hV hcart).toAlgebra
    letI : MulSemiringAction G ↥(Rsub D V hV) := actR D V hV ha_xt
    IsAdicComplete (Ideal.span {algebraMap 𝒪 (↥(Rsub D V hV)) π}) ↥(Rsub D V hV) ∧
    (∀ x : ↥(Rsub D V hV), algebraMap 𝒪 (↥(Rsub D V hV)) π * x = 0 → x = 0) ∧
    Algebra.FiniteType 𝒪 (↥(Rsub D V hV) ⧸ Ideal.span {algebraMap 𝒪 (↥(Rsub D V hV)) π}) ∧
    ∃ lvl : ∀ n : ℕ, (↥(Rsub D V hV) ⧸ Ideal.span {algebraMap 𝒪 (↥(Rsub D V hV)) π ^ (n + 1)}) ≃+* Γ(X n, (D.p n) ⁻¹ᵁ (V n)),
      (∀ (n : ℕ) (f : ↥(Rsub D V hV)), lvl n (Ideal.Quotient.mk _ f) = f.1 n) ∧
      (∀ (n : ℕ) (x : ↥(Rsub D V hV)), (xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((D.p n) ⁻¹ᵁ (V n))
          (by rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hV])
          (lvl (n + 1) (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ x)) ∧
      (∀ (n : ℕ) (g : G) (x : ↥(Rsub D V hV)), (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n))
          (by rw [← Scheme.Hom.comp_preimage, D.p_inv]) (lvl n (Ideal.Quotient.mk _ x)) =
          lvl n (Ideal.Quotient.mk _ (g • x))) ∧
      (∀ (n : ℕ) (o : 𝒪), lvl n (Ideal.Quotient.mk _ (algebraMap 𝒪 (↥(Rsub D V hV)) o)) =
          (xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top
            ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) := by
  classical
  letI algR : Algebra 𝒪 ↥(Rsub D V hV) := (sR D V hV hcart).toAlgebra
  letI actR' : MulSemiringAction G ↥(Rsub D V hV) := actR D V hV ha_xt
  have hWa := isAffineOpen_preimage_p D V hVa
  have hlvl : ∀ n : ℕ, ∃ e : (↥(Rsub D V hV) ⧸ Ideal.span {algebraMap 𝒪 (↥(Rsub D V hV)) π ^ (n + 1)}) ≃+*
      Γ(X n, (D.p n) ⁻¹ᵁ (V n)), (∀ f : ↥(Rsub D V hV), e (Ideal.Quotient.mk _ f) = f.1 n) := fun n =>
    limSubring_exists_levelEquiv (algebraMap 𝒪 (↥(Rsub D V hV)) π) (ρX_surjective D V hV hcart hVa)
      (ρX_ker D V hV hcart hVa) (sX_pow_eq_zero D V) (sX_tors D V hπ hflat hVa) n
  choose lvl hlvl' using hlvl
  have hcompleteR : IsAdicComplete (Ideal.span {algebraMap 𝒪 (↥(Rsub D V hV)) π}) ↥(Rsub D V hV) :=
    limSubring_isAdicComplete (algebraMap 𝒪 (↥(Rsub D V hV)) π) (ρX_surjective D V hV hcart hVa)
      (ρX_ker D V hV hcart hVa) (sX_pow_eq_zero D V) (sX_tors D V hπ hflat hVa)
  have htf : ∀ x : ↥(Rsub D V hV), algebraMap 𝒪 (↥(Rsub D V hV)) π * x = 0 → x = 0 := by
    intro x hx
    apply Subtype.ext; funext m
    have hm : sX D V (m + 1) π * x.1 (m + 1) = 0 := congrArg (fun f : ↥(Rsub D V hV) => f.1 (m + 1)) hx
    obtain ⟨z, hz⟩ := sX_tors D V hπ hflat hVa (m + 1) 1 (by omega) (x.1 (m + 1)) (by simpa using hm)
    show x.1 m = 0
    rw [← x.2 m, hz, map_mul, map_pow, ρX_sX D V hV hcart, Nat.add_sub_cancel, sX_pow_eq_zero, zero_mul]
  have halg : ∀ (n : ℕ) (o : 𝒪), lvl n (Ideal.Quotient.mk _ (algebraMap 𝒪 (↥(Rsub D V hV)) o)) =
      (xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)) := by
    intro n o; rw [hlvl']; rfl
  have hft : Algebra.FiniteType 𝒪 (↥(Rsub D V hV) ⧸ Ideal.span {algebraMap 𝒪 (↥(Rsub D V hV)) π}) := by
    haveI := hproper 0
    exact finiteType_quotient_of_level 𝒪 π 0 (X 0) (xb 0) _ (hWa 0) ↥(Rsub D V hV) (lvl 0) (halg 0)
  refine ⟨hcompleteR, htf, hft, lvl, hlvl', ?_, ?_, halg⟩
  · intro n r; rw [hlvl', hlvl']; exact r.2 n
  · intro n g r; rw [hlvl', hlvl']; rfl

theorem bLevels (hπ : π ≠ 0) (hVa : ∀ n : ℕ, IsAffineOpen (V n)) :
    letI : Algebra 𝒪 ↥(Bsub D V hV) := (sB D V hV).toAlgebra
    ∃ lvlB : ∀ n : ℕ, (↥(Bsub D V hV) ⧸ Ideal.span {algebraMap 𝒪 (↥(Bsub D V hV)) π ^ (n + 1)}) ≃+* Γ(D.Y n, V n),
      ∀ (n : ℕ) (f : ↥(Bsub D V hV)), lvlB n (Ideal.Quotient.mk _ f) = f.1 n := by
  classical
  letI algB : Algebra 𝒪 ↥(Bsub D V hV) := (sB D V hV).toAlgebra
  have h : ∀ n : ℕ, ∃ e : (↥(Bsub D V hV) ⧸ Ideal.span {algebraMap 𝒪 (↥(Bsub D V hV)) π ^ (n + 1)}) ≃+* Γ(D.Y n, V n),
      (∀ f : ↥(Bsub D V hV), e (Ideal.Quotient.mk _ f) = f.1 n) := fun n =>
    limSubring_exists_levelEquiv (algebraMap 𝒪 (↥(Bsub D V hV)) π) (ρY_surjective D V hV hVa)
      (ρY_ker D V hV hVa) (sY_pow_eq_zero D V) (sY_tors D V hπ hVa) n
  choose lvlB hlvlB' using h
  exact ⟨lvlB, hlvlB'⟩

theorem aEquiv (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n) :
    letI : Algebra 𝒪 ↥(Rsub D V hV) := (sR D V hV hcart).toAlgebra
    letI : MulSemiringAction G ↥(Rsub D V hV) := actR D V hV ha_xt
    letI : Algebra 𝒪 ↥(Bsub D V hV) := (sB D V hV).toAlgebra
    ∀ [SMulCommClass G 𝒪 ↥(Rsub D V hV)],
    ∃ eA : ↥(Bsub D V hV) ≃ₐ[𝒪] ↥(FixedPoints.subalgebra 𝒪 (↥(Rsub D V hV)) G),
      ∀ b : ↥(Bsub D V hV), ((eA b : ↥(FixedPoints.subalgebra 𝒪 (↥(Rsub D V hV)) G)) : ↥(Rsub D V hV)) = θ D V hV b := by
  letI algR : Algebra 𝒪 ↥(Rsub D V hV) := (sR D V hV hcart).toAlgebra
  letI actR' : MulSemiringAction G ↥(Rsub D V hV) := actR D V hV ha_xt
  letI algB : Algebra 𝒪 ↥(Bsub D V hV) := (sB D V hV).toAlgebra
  intro _
  let A := FixedPoints.subalgebra 𝒪 (↥(Rsub D V hV)) G
  have hθ_mem : ∀ b : ↥(Bsub D V hV), θ D V hV b ∈ A := fun b g =>
    Subtype.ext (funext fun n => τX_θ D V hV g b n)
  let θalg : ↥(Bsub D V hV) →ₐ[𝒪] ↥(Rsub D V hV) :=
    { θ D V hV with commutes' := fun o => θ_sB D V hV hcart o }
  let θA : ↥(Bsub D V hV) →ₐ[𝒪] ↥A := θalg.codRestrict A hθ_mem
  have hθA : ∀ b : ↥(Bsub D V hV), ((θA b : ↥A) : ↥(Rsub D V hV)) = θ D V hV b := fun b => rfl
  have hθA_bij : Function.Bijective θA := by
    refine ⟨fun b b' h => θ_injective D V hV ((hθA b).symm.trans ((congrArg Subtype.val h).trans (hθA b'))), fun x => ?_⟩
    obtain ⟨b, hb⟩ := exists_θ_eq D V hV x.1 (fun n g => congrArg (fun f : ↥(Rsub D V hV) => f.1 n) (x.2 g))
    exact ⟨b, Subtype.ext ((hθA b).trans hb)⟩
  exact ⟨AlgEquiv.ofBijective θA hθA_bij, fun b => rfl⟩

end Packages

end W2L15

open W2L15 in
set_option maxHeartbeats 4000000 in

theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hproper : ∀ n : ℕ, IsProper (xb n)) (hflat : ∀ n : ℕ, Flat (xb n))
    (G : Type) [Group G] [Finite G] (a : ∀ n : ℕ, G →* Aut (X n))
    (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)
    (V : ∀ n : ℕ, (D.Y n).Opens) (hVa : ∀ n : ℕ, IsAffineOpen (V n))
    (hV : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (V (n + 1)) = V n) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra 𝒪 R) (_ : MulSemiringAction G R) (_ : SMulCommClass G 𝒪 R),
      IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R ∧
      (∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0) ∧
      Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}) ∧
      ∃ (lvl : ∀ n : ℕ, (R ⧸ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) ≃+* Γ(X n, (D.p n) ⁻¹ᵁ (V n)))
        (μ : ∀ n : ℕ, (↥(FixedPoints.subalgebra 𝒪 R G) ⧸
          Ideal.span {algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π ^ (n + 1)}) ≃+* Γ(D.Y n, V n)),

        (∀ (n : ℕ) (x : R), (xt n).appLE ((D.p (n + 1)) ⁻¹ᵁ (V (n + 1))) ((D.p n) ⁻¹ᵁ (V n))
            (by rw [← Scheme.Hom.comp_preimage, D.p_xt, Scheme.Hom.comp_preimage, hV])
            (lvl (n + 1) (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ x)) ∧
        (∀ (n : ℕ) (g : G) (x : R), (a n g⁻¹).hom.appLE ((D.p n) ⁻¹ᵁ (V n)) ((D.p n) ⁻¹ᵁ (V n))
            (by rw [← Scheme.Hom.comp_preimage, D.p_inv]) (lvl n (Ideal.Quotient.mk _ x)) =
            lvl n (Ideal.Quotient.mk _ (g • x))) ∧
        (∀ (n : ℕ) (o : 𝒪), lvl n (Ideal.Quotient.mk _ (algebraMap 𝒪 R o)) =
            (xb n).appLE ⊤ ((D.p n) ⁻¹ᵁ (V n)) le_top
              ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) ∧

        (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.yt n).appLE (V (n + 1)) (V n) (by rw [hV])
            (μ (n + 1) (Ideal.Quotient.mk _ x)) = μ n (Ideal.Quotient.mk _ x)) ∧
        (∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G)), (D.p n).appLE (V n) ((D.p n) ⁻¹ᵁ (V n)) le_rfl
            (μ n (Ideal.Quotient.mk _ x)) = lvl n (Ideal.Quotient.mk _ (x : R))) ∧
        (∀ (n : ℕ) (o : 𝒪), μ n (Ideal.Quotient.mk _ (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) o)) =
            (D.yb n).appLE ⊤ (V n) le_top
              ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))) := by
  classical
  have hπ0 : π ≠ 0 := hπ.ne_zero
  letI algR : Algebra 𝒪 ↥(Rsub D V hV) := (sR D V hV hcart).toAlgebra
  letI actR' : MulSemiringAction G ↥(Rsub D V hV) := actR D V hV ha_xt
  letI algB : Algebra 𝒪 ↥(Bsub D V hV) := (sB D V hV).toAlgebra
  haveI : SMulCommClass G 𝒪 ↥(Rsub D V hV) :=
    ⟨fun g o f => Subtype.ext (funext fun n => by
      show τX D V n g (sX D V n o * f.1 n) = sX D V n o * τX D V n g (f.1 n)
      rw [map_mul, τX_sX D V ha_over])⟩
  obtain ⟨hcompleteR, htf, hft, lvl, hlvl', hcompat, hsmul, halg⟩ := rPackage D V hV hπ0 hcart hproper hflat ha_xt hVa
  obtain ⟨lvlB, hlvlB'⟩ := bLevels D V hV hπ0 hVa
  obtain ⟨eA, heA⟩ := aEquiv D V hV hcart ha_xt ha_over
  have hIJ : ∀ n : ℕ, Ideal.span {algebraMap 𝒪 (↥(Bsub D V hV)) π ^ (n + 1)} =
      (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 (↥(Rsub D V hV)) G)) π ^ (n + 1)}).map (eA.toRingEquiv.symm : ↥(FixedPoints.subalgebra 𝒪 (↥(Rsub D V hV)) G) →+* ↥(Bsub D V hV)) := by
    intro n
    rw [Ideal.map_span, Set.image_singleton, map_pow]
    congr 2
    exact congrArg (fun t => t ^ (n + 1)) (eA.symm.commutes π).symm
  obtain ⟨μ, hμ⟩ : ∃ μ : ∀ n : ℕ, (↥(FixedPoints.subalgebra 𝒪 (↥(Rsub D V hV)) G) ⧸ Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 (↥(Rsub D V hV)) G)) π ^ (n + 1)}) ≃+* Γ(D.Y n, V n),
      ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 (↥(Rsub D V hV)) G)), μ n (Ideal.Quotient.mk _ x) = (eA.symm x).1 n :=
    ⟨fun n => (Ideal.quotientEquiv _ _ eA.toRingEquiv.symm (hIJ n)).trans (lvlB n), fun n x => by
      show lvlB n (Ideal.quotientEquiv _ _ eA.toRingEquiv.symm (hIJ n) (Ideal.Quotient.mk _ x)) = _
      rw [Ideal.quotientEquiv_mk, hlvlB']
      rfl⟩
  have hμ_compat : ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 (↥(Rsub D V hV)) G)), (D.yt n).appLE (V (n + 1)) (V n) (by rw [hV])
      (μ (n + 1) (Ideal.Quotient.mk _ x)) = μ n (Ideal.Quotient.mk _ x) := by
    intro n x
    exact (congrArg (fun t => (D.yt n).appLE (V (n + 1)) (V n) (by rw [hV]) t) (hμ (n + 1) x)).trans
      (((eA.symm x).2 n).trans (hμ n x).symm)
  have hμ_p : ∀ (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 (↥(Rsub D V hV)) G)),
      (D.p n).appLE (V n) ((D.p n) ⁻¹ᵁ (V n)) le_rfl (μ n (Ideal.Quotient.mk _ x)) =
      lvl n (Ideal.Quotient.mk _ (x : ↥(Rsub D V hV))) := by
    intro n x
    have e1 : ∀ y : Γ(D.Y n, V n), (D.p n).appLE (V n) ((D.p n) ⁻¹ᵁ (V n)) le_rfl y = pa D V n y := fun y => by
      rw [pa_apply, Scheme.Hom.app_eq_appLE]
    have e2 : θ D V hV (eA.symm x) = (x : ↥(Rsub D V hV)) :=
      (heA (eA.symm x)).symm.trans (congrArg Subtype.val (AlgEquiv.apply_symm_apply eA x))
    exact (congrArg (fun t => (D.p n).appLE (V n) ((D.p n) ⁻¹ᵁ (V n)) le_rfl t) (hμ n x)).trans
      ((e1 ((eA.symm x).1 n)).trans
      ((θ_apply D V hV (eA.symm x) n).symm.trans
      ((congrArg (fun r : ↥(Rsub D V hV) => r.1 n) e2).trans
      (hlvl' n (x : ↥(Rsub D V hV))).symm)))
  have hμ_alg : ∀ (n : ℕ) (o : 𝒪), μ n (Ideal.Quotient.mk _ (algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 (↥(Rsub D V hV)) G)) o)) =
      (D.yb n).appLE ⊤ (V n) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)) := by
    intro n o
    exact (hμ n _).trans ((congrArg (fun b : ↥(Bsub D V hV) => b.1 n) (eA.symm.commutes o)).trans rfl)
  exact ⟨↥(Rsub D V hV), inferInstance, algR, actR', inferInstance, hcompleteR, htf, hft, lvl, μ,
    hcompat, hsmul, halg, hμ_compat, hμ_p, hμ_alg⟩

end S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_fixedPoints_quotient_of_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_TowerQuotientDatum_exists_ringEquiv_fixedPoints_quotient_of_isAffineOpen (solution)
