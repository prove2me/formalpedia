-- Prove2me | solution 1 for AlgebraicGeometry.nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/636d2f33-e307-5755-b1c5-7dae12ea3aad

import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Theorems.Thm_AlgebraicGeometry_AdmissibleAlgebra_fixedPoints_isAdicComplete_and_finite_and_finiteType
import Theorems.Thm_AlgebraicGeometry_exists_algHom_of_finite_of_valuationRing_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_exists_smul_algHom_eq_of_isInvariant_of_isDomain
import Theorems.Thm_AlgebraicGeometry_isSeparated_of_isFinite_of_surjective_of_comp_eq
import Theorems.Thm_AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_isPullback_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace F4Cover12

section Setup

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G : Type) [Group G] [Finite G] (a : ∀ n : ℕ, G →* Aut (X n))

structure GChain : Type where

  W : ∀ n : ℕ, (X n).Opens

  affine : ∀ n : ℕ, IsAffineOpen (W n)

  stable : ∀ (n : ℕ) (g : G), (a n g).hom ⁻¹ᵁ (W n) = W n

  compat : ∀ n : ℕ, (xt n) ⁻¹ᵁ (W (n + 1)) = W n

structure ChartRing (C : GChain X xt G a) : Type 1 where

  R : Type
  [commRing : CommRing R]
  [algebra : Algebra 𝒪 R]
  [action : MulSemiringAction G R]
  [smulComm : SMulCommClass G 𝒪 R]

  complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R

  torsionFree : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0

  finiteType : Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π})

  lvl : ∀ n : ℕ, (R ⧸ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}) ≃+* Γ(X n, C.W n)

  lvl_compat : ∀ (n : ℕ) (r : R),
    (xt n).appLE (C.W (n + 1)) (C.W n) (by rw [C.compat]) (lvl (n + 1) (Ideal.Quotient.mk _ r)) = lvl n (Ideal.Quotient.mk _ r)

  lvl_smul : ∀ (n : ℕ) (g : G) (r : R),
    (a n g⁻¹).hom.appLE (C.W n) (C.W n) (by rw [C.stable]) (lvl n (Ideal.Quotient.mk _ r)) = lvl n (Ideal.Quotient.mk _ (g • r))

  lvl_algebraMap : ∀ (n : ℕ) (o : 𝒪),
    lvl n (Ideal.Quotient.mk _ (algebraMap 𝒪 R o)) =
      (xb n).appLE ⊤ (C.W n) le_top ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))

attribute [scoped instance] ChartRing.commRing ChartRing.algebra ChartRing.action ChartRing.smulComm

end Setup

end F4Cover12
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

namespace F4Cover12

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

end F4Cover12
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

namespace F4Cover12

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

end F4Cover12
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

namespace F4Cover12

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
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

end F4Cover12
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

namespace F4Cover12

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

private theorem _root_.F4Cover12.appLE_congr_hom {X' Y' : Scheme.{0}} {f g : X' ⟶ Y'} (h : f = g) (U : Y'.Opens) (V : X'.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

p2m_export "F4Cover12" "appLE_congr_hom"
end Helpers
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

end F4Cover12
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

namespace F4Cover12
namespace G2

theorem mem_fixedPoints_subalgebra_iff {𝒪 R G : Type*} [CommSemiring 𝒪] [Semiring R] [Algebra 𝒪 R]
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R] {x : R} :
    x ∈ FixedPoints.subalgebra 𝒪 R G ↔ ∀ g : G, g • x = x := Iff.rfl

theorem eq_zero_of_pow_mul_eq_zero {R : Type*} [CommRing R] {ϖ : R} (htf : ∀ x : R, ϖ * x = 0 → x = 0)
    (k : ℕ) {x : R} (hx : ϖ ^ k * x = 0) : x = 0 := by
  induction k with
  | zero => simpa using hx
  | succ k ih => exact ih (htf _ (by rw [← mul_assoc, ← pow_succ']; exact hx))

theorem mem_span_pow_of_coe_mem {𝒪 R G : Type*} [CommRing 𝒪] [CommRing R] [Algebra 𝒪 R]
    [Group G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R] (π : 𝒪)
    (htf : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0) (k : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 R G))
    (hx : (x : R) ∈ Ideal.span {algebraMap 𝒪 R π ^ k}) :
    x ∈ Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π ^ k} := by
  rw [Ideal.mem_span_singleton'] at hx
  obtain ⟨w, hw⟩ := hx
  have hwinv : ∀ g : G, g • w = w := by
    intro g
    have hxg : g • (x : R) = x := (mem_fixedPoints_subalgebra_iff.1 x.2) g
    have : algebraMap 𝒪 R π ^ k * (g • w - w) = 0 := by
      have h1 : g • (w * algebraMap 𝒪 R π ^ k) = w * algebraMap 𝒪 R π ^ k := by rw [hw]; exact hxg
      rw [smul_mul', smul_pow', smul_algebraMap] at h1
      linear_combination h1
    exact sub_eq_zero.1 (eq_zero_of_pow_mul_eq_zero htf k this)
  rw [Ideal.mem_span_singleton']
  refine ⟨⟨w, mem_fixedPoints_subalgebra_iff.2 hwinv⟩, Subtype.ext ?_⟩
  push_cast
  exact hw

theorem isUnit_of_isUnit_mk {R : Type*} [CommRing R] (ϖ : R) [IsAdicComplete (Ideal.span {ϖ}) R] (x : R)
    (hx : IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ ^ (0 + 1)}) x)) : IsUnit x := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← (Ideal.Quotient.mk _).map_one, Ideal.Quotient.eq, zero_add, pow_one] at hy

  have hJ := IsAdicComplete.le_jacobson_bot (Ideal.span {ϖ}) hy
  have : IsUnit (x * y) := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ hJ
  exact isUnit_of_mul_isUnit_left this

theorem exists_mul_sub_mul_smul_eq_zero_aux
    {A : Type*} [CommRing A] (f ϖ : A) (Af : Type*) [CommRing Af] [Algebra A Af] [IsLocalization.Away f Af]
    [IsNoetherianRing Af]
    {M : Type*} [AddCommGroup M] [Module A M] (Mf : Type*) [AddCommGroup Mf] [Module A Mf] [Module Af Mf]
    [IsScalarTower A Af Mf] (mk : M →ₗ[A] Mf) [IsLocalizedModule (Submonoid.powers f) mk] [Module.Finite Af Mf]
    (x : M) (hx : ∀ i : ℕ, ∃ (a b : ℕ) (y : M), f ^ a • x = ϖ ^ i • f ^ b • y) :
    ∃ (N e : ℕ) (a₀ : A), (f ^ N * (f ^ e - ϖ * a₀)) • x = 0 := by
  classical
  have hfu : IsUnit (algebraMap A Af f) := IsLocalization.Away.algebraMap_isUnit f

  have hmem : mk x ∈ (⨅ i : ℕ, Ideal.span {algebraMap A Af ϖ} ^ i • ⊤ : Submodule Af Mf) := by
    rw [Submodule.mem_iInf]
    intro i
    obtain ⟨a, b, y, h⟩ := hx i
    have h1 : algebraMap A Af (f ^ a) • mk x = algebraMap A Af (ϖ ^ i) • (algebraMap A Af (f ^ b) • mk y) := by
      rw [algebraMap_smul, algebraMap_smul, algebraMap_smul, ← map_smul, h, map_smul, map_smul]
    obtain ⟨u, hu⟩ := hfu.pow a
    have h2 : mk x = algebraMap A Af (ϖ ^ i) • ((↑u⁻¹ : Af) • (algebraMap A Af (f ^ b) • mk y)) := by
      rw [smul_comm (algebraMap A Af (ϖ ^ i)), ← h1, map_pow, ← hu, smul_smul, Units.inv_mul, one_smul]
    have h3 : algebraMap A Af (ϖ ^ i) ∈ Ideal.span {algebraMap A Af ϖ} ^ i := by
      rw [map_pow]; exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) i
    rw [h2]
    exact Submodule.smul_mem_smul h3 Submodule.mem_top
  obtain ⟨⟨ρ, hρ⟩, hρx⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (Ideal.span {algebraMap A Af ϖ}) (mk x)).1 hmem

  rw [Ideal.mem_span_singleton'] at hρ
  obtain ⟨α, rfl⟩ := hρ
  obtain ⟨⟨a₀, ⟨_, e, rfl⟩⟩, hα⟩ := IsLocalization.surj (Submonoid.powers f) α

  have h3 : mk ((f ^ e - ϖ * a₀) • x) = 0 := by
    have hα' : algebraMap A Af a₀ = α * algebraMap A Af (f ^ e) := hα.symm
    have hρx' : (α * algebraMap A Af ϖ) • mk x = mk x := hρx
    rw [map_smul, ← algebraMap_smul (A := Af), map_sub, map_mul, sub_smul, hα',
      show algebraMap A Af ϖ * (α * algebraMap A Af (f ^ e)) = algebraMap A Af (f ^ e) * (α * algebraMap A Af ϖ) by ring,
      mul_smul, hρx', sub_self]
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers f) mk).1 h3
  exact ⟨N, e, a₀, by rw [mul_smul]; exact hN⟩

theorem exists_mul_sub_mul_smul_eq_zero
    {A : Type*} [CommRing A] [IsNoetherianRing A] {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (f ϖ : A) (x : M)
    (hx : ∀ i : ℕ, ∃ (a b : ℕ) (y : M), f ^ a • x = ϖ ^ i • f ^ b • y) :
    ∃ (N e : ℕ) (a₀ : A), (f ^ N * (f ^ e - ϖ * a₀)) • x = 0 := by
  haveI : IsNoetherianRing (Localization.Away f) :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) (Localization.Away f) inferInstance
  haveI : Module.Finite (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) :=
    Module.Finite.of_isLocalizedModule (Submonoid.powers f) (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
  exact exists_mul_sub_mul_smul_eq_zero_aux f ϖ (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M) x hx

section Heart

variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (G : Type) [Group G] [Finite G]
    (R : Type) [CommRing R] [Algebra 𝒪 R] [MulSemiringAction G R] [SMulCommClass G 𝒪 R]
    (R' : Type) [CommRing R'] [Algebra 𝒪 R'] [MulSemiringAction G R'] [SMulCommClass G 𝒪 R']

local notation "A" => FixedPoints.subalgebra 𝒪 R G
local notation "A'" => FixedPoints.subalgebra 𝒪 R' G
local notation "ϖ" => algebraMap 𝒪 R π
local notation "ϖ'" => algebraMap 𝒪 R' π

theorem exists_fixed_sub_mul_mem
    (htf : ∀ x : R, ϖ * x = 0 → x = 0)
    [IsNoetherianRing ↥A] [Module.Finite ↥A R]
    (res : R →ₐ[𝒪] R') (hres_smul : ∀ (g : G) (r : R), res (g • r) = g • res r)
    (f : ↥A)
    (hsurj : ∀ (m : ℕ) (z : R'), ∃ (r : R) (j : ℕ), res ((f : R) ^ j) * z - res r ∈ Ideal.span {ϖ' ^ (m + 1)})
    (hker : ∀ (m : ℕ) (r : R), res r ∈ Ideal.span {ϖ' ^ (m + 1)} → ∃ j : ℕ, (f : R) ^ j * r ∈ Ideal.span {ϖ ^ (m + 1)})
    (n : ℕ) (b' : R') (hb' : ∀ g : G, g • b' = b') :
    ∃ (a : R) (_ : ∀ g : G, g • a = a) (N e j : ℕ) (a₀ : ↥A),
      res a - res ((f : R) ^ N * ((f : R) ^ e - ϖ * (a₀ : R)) * (f : R) ^ j) * b' ∈ Ideal.span {ϖ' ^ (n + 1)} := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hf : ∀ g : G, g • (f : R) = f := mem_fixedPoints_subalgebra_iff.1 f.2
  have hgf : ∀ (g : G) (k : ℕ) (x : R), g • ((f : R) ^ k * x) = (f : R) ^ k * g • x := fun g k x => by
    rw [smul_mul', smul_pow', hf]
  have hgϖ : ∀ (g : G) (k : ℕ) (x : R), g • (ϖ ^ k * x) = ϖ ^ k * g • x := fun g k x => by
    rw [smul_mul', smul_pow', smul_algebraMap]
  have hI' : ∀ (m : ℕ) (g : G) (x : R'), x ∈ Ideal.span {ϖ' ^ (m + 1)} → g • x ∈ Ideal.span {ϖ' ^ (m + 1)} := by
    intro m g x hx
    rw [Ideal.mem_span_singleton'] at hx ⊢
    obtain ⟨t, rfl⟩ := hx
    exact ⟨g • t, by rw [smul_mul', smul_pow', smul_algebraMap]⟩
  have hres_f : ∀ k : ℕ, ∀ g : G, g • res ((f : R) ^ k) = res ((f : R) ^ k) := fun k g => by
    rw [← hres_smul, smul_pow', hf]

  have step12 : ∀ m : ℕ, ∃ (r : R) (j : ℕ), res ((f : R) ^ j) * b' - res r ∈ Ideal.span {ϖ' ^ (m + 1)} ∧
      ∀ g : G, ∃ c : R, g • r - r = ϖ ^ (m + 1) * c := by
    intro m
    obtain ⟨r, j, hrj⟩ := hsurj m b'
    have hg : ∀ g : G, ∃ k : ℕ, (f : R) ^ k * (g • r - r) ∈ Ideal.span {ϖ ^ (m + 1)} := by
      intro g
      apply hker m
      have : res (g • r - r) = -(g • (res ((f : R) ^ j) * b' - res r) - (res ((f : R) ^ j) * b' - res r)) := by
        rw [map_sub, hres_smul, smul_sub, smul_mul', hres_f, hb']; ring
      rw [this]
      exact (Ideal.neg_mem_iff _).2 (Ideal.sub_mem _ (hI' m g _ hrj) hrj)
    choose k hk using hg
    let K : ℕ := ∑ g, k g
    have hkK : ∀ g : G, k g ≤ K := fun g => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)
    refine ⟨(f : R) ^ K * r, j + K, ?_, fun g => ?_⟩
    · have : res ((f : R) ^ (j + K)) * b' - res ((f : R) ^ K * r) = res ((f : R) ^ K) * (res ((f : R) ^ j) * b' - res r) := by
        simp only [map_pow, map_mul, pow_add]; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hrj
    · have hmem : (f : R) ^ K * (g • r - r) ∈ Ideal.span {ϖ ^ (m + 1)} := by
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hkK g)
        rw [hd, pow_add (f : R) (k g) d, mul_comm ((f : R) ^ k g) ((f : R) ^ d), mul_assoc]
        exact Ideal.mul_mem_left _ _ (hk g)
      rw [Ideal.mem_span_singleton'] at hmem
      obtain ⟨c, hc⟩ := hmem
      exact ⟨c, by rw [hgf, ← mul_sub, ← hc, mul_comm]⟩
  choose r j hE hInv using step12
  choose c hc using hInv

  have step4 : ∀ i : ℕ, ∃ (N : ℕ) (y : R), ∀ g : G,
      (f : R) ^ (N + j (n + i)) * c n g = ϖ ^ i * ((f : R) ^ (N + j n) * c (n + i) g) + (g • y - y) := by
    intro i
    have hD : res ((f : R) ^ (j (n + i)) * r n - (f : R) ^ (j n) * r (n + i)) ∈ Ideal.span {ϖ' ^ (n + 1)} := by
      have e2 : res ((f : R) ^ j (n + i)) * b' - res (r (n + i)) ∈ Ideal.span {ϖ' ^ (n + 1)} :=
        Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (by omega)) (hE (n + i))
      have : res ((f : R) ^ (j (n + i)) * r n - (f : R) ^ (j n) * r (n + i)) =
          res ((f : R) ^ (j n)) * (res ((f : R) ^ j (n + i)) * b' - res (r (n + i))) -
          res ((f : R) ^ (j (n + i))) * (res ((f : R) ^ j n) * b' - res (r n)) := by
        simp only [map_sub, map_mul]; ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ e2) (Ideal.mul_mem_left _ _ (hE n))
    obtain ⟨N, hN⟩ := hker n _ hD
    obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 hN
    refine ⟨N, e, fun g => ?_⟩
    have E1 := hc n g
    have E2 := hc (n + i) g
    have E4 : (g • e) * ϖ ^ (n + 1) =
        (f : R) ^ N * ((f : R) ^ (j (n + i)) * g • r n - (f : R) ^ (j n) * g • r (n + i)) := by
      have := congrArg (fun z => g • z) he
      simp only [smul_mul', smul_sub, smul_pow', hf, smul_algebraMap] at this
      exact this
    apply sub_eq_zero.1
    apply eq_zero_of_pow_mul_eq_zero htf (n + 1)
    have hpow : ϖ ^ (n + i + 1) = ϖ ^ (n + 1) * ϖ ^ i := by rw [← pow_add]; congr 1; omega
    rw [hpow] at E2
    linear_combination (-((f : R) ^ N * (f : R) ^ (j (n + i)))) * E1 + ((f : R) ^ N * (f : R) ^ (j n)) * E2 - E4 + he

  have hgA : ∀ (g : G) (s : ↥A) (x : R), g • ((s : R) * x) = (s : R) * g • x := fun g s x => by
    rw [smul_mul', (mem_fixedPoints_subalgebra_iff.1 s.2) g]
  let d : R →ₗ[↥A] (G → R) :=
    { toFun := fun y g => g • y - y
      map_add' := fun y y' => funext fun g => by simp only [Pi.add_apply, smul_add]; ring
      map_smul' := fun s y => funext fun g => by
        simp only [RingHom.id_apply, Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
        rw [hgA]; ring }
  have hd : ∀ (y : R) (g : G), d y g = g • y - y := fun y g => rfl
  obtain ⟨N', e', a₀, hu⟩ := exists_mul_sub_mul_smul_eq_zero (M := (G → R) ⧸ LinearMap.range d)
    f (algebraMap 𝒪 ↥A π) (Submodule.Quotient.mk (c n)) (fun i => by
      obtain ⟨N, y, hy⟩ := step4 i
      refine ⟨N + j (n + i), N + j n, Submodule.Quotient.mk (c (n + i)), ?_⟩
      rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      refine ⟨y, funext fun g => ?_⟩
      rw [hd]
      simp only [Pi.sub_apply, Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      push_cast
      rw [hy]; ring)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at hu
  obtain ⟨y, hy⟩ := hu
  have hy' : ∀ g : G, g • y - y = ((f ^ N' * (f ^ e' - algebraMap 𝒪 ↥A π * a₀) : ↥A) : R) * c n g := fun g => by
    have := congrFun hy g
    rw [hd] at this
    rw [this, Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]

  set u : ↥A := f ^ N' * (f ^ e' - algebraMap 𝒪 ↥A π * a₀) with hudef
  have hucoe : (u : R) = (f : R) ^ N' * ((f : R) ^ e' - ϖ * (a₀ : R)) := by
    rw [hudef]; push_cast; rfl
  refine ⟨(u : R) * r n - ϖ ^ (n + 1) * y, fun g => ?_, N', e', j n, a₀, ?_⟩
  · have E1 := hc n g
    have E3 := hy' g
    rw [smul_sub, hgA, hgϖ]
    linear_combination (u : R) * E1 - ϖ ^ (n + 1) * E3
  · have hresϖ : res ϖ = ϖ' := res.commutes π
    have : res ((u : R) * r n - ϖ ^ (n + 1) * y) - res ((f : R) ^ N' * ((f : R) ^ e' - ϖ * (a₀ : R)) * (f : R) ^ j n) * b'
        = -(res (u : R) * (res ((f : R) ^ j n) * b' - res (r n))) - res y * ϖ' ^ (n + 1) := by
      rw [← hucoe]; simp only [map_sub, map_mul, map_pow, hresϖ]; ring
    rw [this]
    exact Ideal.sub_mem _ ((Ideal.neg_mem_iff _).2 (Ideal.mul_mem_left _ _ (hE n)))
      (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

theorem exists_mul_pow_eq_of_pow_eq_zero {T S : Type*} [CommRing T] [CommRing S] (φ : T →+* S)
    (f p a₀ a : T) (N e j n : ℕ) (hp : p ^ (n + 1) = 0) (z : S)
    (hz : φ a = φ (f ^ N * (f ^ e - p * a₀) * f ^ j) * z) :
    ∃ (K : ℕ) (a'' : T), z * φ f ^ K = φ a'' := by
  refine ⟨N + j + e * (n + 1), a * ∑ i ∈ Finset.range (n + 1), (f ^ e) ^ i * (p * a₀) ^ (n + 1 - 1 - i), ?_⟩
  have key : (∑ i ∈ Finset.range (n + 1), (f ^ e) ^ i * (p * a₀) ^ (n + 1 - 1 - i)) * (f ^ e - p * a₀) =
      (f ^ e) ^ (n + 1) := by
    rw [geom_sum₂_mul, mul_pow p a₀, hp, zero_mul, sub_zero]
  rw [map_mul, hz, mul_comm (φ _) z, mul_assoc, ← map_mul,
    show f ^ N * (f ^ e - p * a₀) * f ^ j * (∑ i ∈ Finset.range (n + 1), (f ^ e) ^ i * (p * a₀) ^ (n + 1 - 1 - i)) =
      f ^ N * f ^ j * ((∑ i ∈ Finset.range (n + 1), (f ^ e) ^ i * (p * a₀) ^ (n + 1 - 1 - i)) * (f ^ e - p * a₀)) by ring,
    key, ← pow_mul, ← pow_add, ← pow_add, map_pow]

theorem isLocalizationAway_fixedPoints_quotient
    (htf : ∀ x : R, ϖ * x = 0 → x = 0) (htf' : ∀ x : R', ϖ' * x = 0 → x = 0)
    (hc' : IsAdicComplete (Ideal.span {ϖ'}) R')
    [IsNoetherianRing ↥A] [Module.Finite ↥A R]
    (res : R →ₐ[𝒪] R') (hres_smul : ∀ (g : G) (r : R), res (g • r) = g • res r)
    (f : ↥A)
    (hunit : ∀ m : ℕ, IsUnit (Ideal.Quotient.mk (Ideal.span {ϖ' ^ (m + 1)}) (res (f : R))))
    (hsurj : ∀ (m : ℕ) (z : R'), ∃ (r : R) (j : ℕ), res ((f : R) ^ j) * z - res r ∈ Ideal.span {ϖ' ^ (m + 1)})
    (hker : ∀ (m : ℕ) (r : R), res r ∈ Ideal.span {ϖ' ^ (m + 1)} → ∃ j : ℕ, (f : R) ^ j * r ∈ Ideal.span {ϖ ^ (m + 1)})
    (n : ℕ)
    (resA : ↥A →+* ↥A') (hresA : ∀ x : ↥A, (resA x : R') = res (x : R))
    (q : (↥A ⧸ Ideal.span {algebraMap 𝒪 ↥A π ^ (n + 1)}) →+* (↥A' ⧸ Ideal.span {algebraMap 𝒪 ↥A' π ^ (n + 1)}))
    (hq : ∀ x : ↥A, q (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (resA x)) :
    letI := q.toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 ↥A π ^ (n + 1)}) f)
      (↥A' ⧸ Ideal.span {algebraMap 𝒪 ↥A' π ^ (n + 1)}) := by
  classical
  letI := q.toAlgebra
  have halg : ∀ x, algebraMap (↥A ⧸ Ideal.span {algebraMap 𝒪 ↥A π ^ (n + 1)})
      (↥A' ⧸ Ideal.span {algebraMap 𝒪 ↥A' π ^ (n + 1)}) x = q x := fun x => rfl
  have hcoeϖ : ((algebraMap 𝒪 ↥A π : ↥A) : R) = ϖ := rfl
  have hcoeϖ' : ((algebraMap 𝒪 ↥A' π : ↥A') : R') = ϖ' := rfl
  apply IsLocalization.Away.mk
  ·
    rw [halg, hq]
    haveI := hc'
    have hu : IsUnit (res (f : R)) := isUnit_of_isUnit_mk ϖ' (res (f : R)) (hunit 0)
    obtain ⟨w, hw⟩ := hu.exists_right_inv
    have hwinv : ∀ g : G, g • w = w := fun g => by
      have h1 : res (f : R) * (g • w) = 1 := by
        have := congrArg (fun z => g • z) hw
        simp only [smul_mul', smul_one, ← hres_smul, (mem_fixedPoints_subalgebra_iff.1 f.2) g] at this
        exact this
      calc g • w = (w * res (f : R)) * (g • w) := by rw [mul_comm w, hw, one_mul]
        _ = w := by rw [mul_assoc, h1, mul_one]
    have : IsUnit (resA f) := by
      refine isUnit_iff_exists_inv.2 ⟨⟨w, mem_fixedPoints_subalgebra_iff.2 hwinv⟩, Subtype.ext ?_⟩
      push_cast
      rw [hresA, hw]
    exact this.map _
  ·
    intro z
    obtain ⟨zb, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, ha, N, e, j, a₀, hmem⟩ := exists_fixed_sub_mul_mem 𝒪 π G R R' htf res hres_smul f hsurj hker n
      (zb : R') (mem_fixedPoints_subalgebra_iff.1 zb.2)

    have ht : resA ⟨a, mem_fixedPoints_subalgebra_iff.2 ha⟩ -
        resA (f ^ N * (f ^ e - algebraMap 𝒪 ↥A π * a₀) * f ^ j) * zb ∈ Ideal.span {algebraMap 𝒪 ↥A' π ^ (n + 1)} := by
      apply mem_span_pow_of_coe_mem π htf' (n + 1)
      push_cast
      rw [hresA, hresA]
      exact hmem
    have hz : q (Ideal.Quotient.mk _ ⟨a, mem_fixedPoints_subalgebra_iff.2 ha⟩) =
        q (Ideal.Quotient.mk _ (f ^ N * (f ^ e - algebraMap 𝒪 ↥A π * a₀) * f ^ j)) * Ideal.Quotient.mk _ zb := by
      rw [hq, hq, ← map_mul, Ideal.Quotient.eq]
      exact ht
    have hϖq : (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 ↥A π ^ (n + 1)}) (algebraMap 𝒪 ↥A π)) ^ (n + 1) = 0 := by
      rw [← map_pow (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 ↥A π ^ (n + 1)})) (algebraMap 𝒪 ↥A π) (n + 1),
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    obtain ⟨K, a'', hK⟩ := exists_mul_pow_eq_of_pow_eq_zero q (Ideal.Quotient.mk _ f)
      (Ideal.Quotient.mk _ (algebraMap 𝒪 ↥A π)) (Ideal.Quotient.mk _ a₀) (Ideal.Quotient.mk _ ⟨a, mem_fixedPoints_subalgebra_iff.2 ha⟩)
      N e j n hϖq (Ideal.Quotient.mk _ zb) (by simpa only [map_mul, map_sub, map_pow] using hz)
    exact ⟨K, a'', by rw [halg, halg]; exact hK⟩
  ·
    intro x y hxy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [halg, halg, hq, hq, Ideal.Quotient.eq] at hxy
    have hR' : res ((x : R) - (y : R)) ∈ Ideal.span {ϖ' ^ (n + 1)} := by
      rw [Ideal.mem_span_singleton'] at hxy ⊢
      obtain ⟨t, ht⟩ := hxy
      refine ⟨(t : R'), ?_⟩
      have := congrArg Subtype.val ht
      push_cast at this
      rw [hresA, hresA] at this
      rw [map_sub]
      exact this
    obtain ⟨k, hk⟩ := hker n _ hR'
    have hA := mem_span_pow_of_coe_mem π htf (n + 1) (f ^ k * (x - y)) (by push_cast; exact hk)
    refine ⟨k, ?_⟩
    have : Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 ↥A π ^ (n + 1)}) (f ^ k * x) =
        Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 ↥A π ^ (n + 1)}) (f ^ k * y) :=
      (Ideal.Quotient.eq).2 (by rw [← mul_sub]; exact hA)
    simpa only [map_mul, map_pow] using this

end Heart
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

end F4Cover12.G2
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

namespace F4Cover12

namespace NoethWs7

theorem isNoetherianRing_of_isAdicComplete_of_quotient
    (R : Type) [CommRing R] (ϖ : R) (hc : IsAdicComplete (Ideal.span {ϖ}) R)
    (hN : IsNoetherianRing (R ⧸ Ideal.span {ϖ})) : IsNoetherianRing R := by
  classical
  obtain ⟨I, hI⟩ : ∃ I : Ideal R, Ideal.span {ϖ} = I := ⟨_, rfl⟩
  rw [hI] at hc hN
  haveI := hN
  have hpow : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by rw [smul_eq_mul, Ideal.mul_top]
  have hImem : ∀ {n : ℕ} {x : R}, x ∈ I ^ n ↔ ∃ t, x = ϖ ^ n * t := fun {n x} => by
    rw [← hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨fun ⟨t, ht⟩ => ⟨t, by rw [← ht, mul_comm]⟩, fun ⟨t, ht⟩ => ⟨t, by rw [ht, mul_comm]⟩⟩
  apply IsNoetherianRing.of_prime
  intro P hP

  set mk := Ideal.Quotient.mk I with hmk
  obtain ⟨S, hS⟩ := (isNoetherianRing_iff_ideal_fg (R ⧸ I)).1 hN (P.map mk)
  have hlift : ∀ s : ↥S, ∃ g : R, g ∈ P ∧ mk g = (s : R ⧸ I) := fun s => by
    have : (s : R ⧸ I) ∈ P.map mk := by rw [← hS]; exact Ideal.subset_span s.2
    obtain ⟨g, hg, hgs⟩ := (Ideal.mem_map_iff_of_surjective mk Ideal.Quotient.mk_surjective).1 this
    exact ⟨g, hg, hgs⟩
  choose g hgP hgmk using hlift
  set G : Ideal R := Ideal.span (Set.range g) with hG
  have hGP : G ≤ P := Ideal.span_le.2 (by rintro _ ⟨s, rfl⟩; exact hgP s)
  have hmapG : G.map mk = P.map mk := by
    rw [hG, Ideal.map_span, ← hS]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩; rw [hgmk]; exact s.2
    · intro hy; exact ⟨g ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, hgmk ⟨y, hy⟩⟩

  have hPGI : P ≤ G ⊔ I := by
    calc P ≤ (P.map mk).comap mk := Ideal.le_comap_map
      _ = (G.map mk).comap mk := by rw [hmapG]
      _ = G ⊔ I := by
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

  have hstep0 : ∀ x ∈ P, ∃ (c : ↥S → R) (x' : R), x = (∑ i, c i * g i) + ϖ * x' := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hPGI hx)
    obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hy
    rw [← hI] at hz
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨c, t, by rw [mul_comm]⟩
  by_cases hϖ : ϖ ∈ P
  ·
    have hIP : I ≤ P := by
      rw [← hI, Ideal.span_le]; simpa using hϖ
    have hPeq : P = G ⊔ I := le_antisymm hPGI (sup_le hGP hIP)
    rw [hPeq]
    refine Submodule.FG.sup ⟨Finset.univ.image g, ?_⟩ ⟨{ϖ}, ?_⟩
    · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    · rw [Finset.coe_singleton]; exact hI
  ·
    have hstep : ∀ x : ↥P, ∃ (c : ↥S → R) (x' : ↥P), x.1 = (∑ i, c i * g i) + ϖ * x'.1 := by
      intro x
      obtain ⟨c, x', hx'⟩ := hstep0 x x.2
      have hx'P : x' ∈ P := by
        have hmem : ϖ * x' ∈ P := by
          have : ϖ * x' = x - ∑ i, c i * g i := by rw [hx']; ring
          rw [this]
          exact P.sub_mem x.2 (P.sum_mem fun i _ => P.mul_mem_left _ (hgP i))
        exact ((hP.mem_or_mem hmem).resolve_left hϖ)
      exact ⟨c, ⟨x', hx'P⟩, hx'⟩
    choose cf nx hnx using hstep
    suffices hPG : P ≤ G by
      rw [le_antisymm hPG hGP]
      exact ⟨Finset.univ.image g, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
    intro p hp

    let sq : ℕ → ↥P := fun k => nx^[k] ⟨p, hp⟩
    have sq_zero : sq 0 = ⟨p, hp⟩ := rfl
    have sq_succ : ∀ k, sq (k + 1) = nx (sq k) := fun k => Function.iterate_succ_apply' nx k _
    let A : ↥S → ℕ → R := fun i k => ∑ j ∈ Finset.range k, ϖ ^ j * cf (sq j) i

    have hinv : ∀ k, p = (∑ i, A i k * g i) + ϖ ^ k * (sq k).1 := by
      intro k
      induction k with
      | zero => simp [A, sq_zero]
      | succ k ih =>
        have h := hnx (sq k)
        have e1 : ∑ i, A i (k + 1) * g i = ∑ i, A i k * g i + ∑ i, ϖ ^ k * cf (sq k) i * g i := by
          simp only [A, Finset.sum_range_succ, add_mul, Finset.sum_add_distrib]
        have e2 : ∑ i, ϖ ^ k * cf (sq k) i * g i = ϖ ^ k * ∑ i, cf (sq k) i * g i := by
          rw [Finset.mul_sum]; simp only [mul_assoc]
        rw [ih, e1, e2, sq_succ, h, pow_succ]
        ring

    have hA : ∀ (i : ↥S) {m n : ℕ}, m ≤ n → A i m ≡ A i n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
      intro i m n hmn
      rw [SModEq.sub_mem, hpow]
      have : A i m - A i n = -(∑ j ∈ Finset.Ico m n, ϖ ^ j * cf (sq j) i) := by
        simp only [A]
        rw [← Finset.sum_range_add_sum_Ico _ hmn]; ring
      rw [this]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
      have hmj : m ≤ j := (Finset.mem_Ico.1 hj).1
      exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hmj (Ideal.pow_mem_pow (hI ▸ Ideal.subset_span rfl) j))

    have hL : ∀ i : ↥S, ∃ L : R, ∀ n, A i n ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] :=
      fun i => hc.toIsPrecomplete.prec' (A i) (hA i)
    choose L hLspec using hL

    have hzero : p - ∑ i, L i * g i = 0 := by
      apply hc.toIsHausdorff.haus'
      intro n
      rw [SModEq.sub_mem, sub_zero, hpow]
      have e : p - ∑ i, L i * g i = ϖ ^ n * (sq n).1 + ∑ i, (A i n - L i) * g i := by
        conv_lhs => rw [hinv n]
        simp only [sub_mul, Finset.sum_sub_distrib]; ring
      rw [e]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hI ▸ Ideal.subset_span rfl) n))
        (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_)
      have := hLspec i n
      rw [SModEq.sub_mem, hpow] at this
      exact this
    rw [sub_eq_zero] at hzero
    rw [hzero, hG]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end NoethWs7
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

theorem isNoetherianRing_and_finite_fixedPoints
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (R : Type) [CommRing R] [Algebra 𝒪 R]
    (hRc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (hRtf : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0)
    (hRft : Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}))
    (G : Type) [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R] :
    IsNoetherianRing ↥(FixedPoints.subalgebra 𝒪 R G) ∧ Module.Finite ↥(FixedPoints.subalgebra 𝒪 R G) R := by
  obtain ⟨hAc, hfin, hAft, -⟩ :=
    AlgebraicGeometry.AdmissibleAlgebra.fixedPoints_isAdicComplete_and_finite_and_finiteType 𝒪 hdvr π hπ hcomplete R hRc hRtf
      hRft G
  refine ⟨?_, hfin⟩
  haveI : IsDiscreteValuationRing 𝒪 := hdvr
  haveI : IsNoetherianRing 𝒪 := inferInstance
  haveI := hAft
  haveI : IsNoetherianRing (↥(FixedPoints.subalgebra 𝒪 R G) ⧸
      Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π}) :=
    Algebra.FiniteType.isNoetherianRing 𝒪 _
  exact NoethWs7.isNoetherianRing_of_isAdicComplete_of_quotient _ _ hAc this

end F4Cover12
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

namespace F4Cover12

section Charts

variable (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hproper : ∀ n : ℕ, IsProper (xb n)) (hflat : ∀ n : ℕ, Flat (xb n))
    (haff : ∀ (n : ℕ) (S : Set (X n)), S.Finite → ∃ U : (X n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (X n)))
    (G : Type) [Group G] [Finite G] (a : ∀ n : ℕ, G →* Aut (X n))
    (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (hcov : ∀ x : X 0, ∃ U : (X 0).Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (a 0 g).hom ⁻¹ᵁ U = U)

include hcart in

theorem isHomeomorph_xt (n : ℕ) : IsHomeomorph (xt n).base := by
  have hle : Ideal.span {π ^ (n + 1 + 1)} ≤ Ideal.span {π ^ (n + 1)} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))
  let φ := Ideal.Quotient.factor hle
  have hφ : Function.Surjective φ := Ideal.Quotient.factor_surjective hle
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) := IsClosedImmersion.spec_of_surjective _ hφ
  haveI : Surjective (Spec.map (CommRingCat.ofHom φ)) := by
    refine ⟨fun y => ?_⟩
    have hy : y ∈ Set.range (PrimeSpectrum.comap φ) := by
      rw [range_comap_of_surjective _ _ hφ]
      refine (PrimeSpectrum.mem_zeroLocus _ _).2 fun x hx => ?_
      rw [SetLike.mem_coe, RingHom.mem_ker] at hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hx' : x ∈ Ideal.span {π ^ (n + 1)} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]; rwa [Ideal.Quotient.factor_mk] at hx

      apply y.2.mem_of_pow_mem 2
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2]
      · exact y.asIdeal.zero_mem
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
      refine Ideal.mem_span_singleton'.2 ⟨c * c * π ^ n, ?_⟩
      ring
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, hx⟩
  haveI : IsClosedImmersion (xt n) := MorphismProperty.of_isPullback (hcart n).flip inferInstance
  haveI : Surjective (xt n) := MorphismProperty.of_isPullback (hcart n).flip inferInstance
  exact isHomeomorph_iff_isEmbedding_surjective.2 ⟨(xt n).isClosedEmbedding.isEmbedding, (xt n).surjective⟩

include hcart hflat hπ in

theorem isAffineOpen_of_preimage_xt (n : ℕ) (U : (X (n + 1)).Opens) (hU : IsAffineOpen ((xt n) ⁻¹ᵁ U)) : IsAffineOpen U :=
  AlgebraicGeometry.isAffineOpen_of_isAffineOpen_preimage_of_isPullback_of_flat 𝒪 π hπ X xb xt hcart hflat n U hU

include hπ hcart hflat ha_xt hcov in

theorem exists_gchain (n : ℕ) (x : X n) : ∃ C : GChain X xt G a, x ∈ C.W n := by
  classical
  have hhom := isHomeomorph_xt 𝒪 π X xb xt hcart

  have key : ∀ x₀ : X 0, ∃ C : GChain X xt G a, x₀ ∈ C.W 0 := by
    intro x₀
    obtain ⟨U₀, hU₀aff, hx₀, hU₀st⟩ := hcov x₀

    let W : ∀ m : ℕ, (X m).Opens := fun m =>
      Nat.rec (motive := fun m => (X m).Opens) U₀
        (fun m Wm => ⟨(xt m).base '' (Wm : Set (X m)), (hhom m).isOpenMap _ Wm.isOpen⟩) m
    have hWzero : W 0 = U₀ := rfl
    have hWsucc : ∀ (m : ℕ) (y : X (m + 1)), y ∈ W (m + 1) ↔ y ∈ (xt m).base '' (W m : Set (X m)) := fun m y => Iff.rfl
    have hcompat : ∀ m : ℕ, (xt m) ⁻¹ᵁ (W (m + 1)) = W m := by
      intro m
      ext y
      show (xt m).base y ∈ W (m + 1) ↔ y ∈ (W m : Set (X m))
      rw [hWsucc, (hhom m).injective.mem_set_image]
    have hstable : ∀ (m : ℕ) (g : G), (a m g).hom ⁻¹ᵁ (W m) = W m := by
      intro m
      induction m with
      | zero => exact hU₀st
      | succ m ih =>
        intro g
        ext y
        obtain ⟨y', rfl⟩ := (hhom m).surjective y
        show (a (m + 1) g).hom.base ((xt m).base y') ∈ W (m + 1) ↔ (xt m).base y' ∈ W (m + 1)
        have hpt : (a (m + 1) g).hom.base ((xt m).base y') = (xt m).base ((a m g).hom.base y') := by
          have := congrArg (fun f : X m ⟶ X (m + 1) => f.base y') (ha_xt m g)
          exact this.symm
        rw [hpt, hWsucc, hWsucc, (hhom m).injective.mem_set_image, (hhom m).injective.mem_set_image]
        show (a m g).hom.base y' ∈ (W m : Set (X m)) ↔ y' ∈ (W m : Set (X m))
        have := congrArg (fun V : (X m).Opens => (y' ∈ V)) (ih g)
        exact Iff.of_eq this
    have haffine : ∀ m : ℕ, IsAffineOpen (W m) := by
      intro m
      induction m with
      | zero => exact hU₀aff
      | succ m ih => exact isAffineOpen_of_preimage_xt 𝒪 π hπ X xb xt hcart hflat m _ (by rw [hcompat]; exact ih)
    exact ⟨{ W := W, affine := haffine, stable := hstable, compat := hcompat }, hx₀⟩

  induction n with
  | zero => exact key x
  | succ n ih =>
    obtain ⟨x', rfl⟩ := (hhom n).surjective x
    obtain ⟨C, hC⟩ := ih x'
    refine ⟨C, ?_⟩
    have : x' ∈ (xt n) ⁻¹ᵁ (C.W (n + 1)) := by rw [C.compat]; exact hC
    exact this

include hproper in

theorem gchain_inf (C C' : GChain X xt G a) : ∃ C'' : GChain X xt G a, ∀ n : ℕ, C''.W n = C.W n ⊓ C'.W n := by
  have hsep : ∀ n : ℕ, IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from (X n))) := by
    intro n
    haveI := hproper n
    have : Limits.terminal.from (X n) = xb n ≫ Limits.terminal.from _ := Limits.terminal.hom_ext _ _
    haveI : IsSeparated (Limits.terminal.from (X n)) := by rw [this]; infer_instance
    haveI : IsClosedImmersion (Limits.pullback.diagonal (Limits.terminal.from (X n))) := IsSeparated.isClosedImmersion_diagonal
    infer_instance
  refine ⟨{ W := fun n => C.W n ⊓ C'.W n
            affine := fun n => (C.affine n).inf (C'.affine n)
            stable := fun n g => by rw [Scheme.Hom.preimage_inf, C.stable, C'.stable]
            compat := fun n => by rw [Scheme.Hom.preimage_inf, C.compat, C'.compat] }, fun n => rfl⟩

include hdvr hπ hcomplete hcart hproper hflat ha_over ha_xt in

theorem nonempty_chartRing (C : GChain X xt G a) : Nonempty (ChartRing 𝒪 π X xb xt G a C) := by
  classical

  let ρ : ∀ n : ℕ, Γ(X (n + 1), C.W (n + 1)) →+* Γ(X n, C.W n) :=
    fun n => ((xt n).appLE (C.W (n + 1)) (C.W n) (by rw [C.compat])).hom

  let Rsub : Subring (∀ n : ℕ, Γ(X n, C.W n)) := limSubring ρ

  let s : ∀ n : ℕ, 𝒪 →+* Γ(X n, C.W n) := fun n =>
    ((xb n).appLE ⊤ (C.W n) le_top).hom.comp
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv.hom.comp
        (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)})))

  have hs : ∀ (n : ℕ) (o : 𝒪), ρ n (s (n + 1) o) = s n o := by
    intro n o
    let φ : CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)}) ⟶ CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) :=
      CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))
    have hw : xt n ≫ xb (n + 1) = xb n ≫ Spec.map φ := (hcart n).w
    show ((xb (n + 1)).appLE ⊤ (C.W (n + 1)) le_top ≫ (xt n).appLE (C.W (n + 1)) (C.W n) (by rw [C.compat]))
        ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1 + 1)}))).inv (Ideal.Quotient.mk _ o)) =
      ((xb n).appLE ⊤ (C.W n) le_top) ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))
    rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hw ⊤ (C.W n) _ le_top,
      ← Scheme.Hom.appLE_comp_appLE (xb n) (Spec.map φ) ⊤ ⊤ (C.W n) le_top le_top]
    show ((xb n).appLE ⊤ (C.W n) le_top) (((Spec.map φ).appLE ⊤ ⊤ le_top)
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
  let sR : 𝒪 →+* ↥Rsub :=
    { toFun := fun o => ⟨fun n => s n o, fun n => hs n o⟩
      map_one' := Subtype.ext (funext fun n => by simp)
      map_mul' := fun o o' => Subtype.ext (funext fun n => by simp)
      map_zero' := Subtype.ext (funext fun n => by simp)
      map_add' := fun o o' => Subtype.ext (funext fun n => by simp) }
  letI : Algebra 𝒪 ↥Rsub := sR.toAlgebra

  let τ : ∀ (n : ℕ) (g : G), Γ(X n, C.W n) →+* Γ(X n, C.W n) :=
    fun n g => ((a n g⁻¹).hom.appLE (C.W n) (C.W n) (by rw [C.stable])).hom

  have hτρ : ∀ (n : ℕ) (g : G) (y : Γ(X (n + 1), C.W (n + 1))), ρ n (τ (n + 1) g y) = τ n g (ρ n y) := by
    intro n g y
    show ((a (n + 1) g⁻¹).hom.appLE (C.W (n + 1)) (C.W (n + 1)) (by rw [C.stable]) ≫ (xt n).appLE (C.W (n + 1)) (C.W n) (by rw [C.compat])) y =
      ((xt n).appLE (C.W (n + 1)) (C.W n) (by rw [C.compat]) ≫ (a n g⁻¹).hom.appLE (C.W n) (C.W n) (by rw [C.stable])) y
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (ha_xt n g⁻¹).symm]

  have hτ_one : ∀ (n : ℕ) (y : Γ(X n, C.W n)), τ n 1 y = y := by
    intro n y
    have h1 : (a n 1⁻¹).hom = 𝟙 (X n) := by rw [inv_one, map_one]; rfl
    have key : ∀ (e : C.W n ≤ (𝟙 (X n)) ⁻¹ᵁ C.W n), (𝟙 (X n) : X n ⟶ X n).appLE (C.W n) (C.W n) e = 𝟙 _ := by
      intro e
      rw [Scheme.Hom.appLE, show homOfLE e = 𝟙 (C.W n) from Subsingleton.elim _ _]
      erw [CategoryTheory.op_id, CategoryTheory.Functor.map_id, Category.comp_id]
      simp
    have e1 : C.W n ≤ (𝟙 (X n)) ⁻¹ᵁ C.W n := le_of_eq (by simp)
    have : (a n 1⁻¹).hom.appLE (C.W n) (C.W n) (by rw [C.stable]) = 𝟙 _ :=
      (appLE_congr_hom h1 (C.W n) (C.W n) _ e1).trans (key e1)
    show ((a n 1⁻¹).hom.appLE (C.W n) (C.W n) (by rw [C.stable])) y = y
    rw [this]; rfl
  have hτ_mul : ∀ (n : ℕ) (g h : G) (y : Γ(X n, C.W n)), τ n (g * h) y = τ n g (τ n h y) := by
    intro n g h y
    have hm : (a n (g * h)⁻¹).hom = (a n g⁻¹).hom ≫ (a n h⁻¹).hom := by
      rw [mul_inv_rev, map_mul, Aut.Aut_mul_def]; rfl
    show ((a n (g * h)⁻¹).hom.appLE (C.W n) (C.W n) (by rw [C.stable])) y =
      ((a n h⁻¹).hom.appLE (C.W n) (C.W n) (by rw [C.stable]) ≫ (a n g⁻¹).hom.appLE (C.W n) (C.W n) (by rw [C.stable])) y
    rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hm]

  have hτs : ∀ (n : ℕ) (g : G) (o : 𝒪), τ n g (s n o) = s n o := by
    intro n g o
    show ((xb n).appLE ⊤ (C.W n) le_top ≫ (a n g⁻¹).hom.appLE (C.W n) (C.W n) (by rw [C.stable]))
        ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)) =
      ((xb n).appLE ⊤ (C.W n) le_top) ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))
    rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom (ha_over n g⁻¹)]
  letI : MulSemiringAction G ↥Rsub :=
    { smul := fun g f => ⟨fun n => τ n g (f.1 n), fun n => by rw [hτρ, f.2 n]⟩
      one_smul := fun f => Subtype.ext (funext fun n => hτ_one n (f.1 n))
      mul_smul := fun g h f => Subtype.ext (funext fun n => hτ_mul n g h (f.1 n))
      smul_zero := fun g => Subtype.ext (funext fun n => by show τ n g 0 = 0; exact map_zero _)
      smul_add := fun g f f' => Subtype.ext (funext fun n => by show τ n g (f.1 n + f'.1 n) = _; exact map_add _ _ _)
      smul_one := fun g => Subtype.ext (funext fun n => by show τ n g 1 = 1; exact map_one _)
      smul_mul := fun g f f' => Subtype.ext (funext fun n => by show τ n g (f.1 n * f'.1 n) = _; exact map_mul _ _ _) }
  haveI : SMulCommClass G 𝒪 ↥Rsub :=
    ⟨fun g o f => Subtype.ext (funext fun n => by
      show τ n g (s n o * f.1 n) = s n o * τ n g (f.1 n)
      rw [map_mul, hτs])⟩

  let sq : ∀ m : ℕ, (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) →+* Γ(X m, C.W m) := fun m =>
    ((xb m).appLE ⊤ (C.W m) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (m + 1)}))).inv.hom
  have hsq : ∀ (m : ℕ) (o : 𝒪), sq m (Ideal.Quotient.mk _ o) = s m o := fun m o => rfl
  have hsqflat : ∀ m : ℕ, (sq m).Flat := by
    intro m
    have h1 : ((xb m).appLE ⊤ (C.W m) le_top).hom.Flat :=
      HasRingHomProperty.appLE @Flat (xb m) (hflat m) ⟨⊤, isAffineOpen_top _⟩ ⟨C.W m, C.affine m⟩ le_top
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (m + 1)}))).inv.hom.Flat :=
      RingHom.Flat.of_bijective (Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (m + 1)}))).commRingCatIsoToRingEquiv.symm.bijective
    exact RingHom.Flat.comp h2 h1
  have hlevel_tors : ∀ (m j : ℕ) (hj : j ≤ m + 1) (y : Γ(X m, C.W m)), (s m π) ^ j * y = 0 →
      ∃ z : Γ(X m, C.W m), y = (s m π) ^ (m + 1 - j) * z := by
    intro m j hj y hy
    letI : Algebra (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) Γ(X m, C.W m) := (sq m).toAlgebra
    haveI : Module.Flat (𝒪 ⧸ Ideal.span {π ^ (m + 1)}) Γ(X m, C.W m) := hsqflat m
    have hπ0 : π ≠ 0 := hπ.ne_zero
    obtain ⟨z, hz⟩ := smul_pow_eq_zero_imp_of_flat 𝒪 π hπ0 (m + 1) Γ(X m, C.W m) j hj y (by
      rw [Algebra.smul_def, map_pow]; show (sq m (Ideal.Quotient.mk _ π)) ^ j * y = 0; rw [hsq]; exact hy)
    refine ⟨z, ?_⟩
    rw [hz, Algebra.smul_def, map_pow]; show (sq m (Ideal.Quotient.mk _ π)) ^ (m + 1 - j) * z = _; rw [hsq]
  have hlevel_nil : ∀ m : ℕ, (s m π) ^ (m + 1) = 0 := by
    intro m
    rw [← map_pow, ← hsq, show Ideal.Quotient.mk (Ideal.span {π ^ (m + 1)}) (π ^ (m + 1)) = 0 from
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl), map_zero]

  have L1_surj : ∀ m : ℕ, Function.Surjective (ρ m) := fun m =>
    (level_surjective_and_ker 𝒪 π m (X m) (X (m + 1)) (xb m) (xb (m + 1)) (xt m) (hcart m)
        (C.W m) (C.affine m) (C.W (m + 1)) (C.affine (m + 1)) (C.compat m) (by rw [C.compat])).1
  have L1_ker : ∀ (m : ℕ) (y : Γ(X (m + 1), C.W (m + 1))), ρ m y = 0 →
      ∃ z : Γ(X (m + 1), C.W (m + 1)), y = (s (m + 1) π) ^ (m + 1) * z := fun m y hy =>
    ((level_surjective_and_ker 𝒪 π m (X m) (X (m + 1)) (xb m) (xb (m + 1)) (xt m) (hcart m)
        (C.W m) (C.affine m) (C.W (m + 1)) (C.affine (m + 1)) (C.compat m) (by rw [C.compat])).2 y).1 hy

  have hlvl : ∀ n : ℕ, ∃ e : (↥Rsub ⧸ Ideal.span {algebraMap 𝒪 (↥Rsub) π ^ (n + 1)}) ≃+* Γ(X n, C.W n),
      (∀ f : ↥Rsub, e (Ideal.Quotient.mk _ f) = f.1 n) := fun n =>
    limSubring_exists_levelEquiv (algebraMap 𝒪 (↥Rsub) π) L1_surj L1_ker hlevel_nil hlevel_tors n
  choose lvl hlvl' using hlvl
  have hcompleteR : IsAdicComplete (Ideal.span {algebraMap 𝒪 (↥Rsub) π}) ↥Rsub :=
    limSubring_isAdicComplete (algebraMap 𝒪 (↥Rsub) π) L1_surj L1_ker hlevel_nil hlevel_tors
  have htf : ∀ x : ↥Rsub, algebraMap 𝒪 (↥Rsub) π * x = 0 → x = 0 := by
    intro x hx
    apply Subtype.ext; funext m
    have hm : s (m + 1) π * x.1 (m + 1) = 0 := by
      have := congrArg (fun f : ↥Rsub => f.1 (m + 1)) hx
      exact this
    obtain ⟨z, hz⟩ := hlevel_tors (m + 1) 1 (by omega) (x.1 (m + 1)) (by simpa using hm)
    show x.1 m = 0
    rw [← x.2 m, hz, map_mul, map_pow, hs, Nat.add_sub_cancel, hlevel_nil, zero_mul]
  have hcompat : ∀ (n : ℕ) (r : ↥Rsub),
      (xt n).appLE (C.W (n + 1)) (C.W n) (by rw [C.compat]) (lvl (n + 1) (Ideal.Quotient.mk _ r)) = lvl n (Ideal.Quotient.mk _ r) := by
    intro n r; rw [hlvl', hlvl']; exact r.2 n
  have hsmul : ∀ (n : ℕ) (g : G) (r : ↥Rsub),
      (a n g⁻¹).hom.appLE (C.W n) (C.W n) (by rw [C.stable]) (lvl n (Ideal.Quotient.mk _ r)) = lvl n (Ideal.Quotient.mk _ (g • r)) := by
    intro n g r; rw [hlvl', hlvl']; rfl
  have halg : ∀ (n : ℕ) (o : 𝒪), lvl n (Ideal.Quotient.mk _ (algebraMap 𝒪 (↥Rsub) o)) =
      (xb n).appLE ⊤ (C.W n) le_top ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)) := by
    intro n o; rw [hlvl']; rfl

  have hft : Algebra.FiniteType 𝒪 (↥Rsub ⧸ Ideal.span {algebraMap 𝒪 (↥Rsub) π}) := by
    haveI := hproper 0
    exact finiteType_quotient_of_level 𝒪 π 0 (X 0) (xb 0) (C.W 0) (C.affine 0) ↥Rsub (lvl 0) (halg 0)
  exact ⟨{ R := ↥Rsub, complete := hcompleteR, torsionFree := htf, finiteType := hft, lvl := lvl, lvl_compat := hcompat, lvl_smul := hsmul, lvl_algebraMap := halg }⟩

abbrev ChartRing.A {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) : Subalgebra 𝒪 RC.R :=
  FixedPoints.subalgebra 𝒪 RC.R G

structure Pieces (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) : Type 2 where

  Y : ℕ → Scheme.{0}

  yb : ∀ n : ℕ, Y n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))

  yt : ∀ n : ℕ, Y n ⟶ Y (n + 1)

  p : ∀ n : ℕ, X n ⟶ Y n

  p_over : ∀ n : ℕ, p n ≫ yb n = xb n

  p_xt : ∀ n : ℕ, xt n ≫ p (n + 1) = p n ≫ yt n

  p_inv : ∀ (n : ℕ) (g : G), (a n g).hom ≫ p n = p n

  yt_over : ∀ n : ℕ, yt n ≫ yb (n + 1) =
    yb n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))

  V : ∀ (C : GChain X xt G a) (n : ℕ), (Y n).Opens

  V_affine : ∀ (C : GChain X xt G a) (n : ℕ), IsAffineOpen (V C n)

  V_pre : ∀ (C : GChain X xt G a) (n : ℕ), (p n) ⁻¹ᵁ (V C n) = C.W n

  V_compat : ∀ (C : GChain X xt G a) (n : ℕ), (yt n) ⁻¹ᵁ (V C (n + 1)) = V C n

  V_cover : ∀ (n : ℕ) (y : Y n), ∃ C : GChain X xt G a, y ∈ V C n

  chart : ∀ (C : GChain X xt G a) (n : ℕ),
    (↥(ChartRing.A 𝒪 π X xb xt G a (RC C)) ⧸ Ideal.span {algebraMap 𝒪 ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)) π ^ (n + 1)}) ≃+* Γ(Y n, V C n)

  chart_p : ∀ (C : GChain X xt G a) (n : ℕ) (x : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C))),
    (p n).appLE (V C n) (C.W n) (by rw [V_pre]) (chart C n (Ideal.Quotient.mk _ x)) =
      (RC C).lvl n (Ideal.Quotient.mk _ (x : (RC C).R))

  chart_yt : ∀ (C : GChain X xt G a) (n : ℕ) (x : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C))),
    (yt n).appLE (V C (n + 1)) (V C n) (by rw [V_compat]) (chart C (n + 1) (Ideal.Quotient.mk _ x)) = chart C n (Ideal.Quotient.mk _ x)

  chart_yb : ∀ (C : GChain X xt G a) (n : ℕ) (o : 𝒪),
    chart C n (Ideal.Quotient.mk _ (algebraMap 𝒪 ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)) o)) =
      (yb n).appLE ⊤ (V C n) le_top ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o))

variable {RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C}

noncomputable def homSpecOf (S : Scheme.{0}) (B : CommRingCat.{0}) (φ : B ⟶ Γ(S, ⊤)) : S ⟶ Spec B :=
  S.toSpecΓ ≫ Spec.map φ

omit 𝒪 hdvr π hπ hcomplete X xb xt G a in
theorem homSpecOf_appTop (S : Scheme.{0}) (B : CommRingCat.{0}) (φ : B ⟶ Γ(S, ⊤)) :
    (homSpecOf S B φ).appTop = (Scheme.ΓSpecIso B).hom ≫ φ := by
  rw [homSpecOf, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  exact Scheme.ΓSpecIso_naturality φ

omit 𝒪 hdvr π hπ hcomplete X xb xt G a in

theorem hom_Spec_ext (S : Scheme.{0}) (B : CommRingCat.{0}) (f g : S ⟶ Spec B)
    (h : (Scheme.ΓSpecIso B).inv ≫ f.appTop = (Scheme.ΓSpecIso B).inv ≫ g.appTop) : f = g :=
  ext_of_isAffine ((cancel_epi (Scheme.ΓSpecIso B).inv).mp h)

omit 𝒪 hdvr π hπ hcomplete X xb xt G a in
theorem eq_homSpecOf (S : Scheme.{0}) (B : CommRingCat.{0}) (f : S ⟶ Spec B) :
    f = homSpecOf S B ((Scheme.ΓSpecIso B).inv ≫ f.appTop) := by
  apply ext_of_isAffine
  rw [homSpecOf_appTop, Iso.hom_inv_id_assoc]

noncomputable def secOf {Z : Scheme.{0}} (V : Z.Opens) (B : CommRingCat.{0}) (w : (↑V : Scheme.{0}) ⟶ Spec B) :
    B →+* Γ(Z, V) :=
  ((Scheme.ΓSpecIso B).inv ≫ w.appTop ≫ V.topIso.hom).hom

omit 𝒪 hdvr π hπ hcomplete X xb xt G a in
theorem secOf_resLE {Z Z' : Scheme.{0}} (q : Z ⟶ Z') (V : Z.Opens) (V' : Z'.Opens) (e : V ≤ q ⁻¹ᵁ V')
    (B : CommRingCat.{0}) (w : (↑V' : Scheme.{0}) ⟶ Spec B) (b : B) :
    secOf V B (q.resLE V' V e ≫ w) b = q.appLE V' V e (secOf V' B w b) := by
  simp only [secOf, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  have key := Scheme.Hom.resLE_app_top q e
  rw [← Scheme.Hom.appTop] at key
  rw [key]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  exact Iso.inv_hom_id_apply V.topIso _

omit 𝒪 hdvr π hπ hcomplete X xb xt G a in

theorem eq_of_secOf_eq {Z : Scheme.{0}} (V : Z.Opens) (B : CommRingCat.{0}) (w w' : (↑V : Scheme.{0}) ⟶ Spec B)
    (h : ∀ b : B, secOf V B w b = secOf V B w' b) : w = w' := by
  apply hom_Spec_ext
  rw [← cancel_mono V.topIso.hom]
  ext b
  simpa only [secOf, Category.assoc] using h b

omit 𝒪 hdvr π hπ hcomplete X xb xt G a in

theorem secOf_homSpecOf {Z : Scheme.{0}} (V : Z.Opens) (B : CommRingCat.{0}) (χ : B →+* Γ(Z, V)) (b : B) :
    secOf V B (homSpecOf (↑V) B (CommRingCat.ofHom χ ≫ V.topIso.inv)) b = χ b := by
  simp only [secOf, homSpecOf_appTop, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id,
    CommRingCat.hom_ofHom]

section CartWs7

set_option backward.isDefEq.respectTransparency false

omit hdvr hπ hcomplete X xb xt G a in

theorem isPushout_level (A : Type) [CommRing A] [Algebra 𝒪 A] (k m : ℕ)
    (hO : Ideal.span {π ^ m} ≤ Ideal.span {π ^ k})
    (hA : Ideal.span {algebraMap 𝒪 A π ^ m} ≤ Ideal.span {algebraMap 𝒪 A π ^ k})
    (hm : Ideal.span {π ^ m} ≤ (Ideal.span {algebraMap 𝒪 A π ^ m}).comap (algebraMap 𝒪 A))
    (hk : Ideal.span {π ^ k} ≤ (Ideal.span {algebraMap 𝒪 A π ^ k}).comap (algebraMap 𝒪 A)) :
    IsPushout (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap 𝒪 A) hm))
      (CommRingCat.ofHom (Ideal.Quotient.factor hO))
      (CommRingCat.ofHom (Ideal.Quotient.factor hA))
      (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap 𝒪 A) hk)) := by
  have hw : CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap 𝒪 A) hm) ≫ CommRingCat.ofHom (Ideal.Quotient.factor hA) =
      CommRingCat.ofHom (Ideal.Quotient.factor hO) ≫ CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap 𝒪 A) hk) := by
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun o => ?_))
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Ideal.quotientMap_mk,
      Ideal.Quotient.factor_mk]

  have hker : ∀ (s : Limits.PushoutCocone (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap 𝒪 A) hm))
      (CommRingCat.ofHom (Ideal.Quotient.factor hO))),
      ∀ x ∈ Ideal.span {algebraMap 𝒪 A π ^ k}, (s.inl.hom.comp (Ideal.Quotient.mk _)) x = 0 := by
    intro s x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    have h0 : s.inl.hom (Ideal.Quotient.mk _ (algebraMap 𝒪 A (π ^ k))) = 0 := by
      have := congrArg (fun φ : CommRingCat.of _ ⟶ s.pt => φ.hom (Ideal.Quotient.mk _ (π ^ k))) s.condition
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Ideal.quotientMap_mk,
        Ideal.Quotient.factor_mk] at this
      rw [this, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
    rw [RingHom.comp_apply, map_mul, map_mul,
      show Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 A π ^ m}) (algebraMap 𝒪 A π ^ k) =
        Ideal.Quotient.mk _ (algebraMap 𝒪 A (π ^ k)) by simp only [map_pow], h0, mul_zero]
  refine IsPushout.of_isColimit' ⟨hw⟩ (Limits.PushoutCocone.IsColimit.mk hw
    (fun s => CommRingCat.ofHom (Ideal.Quotient.lift _ (s.inl.hom.comp (Ideal.Quotient.mk _)) (hker s)))
    ?_ ?_ ?_)
  · intro s
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_))
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Ideal.Quotient.factor_mk,
      Ideal.Quotient.lift_mk]
  · intro s
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun o => ?_))
    have := congrArg (fun φ : CommRingCat.of _ ⟶ s.pt => φ.hom (Ideal.Quotient.mk _ o)) s.condition
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Ideal.quotientMap_mk,
      Ideal.Quotient.factor_mk] at this
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Ideal.quotientMap_mk,
      Ideal.Quotient.lift_mk]
    exact this
  · intro s m' h1 _
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_))
    have := congrArg (fun φ : CommRingCat.of _ ⟶ s.pt => φ.hom (Ideal.Quotient.mk _ x)) h1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Ideal.Quotient.factor_mk] at this
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Ideal.Quotient.lift_mk]
    exact this

omit 𝒪 hdvr π hπ hcomplete X xb xt G a in
theorem secOf_comp_SpecMap {Z : Scheme.{0}} (V : Z.Opens) (B B' : CommRingCat.{0}) (w : (↑V : Scheme.{0}) ⟶ Spec B')
    (ψ : B ⟶ B') (b : B) : secOf V B (w ≫ Spec.map ψ) b = secOf V B' w (ψ b) := by
  simp only [secOf, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  congr 2
  have h1 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso B).inv b)) (Scheme.ΓSpecIso_naturality ψ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
  rw [Iso.inv_hom_id_apply (Scheme.ΓSpecIso B)] at h1
  rw [← h1]
  exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso B') _).symm

omit 𝒪 hdvr π hπ hcomplete X xb xt G a in
theorem secOf_isoSpec_hom {Z : Scheme.{0}} (V : Z.Opens) (hV : IsAffineOpen V) (b : Γ(Z, V)) :
    secOf V Γ(Z, V) hV.isoSpec.hom b = b := by
  simp only [secOf, IsAffineOpen.isoSpec_hom_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [Iso.inv_hom_id_apply (V.topIso), Iso.inv_hom_id_apply]

omit 𝒪 hdvr π hπ hcomplete X xb xt G a in
theorem secOf_ι_comp {Z : Scheme.{0}} (V : Z.Opens) (B : CommRingCat.{0}) (q : Z ⟶ Spec B) (b : B) :
    secOf V B (V.ι ≫ q) b = q.appLE ⊤ V le_top ((Scheme.ΓSpecIso B).inv b) := by
  have : q.appTop ≫ V.ι.appTop ≫ V.topIso.hom = q.appLE ⊤ V le_top := by
    simp only [Scheme.Hom.appLE, Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp,
      Scheme.Hom.appTop]
    rfl
  simp only [secOf, Scheme.Hom.comp_appTop, Category.assoc]
  rw [this]
  rfl

theorem Pieces.isPullback_chart (P : Pieces 𝒪 π X xb xt G a RC) (C : GChain X xt G a) (n : ℕ) :
    IsPullback ((P.yt n).resLE (P.V C (n + 1)) (P.V C n) (by rw [P.V_compat]))
      ((P.V C n).ι ≫ P.yb n) ((P.V C (n + 1)).ι ≫ P.yb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))) := by
  let A : Type := ↥(ChartRing.A 𝒪 π X xb xt G a (RC C))
  have hO := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))
  have hA : Ideal.span {algebraMap 𝒪 A π ^ (n + 1 + 1)} ≤ Ideal.span {algebraMap 𝒪 A π ^ (n + 1)} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ (n + 1)))
  have hlev : ∀ k : ℕ, Ideal.span {π ^ k} ≤ (Ideal.span {algebraMap 𝒪 A π ^ k}).comap (algebraMap 𝒪 A) := by
    intro k
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
    exact Ideal.subset_span rfl
  have h0 := isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_level 𝒪 π A (n + 1) (n + 1 + 1) hO hA (hlev _) (hlev _))

  let E : ∀ k : ℕ, (↑(P.V C k) : Scheme.{0}) ≅ Spec (CommRingCat.of (A ⧸ Ideal.span {algebraMap 𝒪 A π ^ (k + 1)})) :=
    fun k => (P.V_affine C k).isoSpec ≪≫ Scheme.Spec.mapIso (P.chart C k).toCommRingCatIso.op
  have hE : ∀ (k : ℕ) (x : A ⧸ Ideal.span {algebraMap 𝒪 A π ^ (k + 1)}),
      secOf (P.V C k) _ (E k).hom x = P.chart C k x := by
    intro k x
    simp only [E, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op]
    rw [secOf_comp_SpecMap, secOf_isoSpec_hom]
    rfl
  refine h0.of_iso' (E n) (E (n + 1)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · apply eq_of_secOf_eq
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [secOf_comp_SpecMap, hE, secOf_resLE, hE]
    change P.chart C n (Ideal.Quotient.factor hA (Ideal.Quotient.mk _ y)) = _
    rw [Ideal.Quotient.factor_mk, P.chart_yt]
  · simp only [Iso.refl_hom, Category.comp_id]
    apply eq_of_secOf_eq
    intro x
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [secOf_comp_SpecMap, hE, secOf_ι_comp]
    change P.chart C n (Ideal.quotientMap _ (algebraMap 𝒪 A) (hlev _) (Ideal.Quotient.mk _ o)) = _
    rw [Ideal.quotientMap_mk, P.chart_yb]
  · simp only [Iso.refl_hom, Category.comp_id]
    apply eq_of_secOf_eq
    intro x
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [secOf_comp_SpecMap, hE, secOf_ι_comp]
    change P.chart C (n + 1) (Ideal.quotientMap _ (algebraMap 𝒪 A) (hlev _) (Ideal.Quotient.mk _ o)) = _
    rw [Ideal.quotientMap_mk, P.chart_yb]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem Pieces.yt_isPullback (P : Pieces 𝒪 π X xb xt G a RC) (n : ℕ) :
    IsPullback (P.yt n) (P.yb n) (P.yb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))) := by
  let 𝒰 : (P.Y (n + 1)).OpenCover := (P.Y (n + 1)).openCoverOfIsOpenCover (fun C : GChain X xt G a => P.V C (n + 1))
    (top_le_iff.1 fun y _ => by
      obtain ⟨C, hy⟩ := P.V_cover (n + 1) y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨C, hy⟩)
  apply Scheme.isPullback_of_openCover _ _ _ _ 𝒰
  intro C
  change IsPullback (Limits.pullback.snd (P.yt n) ((P.V C (n + 1)).ι))
    (Limits.pullback.fst (P.yt n) ((P.V C (n + 1)).ι) ≫ P.yb n) ((P.V C (n + 1)).ι ≫ P.yb (n + 1)) _
  let e₁ : Limits.pullback (P.yt n) (P.V C (n + 1)).ι ≅ ↑(P.V C n) :=
    pullbackRestrictIsoRestrict (P.yt n) (P.V C (n + 1)) ≪≫ (P.Y n).isoOfEq (P.V_compat C n)
  have he₁ : e₁.hom ≫ (P.V C n).ι = Limits.pullback.fst (P.yt n) (P.V C (n + 1)).ι := by
    simp only [e₁, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι, pullbackRestrictIsoRestrict_hom_ι]
  refine (P.isPullback_chart 𝒪 π X xb xt G a C n).of_iso' e₁ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, ← cancel_mono (P.V C (n + 1)).ι, Category.assoc, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, he₁, Limits.pullback.condition]
  · rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, he₁]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

end CartWs7
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

theorem yt_isPullback_of (P : Pieces 𝒪 π X xb xt G a RC) :
    ∀ n : ℕ, IsPullback (P.yt n) (P.yb n) (P.yb (n + 1))
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))) := by
  intro n
  exact Pieces.yt_isPullback 𝒪 π X xb xt G a P n

include hdvr hπ in

include hdvr hπ in

theorem yb_flat_of (P : Pieces 𝒪 π X xb xt G a RC) :
    ∀ n : ℕ, Flat (P.yb n) := by
  classical
  haveI := hdvr
  intro n
  have hcover : (⨆ C : GChain X xt G a, ((⟨P.V C n, P.V_affine C n⟩ : (P.Y n).affineOpens) : (P.Y n).Opens)) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨C, hy⟩ := P.V_cover n y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨C, hy⟩
  apply HasRingHomProperty.of_iSup_eq_top (P := @Flat) _ hcover
  intro C

  let R := (RC C).R
  let A := ChartRing.A 𝒪 π X xb xt G a (RC C)
  let I : Ideal 𝒪 := Ideal.span {π ^ (n + 1)}
  let IA : Ideal ↥A := Ideal.span {algebraMap 𝒪 (↥A) π ^ (n + 1)}
  have hIA : I.map (algebraMap 𝒪 ↥A) = IA := by
    simp only [I, IA, Ideal.map_span, Set.image_singleton, map_pow]

  have htfR : ∀ (j : ℕ) (x : R), (algebraMap 𝒪 R π) ^ j * x = 0 → x = 0 := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      rw [pow_succ, mul_assoc] at hx
      exact (RC C).torsionFree _ (ih _ hx)
  haveI : Module.IsTorsionFree 𝒪 ↥A := by
    refine Module.IsTorsionFree.of_smul_eq_zero (fun r m h => ?_)
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hr hπ
    have h1 : ((π ^ k) • m : ↥A) = 0 := by rw [← hu, mul_comm, mul_smul, h, smul_zero]
    have h2 : (algebraMap 𝒪 R π) ^ k * (m : R) = 0 := by
      have := congrArg (fun z : ↥A => (z : R)) h1
      simp only [Subalgebra.coe_smul, Subalgebra.coe_zero, Algebra.smul_def, map_pow] at this
      exact this
    exact Subtype.ext (htfR k m h2)
  haveI : Module.Flat 𝒪 ↥A := inferInstance

  haveI : Module.Flat (𝒪 ⧸ I) (↥A ⧸ I.map (algebraMap 𝒪 ↥A)) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (↥A) I).toLinearEquiv
  have hβ : (algebraMap (𝒪 ⧸ I) (↥A ⧸ I.map (algebraMap 𝒪 ↥A))).Flat := RingHom.flat_algebraMap_iff.2 inferInstance

  let e : (↥A ⧸ I.map (algebraMap 𝒪 ↥A)) ≃+* (↥A ⧸ IA) := Ideal.quotEquivOfEq hIA
  let s := Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ I))
  have key : ((P.yb n).appLE ⊤ (P.V C n) le_top).hom.comp s.inv.hom =
      ((P.chart C n).toRingHom.comp e.toRingHom).comp (algebraMap (𝒪 ⧸ I) (↥A ⧸ I.map (algebraMap 𝒪 ↥A))) := by
    apply Ideal.Quotient.ringHom_ext
    ext o
    show ((P.yb n).appLE ⊤ (P.V C n) le_top) (s.inv (Ideal.Quotient.mk I o)) =
      P.chart C n (e (algebraMap (𝒪 ⧸ I) (↥A ⧸ I.map (algebraMap 𝒪 ↥A)) (Ideal.Quotient.mk I o)))
    rw [← P.chart_yb C n o]
    congr 1
  have h2 : (((P.yb n).appLE ⊤ (P.V C n) le_top).hom.comp s.inv.hom).Flat := by
    rw [key]
    exact hβ.comp ((RingHom.Flat.of_bijective e.bijective).comp (RingHom.Flat.of_bijective (P.chart C n).bijective))
  exact (RingHom.Flat.comp_iff_of_bijective_right
    (show Function.Bijective s.inv.hom from (s.symm.commRingCatIsoToRingEquiv).bijective)).1 h2

include hcart in

theorem p_isPullback_of (P : Pieces 𝒪 π X xb xt G a RC) :
    ∀ n : ℕ, IsPullback (xt n) (P.p n) (P.p (n + 1)) (P.yt n) := by

  intro n
  have s := hcart n
  rw [← P.p_over n, ← P.p_over (n + 1)] at s
  exact IsPullback.of_bot s (P.p_xt n) (yt_isPullback_of 𝒪 π X xb xt G a P n)

omit hcart hproper hflat haff ha_over ha_xt hcov in

theorem finite_appLE_congr {Y' Z : Scheme.{0}} (f : Z ⟶ Y') {U U' : Y'.Opens} {W W' : Z.Opens} (hU : U = U') (hW : W = W')
    (e : W ≤ f ⁻¹ᵁ U) (e' : W' ≤ f ⁻¹ᵁ U') (h : (f.appLE U W e).hom.Finite) : (f.appLE U' W' e').hom.Finite := by
  subst hU hW; exact h

include hdvr hπ hcomplete in

theorem p_isFinite_of (P : Pieces 𝒪 π X xb xt G a RC) :
    ∀ n : ℕ, IsFinite (P.p n) := by
  classical
  intro n
  have hcover : (⨆ C : GChain X xt G a, ((⟨P.V C n, P.V_affine C n⟩ : (P.Y n).affineOpens) : (P.Y n).Opens)) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨C, hy⟩ := P.V_cover n y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨C, hy⟩
  rw [HasAffineProperty.iff_of_iSup_eq_top (P := @IsFinite) _ hcover]
  intro C

  let R := (RC C).R
  let A := ChartRing.A 𝒪 π X xb xt G a (RC C)
  let IA : Ideal ↥A := Ideal.span {algebraMap 𝒪 (↥A) π ^ (n + 1)}
  let IR : Ideal R := Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}
  have hIAR : IA ≤ IR.comap (algebraMap (↥A) R) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow,
      ← IsScalarTower.algebraMap_apply 𝒪 (↥A) R π]
    exact Ideal.subset_span rfl
  let ι : (↥A ⧸ IA) →+* (R ⧸ IR) := Ideal.quotientMap IR (algebraMap (↥A) R) hIAR
  obtain ⟨-, hfin, -, -⟩ := AlgebraicGeometry.AdmissibleAlgebra.fixedPoints_isAdicComplete_and_finite_and_finiteType 𝒪 hdvr π hπ
    hcomplete R (RC C).complete (RC C).torsionFree (RC C).finiteType G
  have hιfin : ι.Finite := by
    apply RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk IA)
    rw [show ι.comp (Ideal.Quotient.mk IA) = (Ideal.Quotient.mk IR).comp (algebraMap (↥A) R) from Ideal.quotientMap_comp_mk hIAR]
    refine RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) ?_
    rw [RingHom.finite_algebraMap]
    exact hfin

  have hW : IsAffineOpen (C.W n) := C.affine n
  have hle : C.W n ≤ (P.p n) ⁻¹ᵁ (P.V C n) := by rw [P.V_pre]
  have happ : ((P.p n).appLE (P.V C n) (C.W n) hle).hom =
      (((RC C).lvl n).toRingHom.comp ι).comp (P.chart C n).symm.toRingHom := by
    ext y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective ((P.chart C n).symm y)
    have hy : y = P.chart C n (Ideal.Quotient.mk IA x) := by rw [hx, RingEquiv.apply_symm_apply]
    rw [hy]
    show (P.p n).appLE (P.V C n) (C.W n) hle (P.chart C n (Ideal.Quotient.mk _ x)) = (RC C).lvl n (ι ((P.chart C n).symm (P.chart C n _)))
    rw [RingEquiv.symm_apply_apply, P.chart_p C n x]
    rfl
  have hfinLE : ((P.p n).appLE (P.V C n) (C.W n) hle).hom.Finite := by
    rw [happ]
    exact (RingHom.Finite.comp (RingHom.Finite.of_surjective _ ((RC C).lvl n).surjective) hιfin).comp
      (RingHom.Finite.of_surjective _ (P.chart C n).symm.surjective)
  refine ⟨?_, ?_⟩
  ·
    show IsAffine ↑((P.p n) ⁻¹ᵁ (P.V C n))
    rw [P.V_pre]; exact hW
  · rw [Scheme.Hom.appTop, morphismRestrict_app']
    exact finite_appLE_congr (P.p n) (P.V C n).ι_image_top.symm
      (by rw [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top, P.V_pre]) hle _ hfinLE

include hdvr hπ hcomplete in

theorem p_surjective_of (P : Pieces 𝒪 π X xb xt G a RC) :
    ∀ n : ℕ, Surjective (P.p n) := by
  classical
  intro n
  refine ⟨fun y => ?_⟩
  obtain ⟨C, hy⟩ := P.V_cover n y

  let R := (RC C).R
  let A := ChartRing.A 𝒪 π X xb xt G a (RC C)
  haveI : Algebra.IsInvariant (↥A) R G := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  haveI : Algebra.IsIntegral (↥A) R := Algebra.IsInvariant.isIntegral (↥A) R G
  let IA : Ideal ↥A := Ideal.span {algebraMap 𝒪 (↥A) π ^ (n + 1)}
  let IR : Ideal R := Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}
  have hIAR : IA ≤ IR.comap (algebraMap (↥A) R) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow,
      ← IsScalarTower.algebraMap_apply 𝒪 (↥A) R π]
    exact Ideal.subset_span rfl
  let ι : (↥A ⧸ IA) →+* (R ⧸ IR) := Ideal.quotientMap IR (algebraMap (↥A) R) hIAR

  have hιint : ι.IsIntegral := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hr : IsIntegral (↥A) r := Algebra.IsIntegral.isIntegral r
    obtain ⟨p, hp, hpr⟩ := hr
    refine ⟨p.map (Ideal.Quotient.mk IA), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, show ι.comp (Ideal.Quotient.mk IA) = (Ideal.Quotient.mk IR).comp (algebraMap (↥A) R) from
      Ideal.quotientMap_comp_mk hIAR, ← Polynomial.hom_eval₂, hpr, map_zero]
  have hιinj : Function.Injective ι := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
    rw [Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨-, -, -, htors⟩ := AlgebraicGeometry.AdmissibleAlgebra.fixedPoints_isAdicComplete_and_finite_and_finiteType 𝒪 hdvr π hπ
      hcomplete R (RC C).complete (RC C).torsionFree (RC C).finiteType G
    exact htors (n + 1) x hz
  have hsurjι : Function.Surjective (PrimeSpectrum.comap ι) := hιint.comap_surjective hιinj

  have hW : IsAffineOpen (C.W n) := C.affine n
  have hV : IsAffineOpen (P.V C n) := P.V_affine C n
  have hle : C.W n ≤ (P.p n) ⁻¹ᵁ (P.V C n) := by rw [P.V_pre]
  have happ : ∀ z : ↥A ⧸ IA, (P.p n).appLE (P.V C n) (C.W n) hle (P.chart C n z) = (RC C).lvl n (ι z) := by
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [P.chart_p C n x]
    rfl

  have hyV : y ∈ Set.range hV.fromSpec := by rw [IsAffineOpen.range_fromSpec]; exact hy
  obtain ⟨q, rfl⟩ := hyV

  obtain ⟨r, hr⟩ := hsurjι (PrimeSpectrum.comap (P.chart C n).toRingHom q)
  refine ⟨hW.fromSpec (PrimeSpectrum.comap ((RC C).lvl n).symm.toRingHom r), ?_⟩
  have key := congrArg (fun f : Spec _ ⟶ P.Y n => f (PrimeSpectrum.comap ((RC C).lvl n).symm.toRingHom r))
    (IsAffineOpen.SpecMap_appLE_fromSpec (P.p n) hV hW hle)
  simp only [Scheme.Hom.comp_apply] at key
  rw [← key, Spec.map_apply]
  congr 1

  apply PrimeSpectrum.ext
  ext s
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have hs : s = P.chart C n ((P.chart C n).symm s) := ((P.chart C n).apply_symm_apply s).symm
  conv_lhs => rw [hs, show ((P.p n).appLE (P.V C n) (C.W n) hle).hom (P.chart C n ((P.chart C n).symm s)) =
    (RC C).lvl n (ι ((P.chart C n).symm s)) from happ _]
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  have hr' := congrArg (fun J : PrimeSpectrum (↥A ⧸ IA) => ((P.chart C n).symm s) ∈ J.asIdeal) hr
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hr'
  rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at hr'
  exact hr'.to_iff

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem finiteType_quotient_pow (A' : Type) [CommRing A'] [Algebra 𝒪 A']
    (hft : Algebra.FiniteType 𝒪 (A' ⧸ Ideal.span {algebraMap 𝒪 A' π})) (k : ℕ) :
    Algebra.FiniteType 𝒪 (A' ⧸ Ideal.span {algebraMap 𝒪 A' π ^ k}) := by
  classical
  set ϖ := algebraMap 𝒪 A' π with hϖ
  obtain ⟨s, hs⟩ := hft

  let t : Finset A' := s.image (Function.surjInv Ideal.Quotient.mk_surjective)
  let S : Subalgebra 𝒪 A' := Algebra.adjoin 𝒪 (t : Set A')
  have ht : (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {ϖ})) '' (t : Set A') = (s : Set _) := by
    rw [Finset.coe_image, Set.image_image]
    refine (Set.image_congr' fun x => ?_).trans (Set.image_id _)
    rw [Ideal.Quotient.mkₐ_eq_mk]
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective x
  have hmapS : S.map (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {ϖ})) = ⊤ := by
    rw [AlgHom.map_adjoin, ht, hs]
  have hS1 : ∀ y : A', ∃ s₁ ∈ S, y - s₁ ∈ Ideal.span {ϖ} := by
    intro y
    have : Ideal.Quotient.mkₐ 𝒪 (Ideal.span {ϖ}) y ∈ S.map (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {ϖ})) := by
      rw [hmapS]; exact Algebra.mem_top
    obtain ⟨s₁, hs₁, h⟩ := Subalgebra.mem_map.1 this
    refine ⟨s₁, hs₁, ?_⟩
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact (h.symm : _)
  have hϖS : ∀ j : ℕ, ϖ ^ j ∈ S := fun j => by rw [hϖ, ← map_pow]; exact S.algebraMap_mem _

  have hSk : ∀ (j : ℕ) (x : A'), ∃ s₀ ∈ S, x - s₀ ∈ Ideal.span {ϖ ^ j} := by
    intro j
    induction j with
    | zero => intro x; exact ⟨0, S.zero_mem, by simp⟩
    | succ j ih =>
      intro x
      obtain ⟨s₀, hs₀, hx⟩ := ih x
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx
      obtain ⟨s₁, hs₁, hy1⟩ := hS1 y
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hy1
      refine ⟨s₀ + s₁ * ϖ ^ j, S.add_mem hs₀ (S.mul_mem hs₁ (hϖS j)), Ideal.mem_span_singleton'.2 ⟨z, ?_⟩⟩
      have : x - (s₀ + s₁ * ϖ ^ j) = (y - s₁) * ϖ ^ j := by rw [sub_mul, hy]; ring
      rw [this, ← hz]; ring
  refine ⟨⟨t.image (Ideal.Quotient.mk (Ideal.span {ϖ ^ k})), ?_⟩⟩
  rw [Finset.coe_image, show (Ideal.Quotient.mk (Ideal.span {ϖ ^ k}) : A' → _) = Ideal.Quotient.mkₐ 𝒪 (Ideal.span {ϖ ^ k}) from rfl,
    ← AlgHom.map_adjoin]
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨s₀, hs₀, hx⟩ := hSk k x
  refine Subalgebra.mem_map.2 ⟨s₀, hs₀, ?_⟩
  rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  rw [← Ideal.neg_mem_iff, neg_sub]; exact hx

include hdvr hπ hcomplete hproper in

theorem yb_isProper_of (P : Pieces 𝒪 π X xb xt G a RC) :
    ∀ n : ℕ, IsProper (P.yb n) := by
  classical
  intro n
  haveI := hproper n
  haveI := p_isFinite_of 𝒪 hdvr π hπ hcomplete X xb xt G a P n
  haveI := p_surjective_of 𝒪 hdvr π hπ hcomplete X xb xt G a P n
  haveI : IsSeparated (P.yb n) :=
    AlgebraicGeometry.isSeparated_of_isFinite_of_surjective_of_comp_eq (P.p n) (xb n) (P.yb n) (P.p_over n)
  haveI : UniversallyClosed (P.yb n) := by
    have : UniversallyClosed (P.p n ≫ P.yb n) := by rw [P.p_over]; infer_instance
    exact UniversallyClosed.of_comp_surjective (P.p n) (P.yb n)
  haveI : LocallyOfFiniteType (P.yb n) := by
    have hcover : (⨆ C : GChain X xt G a, ((⟨P.V C n, P.V_affine C n⟩ : (P.Y n).affineOpens) : (P.Y n).Opens)) = ⊤ := by
      refine top_le_iff.1 fun y _ => ?_
      obtain ⟨C, hy⟩ := P.V_cover n y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨C, hy⟩
    apply HasRingHomProperty.of_iSup_eq_top (P := @LocallyOfFiniteType) _ hcover
    intro C
    let R := (RC C).R
    let A := ChartRing.A 𝒪 π X xb xt G a (RC C)
    let I : Ideal 𝒪 := Ideal.span {π ^ (n + 1)}
    let IA : Ideal ↥A := Ideal.span {algebraMap 𝒪 (↥A) π ^ (n + 1)}
    have hIA : I.map (algebraMap 𝒪 ↥A) = IA := by
      simp only [I, IA, Ideal.map_span, Set.image_singleton, map_pow]
    obtain ⟨-, -, hft, -⟩ := AlgebraicGeometry.AdmissibleAlgebra.fixedPoints_isAdicComplete_and_finite_and_finiteType 𝒪 hdvr π hπ
      hcomplete R (RC C).complete (RC C).torsionFree (RC C).finiteType G
    haveI hftk : Algebra.FiniteType 𝒪 (↥A ⧸ IA) := finiteType_quotient_pow 𝒪 π (↥A) hft (n + 1)
    haveI : Algebra.FiniteType 𝒪 (↥A ⧸ I.map (algebraMap 𝒪 ↥A)) := hftk.equiv (Ideal.quotientEquivAlgOfEq 𝒪 hIA.symm)
    haveI : Algebra.FiniteType (𝒪 ⧸ I) (↥A ⧸ I.map (algebraMap 𝒪 ↥A)) :=
      Algebra.FiniteType.of_restrictScalars_finiteType 𝒪 (𝒪 ⧸ I) (↥A ⧸ I.map (algebraMap 𝒪 ↥A))
    have hβ : (algebraMap (𝒪 ⧸ I) (↥A ⧸ I.map (algebraMap 𝒪 ↥A))).FiniteType := by
      rw [RingHom.finiteType_algebraMap]; infer_instance
    let e : (↥A ⧸ I.map (algebraMap 𝒪 ↥A)) ≃+* (↥A ⧸ IA) := Ideal.quotEquivOfEq hIA
    let s := Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ I))
    have key : ((P.yb n).appLE ⊤ (P.V C n) le_top).hom.comp s.inv.hom =
        ((P.chart C n).toRingHom.comp e.toRingHom).comp (algebraMap (𝒪 ⧸ I) (↥A ⧸ I.map (algebraMap 𝒪 ↥A))) := by
      apply Ideal.Quotient.ringHom_ext
      ext o
      show ((P.yb n).appLE ⊤ (P.V C n) le_top) (s.inv (Ideal.Quotient.mk I o)) =
        P.chart C n (e (algebraMap (𝒪 ⧸ I) (↥A ⧸ I.map (algebraMap 𝒪 ↥A)) (Ideal.Quotient.mk I o)))
      rw [← P.chart_yb C n o]
      congr 1
    have h2 : (((P.yb n).appLE ⊤ (P.V C n) le_top).hom.comp s.inv.hom).FiniteType := by
      rw [key]
      exact ((RingHom.FiniteType.of_surjective (P.chart C n).toRingHom (P.chart C n).surjective).comp
        (RingHom.FiniteType.of_surjective e.toRingHom e.surjective)).comp hβ
    have h3 := h2.comp (RingHom.FiniteType.of_surjective s.hom.hom s.commRingCatIsoToRingEquiv.surjective)
    rwa [RingHom.comp_assoc, ← CommRingCat.hom_comp, s.hom_inv_id, CommRingCat.hom_id, RingHom.comp_id] at h3
  exact @IsProper.mk _ _ _ ‹_› ‹_› ‹_›

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem Pieces.preimage_basicOpen_chart (P : Pieces 𝒪 π X xb xt G a RC) (C : GChain X xt G a) (n : ℕ)
    (x : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C))) :
    (P.p n) ⁻¹ᵁ ((P.Y n).basicOpen (P.chart C n (Ideal.Quotient.mk _ x))) =
      (X n).basicOpen ((RC C).lvl n (Ideal.Quotient.mk _ (x : (RC C).R))) := by
  rw [← P.chart_p C n x, Scheme.basicOpen_appLE, ← P.V_pre C n]
  exact (inf_eq_right.2 ((P.p n).preimage_mono (Scheme.basicOpen_le _ _))).symm

include hdvr hπ hcomplete in

theorem Pieces.eq_of_preimage_eq (P : Pieces 𝒪 π X xb xt G a RC) (n : ℕ) (U U' : (P.Y n).Opens)
    (h : (P.p n) ⁻¹ᵁ U = (P.p n) ⁻¹ᵁ U') : U = U' := by
  have hs : Function.Surjective (P.p n).base := (p_surjective_of 𝒪 hdvr π hπ hcomplete X xb xt G a P n).surj
  ext y
  obtain ⟨x, rfl⟩ := hs y
  have := congrArg (fun W : (X n).Opens => x ∈ W) h
  simpa using this

universe u_el

namespace EpiLoc7

open scoped Pointwise

theorem epi_morphismRestrict_of_surjective_of_stalkMap_injective
    {X Y : Scheme.{u_el}} (f : X ⟶ Y) [Surjective f]
    (hinj : ∀ x : X, Function.Injective (f.stalkMap x)) (U : Y.Opens) :
    Epi (f ∣_ U) := by
  have hsurjU : Surjective (f ∣_ U) := IsZariskiLocalAtTarget.restrict ‹Surjective f› U
  apply CategoryTheory.Functor.epi_of_epi_map (Scheme.forgetToLocallyRingedSpace)
  apply CategoryTheory.Functor.epi_of_epi_map (LocallyRingedSpace.forgetToSheafedSpace)
  apply SheafedSpace.epi_of_base_surjective_of_stalk_mono _ hsurjU.surj
  intro x
  have hm : Mono (f.stalkMap x.1) := ConcreteCategory.mono_of_injective _ (hinj x.1)
  exact ((MorphismProperty.monomorphisms CommRingCat).arrow_mk_iso_iff (morphismRestrictStalkMap f U x)).2 hm

theorem epi_of_surjective_of_stalkMap_injective
    {X Y : Scheme.{u_el}} (f : X ⟶ Y) [Surjective f]
    (hinj : ∀ x : X, Function.Injective (f.stalkMap x)) : Epi f := by
  apply CategoryTheory.Functor.epi_of_epi_map (Scheme.forgetToLocallyRingedSpace)
  apply CategoryTheory.Functor.epi_of_epi_map (LocallyRingedSpace.forgetToSheafedSpace)
  apply SheafedSpace.epi_of_base_surjective_of_stalk_mono _ ‹Surjective f›.surj
  intro x
  exact ConcreteCategory.mono_of_injective _ (hinj x)

theorem exists_not_mem_under_and_mul_mem_of_mul_mem
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (I : Ideal B) (hI : ∀ (g : G) (x : B), x ∈ I → g • x ∈ I)
    (a : A) (𝔓 : Ideal B) [𝔓.IsPrime] (t : B) (ht : t ∉ 𝔓) (hta : t * algebraMap A B a ∈ I) :
    ∃ u : A, algebraMap A B u ∉ 𝔓 ∧ algebraMap A B u * algebraMap A B a ∈ I := by
  classical
  haveI : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G

  let J : Ideal B := Submodule.colon I (Ideal.span {algebraMap A B a})
  have hJ : ∀ r : B, r ∈ J ↔ r * algebraMap A B a ∈ I := fun r => by
    constructor
    · intro h
      have := (Submodule.mem_colon.1 h) (algebraMap A B a) (Ideal.mem_span_singleton_self _)
      rwa [smul_eq_mul] at this
    · intro h
      refine Submodule.mem_colon.2 (fun p hp => ?_)
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hp
      rw [smul_eq_mul, show r * (c * algebraMap A B a) = c * (r * algebraMap A B a) by ring]
      exact I.mul_mem_left c h
  have hga : ∀ g : G, g • algebraMap A B a = algebraMap A B a := fun g => by
    rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
  have hJstab : ∀ (g : G) (r : B), r ∈ J → g • r ∈ J := by
    intro g r hr
    rw [hJ] at hr ⊢
    have : g • r * algebraMap A B a = g • (r * algebraMap A B a) := by rw [smul_mul', hga]
    rw [this]; exact hI g _ hr
  have htJ : t ∈ J := (hJ t).2 hta
  by_contra hcon
  push Not at hcon

  have hle : J.comap (algebraMap A B) ≤ 𝔓.under A := by
    intro u hu
    rw [Ideal.mem_comap] at hu
    by_contra hu'
    exact hcon u (fun h => hu' (by rw [Ideal.under_def, Ideal.mem_comap]; exact h)) ((hJ _).1 hu)
  obtain ⟨Q, hJQ, hQ, hQunder⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (𝔓.under A) J hle
  haveI := hQ
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq A B G 𝔓 Q
    (by rw [Ideal.under_def, Ideal.under_def, hQunder])

  have : g⁻¹ • t ∈ 𝔓 := by
    have h1 : t ∈ g • 𝔓 := hg ▸ hJQ htJ
    exact (Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 h1

  have h2 : g • t ∈ J := hJstab g t htJ
  have h3 : g • t ∈ g • 𝔓 := hg ▸ hJQ h2
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_smul_smul] at h3
  exact ht h3

theorem injective_of_isLocalization_atPrime_of_isInvariant
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G]
    (I : Ideal B) (hI : ∀ (g : G) (x : B), x ∈ I → g • x ∈ I)
    {A' B' : Type*} [CommRing A'] [CommRing B'] (qA : A →+* A') (qB : B →+* B')
    (hqA : Function.Surjective qA) (hqB : Function.Surjective qB) (hker : ∀ b : B, qB b = 0 ↔ b ∈ I)
    (φ : A' →+* B') (hφ : ∀ a : A, φ (qA a) = qB (algebraMap A B a)) (hφinj : Function.Injective φ)
    (𝔓' : Ideal B') [𝔓'.IsPrime]
    (Aₚ Bₚ : Type*) [CommRing Aₚ] [CommRing Bₚ] [Algebra A' Aₚ] [Algebra B' Bₚ]
    [IsLocalization.AtPrime Aₚ (𝔓'.comap φ)] [IsLocalization.AtPrime Bₚ 𝔓']
    (ψ : Aₚ →+* Bₚ) (hψ : ∀ x : A', ψ (algebraMap A' Aₚ x) = algebraMap B' Bₚ (φ x)) :
    Function.Injective ψ := by
  classical
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨⟨a', s⟩, rfl⟩ := IsLocalization.mk'_surjective (𝔓'.comap φ).primeCompl x
  have h1 : algebraMap B' Bₚ (φ a') = 0 := by
    have : ψ (algebraMap A' Aₚ a') = 0 := by
      rw [← IsLocalization.mk'_spec Aₚ a' s, map_mul, hx, zero_mul]
    rwa [hψ] at this
  obtain ⟨⟨t', ht'⟩, ht'a⟩ := (IsLocalization.map_eq_zero_iff 𝔓'.primeCompl Bₚ (φ a')).1 h1
  obtain ⟨a, rfl⟩ := hqA a'
  obtain ⟨t, rfl⟩ := hqB t'

  haveI : (𝔓'.comap qB).IsPrime := Ideal.IsPrime.comap qB
  have ht𝔓 : t ∉ 𝔓'.comap qB := fun h => ht' (Ideal.mem_comap.1 h)
  have hta : t * algebraMap A B a ∈ I := by
    rw [← hker, map_mul, ← hφ]; exact ht'a
  obtain ⟨u, hu𝔓, hua⟩ := exists_not_mem_under_and_mul_mem_of_mul_mem G I hI a (𝔓'.comap qB) t ht𝔓 hta

  have hu' : qA u ∈ (𝔓'.comap φ).primeCompl := by
    intro h
    apply hu𝔓
    rw [Ideal.mem_comap, ← hφ]
    exact Ideal.mem_comap.1 h
  have hzero : qA u * qA a = 0 := by
    apply hφinj
    rw [map_mul, hφ, hφ, ← map_mul, map_zero]
    exact (hker _).2 hua
  rw [IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨qA u, hu'⟩, hzero⟩

theorem isLocalization_atPrime_congr {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P Q : Ideal R} [P.IsPrime] [Q.IsPrime] (h : P = Q) [IsLocalization.AtPrime S P] :
    IsLocalization.AtPrime S Q := by
  subst h; assumption

end EpiLoc7
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

include hdvr hπ hcomplete in

theorem p_epi_loc_of (P : Pieces 𝒪 π X xb xt G a RC) :
    ∀ (n : ℕ) (U : (P.Y n).Opens), Epi ((P.p n) ∣_ U) := by
  classical
  intro n U
  haveI : Surjective (P.p n) := p_surjective_of 𝒪 hdvr π hπ hcomplete X xb xt G a P n
  refine EpiLoc7.epi_morphismRestrict_of_surjective_of_stalkMap_injective (P.p n) (fun x => ?_) U

  obtain ⟨C, hxV⟩ := P.V_cover n ((P.p n).base x)
  have hxW : x ∈ C.W n := by
    have : x ∈ (P.p n) ⁻¹ᵁ (P.V C n) := hxV
    rwa [P.V_pre C n] at this

  let R := (RC C).R
  let A := ChartRing.A 𝒪 π X xb xt G a (RC C)
  haveI : Algebra.IsInvariant (↥A) R G := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  haveI : SMulCommClass G (↥A) R := ⟨fun g b r => by
    show g • ((b : R) * r) = (b : R) * (g • r)
    rw [smul_mul', b.2 g]⟩
  let IA : Ideal ↥A := Ideal.span {algebraMap 𝒪 (↥A) π ^ (n + 1)}
  let IR : Ideal R := Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}

  have hIRstab : ∀ (g : G) (r : R), r ∈ IR → g • r ∈ IR := by
    intro g r hr
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    have hgπ : g • (algebraMap 𝒪 R π ^ (n + 1)) = algebraMap 𝒪 R π ^ (n + 1) := by
      rw [smul_pow', Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
    rw [smul_mul', hgπ]
    exact Ideal.mem_span_singleton'.2 ⟨g • c, rfl⟩

  have hW : IsAffineOpen (C.W n) := C.affine n
  have hV : IsAffineOpen (P.V C n) := P.V_affine C n
  have hle : C.W n ≤ (P.p n) ⁻¹ᵁ (P.V C n) := by rw [P.V_pre]
  let φ : Γ(P.Y n, P.V C n) →+* Γ(X n, C.W n) := ((P.p n).appLE (P.V C n) (C.W n) hle).hom
  let qA : ↥A →+* Γ(P.Y n, P.V C n) := (P.chart C n).toRingHom.comp (Ideal.Quotient.mk IA)
  let qB : R →+* Γ(X n, C.W n) := ((RC C).lvl n).toRingHom.comp (Ideal.Quotient.mk IR)
  have hqA : Function.Surjective qA := (P.chart C n).surjective.comp Ideal.Quotient.mk_surjective
  have hqB : Function.Surjective qB := ((RC C).lvl n).surjective.comp Ideal.Quotient.mk_surjective
  have hker : ∀ b : R, qB b = 0 ↔ b ∈ IR := fun b => by
    show (RC C).lvl n (Ideal.Quotient.mk IR b) = 0 ↔ b ∈ IR
    rw [((RC C).lvl n).map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hφ : ∀ z : ↥A, φ (qA z) = qB (algebraMap (↥A) R z) := fun z => by
    show (P.p n).appLE (P.V C n) (C.W n) hle (P.chart C n (Ideal.Quotient.mk IA z)) =
      (RC C).lvl n (Ideal.Quotient.mk IR (z : R))
    rw [P.chart_p C n z]

  obtain ⟨-, -, -, htors⟩ := AlgebraicGeometry.AdmissibleAlgebra.fixedPoints_isAdicComplete_and_finite_and_finiteType 𝒪 hdvr π hπ
    hcomplete R (RC C).complete (RC C).torsionFree (RC C).finiteType G
  have hφinj : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro z hz
    obtain ⟨w, rfl⟩ := hqA z
    rw [hφ, hker] at hz
    have hw : w ∈ IA := htors (n + 1) w hz
    show P.chart C n (Ideal.Quotient.mk IA w) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hw, map_zero]

  let 𝔓' : Ideal Γ(X n, C.W n) := (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
  letI algW := (X n).presheaf.algebra_section_stalk (⟨x, hxW⟩ : C.W n)
  letI algV := (P.Y n).presheaf.algebra_section_stalk (⟨(P.p n).base x, hxV⟩ : P.V C n)
  haveI iW : IsLocalization.AtPrime ((X n).presheaf.stalk x) 𝔓' := hW.isLocalization_stalk ⟨x, hxW⟩
  have hcomap : (hV.primeIdealOf ⟨(P.p n).base x, hxV⟩).asIdeal = 𝔓'.comap φ := by
    rw [← IsAffineOpen.comap_primeIdealOf_appLE (P.V C n) hV (C.W n) hW hle hxW, PrimeSpectrum.comap_asIdeal]
  haveI iV₀ : IsLocalization.AtPrime ((P.Y n).presheaf.stalk ((P.p n).base x)) (hV.primeIdealOf ⟨(P.p n).base x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨(P.p n).base x, hxV⟩
  haveI iV : IsLocalization.AtPrime ((P.Y n).presheaf.stalk ((P.p n).base x)) (𝔓'.comap φ) :=
    EpiLoc7.isLocalization_atPrime_congr hcomap
  have hψ : ∀ s : Γ(P.Y n, P.V C n),
      ((P.p n).stalkMap x).hom (algebraMap Γ(P.Y n, P.V C n) ((P.Y n).presheaf.stalk ((P.p n).base x)) s) =
        algebraMap Γ(X n, C.W n) ((X n).presheaf.stalk x) (φ s) := fun s => by
    show (P.p n).stalkMap x ((P.Y n).presheaf.germ (P.V C n) ((P.p n).base x) hxV s) =
      (X n).presheaf.germ (C.W n) x hxW ((P.p n).appLE (P.V C n) (C.W n) hle s)
    rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  exact EpiLoc7.injective_of_isLocalization_atPrime_of_isInvariant G IR hIRstab qA qB hqA hqB hker φ hφ hφinj 𝔓'
    ((P.Y n).presheaf.stalk ((P.p n).base x)) ((X n).presheaf.stalk x) ((P.p n).stalkMap x).hom hψ

theorem ChartRing.exists_lift {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) (B : Type) [CommRing B]
    (ψ : ∀ m : ℕ, B →+* Γ(X m, C.W m))
    (hψt : ∀ (m : ℕ) (b : B), (xt m).appLE (C.W (m + 1)) (C.W m) (by rw [C.compat]) (ψ (m + 1) b) = ψ m b)
    (hψg : ∀ (m : ℕ) (g : G) (b : B), (a m g⁻¹).hom.appLE (C.W m) (C.W m) (by rw [C.stable]) (ψ m b) = ψ m b) :
    ∃ Φ : B →+* RC.R, (∀ (m : ℕ) (b : B), RC.lvl m (Ideal.Quotient.mk _ (Φ b)) = ψ m b) ∧
      ∀ (g : G) (b : B), g • Φ b = Φ b := by
  classical
  haveI := RC.complete
  let I : Ideal RC.R := Ideal.span {algebraMap 𝒪 RC.R π}
  have hI : ∀ m : ℕ, I ^ (m + 1) = Ideal.span {algebraMap 𝒪 RC.R π ^ (m + 1)} := fun m =>
    Ideal.span_singleton_pow _ _
  let e : ∀ m : ℕ, (RC.R ⧸ I ^ (m + 1)) ≃+* (RC.R ⧸ Ideal.span {algebraMap 𝒪 RC.R π ^ (m + 1)}) := fun m =>
    Ideal.quotEquivOfEq (hI m)
  let f : ∀ m : ℕ, B →+* RC.R ⧸ I ^ (m + 1) := fun m =>
    (e m).symm.toRingHom.comp ((RC.lvl m).symm.toRingHom.comp (ψ m))

  have hf0 : ∀ (m : ℕ) (b : B), RC.lvl m (e m (f m b)) = ψ m b := by
    intro m b
    simp [f]
  have ha : StrictMono (fun n : ℕ => n + 1) := fun _ _ h => Nat.succ_lt_succ h
  have hf : ∀ {m : ℕ}, (Ideal.Quotient.factorPow I (ha.monotone m.le_succ)).comp (f (m + 1)) = f m := by
    intro m
    ext b
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (f (m + 1) b)
    have h1 : ψ (m + 1) b = RC.lvl (m + 1) (Ideal.Quotient.mk _ r) := by
      rw [← hf0 (m + 1) b, ← hr, Ideal.quotEquivOfEq_mk]
    have h2 : ψ m b = RC.lvl m (Ideal.Quotient.mk _ r) := by
      rw [← hψt m b, h1, RC.lvl_compat]
    apply (e m).injective
    apply (RC.lvl m).injective
    rw [RingHom.comp_apply, ← hr, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, hf0, h2,
      Ideal.quotEquivOfEq_mk]
  refine ⟨IsAdicComplete.StrictMono.liftRingHom I ha f hf, ?_, ?_⟩
  · intro m b
    have := IsAdicComplete.StrictMono.mk_liftRingHom I ha f hf (n := m) b
    rw [← hf0 m b, ← this, Ideal.quotEquivOfEq_mk]
  · intro g b
    set Φ := IsAdicComplete.StrictMono.liftRingHom I ha f hf with hΦ
    have key : ∀ (m : ℕ) (b : B), RC.lvl m (Ideal.Quotient.mk _ (Φ b)) = ψ m b := by
      intro m b
      have := IsAdicComplete.StrictMono.mk_liftRingHom I ha f hf (n := m) b
      rw [← hf0 m b, ← this, Ideal.quotEquivOfEq_mk]
    have : (MulSemiringAction.toRingHom G RC.R g).comp Φ = Φ := by
      rw [hΦ]
      apply IsAdicComplete.StrictMono.eq_liftRingHom I ha f hf
      intro m
      ext b'
      apply (e m).injective
      apply (RC.lvl m).injective
      rw [RingHom.comp_apply, RingHom.comp_apply, MulSemiringAction.toRingHom_apply, Ideal.quotEquivOfEq_mk,
        ← RC.lvl_smul m g, ← hΦ, key, hψg, hf0]
    exact congrArg (fun F : B →+* RC.R => F b) this

theorem Pieces.univ_chart (P : Pieces 𝒪 π X xb xt G a RC) (C : GChain X xt G a) (B : CommRingCat.{0})
    (w : ∀ m : ℕ, (↑(C.W m) : Scheme.{0}) ⟶ Spec B)
    (hwg : ∀ (m : ℕ) (g : G), (a m g).hom.resLE (C.W m) (C.W m) (by rw [C.stable]) ≫ w m = w m)
    (hwt : ∀ m : ℕ, (xt m).resLE (C.W (m + 1)) (C.W m) (by rw [C.compat]) ≫ w (m + 1) = w m) :
    ∃ v : ∀ m : ℕ, (↑(P.V C m) : Scheme.{0}) ⟶ Spec B,
      ∀ m : ℕ, (P.p m).resLE (P.V C m) (C.W m) (by rw [P.V_pre]) ≫ v m = w m := by
  let ψ : ∀ m : ℕ, (B : Type) →+* Γ(X m, C.W m) := fun m => secOf (C.W m) B (w m)
  have hψt : ∀ (m : ℕ) (b : B), (xt m).appLE (C.W (m + 1)) (C.W m) (by rw [C.compat]) (ψ (m + 1) b) = ψ m b := by
    intro m b
    simp only [ψ]
    rw [← secOf_resLE, hwt]
  have hψg : ∀ (m : ℕ) (g : G) (b : B),
      (a m g⁻¹).hom.appLE (C.W m) (C.W m) (by rw [C.stable]) (ψ m b) = ψ m b := by
    intro m g b
    simp only [ψ]
    rw [← secOf_resLE, hwg]
  obtain ⟨Φ, hΦ, hΦG⟩ := ChartRing.exists_lift 𝒪 π X xb xt G a (RC C) B ψ hψt hψg
  let ΦA : (B : Type) →+* ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)) :=
    Φ.codRestrict (ChartRing.A 𝒪 π X xb xt G a (RC C)) (fun b g => hΦG g b)
  let χ : ∀ m : ℕ, (B : Type) →+* Γ(P.Y m, P.V C m) := fun m =>
    (P.chart C m).toRingHom.comp ((Ideal.Quotient.mk _).comp ΦA)
  refine ⟨fun m => homSpecOf _ B (CommRingCat.ofHom (χ m) ≫ (P.V C m).topIso.inv), fun m => ?_⟩
  apply eq_of_secOf_eq
  intro b
  rw [secOf_resLE, secOf_homSpecOf]
  change (P.p m).appLE (P.V C m) (C.W m) _ (P.chart C m (Ideal.Quotient.mk _ (ΦA b))) = ψ m b
  rw [P.chart_p C m (ΦA b)]
  exact hΦ m b

omit hdvr hπ hcomplete in

theorem preimage_eq_of_inf_eq {Z Z' : Scheme.{0}} (q : Z ⟶ Z') (W : Z.Opens) (W' : Z'.Opens) (D : Z.Opens) (D' : Z'.Opens)
    (hW : q ⁻¹ᵁ W' = W) (hD' : D' ≤ W') (h : W ⊓ q ⁻¹ᵁ D' = D) : q ⁻¹ᵁ D' = D := by
  rw [← h]
  refine (inf_eq_right.2 ?_).symm
  rw [← hW]
  exact q.preimage_mono hD'

noncomputable def GChain.cut (C : GChain X xt G a) (RC : ChartRing 𝒪 π X xb xt G a C) (f : ↥(ChartRing.A 𝒪 π X xb xt G a RC)) :
    GChain X xt G a where
  W m := (X m).basicOpen (RC.lvl m (Ideal.Quotient.mk _ (f : RC.R)))
  affine m := (C.affine m).basicOpen _
  stable m g := by
    apply preimage_eq_of_inf_eq (a m g).hom (C.W m) (C.W m) _ _ (C.stable m g) ((X m).basicOpen_le _)
    have h := RC.lvl_smul m g⁻¹ (f : RC.R)
    simp only [inv_inv] at h
    rw [← Scheme.basicOpen_appLE (a m g).hom (C.W m) (C.W m) (by rw [C.stable]), h,
      show g⁻¹ • (f : RC.R) = f from f.2 g⁻¹]
  compat m := by
    apply preimage_eq_of_inf_eq (xt m) (C.W m) (C.W (m + 1)) _ _ (C.compat m) ((X (m + 1)).basicOpen_le _)
    rw [← Scheme.basicOpen_appLE (xt m) (C.W m) (C.W (m + 1)) (by rw [C.compat]), RC.lvl_compat]

omit hdvr hπ hcomplete in
theorem GChain.cut_W (C : GChain X xt G a) (RC : ChartRing 𝒪 π X xb xt G a C) (f : ↥(ChartRing.A 𝒪 π X xb xt G a RC)) (m : ℕ) :
    (C.cut 𝒪 π X xb xt G a RC f).W m = (X m).basicOpen (RC.lvl m (Ideal.Quotient.mk _ (f : RC.R))) := rfl

omit hdvr hπ hcomplete in
theorem GChain.cut_W_le (C : GChain X xt G a) (RC : ChartRing 𝒪 π X xb xt G a C) (f : ↥(ChartRing.A 𝒪 π X xb xt G a RC))
    (m : ℕ) : (C.cut 𝒪 π X xb xt G a RC f).W m ≤ C.W m :=
  (X m).basicOpen_le _

include hdvr hπ hcomplete in

theorem Pieces.V_cut (P : Pieces 𝒪 π X xb xt G a RC) (C : GChain X xt G a) (f : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)))
    (m : ℕ) : P.V (C.cut 𝒪 π X xb xt G a (RC C) f) m = (P.Y m).basicOpen (P.chart C m (Ideal.Quotient.mk _ f)) := by
  apply Pieces.eq_of_preimage_eq 𝒪 hdvr π hπ hcomplete X xb xt G a P m
  rw [P.V_pre, Pieces.preimage_basicOpen_chart]
  rfl

omit hdvr hπ hcomplete X xb xt G a in

theorem surjective_SpecMap_factor (n : ℕ) :
    Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))).base := by
  have hST : Ideal.span {π ^ (n + 1 + 1)} ≤ Ideal.span {π ^ (n + 1)} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))
  have key : Function.Surjective (PrimeSpectrum.comap (Ideal.Quotient.factor hST)) := by
    intro x
    have hx : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor hST)) := by
      rw [range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective hST)]
      intro z hz
      obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective z
      have ho : o ∈ Ideal.span {π ^ (n + 1)} := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.factor_mk hST]
        exact hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ho
      have hπx : Ideal.Quotient.mk (Ideal.span {π ^ (n + 1 + 1)}) π ∈ x.asIdeal := by
        apply x.isPrime.mem_of_pow_mem (n + 1 + 1)
        rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)]
        exact x.asIdeal.zero_mem
      rw [map_mul, map_pow]
      exact x.asIdeal.mul_mem_left _ (x.asIdeal.pow_mem_of_mem hπx _ (Nat.succ_pos _))
    exact hx
  intro x
  obtain ⟨y, hy⟩ := key x
  refine ⟨y, ?_⟩
  rw [← hy]
  erw [Spec.map_apply, CommRingCat.hom_ofHom]

theorem Pieces.yt_surjective (P : Pieces 𝒪 π X xb xt G a RC) (n : ℕ) : Function.Surjective (P.yt n).base := by
  have h := yt_isPullback_of 𝒪 π X xb xt G a P n
  haveI : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))) :=
    ⟨surjective_SpecMap_factor 𝒪 π n⟩
  exact (MorphismProperty.of_isPullback (P := @Surjective) h.flip this).surj

omit hdvr hπ hcomplete in

theorem Pieces.V_le_iff_succ (P : Pieces 𝒪 π X xb xt G a RC) (U : ∀ n : ℕ, (P.Y n).Opens)
    (hU : ∀ n : ℕ, (P.yt n) ⁻¹ᵁ (U (n + 1)) = U n) (C : GChain X xt G a) (m : ℕ) :
    P.V C m ≤ U m ↔ P.V C (m + 1) ≤ U (m + 1) := by
  constructor
  · intro h y hy
    obtain ⟨y', rfl⟩ := P.yt_surjective 𝒪 π X xb xt G a m y
    have hy' : y' ∈ (P.yt m) ⁻¹ᵁ (P.V C (m + 1)) := hy
    rw [P.V_compat] at hy'
    have := h hy'
    rw [← hU] at this
    exact this
  · intro h
    rw [← P.V_compat, ← hU]
    exact (P.yt m).preimage_mono h

omit hdvr hπ hcomplete in
theorem Pieces.V_le_forall (P : Pieces 𝒪 π X xb xt G a RC) (U : ∀ n : ℕ, (P.Y n).Opens)
    (hU : ∀ n : ℕ, (P.yt n) ⁻¹ᵁ (U (n + 1)) = U n) (C : GChain X xt G a) {n : ℕ} (h : P.V C n ≤ U n) (m : ℕ) :
    P.V C m ≤ U m := by
  have key : ∀ k : ℕ, (P.V C k ≤ U k ↔ P.V C 0 ≤ U 0) := by
    intro k
    induction k with
    | zero => exact Iff.rfl
    | succ k ih => exact (P.V_le_iff_succ 𝒪 π X xb xt G a U hU C k).symm.trans ih
  exact (key m).2 ((key n).1 h)

include hdvr hπ hcomplete in

theorem Pieces.univ_loc_Spec (P : Pieces 𝒪 π X xb xt G a RC) (B : CommRingCat.{0})
    (U : ∀ n : ℕ, (P.Y n).Opens) (hU : ∀ n : ℕ, (P.yt n) ⁻¹ᵁ (U (n + 1)) = U n)
    (u : ∀ n : ℕ, (↑((P.p n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ Spec B)
    (hug : ∀ (n : ℕ) (g : G),
      Scheme.Hom.resLE (a n g).hom ((P.p n) ⁻¹ᵁ (U n)) ((P.p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_inv]) ≫ u n = u n)
    (hut : ∀ n : ℕ,
      Scheme.Hom.resLE (xt n) ((P.p (n + 1)) ⁻¹ᵁ (U (n + 1))) ((P.p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_xt, Scheme.Hom.comp_preimage, hU]) ≫ u (n + 1) = u n) :
    ∃ v : ∀ n : ℕ, (↑(U n) : Scheme.{0}) ⟶ Spec B, ∀ n : ℕ, (P.p n) ∣_ (U n) ≫ v n = u n := by
  classical

  let I : Type := {C : GChain X xt G a // ∀ m : ℕ, P.V C m ≤ U m}
  have hW : ∀ (i : I) (m : ℕ), i.1.W m ≤ (P.p m) ⁻¹ᵁ (U m) := fun i m => by
    rw [← P.V_pre]; exact (P.p m).preimage_mono (i.2 m)

  let w : ∀ (i : I) (m : ℕ), (↑(i.1.W m) : Scheme.{0}) ⟶ Spec B := fun i m => (X m).homOfLE (hW i m) ≫ u m
  have hwg : ∀ (i : I) (m : ℕ) (g : G), (a m g).hom.resLE (i.1.W m) (i.1.W m) (by rw [i.1.stable]) ≫ w i m = w i m := by
    intro i m g
    have e1 : (a m g).hom.resLE (i.1.W m) (i.1.W m) (by rw [i.1.stable]) ≫ (X m).homOfLE (hW i m) =
        (X m).homOfLE (hW i m) ≫ (a m g).hom.resLE ((P.p m) ⁻¹ᵁ (U m)) ((P.p m) ⁻¹ᵁ (U m))
          (by rw [← Scheme.Hom.comp_preimage, P.p_inv]) := by
      simp [← cancel_mono (Scheme.Opens.ι _)]
    simp only [w]
    rw [← Category.assoc, e1, Category.assoc, hug]
  have hwt : ∀ (i : I) (m : ℕ), (xt m).resLE (i.1.W (m + 1)) (i.1.W m) (by rw [i.1.compat]) ≫ w i (m + 1) = w i m := by
    intro i m
    have e1 : (xt m).resLE (i.1.W (m + 1)) (i.1.W m) (by rw [i.1.compat]) ≫ (X (m + 1)).homOfLE (hW i (m + 1)) =
        (X m).homOfLE (hW i m) ≫ (xt m).resLE ((P.p (m + 1)) ⁻¹ᵁ (U (m + 1))) ((P.p m) ⁻¹ᵁ (U m))
          (by rw [← Scheme.Hom.comp_preimage, P.p_xt, Scheme.Hom.comp_preimage, hU]) := by
      simp [← cancel_mono (Scheme.Opens.ι _)]
    simp only [w]
    rw [← Category.assoc, e1, Category.assoc, hut]

  have hv := fun i : I => P.univ_chart 𝒪 π X xb xt G a i.1 B (w i) (hwg i) (hwt i)
  choose v hv using hv

  have agree : ∀ (n : ℕ) (i : I) (O : (P.Y n).Opens) (hO : O ≤ P.V i.1 n),
      (P.p n) ∣_ O ≫ (P.Y n).homOfLE hO ≫ v i n =
        (X n).homOfLE (((P.p n).preimage_mono hO).trans ((P.p n).preimage_mono (i.2 n))) ≫ u n := by
    intro n i O hO
    have h1 : (P.p n) ⁻¹ᵁ O ≤ i.1.W n := by rw [← P.V_pre]; exact (P.p n).preimage_mono hO
    have e2 : (P.p n) ∣_ O ≫ (P.Y n).homOfLE hO =
        (X n).homOfLE h1 ≫ (P.p n).resLE (P.V i.1 n) (i.1.W n) (by rw [P.V_pre]) := by
      simp [← cancel_mono (Scheme.Opens.ι _)]
    rw [← Category.assoc, e2, Category.assoc, hv i n]
    simp only [w]
    rw [← Category.assoc, Scheme.homOfLE_homOfLE]

  have hcovU : ∀ (n : ℕ) (y : P.Y n), y ∈ U n → ∃ i : I, y ∈ P.V i.1 n := by
    intro n y hy
    obtain ⟨C, hC⟩ := P.V_cover n y
    obtain ⟨s, hsU, hys⟩ := (P.V_affine C n).exists_basicOpen_le ⟨y, hy⟩ hC
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective ((P.chart C n).symm s)
    have hVs : P.V (C.cut 𝒪 π X xb xt G a (RC C) f) n = (P.Y n).basicOpen s := by
      rw [P.V_cut 𝒪 hdvr π hπ hcomplete X xb xt G a C f n, hf, RingEquiv.apply_symm_apply]
    refine ⟨⟨C.cut 𝒪 π X xb xt G a (RC C) f, P.V_le_forall 𝒪 π X xb xt G a U hU _ (n := n) ?_⟩, ?_⟩
    · rw [hVs]; exact hsU
    · show y ∈ P.V (C.cut 𝒪 π X xb xt G a (RC C) f) n
      rw [hVs]; exact hys

  have hglue : ∀ n : ℕ, ∃ vn : (↑(U n) : Scheme.{0}) ⟶ Spec B, (P.p n) ∣_ (U n) ≫ vn = u n := by
    intro n
    let 𝒰 : (↑(U n) : Scheme.{0}).OpenCover :=
      { I₀ := I
        X := fun i => ↑(P.V i.1 n)
        f := fun i => (P.Y n).homOfLE (i.2 n)
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          refine ⟨fun x => ?_, inferInstance⟩
          obtain ⟨i, hi⟩ := hcovU n x.1 x.2
          exact ⟨i, ⟨x.1, hi⟩, Subtype.ext (by simp)⟩ }
    have hcompat : ∀ i j : 𝒰.I₀, Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ v i n = Limits.pullback.snd (𝒰.f i) (𝒰.f j) ≫ v j n := by
      intro i j
      refine (cancel_epi (isPullback_opens_inf_le (i.2 n) (j.2 n)).isoPullback.hom).mp ?_
      simp only [𝒰, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
      haveI := p_epi_loc_of 𝒪 hdvr π hπ hcomplete X xb xt G a P n (P.V i.1 n ⊓ P.V j.1 n)
      rw [← cancel_epi ((P.p n) ∣_ (P.V i.1 n ⊓ P.V j.1 n)), agree n i _ inf_le_left, agree n j _ inf_le_right]
    refine ⟨𝒰.glueMorphisms (fun i => v i n) hcompat, ?_⟩

    let 𝒱 : (↑((P.p n) ⁻¹ᵁ (U n)) : Scheme.{0}).OpenCover :=
      { I₀ := I
        X := fun i => ↑((P.p n) ⁻¹ᵁ (P.V i.1 n))
        f := fun i => (X n).homOfLE ((P.p n).preimage_mono (i.2 n))
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          refine ⟨fun x => ?_, inferInstance⟩
          obtain ⟨i, hi⟩ := hcovU n ((P.p n).base x.1) x.2
          exact ⟨i, ⟨x.1, hi⟩, Subtype.ext (by simp)⟩ }
    refine 𝒱.hom_ext _ _ fun i => ?_
    have e3 : (X n).homOfLE ((P.p n).preimage_mono (i.2 n)) ≫ (P.p n) ∣_ (U n) =
        (P.p n) ∣_ (P.V i.1 n) ≫ (P.Y n).homOfLE (i.2 n) := by
      simp [← cancel_mono (Scheme.Opens.ι _)]
    simp only [𝒱]
    rw [← Category.assoc, e3, Category.assoc]
    change (P.p n) ∣_ (P.V i.1 n) ≫ 𝒰.f i ≫ 𝒰.glueMorphisms (fun i => v i n) hcompat = _
    rw [Scheme.Cover.ι_glueMorphisms]
    have := agree n i (P.V i.1 n) le_rfl
    rw [Scheme.homOfLE_rfl, Category.id_comp] at this
    exact this
  choose vn hvn using hglue
  exact ⟨vn, hvn⟩

include hdvr hπ hcomplete in

theorem Pieces.univ_loc_affine (P : Pieces 𝒪 π X xb xt G a RC) (T : Scheme.{0}) [IsAffine T]
    (U : ∀ n : ℕ, (P.Y n).Opens) (hU : ∀ n : ℕ, (P.yt n) ⁻¹ᵁ (U (n + 1)) = U n)
    (u : ∀ n : ℕ, (↑((P.p n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T)
    (hug : ∀ (n : ℕ) (g : G),
      Scheme.Hom.resLE (a n g).hom ((P.p n) ⁻¹ᵁ (U n)) ((P.p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_inv]) ≫ u n = u n)
    (hut : ∀ n : ℕ,
      Scheme.Hom.resLE (xt n) ((P.p (n + 1)) ⁻¹ᵁ (U (n + 1))) ((P.p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_xt, Scheme.Hom.comp_preimage, hU]) ≫ u (n + 1) = u n) :
    ∃ v : ∀ n : ℕ, (↑(U n) : Scheme.{0}) ⟶ T, ∀ n : ℕ, (P.p n) ∣_ (U n) ≫ v n = u n := by
  obtain ⟨v, hv⟩ := P.univ_loc_Spec 𝒪 hdvr π hπ hcomplete X xb xt G a Γ(T, ⊤) U hU (fun n => u n ≫ T.isoSpec.hom)
    (fun n g => by rw [← Category.assoc, hug]) (fun n => by rw [← Category.assoc, hut])
  exact ⟨fun n => v n ≫ T.isoSpec.inv, fun n => by
    rw [← Category.assoc, hv, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩

open scoped Pointwise in
include hdvr hπ hcomplete in

theorem Pieces.exists_smul_eq_of_apply_eq (P : Pieces 𝒪 π X xb xt G a RC) (n : ℕ) (x x' : X n)
    (h : (P.p n).base x = (P.p n).base x') : ∃ g : G, (a n g).hom.base x = x' := by
  classical
  obtain ⟨C, hy⟩ := P.V_cover n ((P.p n).base x)

  let R := (RC C).R
  let A := ChartRing.A 𝒪 π X xb xt G a (RC C)
  haveI : Algebra.IsInvariant (↥A) R G := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have hW : IsAffineOpen (C.W n) := C.affine n
  have hV : IsAffineOpen (P.V C n) := P.V_affine C n
  have hle : C.W n ≤ (P.p n) ⁻¹ᵁ (P.V C n) := by rw [P.V_pre]
  have hx : x ∈ C.W n := by rw [← P.V_pre]; exact hy
  have hx' : x' ∈ C.W n := by rw [← P.V_pre]; show (P.p n).base x' ∈ P.V C n; rw [← h]; exact hy

  let ρ : R →+* Γ(X n, C.W n) := ((RC C).lvl n).toRingHom.comp (Ideal.Quotient.mk _)
  have hρ : Function.Surjective ρ := ((RC C).lvl n).surjective.comp Ideal.Quotient.mk_surjective

  let 𝔭 := hW.primeIdealOf ⟨x, hx⟩
  let 𝔭' := hW.primeIdealOf ⟨x', hx'⟩
  let Q : Ideal R := 𝔭.asIdeal.comap ρ
  let Q' : Ideal R := 𝔭'.asIdeal.comap ρ
  haveI : Q.IsPrime := Ideal.comap_isPrime ρ 𝔭.asIdeal
  haveI : Q'.IsPrime := Ideal.comap_isPrime ρ 𝔭'.asIdeal

  have hunder : ∀ (z : X n) (hz : z ∈ C.W n),
      ((hW.primeIdealOf ⟨z, hz⟩).asIdeal.comap ρ).under (↥A) =
        ((hV.primeIdealOf ⟨(P.p n).base z, hle hz⟩).asIdeal.comap
          ((P.chart C n).toRingHom.comp (Ideal.Quotient.mk _))) := by
    intro z hz
    rw [Ideal.under_def, Ideal.comap_comap, ← IsAffineOpen.comap_primeIdealOf_appLE (P.V C n) hV (C.W n) hW hle hz,
      PrimeSpectrum.comap_asIdeal, Ideal.comap_comap]
    congr 1
    ext b
    show ρ (b : R) = (P.p n).appLE (P.V C n) (C.W n) hle (P.chart C n (Ideal.Quotient.mk _ b))
    rw [P.chart_p C n b]
    rfl
  have hQQ' : Q.under (↥A) = Q'.under (↥A) := by
    simp only [Q, Q', 𝔭, 𝔭', hunder]
    simp only [h]
  haveI : SMulCommClass G (↥A) R := ⟨fun g b r => by
    change g • ((b : R) * r) = (b : R) * g • r
    rw [smul_mul', show g • (b : R) = b from b.2 g]⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (↥A) R G Q Q' hQQ'
  refine ⟨g, ?_⟩

  have hgx : (a n g).hom.base x ∈ C.W n := by
    show x ∈ (a n g).hom ⁻¹ᵁ (C.W n); rw [C.stable]; exact hx
  have hsymm : ∀ r : R, ((MulSemiringAction.toRingAut G R) g).symm r = g⁻¹ • r := fun r => rfl
  have hsmul : (hW.primeIdealOf ⟨(a n g).hom.base x, hgx⟩).asIdeal.comap ρ = g • Q := by
    rw [← IsAffineOpen.comap_primeIdealOf_appLE (C.W n) hW (C.W n) hW (by rw [C.stable]) hx,
      PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, Ideal.pointwise_smul_eq_comap]
    ext r
    have hl := (RC C).lvl_smul n g⁻¹ r
    simp only [inv_inv] at hl
    simp only [Ideal.mem_comap, Q, 𝔭, RingHom.coe_comp, Function.comp_apply, hsymm]
    exact Iff.of_eq (congrArg (fun s => s ∈ (hW.primeIdealOf ⟨x, hx⟩).asIdeal) hl)

  have key : hW.primeIdealOf ⟨(a n g).hom.base x, hgx⟩ = 𝔭' := by
    apply PrimeSpectrum.ext
    apply Ideal.comap_injective_of_surjective ρ hρ
    rw [hsmul, ← hg]
  have := congrArg hW.fromSpec key
  rwa [IsAffineOpen.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_primeIdealOf] at this

include hdvr hπ hcomplete in

theorem Pieces.exists_preimage_eq_of_stable (P : Pieces 𝒪 π X xb xt G a RC) (n : ℕ) (O : (X n).Opens)
    (hO : ∀ g : G, (a n g).hom ⁻¹ᵁ O = O) : ∃ U' : (P.Y n).Opens, (P.p n) ⁻¹ᵁ U' = O := by
  haveI := p_isFinite_of 𝒪 hdvr π hπ hcomplete X xb xt G a P n
  have hcl : IsClosedMap (P.p n).base := (P.p n).isClosedMap
  refine ⟨⟨((P.p n).base '' (O : Set (X n))ᶜ)ᶜ, (hcl _ (isClosed_compl_iff.2 O.2)).isOpen_compl⟩, ?_⟩
  ext z
  change (P.p n).base z ∈ ((P.p n).base '' (O : Set (X n))ᶜ)ᶜ ↔ z ∈ O
  rw [Set.mem_compl_iff, Set.mem_image]
  constructor
  · intro hz
    by_contra hzO
    exact hz ⟨z, hzO, rfl⟩
  · rintro hz ⟨z', hz', e⟩
    obtain ⟨g, rfl⟩ := P.exists_smul_eq_of_apply_eq 𝒪 hdvr π hπ hcomplete X xb xt G a n z z' e.symm
    apply hz'
    have : z ∈ (a n g).hom ⁻¹ᵁ O := by rw [hO]; exact hz
    exact this

include hdvr hπ hcomplete in

theorem Pieces.glue_descended (P : Pieces 𝒪 π X xb xt G a RC) (n : ℕ) (T : Scheme.{0}) (U : (P.Y n).Opens)
    (u : (↑((P.p n) ⁻¹ᵁ U) : Scheme.{0}) ⟶ T) {J : Type} (Uj : J → (P.Y n).Opens) (hle : ∀ j : J, Uj j ≤ U)
    (hcov : ∀ y : P.Y n, y ∈ U → ∃ j : J, y ∈ Uj j) (v : ∀ j : J, (↑(Uj j) : Scheme.{0}) ⟶ T)
    (hv : ∀ j : J, (P.p n) ∣_ (Uj j) ≫ v j = (X n).homOfLE ((P.p n).preimage_mono (hle j)) ≫ u) :
    ∃ w : (↑U : Scheme.{0}) ⟶ T, (P.p n) ∣_ U ≫ w = u := by
  classical
  have agree : ∀ (j : J) (O : (P.Y n).Opens) (hO : O ≤ Uj j),
      (P.p n) ∣_ O ≫ (P.Y n).homOfLE hO ≫ v j =
        (X n).homOfLE (((P.p n).preimage_mono hO).trans ((P.p n).preimage_mono (hle j))) ≫ u := by
    intro j O hO
    have e2 : (P.p n) ∣_ O ≫ (P.Y n).homOfLE hO = (X n).homOfLE ((P.p n).preimage_mono hO) ≫ (P.p n) ∣_ (Uj j) := by
      simp [← cancel_mono (Scheme.Opens.ι _)]
    rw [← Category.assoc, e2, Category.assoc, hv j, ← Category.assoc, Scheme.homOfLE_homOfLE]
  let 𝒰 : (↑U : Scheme.{0}).OpenCover :=
    { I₀ := J
      X := fun j => ↑(Uj j)
      f := fun j => (P.Y n).homOfLE (hle j)
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ?_, inferInstance⟩
        obtain ⟨j, hj⟩ := hcov x.1 x.2
        exact ⟨j, ⟨x.1, hj⟩, Subtype.ext (by simp)⟩ }
  have hcompat : ∀ i j : 𝒰.I₀,
      Limits.pullback.fst (𝒰.f i) (𝒰.f j) ≫ v i = Limits.pullback.snd (𝒰.f i) (𝒰.f j) ≫ v j := by
    intro i j
    refine (cancel_epi (isPullback_opens_inf_le (hle i) (hle j)).isoPullback.hom).mp ?_
    simp only [𝒰, IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
    haveI := p_epi_loc_of 𝒪 hdvr π hπ hcomplete X xb xt G a P n (Uj i ⊓ Uj j)
    rw [← cancel_epi ((P.p n) ∣_ (Uj i ⊓ Uj j)), agree i _ inf_le_left, agree j _ inf_le_right]
  refine ⟨𝒰.glueMorphisms v hcompat, ?_⟩
  let 𝒱 : (↑((P.p n) ⁻¹ᵁ U) : Scheme.{0}).OpenCover :=
    { I₀ := J
      X := fun j => ↑((P.p n) ⁻¹ᵁ (Uj j))
      f := fun j => (X n).homOfLE ((P.p n).preimage_mono (hle j))
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ?_, inferInstance⟩
        obtain ⟨j, hj⟩ := hcov ((P.p n).base x.1) x.2
        exact ⟨j, ⟨x.1, hj⟩, Subtype.ext (by simp)⟩ }
  refine 𝒱.hom_ext _ _ fun j => ?_
  have e3 : (X n).homOfLE ((P.p n).preimage_mono (hle j)) ≫ (P.p n) ∣_ U = (P.p n) ∣_ (Uj j) ≫ (P.Y n).homOfLE (hle j) := by
    simp [← cancel_mono (Scheme.Opens.ι _)]
  simp only [𝒱]
  rw [← Category.assoc, e3, Category.assoc]
  change (P.p n) ∣_ (Uj j) ≫ 𝒰.f j ≫ 𝒰.glueMorphisms v hcompat = _
  rw [Scheme.Cover.ι_glueMorphisms, hv]

include hdvr hπ hcomplete in
theorem Pieces.le_of_preimage_le (P : Pieces 𝒪 π X xb xt G a RC) (n : ℕ) (U U' : (P.Y n).Opens)
    (h : (P.p n) ⁻¹ᵁ U ≤ (P.p n) ⁻¹ᵁ U') : U ≤ U' := by
  intro y hy
  obtain ⟨x, rfl⟩ := (p_surjective_of 𝒪 hdvr π hπ hcomplete X xb xt G a P n).surj y
  exact h hy

include hdvr hπ hcomplete in

theorem Pieces.univ_loc (P : Pieces 𝒪 π X xb xt G a RC) :
    ∀ (T : Scheme.{0}) (U : ∀ n : ℕ, (P.Y n).Opens) (hU : ∀ n : ℕ, (P.yt n) ⁻¹ᵁ (U (n + 1)) = U n)
    (u : ∀ n : ℕ, (↑((P.p n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T),
    (∀ (n : ℕ) (g : G),
      Scheme.Hom.resLE (a n g).hom ((P.p n) ⁻¹ᵁ (U n)) ((P.p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_inv]) ≫ u n = u n) →
    (∀ n : ℕ,
      Scheme.Hom.resLE (xt n) ((P.p (n + 1)) ⁻¹ᵁ (U (n + 1))) ((P.p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_xt, Scheme.Hom.comp_preimage, hU]) ≫ u (n + 1) = u n) →
    ∃ v : ∀ n : ℕ, (↑(U n) : Scheme.{0}) ⟶ T, ∀ n : ℕ, (P.p n) ∣_ (U n) ≫ v n = u n := by
  intro T U hU u hug hut
  classical
  let J : Type := T.affineOpens

  let O : J → ∀ n : ℕ, (X n).Opens := fun j n => ((P.p n) ⁻¹ᵁ (U n)).ι ''ᵁ ((u n) ⁻¹ᵁ (j : T.Opens))
  have hOle : ∀ (j : J) (n : ℕ), O j n ≤ (P.p n) ⁻¹ᵁ (U n) := fun j n => Scheme.Opens.ι_image_le _ _

  have hOg : ∀ (j : J) (n : ℕ) (g : G), (a n g).hom ⁻¹ᵁ (O j n) = O j n := by
    intro j n g
    have hpre : (a n g).hom ⁻¹ᵁ ((P.p n) ⁻¹ᵁ (U n)) = (P.p n) ⁻¹ᵁ (U n) := by
      rw [← Scheme.Hom.comp_preimage, P.p_inv]
    apply preimage_eq_of_inf_eq (a n g).hom _ _ _ _ hpre (hOle j n)
    have := congrArg (fun W => ((P.p n) ⁻¹ᵁ (U n)).ι ''ᵁ W)
      (congrArg (fun f : (↑((P.p n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T => f ⁻¹ᵁ (j : T.Opens)) (hug n g))
    simp only [Scheme.Hom.comp_preimage, Scheme.Hom.resLE_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι] at this
    exact this

  have hOt : ∀ (j : J) (n : ℕ), (xt n) ⁻¹ᵁ (O j (n + 1)) = O j n := by
    intro j n
    have hpre : (xt n) ⁻¹ᵁ ((P.p (n + 1)) ⁻¹ᵁ (U (n + 1))) = (P.p n) ⁻¹ᵁ (U n) := by
      rw [← Scheme.Hom.comp_preimage, P.p_xt, Scheme.Hom.comp_preimage, hU]
    apply preimage_eq_of_inf_eq (xt n) _ _ _ _ hpre (hOle j (n + 1))
    have := congrArg (fun W => ((P.p n) ⁻¹ᵁ (U n)).ι ''ᵁ W)
      (congrArg (fun f : (↑((P.p n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T => f ⁻¹ᵁ (j : T.Opens)) (hut n))
    simp only [Scheme.Hom.comp_preimage, Scheme.Hom.resLE_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι] at this
    exact this

  have hdesc := fun (j : J) (n : ℕ) => P.exists_preimage_eq_of_stable 𝒪 hdvr π hπ hcomplete X xb xt G a n (O j n) (hOg j n)
  choose U' hU' using hdesc
  have hU'le : ∀ (j : J) (n : ℕ), U' j n ≤ U n := fun j n =>
    P.le_of_preimage_le 𝒪 hdvr π hπ hcomplete X xb xt G a n _ _ (by rw [hU']; exact hOle j n)
  have hU'c : ∀ (j : J) (n : ℕ), (P.yt n) ⁻¹ᵁ (U' j (n + 1)) = U' j n := by
    intro j n
    apply Pieces.eq_of_preimage_eq 𝒪 hdvr π hπ hcomplete X xb xt G a P n
    rw [← Scheme.Hom.comp_preimage, ← P.p_xt, Scheme.Hom.comp_preimage, hU', hOt, hU']
  have hle' : ∀ (j : J) (n : ℕ), (P.p n) ⁻¹ᵁ (U' j n) ≤ (P.p n) ⁻¹ᵁ (U n) := fun j n =>
    (P.p n).preimage_mono (hU'le j n)

  have hrange : ∀ (j : J) (n : ℕ),
      Set.range ((X n).homOfLE (hle' j n) ≫ u n).base ⊆ Set.range (j : T.Opens).ι.base := by
    rintro j n _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hz : z.1 ∈ O j n := by rw [← hU']; exact z.2
    obtain ⟨w, hw, hwz⟩ := hz
    have : (X n).homOfLE (hle' j n) z = w := Subtype.ext (by rw [Scheme.homOfLE_apply]; exact hwz.symm)
    show u n ((X n).homOfLE (hle' j n) z) ∈ (j : T.Opens)
    rw [this]
    exact hw
  let u' : ∀ (j : J) (n : ℕ), (↑((P.p n) ⁻¹ᵁ (U' j n)) : Scheme.{0}) ⟶ ↑(j : T.Opens) := fun j n =>
    IsOpenImmersion.lift (j : T.Opens).ι ((X n).homOfLE (hle' j n) ≫ u n) (hrange j n)
  have hu' : ∀ (j : J) (n : ℕ), u' j n ≫ (j : T.Opens).ι = (X n).homOfLE (hle' j n) ≫ u n := fun j n =>
    IsOpenImmersion.lift_fac _ _ _
  have hug' : ∀ (j : J) (n : ℕ) (g : G),
      Scheme.Hom.resLE (a n g).hom ((P.p n) ⁻¹ᵁ (U' j n)) ((P.p n) ⁻¹ᵁ (U' j n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_inv]) ≫ u' j n = u' j n := by
    intro j n g
    rw [← cancel_mono (j : T.Opens).ι, Category.assoc, hu']
    have e1 : Scheme.Hom.resLE (a n g).hom ((P.p n) ⁻¹ᵁ (U' j n)) ((P.p n) ⁻¹ᵁ (U' j n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_inv]) ≫ (X n).homOfLE (hle' j n) =
        (X n).homOfLE (hle' j n) ≫ Scheme.Hom.resLE (a n g).hom ((P.p n) ⁻¹ᵁ (U n)) ((P.p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_inv]) := by
      simp [← cancel_mono (Scheme.Opens.ι _)]
    rw [← Category.assoc, e1, Category.assoc, hug]
  have hut' : ∀ (j : J) (n : ℕ),
      Scheme.Hom.resLE (xt n) ((P.p (n + 1)) ⁻¹ᵁ (U' j (n + 1))) ((P.p n) ⁻¹ᵁ (U' j n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_xt, Scheme.Hom.comp_preimage, hU'c]) ≫ u' j (n + 1) = u' j n := by
    intro j n
    rw [← cancel_mono (j : T.Opens).ι, Category.assoc, hu', hu']
    have e1 : Scheme.Hom.resLE (xt n) ((P.p (n + 1)) ⁻¹ᵁ (U' j (n + 1))) ((P.p n) ⁻¹ᵁ (U' j n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_xt, Scheme.Hom.comp_preimage, hU'c]) ≫ (X (n + 1)).homOfLE (hle' j (n + 1)) =
        (X n).homOfLE (hle' j n) ≫ Scheme.Hom.resLE (xt n) ((P.p (n + 1)) ⁻¹ᵁ (U (n + 1))) ((P.p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_xt, Scheme.Hom.comp_preimage, hU]) := by
      simp [← cancel_mono (Scheme.Opens.ι _)]
    rw [← Category.assoc, e1, Category.assoc, hut]

  have hv' := fun j : J => by
    haveI : IsAffine (↑(j : T.Opens) : Scheme.{0}) := j.2
    exact P.univ_loc_affine 𝒪 hdvr π hπ hcomplete X xb xt G a (↑(j : T.Opens)) (U' j) (hU'c j) (u' j) (hug' j) (hut' j)
  choose v' hv' using hv'

  have hcov : ∀ (n : ℕ) (y : P.Y n), y ∈ U n → ∃ j : J, y ∈ U' j n := by
    intro n y hy
    obtain ⟨x, rfl⟩ := (p_surjective_of 𝒪 hdvr π hπ hcomplete X xb xt G a P n).surj y
    have ht : u n ⟨x, hy⟩ ∈ (⊤ : T.Opens) := trivial
    rw [← iSup_affineOpens_eq_top, TopologicalSpace.Opens.mem_iSup] at ht
    obtain ⟨j, hj⟩ := ht
    refine ⟨j, ?_⟩
    show x ∈ (P.p n) ⁻¹ᵁ (U' j n)
    rw [hU']
    exact ⟨⟨x, hy⟩, hj, rfl⟩

  have hglue := fun n : ℕ => P.glue_descended 𝒪 hdvr π hπ hcomplete X xb xt G a n T (U n) (u n) (fun j : J => U' j n)
    (fun j => hU'le j n) (hcov n) (fun j => v' j n ≫ (j : T.Opens).ι)
    (fun j => by rw [← Category.assoc, hv', hu'])
  choose v hv using hglue
  exact ⟨v, hv⟩

include hdvr hπ hcomplete in

theorem univ_loc_of (P : Pieces 𝒪 π X xb xt G a RC) :
    ∀ (T : Scheme.{0}) (U : ∀ n : ℕ, (P.Y n).Opens) (hU : ∀ n : ℕ, (P.yt n) ⁻¹ᵁ (U (n + 1)) = U n)
    (u : ∀ n : ℕ, (↑((P.p n) ⁻¹ᵁ (U n)) : Scheme.{0}) ⟶ T),
    (∀ (n : ℕ) (g : G),
      Scheme.Hom.resLE (a n g).hom ((P.p n) ⁻¹ᵁ (U n)) ((P.p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_inv]) ≫ u n = u n) →
    (∀ n : ℕ,
      Scheme.Hom.resLE (xt n) ((P.p (n + 1)) ⁻¹ᵁ (U (n + 1))) ((P.p n) ⁻¹ᵁ (U n))
        (by rw [← Scheme.Hom.comp_preimage, P.p_xt, Scheme.Hom.comp_preimage, hU]) ≫ u (n + 1) = u n) →
    ∃ v : ∀ n : ℕ, (↑(U n) : Scheme.{0}) ⟶ T, ∀ n : ℕ, (P.p n) ∣_ (U n) ≫ v n = u n := by
  exact Pieces.univ_loc 𝒪 hdvr π hπ hcomplete X xb xt G a P

universe u_ig

namespace Fib7

theorem exists_ringHom_comp_eq_of_isIntegral_of_isAlgClosed
    {A D k : Type*} [CommRing A] [CommRing D] [Algebra A D] [Algebra.IsIntegral A D]
    (hinj : Function.Injective (algebraMap A D)) [Field k] [IsAlgClosed k] (φ : A →+* k) :
    ∃ ψ : D →+* k, ψ.comp (algebraMap A D) = φ := by
  classical
  let 𝔭 : Ideal A := RingHom.ker φ
  haveI h𝔭 : 𝔭.IsPrime := RingHom.ker_isPrime φ
  obtain ⟨𝔓, -, h𝔓, h𝔓𝔭⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭 (⊥ : Ideal D)
    (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
  haveI := h𝔓

  let 𝔭' : Ideal A := 𝔓.comap (algebraMap A D)
  let φbar : A ⧸ 𝔭' →+* k := Ideal.Quotient.lift 𝔭' φ (fun a ha => by
    have : a ∈ 𝔭 := by rw [← h𝔓𝔭]; exact ha
    exact this)
  have hφbar : Function.Injective φbar := by
    rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    show a ∈ 𝔓.comap (algebraMap A D)
    rw [h𝔓𝔭]; exact hx
  letI algAk : Algebra (A ⧸ 𝔭') k := φbar.toAlgebra
  haveI : IsDomain (D ⧸ 𝔓) := Ideal.Quotient.isDomain 𝔓
  haveI : IsDomain (A ⧸ 𝔭') := Ideal.Quotient.isDomain _
  haveI : Module.IsTorsionFree (A ⧸ 𝔭') (D ⧸ 𝔓) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (A ⧸ 𝔭') k := (Module.isTorsionFree_iff_algebraMap_injective).mpr hφbar
  haveI : Algebra.IsAlgebraic (A ⧸ 𝔭') (D ⧸ 𝔓) := Algebra.IsIntegral.isAlgebraic
  let ψbar : (D ⧸ 𝔓) →ₐ[A ⧸ 𝔭'] k := IsAlgClosed.lift
  refine ⟨ψbar.toRingHom.comp (Ideal.Quotient.mk 𝔓), ?_⟩
  ext a
  show ψbar (Ideal.Quotient.mk 𝔓 (algebraMap A D a)) = φ a
  rw [show Ideal.Quotient.mk 𝔓 (algebraMap A D a) = algebraMap (A ⧸ 𝔭') (D ⧸ 𝔓) (Ideal.Quotient.mk 𝔭' a) from rfl,
    ψbar.commutes]
  rfl

theorem hom_ext_of_isAffineOpen {T X : Scheme.{u_ig}} {U : X.Opens} (hU : IsAffineOpen U) {f g : T ⟶ X}
    (hf : (⊤ : T.Opens) ≤ f ⁻¹ᵁ U) (hg : (⊤ : T.Opens) ≤ g ⁻¹ᵁ U)
    (e : f.appLE U ⊤ hf = g.appLE U ⊤ hg) : f = g := by
  haveI : IsAffine (↑U : Scheme.{u_ig}) := hU
  have h1 : f.resLE U ⊤ hf = g.resLE U ⊤ hg := ext_of_isAffine (by
    rw [Scheme.Hom.appTop, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Scheme.Hom.resLE_app_top, e])
  have h2 : (⊤ : T.Opens).ι ≫ f = (⊤ : T.Opens).ι ≫ g := by
    rw [← Scheme.Hom.resLE_comp_ι f hf, h1, Scheme.Hom.resLE_comp_ι]
  haveI : IsIso (⊤ : T.Opens).ι := (inferInstance : IsIso T.topIso.hom)
  exact (cancel_epi _).mp h2

noncomputable def homOfSections {X : Scheme.{u_ig}} {U : X.Opens} (hU : IsAffineOpen U) {R : CommRingCat.{u_ig}}
    (θ : Γ(X, U) ⟶ R) : Spec R ⟶ X :=
  Spec.map θ ≫ hU.fromSpec

theorem homOfSections_preimage {X : Scheme.{u_ig}} {U : X.Opens} (hU : IsAffineOpen U) {R : CommRingCat.{u_ig}}
    (θ : Γ(X, U) ⟶ R) : (⊤ : (Spec R).Opens) ≤ (homOfSections hU θ) ⁻¹ᵁ U := by
  show ⊤ ≤ (Spec.map θ ≫ hU.fromSpec) ⁻¹ᵁ U
  rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self, Scheme.Hom.preimage_top]

theorem fromSpec_appLE_top {X : Scheme.{u_ig}} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec.appLE U ⊤ (by rw [hU.fromSpec_preimage_self]) = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  convert Category.comp_id _
  rfl

theorem appLE_homOfSections {X : Scheme.{u_ig}} {U : X.Opens} (hU : IsAffineOpen U) {R : CommRingCat.{u_ig}}
    (θ : Γ(X, U) ⟶ R) :
    (homOfSections hU θ).appLE U ⊤ (homOfSections_preimage hU θ) = θ ≫ (Scheme.ΓSpecIso R).inv := by
  have e₂ : (⊤ : (Spec R).Opens) ≤ (Spec.map θ) ⁻¹ᵁ ⊤ := by rw [Scheme.Hom.preimage_top]
  have h := Scheme.Hom.appLE_comp_appLE (Spec.map θ) hU.fromSpec U ⊤ ⊤ (by rw [hU.fromSpec_preimage_self]) e₂
  show Scheme.Hom.appLE (Spec.map θ ≫ hU.fromSpec) U ⊤ (homOfSections_preimage hU θ) = _
  rw [← h, fromSpec_appLE_top, Scheme.ΓSpecIso_inv_naturality]
  congr 1

end Fib7
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

include hdvr hπ hcomplete in

theorem fib_of (P : Pieces 𝒪 π X xb xt G a RC) :
    ∀ (n : ℕ) (k : Type) [Field k] [IsAlgClosed k] (y : Spec (CommRingCat.of k) ⟶ P.Y n),
    (∃ x : Spec (CommRingCat.of k) ⟶ X n, x ≫ P.p n = y) ∧
    ∀ x x' : Spec (CommRingCat.of k) ⟶ X n, x ≫ P.p n = y → (x' ≫ P.p n = y ↔ ∃ g : G, x' = x ≫ (a n g).hom) := by
  intro n k _ _ y
  classical

  obtain ⟨C, hC⟩ := P.V_cover n (y.base default)
  let R := (RC C).R
  let A : Subalgebra 𝒪 R := ChartRing.A 𝒪 π X xb xt G a (RC C)
  have hyV : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤ y ⁻¹ᵁ (P.V C n) := by
    intro z _
    rw [Subsingleton.elim z default]
    exact hC

  let I : Ideal ↥A := Ideal.span {algebraMap 𝒪 ↥A π ^ (n + 1)}
  let J : Ideal R := Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}
  let ρY : Γ(P.Y n, P.V C n) →+* k :=
    ((y.appLE (P.V C n) ⊤ hyV ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom)
  let φA : ↥A →+* k := ρY.comp ((P.chart C n).toRingHom.comp (Ideal.Quotient.mk I))

  haveI hinv : Algebra.IsInvariant ↥A R G := ⟨fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩
  haveI : SMulCommClass G ↥A R := ⟨fun g b r => by
    show g • ((b : R) * r) = (b : R) * (g • r)
    rw [smul_mul', b.2 g]⟩
  haveI : Algebra.IsIntegral ↥A R := Algebra.IsInvariant.isIntegral ↥A R G
  have hinj : Function.Injective (algebraMap ↥A R) := Subtype.val_injective

  have hsurjY : ∀ s : Γ(P.Y n, P.V C n), ∃ b : ↥A, P.chart C n (Ideal.Quotient.mk I b) = s := fun s => by
    obtain ⟨z, hz⟩ := (P.chart C n).surjective s
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨b, hz⟩
  have hsurjX : ∀ s : Γ(X n, C.W n), ∃ r : R, (RC C).lvl n (Ideal.Quotient.mk J r) = s := fun s => by
    obtain ⟨z, hz⟩ := ((RC C).lvl n).surjective s
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨r, hz⟩
  have hWV : C.W n ≤ (P.p n) ⁻¹ᵁ (P.V C n) := (P.V_pre C n).ge

  obtain ⟨ψ, hψ⟩ := Fib7.exists_ringHom_comp_eq_of_isIntegral_of_isAlgClosed hinj φA
  have hψA : ∀ b : ↥A, ψ (b : R) = φA b := fun b => by rw [← hψ]; rfl
  have hψJ : ∀ r ∈ J, ψ r = 0 := by
    intro r hr
    rw [Ideal.mem_span_singleton] at hr
    obtain ⟨s, rfl⟩ := hr
    rw [map_mul, show algebraMap 𝒪 R π ^ (n + 1) = ((algebraMap 𝒪 ↥A π ^ (n + 1) : ↥A) : R) from by simp, hψA]
    have h0 : Ideal.Quotient.mk I (algebraMap 𝒪 ↥A π ^ (n + 1)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp only [φA, RingHom.comp_apply, h0, map_zero, zero_mul]
  let ψbar : R ⧸ J →+* k := Ideal.Quotient.lift J ψ hψJ
  let θ : Γ(X n, C.W n) ⟶ CommRingCat.of k := CommRingCat.ofHom (ψbar.comp ((RC C).lvl n).symm.toRingHom)
  have hθ : ∀ r : R, θ.hom ((RC C).lvl n (Ideal.Quotient.mk J r)) = ψ r := fun r => by
    show ψbar (((RC C).lvl n).symm ((RC C).lvl n (Ideal.Quotient.mk J r))) = ψ r
    rw [RingEquiv.symm_apply_apply]; rfl
  let x : Spec (CommRingCat.of k) ⟶ X n := Fib7.homOfSections (C.affine n) θ
  have hxW := Fib7.homOfSections_preimage (C.affine n) θ
  have hxapp := Fib7.appLE_homOfSections (C.affine n) θ
  have hxpV : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤ (x ≫ P.p n) ⁻¹ᵁ (P.V C n) := fun z hz => hWV (hxW hz)
  have key : (x ≫ P.p n).appLE (P.V C n) ⊤ hxpV = y.appLE (P.V C n) ⊤ hyV := by
    rw [← Scheme.Hom.appLE_comp_appLE x (P.p n) (P.V C n) (C.W n) ⊤ hWV hxW, hxapp]
    ext s
    obtain ⟨b, rfl⟩ := hsurjY s
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, P.chart_p C n b, hθ, hψA]
    show (Scheme.ΓSpecIso (CommRingCat.of k)).inv ((Scheme.ΓSpecIso (CommRingCat.of k)).hom _) = _
    rw [Iso.hom_inv_id_apply]
    rfl
  refine ⟨⟨x, Fib7.hom_ext_of_isAffineOpen (P.V_affine C n) hxpV hyV key⟩, ?_⟩

  intro x₁ x₂ hx₁
  have landsW : ∀ z : Spec (CommRingCat.of k) ⟶ X n, z ≫ P.p n = y →
      (⊤ : (Spec (CommRingCat.of k)).Opens) ≤ z ⁻¹ᵁ (C.W n) := fun z hz => by
    rw [← P.V_pre C n, ← Scheme.Hom.comp_preimage, hz]; exact hyV
  letI algAk : Algebra ↥A k := φA.toAlgebra

  have mkHom : ∀ (z : Spec (CommRingCat.of k) ⟶ X n) (hz : z ≫ P.p n = y), ∃ s : R →ₐ[↥A] k, ∀ r : R,
      s r = ((z.appLE (C.W n) ⊤ (landsW z hz) ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom)
        ((RC C).lvl n (Ideal.Quotient.mk J r)) := by
    intro z hz
    let t : R →+* k := ((z.appLE (C.W n) ⊤ (landsW z hz) ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom).comp
      (((RC C).lvl n).toRingHom.comp (Ideal.Quotient.mk J))
    have ht : ∀ b : ↥A, t (b : R) = φA b := by
      intro b
      have e := Scheme.Hom.appLE_comp_appLE z (P.p n) (P.V C n) (C.W n) ⊤ hWV (landsW z hz)
      have e2 : (z ≫ P.p n).appLE (P.V C n) ⊤ (fun w hw => hWV (landsW z hz hw)) = y.appLE (P.V C n) ⊤ hyV := by
        subst hz; rfl
      show (Scheme.ΓSpecIso (CommRingCat.of k)).hom (z.appLE (C.W n) ⊤ (landsW z hz) ((RC C).lvl n (Ideal.Quotient.mk J (b : R)))) =
        (Scheme.ΓSpecIso (CommRingCat.of k)).hom (y.appLE (P.V C n) ⊤ hyV (P.chart C n (Ideal.Quotient.mk I b)))
      rw [← e2, ← e, CommRingCat.comp_apply, P.chart_p C n b]
    exact ⟨{ toRingHom := t, commutes' := fun b => ht b }, fun r => rfl⟩
  obtain ⟨s₁, hs₁⟩ := mkHom x₁ hx₁
  constructor
  · intro hx₂
    obtain ⟨s₂, hs₂⟩ := mkHom x₂ hx₂
    obtain ⟨g, hg⟩ := AlgebraicGeometry.exists_smul_algHom_eq_of_isInvariant_of_isDomain ↥A R G k s₁ s₂
    refine ⟨g⁻¹, ?_⟩
    have hgW : (⊤ : (Spec (CommRingCat.of k)).Opens) ≤ (x₁ ≫ (a n g⁻¹).hom) ⁻¹ᵁ (C.W n) := by
      rw [Scheme.Hom.comp_preimage, C.stable]; exact landsW x₁ hx₁
    apply Fib7.hom_ext_of_isAffineOpen (C.affine n) (landsW x₂ hx₂) hgW
    rw [← Scheme.Hom.appLE_comp_appLE x₁ (a n g⁻¹).hom (C.W n) (C.W n) ⊤ (by rw [C.stable]) (landsW x₁ hx₁)]
    ext s
    obtain ⟨r, rfl⟩ := hsurjX s
    rw [CommRingCat.comp_apply, (RC C).lvl_smul n g r]
    apply (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.injective
    show ((x₂.appLE (C.W n) ⊤ (landsW x₂ hx₂) ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom) ((RC C).lvl n (Ideal.Quotient.mk J r)) =
      ((x₁.appLE (C.W n) ⊤ (landsW x₁ hx₁) ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom) ((RC C).lvl n (Ideal.Quotient.mk J (g • r)))
    rw [← hs₂, ← hs₁, hg]
  · rintro ⟨g, rfl⟩
    rw [Category.assoc, P.p_inv, hx₁]

namespace Fib7

theorem top_le_preimage_of_closedPoint_mem {S : Type} [CommRing S] [IsLocalRing S] {Y : Scheme.{0}}
    (f : Spec (CommRingCat.of S) ⟶ Y) (V : Y.Opens) (h : f.base (IsLocalRing.closedPoint S) ∈ V) :
    (⊤ : (Spec (CommRingCat.of S)).Opens) ≤ f ⁻¹ᵁ V := by
  intro z _
  have hz : z ⤳ IsLocalRing.closedPoint S := IsLocalRing.specializes_closedPoint z
  exact (hz.map f.base.hom.continuous).mem_open V.isOpen h

theorem not_isUnit_of_isAdicComplete {R : Type} [CommRing R] [Nontrivial R] (ϖ : R)
    [IsAdicComplete (Ideal.span {ϖ}) R] : ¬ IsUnit ϖ := by
  intro hu
  have htop : Ideal.span {ϖ} = ⊤ := Ideal.span_singleton_eq_top.mpr hu
  have h1 : (1 : R) = 0 := by
    refine IsHausdorff.haus (I := Ideal.span {ϖ}) (M := R) inferInstance 1 (fun n => ?_)
    rw [htop, Ideal.top_pow]
    rw [Submodule.top_smul]; exact (Submodule.Quotient.eq _).mpr (by simp)
  exact one_ne_zero h1

theorem appLE_congr_hom {T Y : Scheme.{0}} {f g : T ⟶ Y} (h : f = g) (U : Y.Opens) (V : T.Opens)
    (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) : f.appLE U V hf = g.appLE U V hg := by
  subst h; rfl

theorem appLE_top_top {T Y : Scheme.{0}} (f : T ⟶ Y) (h : (⊤ : T.Opens) ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ h = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

end Fib7
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

set_option maxHeartbeats 1600000 in
include hdvr hπ hcomplete in

theorem adicFib_of (P : Pieces 𝒪 π X xb xt G a RC) :
    ∀ (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra 𝒪 R],
    IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R → IsAlgClosed (FractionRing R) →
    ∀ (y : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)})) ⟶ P.Y n),
    (∀ n : ℕ, y n ≫ P.yb n = Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)}) (algebraMap 𝒪 R)
      (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))) →
    (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ y (n + 1) = y n ≫ P.yt n) →
    (∃ x : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)})) ⟶ X n,
      (∀ n : ℕ, x n ≫ P.p n = y n) ∧
      ∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ x (n + 1) = x n ≫ xt n) ∧
    ∀ x x' : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)})) ⟶ X n,
      (∀ n : ℕ, x n ≫ P.p n = y n) → (∀ n : ℕ, x' n ≫ P.p n = y n) →
      (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ x (n + 1) = x n ≫ xt n) →
      (∀ n : ℕ, Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
        (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 R π) (Nat.le_succ (n + 1)))))) ≫ x' (n + 1) = x' n ≫ xt n) →
      ∃ g : G, ∀ n : ℕ, x' n = x n ≫ (a n g).hom := by
  intro R _ _ _ _ hcR hKR y hyb hyt
  classical

  let πR : R := algebraMap 𝒪 R π
  let I : Ideal R := Ideal.span {πR}
  have hI : ∀ n : ℕ, Ideal.span {πR ^ (n + 1)} = I ^ (n + 1) := fun n => (Ideal.span_singleton_pow πR (n + 1)).symm
  haveI : IsAdicComplete I R := hcR

  have hπR : ¬ IsUnit πR := Fib7.not_isUnit_of_isAdicComplete πR
  have hne : ∀ n : ℕ, Ideal.span {πR ^ (n + 1)} ≠ ⊤ := fun n h =>
    hπR ((isUnit_pow_iff (Nat.succ_ne_zero n)).mp (Ideal.span_singleton_eq_top.mp h))
  have hnt : ∀ n : ℕ, Nontrivial (R ⧸ Ideal.span {πR ^ (n + 1)}) := fun n => Ideal.Quotient.nontrivial_iff.mpr (hne n)
  have hloc : ∀ n : ℕ, IsLocalRing (R ⧸ Ideal.span {πR ^ (n + 1)}) := fun n =>
    haveI := hnt n; IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

  let hle : ∀ n : ℕ, Ideal.span {πR ^ (n + 1 + 1)} ≤ Ideal.span {πR ^ (n + 1)} := fun n =>
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow πR (Nat.le_succ (n + 1)))
  let tr : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)})) ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1 + 1)})) :=
    fun n => Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hle n)))
  have htr : ∀ n : ℕ, tr n ≫ y (n + 1) = y n ≫ P.yt n := fun n => hyt n
  let cp : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)})) := fun n =>
    haveI := hloc n; IsLocalRing.closedPoint (R ⧸ Ideal.span {πR ^ (n + 1)})
  have hcp : ∀ n : ℕ, (tr n).base (cp n) = cp (n + 1) := by
    intro n
    haveI := hloc n; haveI := hloc (n + 1); haveI := hnt n
    haveI : IsLocalHom (Ideal.Quotient.factor (hle n)) :=
      IsLocalHom.of_surjective _ (Ideal.Quotient.factor_surjective (hle n))
    exact IsLocalRing.comap_closedPoint (Ideal.Quotient.factor (hle n))

  obtain ⟨C, hC0⟩ := P.V_cover 0 ((y 0).base (cp 0))
  have hC : ∀ n : ℕ, (y n).base (cp n) ∈ P.V C n := by
    intro n
    induction n with
    | zero => exact hC0
    | succ n ih =>
      rw [← hcp n, ← Scheme.Hom.comp_apply, htr n, Scheme.Hom.comp_apply]
      have : (y n).base (cp n) ∈ (P.yt n) ⁻¹ᵁ (P.V C (n + 1)) := by rw [P.V_compat]; exact ih
      exact this
  have hVtop : ∀ n : ℕ, (⊤ : (Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).Opens) ≤ (y n) ⁻¹ᵁ (P.V C n) :=
    fun n => by haveI := hloc n; exact Fib7.top_le_preimage_of_closedPoint_mem (y n) (P.V C n) (hC n)

  let RW := (RC C).R
  let A : Subalgebra 𝒪 RW := ChartRing.A 𝒪 π X xb xt G a (RC C)
  let IA : ℕ → Ideal ↥A := fun n => Ideal.span {algebraMap 𝒪 ↥A π ^ (n + 1)}
  let J : ℕ → Ideal RW := fun n => Ideal.span {algebraMap 𝒪 RW π ^ (n + 1)}
  haveI hinv : Algebra.IsInvariant ↥A RW G := ⟨fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩
  haveI : SMulCommClass G ↥A RW := ⟨fun g b r => by
    show g • ((b : RW) * r) = (b : RW) * (g • r)
    rw [smul_mul', b.2 g]⟩
  haveI : Algebra.IsIntegral ↥A RW := Algebra.IsInvariant.isIntegral ↥A RW G
  have hinjA : Function.Injective (algebraMap ↥A RW) := Subtype.val_injective
  have hsurjY : ∀ (n : ℕ) (s : Γ(P.Y n, P.V C n)), ∃ b : ↥A, P.chart C n (Ideal.Quotient.mk (IA n) b) = s := fun n s => by
    obtain ⟨z, hz⟩ := (P.chart C n).surjective s
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨b, hz⟩
  have hsurjX : ∀ (n : ℕ) (s : Γ(X n, C.W n)), ∃ r : RW, (RC C).lvl n (Ideal.Quotient.mk (J n) r) = s := fun n s => by
    obtain ⟨z, hz⟩ := ((RC C).lvl n).surjective s
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨r, hz⟩

  let e : ∀ n : ℕ, (R ⧸ Ideal.span {πR ^ (n + 1)}) ≃+* R ⧸ I ^ (n + 1) := fun n => Ideal.quotEquivOfEq (hI n)
  let ρ : ∀ n : ℕ, Γ(P.Y n, P.V C n) →+* R ⧸ Ideal.span {πR ^ (n + 1)} := fun n =>
    ((y n).appLE (P.V C n) ⊤ (hVtop n) ≫ (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).hom).hom
  let f : ∀ n : ℕ, ↥A →+* R ⧸ I ^ (n + 1) := fun n =>
    (e n).toRingHom.comp ((ρ n).comp ((P.chart C n).toRingHom.comp (Ideal.Quotient.mk (IA n))))

  have hρ : ∀ (n : ℕ) (b : ↥A),
      Ideal.Quotient.factor (hle n) (ρ (n + 1) (P.chart C (n + 1) (Ideal.Quotient.mk (IA (n + 1)) b))) =
        ρ n (P.chart C n (Ideal.Quotient.mk (IA n) b)) := by
    intro n b
    have hV2 : (⊤ : (Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).Opens) ≤ (y n ≫ P.yt n) ⁻¹ᵁ (P.V C (n + 1)) := by
      rw [Scheme.Hom.comp_preimage, P.V_compat]; exact hVtop n
    have hV1 : (⊤ : (Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).Opens) ≤ (tr n ≫ y (n + 1)) ⁻¹ᵁ (P.V C (n + 1)) := by
      rw [htr n]; exact hV2
    have hcomp := Fib7.appLE_congr_hom (htr n) (P.V C (n + 1)) ⊤ hV1 hV2
    rw [← Scheme.Hom.appLE_comp_appLE (tr n) (y (n + 1)) (P.V C (n + 1)) ⊤ ⊤ (hVtop (n + 1))
        (by rw [Scheme.Hom.preimage_top]),
      ← Scheme.Hom.appLE_comp_appLE (y n) (P.yt n) (P.V C (n + 1)) (P.V C n) ⊤ (by rw [P.V_compat]) (hVtop n)] at hcomp
    have h2 := congrArg (fun φ => (φ ≫ (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).hom).hom
      (P.chart C (n + 1) (Ideal.Quotient.mk (IA (n + 1)) b))) hcomp
    simp only [Category.assoc, CommRingCat.hom_comp, RingHom.comp_apply] at h2
    rw [P.chart_yt C n b] at h2
    show Ideal.Quotient.factor (hle n) (((y (n + 1)).appLE (P.V C (n + 1)) ⊤ (hVtop (n + 1)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1 + 1)}))).hom).hom
          (P.chart C (n + 1) (Ideal.Quotient.mk (IA (n + 1)) b))) =
      ((y n).appLE (P.V C n) ⊤ (hVtop n) ≫ (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).hom).hom
        (P.chart C n (Ideal.Quotient.mk (IA n) b))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, IA] at h2 ⊢
    rw [← h2]

    have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.factor (hle n)))
    have hnat' := congrArg (fun φ => φ.hom ((y (n + 1)).appLE (P.V C (n + 1)) ⊤ (hVtop (n + 1))
      (P.chart C (n + 1) (Ideal.Quotient.mk (IA (n + 1)) b)))) hnat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat'
    rw [← hnat']
    simp only [Fib7.appLE_top_top]
    rfl

  have ha : StrictMono (fun n : ℕ => n + 1) := fun _ _ h => Nat.succ_lt_succ h
  have hf : ∀ {m : ℕ}, (Ideal.Quotient.factorPow I (ha.monotone m.le_succ)).comp (f (m + 1)) = f m := by
    intro m; ext b
    show Ideal.Quotient.factorPow I (ha.monotone m.le_succ) (e (m + 1) (ρ (m + 1) (P.chart C (m + 1) (Ideal.Quotient.mk (IA (m + 1)) b)))) =
      e m (ρ m (P.chart C m (Ideal.Quotient.mk (IA m) b)))
    rw [← hρ m b]
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (ρ (m + 1) (P.chart C (m + 1) (Ideal.Quotient.mk (IA (m + 1)) b)))
    rw [← hz]
    simp only [e, Ideal.quotEquivOfEq_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factorPow]
  let Φ : ↥A →+* R := IsAdicComplete.StrictMono.liftRingHom I ha f hf
  have hΦ : ∀ (n : ℕ) (b : ↥A), Ideal.Quotient.mk (I ^ (n + 1)) (Φ b) = f n b := fun n b =>
    IsAdicComplete.StrictMono.mk_liftRingHom I ha f hf b
  have hΦ' : ∀ (n : ℕ) (b : ↥A), Ideal.Quotient.mk (Ideal.span {πR ^ (n + 1)}) (Φ b) =
      ρ n (P.chart C n (Ideal.Quotient.mk (IA n) b)) := by
    intro n b
    apply (e n).injective
    rw [show e n (Ideal.Quotient.mk _ (Φ b)) = Ideal.Quotient.mk (I ^ (n + 1)) (Φ b) from Ideal.quotEquivOfEq_mk _ _, hΦ]
    rfl

  let K := FractionRing R
  haveI : IsAlgClosed K := hKR
  obtain ⟨ψ₀, hψ₀⟩ := Fib7.exists_ringHom_comp_eq_of_isIntegral_of_isAlgClosed hinjA ((algebraMap R K).comp Φ)
  have hψ₀A : ∀ b : ↥A, ψ₀ (b : RW) = algebraMap R K (Φ b) := fun b => by rw [← RingHom.comp_apply, ← hψ₀]; rfl
  have hintK : ∀ r : RW, IsIntegral R (ψ₀ r) := by
    intro r
    obtain ⟨p, hp, hpr⟩ := Algebra.IsIntegral.isIntegral (R := ↥A) r
    refine ⟨p.map Φ, hp.map Φ, ?_⟩
    rw [Polynomial.eval₂_map, hψ₀.symm, ← Polynomial.hom_eval₂, hpr, map_zero]
  have hVI : Valuation.Integers (ValuationRing.valuation R K) R :=
    { hom_inj := IsFractionRing.injective R K
      map_le_one := fun r => (ValuationRing.mem_integer_iff R K _).mpr ⟨r, rfl⟩
      exists_of_le_one := fun x hx => (ValuationRing.mem_integer_iff R K x).mp hx }
  haveI hIC : IsIntegrallyClosed R := hVI.isIntegrallyClosed
  have hrange : ∀ r : RW, ψ₀ r ∈ (algebraMap R K).range := fun r => by
    obtain ⟨s, hs⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := K)).mp (hintK r)
    exact ⟨s, hs⟩
  let ψ₁ : RW →+* ↥(algebraMap R K).range := ψ₀.codRestrict _ hrange
  let eR : R ≃+* ↥(algebraMap R K).range :=
    RingEquiv.ofBijective (algebraMap R K).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective R K (congrArg Subtype.val h), (algebraMap R K).rangeRestrict_surjective⟩
  let Ψ : RW →+* R := eR.symm.toRingHom.comp ψ₁
  have hΨK : ∀ r : RW, algebraMap R K (Ψ r) = ψ₀ r := fun r => by
    have : eR (eR.symm (ψ₁ r)) = ψ₁ r := eR.apply_symm_apply _
    exact congrArg Subtype.val this
  have hΨA : ∀ b : ↥A, Ψ (b : RW) = Φ b := fun b =>
    IsFractionRing.injective R K (by rw [hΨK, hψ₀A])

  have hΦ𝒪 : ∀ (n : ℕ) (o : 𝒪), Ideal.Quotient.mk (Ideal.span {πR ^ (n + 1)}) (Φ (algebraMap 𝒪 ↥A o)) =
      Ideal.Quotient.mk (Ideal.span {πR ^ (n + 1)}) (algebraMap 𝒪 R o) := by
    intro n o
    rw [hΦ', P.chart_yb C n o]
    have hb1 : (⊤ : (Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).Opens) ≤ (y n ≫ P.yb n) ⁻¹ᵁ ⊤ := le_top
    have e1 := Scheme.Hom.appLE_comp_appLE (y n) (P.yb n) ⊤ (P.V C n) ⊤ le_top (hVtop n)
    have e2 := Fib7.appLE_congr_hom (hyb n) ⊤ ⊤ hb1 (by rw [Scheme.Hom.preimage_top])
    show (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).hom.hom
        (((y n).appLE (P.V C n) ⊤ (hVtop n)).hom (((P.yb n).appLE ⊤ (P.V C n) le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv.hom (Ideal.Quotient.mk _ o)))) = _
    rw [← CommRingCat.comp_apply ((P.yb n).appLE ⊤ (P.V C n) le_top), e1, e2]
    have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)}) (algebraMap 𝒪 R)
      (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))
    have hnat' := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv.hom (Ideal.Quotient.mk _ o))) hnat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat'
    have hR : Ideal.Quotient.mk (Ideal.span {πR ^ (n + 1)}) (algebraMap 𝒪 R o) =
        (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 R π) ^ (n + 1)}) (algebraMap 𝒪 R)
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))
          ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).hom.hom
            ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv.hom (Ideal.Quotient.mk _ o))) := by
      rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, Ideal.quotientMap_mk]
    rw [hR, ← hnat']
    simp only [Fib7.appLE_top_top]
    rfl

  have hπW : algebraMap 𝒪 RW π = ((algebraMap 𝒪 ↥A π : ↥A) : RW) := rfl
  have hΨJ : ∀ (n : ℕ) (r : RW), r ∈ J n → Ideal.Quotient.mk (Ideal.span {πR ^ (n + 1)}) (Ψ r) = 0 := by
    intro n r hr
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have h1 : Ideal.Quotient.mk (Ideal.span {πR ^ (n + 1)}) (Ψ (algebraMap 𝒪 RW π)) = Ideal.Quotient.mk _ πR := by
      rw [hπW, hΨA, hΦ𝒪 n π]
    rw [map_mul, map_pow, map_mul, map_pow, h1, ← map_pow (Ideal.Quotient.mk (Ideal.span {πR ^ (n + 1)})),
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), mul_zero]
  let Ψbar : ∀ n : ℕ, RW ⧸ J n →+* R ⧸ Ideal.span {πR ^ (n + 1)} := fun n =>
    Ideal.Quotient.lift (J n) ((Ideal.Quotient.mk _).comp Ψ) (fun r hr => hΨJ n r hr)
  have hΨbar : ∀ (n : ℕ) (r : RW), Ψbar n (Ideal.Quotient.mk (J n) r) = Ideal.Quotient.mk _ (Ψ r) := fun n r => rfl
  obtain ⟨θ, hθ⟩ : ∃ θ : ∀ n : ℕ, Γ(X n, C.W n) ⟶ CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}),
      ∀ (n : ℕ) (r : RW), (θ n).hom ((RC C).lvl n (Ideal.Quotient.mk (J n) r)) = Ideal.Quotient.mk _ (Ψ r) := by
    refine ⟨fun n => CommRingCat.ofHom ((Ψbar n).comp ((RC C).lvl n).symm.toRingHom), fun n r => ?_⟩
    show Ψbar n (((RC C).lvl n).symm ((RC C).lvl n (Ideal.Quotient.mk (J n) r))) = _
    rw [RingEquiv.symm_apply_apply]; rfl
  obtain ⟨x, hxW, hxapp⟩ : ∃ (x : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)})) ⟶ X n)
      (hxW : ∀ n : ℕ, (⊤ : (Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).Opens) ≤ (x n) ⁻¹ᵁ (C.W n)),
      ∀ n : ℕ, (x n).appLE (C.W n) ⊤ (hxW n) = θ n ≫ (Scheme.ΓSpecIso _).inv :=
    ⟨fun n => Fib7.homOfSections (C.affine n) (θ n), fun n => Fib7.homOfSections_preimage (C.affine n) (θ n),
      fun n => Fib7.appLE_homOfSections (C.affine n) (θ n)⟩
  have hWV : ∀ n : ℕ, C.W n ≤ (P.p n) ⁻¹ᵁ (P.V C n) := fun n => (P.V_pre C n).ge

  have hxp : ∀ n : ℕ, x n ≫ P.p n = y n := by
    intro n
    have hxpV : (⊤ : (Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).Opens) ≤ (x n ≫ P.p n) ⁻¹ᵁ (P.V C n) :=
      fun z hz => hWV n (hxW n hz)
    apply Fib7.hom_ext_of_isAffineOpen (P.V_affine C n) hxpV (hVtop n)
    rw [← Scheme.Hom.appLE_comp_appLE (x n) (P.p n) (P.V C n) (C.W n) ⊤ (hWV n) (hxW n), hxapp n]
    ext s
    obtain ⟨b, rfl⟩ := hsurjY n s
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, P.chart_p C n b, hθ n, hΨA]
    apply (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).commRingCatIsoToRingEquiv.injective
    show (Scheme.ΓSpecIso _).hom.hom ((Scheme.ΓSpecIso _).inv.hom (Ideal.Quotient.mk _ (Φ b))) =
      (Scheme.ΓSpecIso _).hom.hom (((y n).appLE (P.V C n) ⊤ (hVtop n)).hom (P.chart C n (Ideal.Quotient.mk (IA n) b)))
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply, hΦ']
    rfl

  have hxt' : ∀ n : ℕ, tr n ≫ x (n + 1) = x n ≫ xt n := by
    intro n
    have h1 : (⊤ : (Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).Opens) ≤ (tr n ≫ x (n + 1)) ⁻¹ᵁ (C.W (n + 1)) := by
      rw [Scheme.Hom.comp_preimage, top_le_iff.mp (hxW (n + 1)), Scheme.Hom.preimage_top]
    have h2 : (⊤ : (Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).Opens) ≤ (x n ≫ xt n) ⁻¹ᵁ (C.W (n + 1)) := by
      rw [Scheme.Hom.comp_preimage, C.compat]; exact hxW n
    apply Fib7.hom_ext_of_isAffineOpen (C.affine (n + 1)) h1 h2
    rw [← Scheme.Hom.appLE_comp_appLE (tr n) (x (n + 1)) (C.W (n + 1)) ⊤ ⊤ (hxW (n + 1)) (by rw [Scheme.Hom.preimage_top]),
      ← Scheme.Hom.appLE_comp_appLE (x n) (xt n) (C.W (n + 1)) (C.W n) ⊤ (by rw [C.compat]) (hxW n),
      hxapp (n + 1), hxapp n]
    ext s
    obtain ⟨r, rfl⟩ := hsurjX (n + 1) s
    simp only [CommRingCat.comp_apply]
    rw [(RC C).lvl_compat n r, hθ (n + 1), hθ n]
    have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.factor (hle n)))
    have hnat' := congrArg (fun φ => φ.hom (Ideal.Quotient.mk _ (Ψ r))) hnat
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Ideal.Quotient.factor_mk] at hnat'
    rw [hnat']
    simp only [Fib7.appLE_top_top]
    rfl
  refine ⟨⟨x, hxp, hxt'⟩, ?_⟩

  intro z₁ z₂ hz₁ hz₂ hzt₁ hzt₂
  have landsW : ∀ (z : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)})) ⟶ X n),
      (∀ n : ℕ, z n ≫ P.p n = y n) →
      ∀ n : ℕ, (⊤ : (Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).Opens) ≤ (z n) ⁻¹ᵁ (C.W n) := by
    intro z hz n
    rw [← P.V_pre C n, ← Scheme.Hom.comp_preimage, hz n]; exact hVtop n
  letI algAR : Algebra ↥A R := Φ.toAlgebra

  have mkSg : ∀ (z : ∀ n : ℕ, Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)})) ⟶ X n)
      (hz : ∀ n : ℕ, z n ≫ P.p n = y n) (hzt : ∀ n : ℕ, tr n ≫ z (n + 1) = z n ≫ xt n),
      ∃ s : RW →ₐ[↥A] R, ∀ (n : ℕ) (r : RW), Ideal.Quotient.mk (Ideal.span {πR ^ (n + 1)}) (s r) =
        (((z n).appLE (C.W n) ⊤ (landsW z hz n)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).hom).hom
          ((RC C).lvl n (Ideal.Quotient.mk (J n) r)) := by
    intro z hz hzt
    let τ : ∀ n : ℕ, Γ(X n, C.W n) →+* R ⧸ Ideal.span {πR ^ (n + 1)} := fun n =>
      (((z n).appLE (C.W n) ⊤ (landsW z hz n)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).hom).hom
    let σ : ∀ n : ℕ, RW →+* R ⧸ I ^ (n + 1) := fun n =>
      (e n).toRingHom.comp ((τ n).comp (((RC C).lvl n).toRingHom.comp (Ideal.Quotient.mk (J n))))

    have hτ : ∀ (n : ℕ) (r : RW), Ideal.Quotient.factor (hle n) (τ (n + 1) ((RC C).lvl (n + 1) (Ideal.Quotient.mk (J (n + 1)) r))) =
        τ n ((RC C).lvl n (Ideal.Quotient.mk (J n) r)) := by
      intro n r
      have hV1 : (⊤ : (Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).Opens) ≤ (tr n ≫ z (n + 1)) ⁻¹ᵁ (C.W (n + 1)) := by
        rw [Scheme.Hom.comp_preimage, top_le_iff.mp (landsW z hz (n + 1)), Scheme.Hom.preimage_top]
      have hV2 : (⊤ : (Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).Opens) ≤ (z n ≫ xt n) ⁻¹ᵁ (C.W (n + 1)) := by
        rw [Scheme.Hom.comp_preimage, C.compat]; exact landsW z hz n
      have hcomp := Fib7.appLE_congr_hom (hzt n) (C.W (n + 1)) ⊤ hV1 hV2
      rw [← Scheme.Hom.appLE_comp_appLE (tr n) (z (n + 1)) (C.W (n + 1)) ⊤ ⊤ (landsW z hz (n + 1))
          (by rw [Scheme.Hom.preimage_top]),
        ← Scheme.Hom.appLE_comp_appLE (z n) (xt n) (C.W (n + 1)) (C.W n) ⊤ (by rw [C.compat]) (landsW z hz n)] at hcomp
      have h2 := congrArg (fun φ => (φ ≫ (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).hom).hom
        ((RC C).lvl (n + 1) (Ideal.Quotient.mk (J (n + 1)) r))) hcomp
      simp only [Category.assoc, CommRingCat.hom_comp, RingHom.comp_apply] at h2
      rw [(RC C).lvl_compat n r] at h2
      show Ideal.Quotient.factor (hle n) (((z (n + 1)).appLE (C.W (n + 1)) ⊤ (landsW z hz (n + 1)) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1 + 1)}))).hom).hom
            ((RC C).lvl (n + 1) (Ideal.Quotient.mk (J (n + 1)) r))) =
        ((z n).appLE (C.W n) ⊤ (landsW z hz n) ≫ (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).hom).hom
          ((RC C).lvl n (Ideal.Quotient.mk (J n) r))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, J] at h2 ⊢
      rw [← h2]
      have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.factor (hle n)))
      have hnat' := congrArg (fun φ => φ.hom ((z (n + 1)).appLE (C.W (n + 1)) ⊤ (landsW z hz (n + 1))
        ((RC C).lvl (n + 1) (Ideal.Quotient.mk _ r)))) hnat
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hnat'
      rw [← hnat']
      simp only [Fib7.appLE_top_top]
      rfl
    have hσ : ∀ {m : ℕ}, (Ideal.Quotient.factorPow I (ha.monotone m.le_succ)).comp (σ (m + 1)) = σ m := by
      intro m; ext r
      show Ideal.Quotient.factorPow I (ha.monotone m.le_succ) (e (m + 1) (τ (m + 1) ((RC C).lvl (m + 1) (Ideal.Quotient.mk (J (m + 1)) r)))) =
        e m (τ m ((RC C).lvl m (Ideal.Quotient.mk (J m) r)))
      rw [← hτ m r]
      obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (τ (m + 1) ((RC C).lvl (m + 1) (Ideal.Quotient.mk (J (m + 1)) r)))
      rw [← hw]
      simp only [e, Ideal.quotEquivOfEq_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factorPow]
    let Sg : RW →+* R := IsAdicComplete.StrictMono.liftRingHom I ha σ hσ
    have hSg : ∀ (n : ℕ) (r : RW), Ideal.Quotient.mk (I ^ (n + 1)) (Sg r) = σ n r := fun n r =>
      IsAdicComplete.StrictMono.mk_liftRingHom I ha σ hσ r
    have hSg' : ∀ (n : ℕ) (r : RW), Ideal.Quotient.mk (Ideal.span {πR ^ (n + 1)}) (Sg r) =
        τ n ((RC C).lvl n (Ideal.Quotient.mk (J n) r)) := by
      intro n r
      apply (e n).injective
      rw [show e n (Ideal.Quotient.mk _ (Sg r)) = Ideal.Quotient.mk (I ^ (n + 1)) (Sg r) from Ideal.quotEquivOfEq_mk _ _, hSg]
      rfl

    have hτA : ∀ (n : ℕ) (b : ↥A), τ n ((RC C).lvl n (Ideal.Quotient.mk (J n) (b : RW))) = ρ n (P.chart C n (Ideal.Quotient.mk (IA n) b)) := by
      intro n b
      have hV3 : (⊤ : (Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).Opens) ≤ (z n ≫ P.p n) ⁻¹ᵁ (P.V C n) := by
        rw [hz n]; exact hVtop n
      have hc := Fib7.appLE_congr_hom (hz n) (P.V C n) ⊤ hV3 (hVtop n)
      rw [← Scheme.Hom.appLE_comp_appLE (z n) (P.p n) (P.V C n) (C.W n) ⊤ (hWV n) (landsW z hz n)] at hc
      have hc2 := congrArg (fun φ => (φ ≫ (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).hom).hom
        (P.chart C n (Ideal.Quotient.mk (IA n) b))) hc
      simp only [Category.assoc, CommRingCat.hom_comp, RingHom.comp_apply] at hc2
      rw [P.chart_p C n b] at hc2
      show ((z n).appLE (C.W n) ⊤ (landsW z hz n) ≫ (Scheme.ΓSpecIso _).hom).hom ((RC C).lvl n (Ideal.Quotient.mk (J n) (b : RW))) =
        ((y n).appLE (P.V C n) ⊤ (hVtop n) ≫ (Scheme.ΓSpecIso _).hom).hom (P.chart C n (Ideal.Quotient.mk (IA n) b))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, J] at hc2 ⊢
      exact hc2
    have hSgA : Sg.comp (algebraMap ↥A RW) = Φ := by
      apply IsAdicComplete.StrictMono.eq_liftRingHom I ha f hf
      intro n; ext b
      show Ideal.Quotient.mk (I ^ (n + 1)) (Sg (b : RW)) = f n b
      rw [hSg]
      show e n (τ n ((RC C).lvl n (Ideal.Quotient.mk (J n) (b : RW)))) = e n (ρ n (P.chart C n (Ideal.Quotient.mk (IA n) b)))
      rw [hτA]
    refine ⟨{ toRingHom := Sg, commutes' := fun b => ?_ }, fun n r => hSg' n r⟩
    exact congrArg (fun φ : ↥A →+* R => φ b) hSgA
  obtain ⟨s₁, hs₁⟩ := mkSg z₁ hz₁ hzt₁
  obtain ⟨s₂, hs₂⟩ := mkSg z₂ hz₂ hzt₂
  obtain ⟨g, hg⟩ := AlgebraicGeometry.exists_smul_algHom_eq_of_isInvariant_of_isDomain ↥A RW G R s₁ s₂
  refine ⟨g⁻¹, fun n => ?_⟩
  have hgW : (⊤ : (Spec (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).Opens) ≤ (z₁ n ≫ (a n g⁻¹).hom) ⁻¹ᵁ (C.W n) := by
    rw [Scheme.Hom.comp_preimage, C.stable]; exact landsW z₁ hz₁ n
  apply Fib7.hom_ext_of_isAffineOpen (C.affine n) (landsW z₂ hz₂ n) hgW
  rw [← Scheme.Hom.appLE_comp_appLE (z₁ n) (a n g⁻¹).hom (C.W n) (C.W n) ⊤ (by rw [C.stable]) (landsW z₁ hz₁ n)]
  ext s
  obtain ⟨r, rfl⟩ := hsurjX n s
  rw [CommRingCat.comp_apply, (RC C).lvl_smul n g r]
  apply (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {πR ^ (n + 1)}))).commRingCatIsoToRingEquiv.injective
  show (((z₂ n).appLE (C.W n) ⊤ (landsW z₂ hz₂ n)) ≫ (Scheme.ΓSpecIso _).hom).hom ((RC C).lvl n (Ideal.Quotient.mk (J n) r)) =
    (((z₁ n).appLE (C.W n) ⊤ (landsW z₁ hz₁ n)) ≫ (Scheme.ΓSpecIso _).hom).hom ((RC C).lvl n (Ideal.Quotient.mk (J n) (g • r)))
  rw [← hs₂, ← hs₁, hg]

theorem ChartRing.eq_of_forall_mk_eq {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) (y y' : RC.R)
    (h : ∀ m : ℕ, Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 RC.R π ^ (m + 1)}) y =
      Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 RC.R π ^ (m + 1)}) y') : y = y' := by
  haveI := RC.complete
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {algebraMap 𝒪 RC.R π}) (R := RC.R)) (y - y') fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  rcases n with _ | n
  · rw [pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top
  · rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]; exact h n

theorem ChartRing.eq_of_forall_lvl_eq {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) (y y' : RC.R)
    (h : ∀ m : ℕ, RC.lvl m (Ideal.Quotient.mk _ y) = RC.lvl m (Ideal.Quotient.mk _ y')) : y = y' :=
  RC.eq_of_forall_mk_eq 𝒪 π X xb xt G a y y' fun m => (RC.lvl m).injective (h m)

noncomputable def GChain.resΓ {C C' : GChain X xt G a} (h : ∀ m : ℕ, C'.W m ≤ C.W m) (m : ℕ) :
    Γ(X m, C.W m) →+* Γ(X m, C'.W m) :=
  ((X m).presheaf.map (homOfLE (h m)).op).hom

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
theorem GChain.resΓ_apply {C C' : GChain X xt G a} (h : ∀ m : ℕ, C'.W m ≤ C.W m) (m : ℕ) (s : Γ(X m, C.W m)) :
    GChain.resΓ X xt G a h m s = (X m).presheaf.map (homOfLE (h m)).op s := rfl

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem GChain.appLE_resΓ {C C' : GChain X xt G a} (h : ∀ m : ℕ, C'.W m ≤ C.W m) {m m' : ℕ} (φ : X m' ⟶ X m)
    (e : C.W m' ≤ φ ⁻¹ᵁ C.W m) (e' : C'.W m' ≤ φ ⁻¹ᵁ C'.W m) (s : Γ(X m, C.W m)) :
    φ.appLE (C'.W m) (C'.W m') e' (GChain.resΓ X xt G a h m s) = GChain.resΓ X xt G a h m' (φ.appLE (C.W m) (C.W m') e s) := by
  simp only [GChain.resΓ_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem exists_chartRing_restrict (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C)
    (C C' : GChain X xt G a) (h : ∀ m : ℕ, C'.W m ≤ C.W m) :
    ∃ res : (RC C).R →ₐ[𝒪] (RC C').R,
      (∀ (g : G) (r : (RC C).R), res (g • r) = g • res r) ∧
      ∀ (m : ℕ) (r : (RC C).R),
        (RC C').lvl m (Ideal.Quotient.mk _ (res r)) =
          (X m).presheaf.map (homOfLE (h m)).op ((RC C).lvl m (Ideal.Quotient.mk _ r)) := by
  classical
  let R := (RC C).R
  let R' := (RC C').R
  haveI := (RC C').complete

  let ψ : ∀ m : ℕ, R →+* Γ(X m, C'.W m) := fun m =>
    (GChain.resΓ X xt G a h m).comp (((RC C).lvl m).toRingHom.comp (Ideal.Quotient.mk _))
  have hψ : ∀ (m : ℕ) (r : R), ψ m r = GChain.resΓ X xt G a h m ((RC C).lvl m (Ideal.Quotient.mk _ r)) := fun m r => rfl
  have hψt : ∀ (m : ℕ) (r : R), (xt m).appLE (C'.W (m + 1)) (C'.W m) (by rw [C'.compat]) (ψ (m + 1) r) = ψ m r := by
    intro m r
    rw [hψ, hψ, GChain.appLE_resΓ X xt G a h (xt m) (by rw [C.compat]) (by rw [C'.compat]), (RC C).lvl_compat]

  let I : Ideal R' := Ideal.span {algebraMap 𝒪 R' π}
  have hI : ∀ m : ℕ, I ^ (m + 1) = Ideal.span {algebraMap 𝒪 R' π ^ (m + 1)} := fun m => Ideal.span_singleton_pow _ _
  let e : ∀ m : ℕ, (R' ⧸ I ^ (m + 1)) ≃+* (R' ⧸ Ideal.span {algebraMap 𝒪 R' π ^ (m + 1)}) := fun m => Ideal.quotEquivOfEq (hI m)
  let f : ∀ m : ℕ, R →+* R' ⧸ I ^ (m + 1) := fun m => (e m).symm.toRingHom.comp (((RC C').lvl m).symm.toRingHom.comp (ψ m))
  have hf0 : ∀ (m : ℕ) (r : R), (RC C').lvl m (e m (f m r)) = ψ m r := by intro m r; simp [f]
  have ha : StrictMono (fun n : ℕ => n + 1) := fun _ _ hh => Nat.succ_lt_succ hh
  have hf : ∀ {m : ℕ}, (Ideal.Quotient.factorPow I (ha.monotone m.le_succ)).comp (f (m + 1)) = f m := by
    intro m
    ext r
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (f (m + 1) r)
    have h1 : ψ (m + 1) r = (RC C').lvl (m + 1) (Ideal.Quotient.mk _ y) := by
      rw [← hf0 (m + 1) r, ← hy, Ideal.quotEquivOfEq_mk]
    have h2 : ψ m r = (RC C').lvl m (Ideal.Quotient.mk _ y) := by
      rw [← hψt m r, h1, (RC C').lvl_compat]
    apply (e m).injective
    apply ((RC C').lvl m).injective
    rw [RingHom.comp_apply, ← hy, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, hf0, h2, Ideal.quotEquivOfEq_mk]
  let Φ : R →+* R' := IsAdicComplete.StrictMono.liftRingHom I ha f hf
  have key : ∀ (m : ℕ) (r : R), (RC C').lvl m (Ideal.Quotient.mk _ (Φ r)) = ψ m r := by
    intro m r
    have := IsAdicComplete.StrictMono.mk_liftRingHom I ha f hf (n := m) r
    rw [← hf0 m r, ← this, Ideal.quotEquivOfEq_mk]

  have hcomm : ∀ o : 𝒪, Φ (algebraMap 𝒪 R o) = algebraMap 𝒪 R' o := by
    intro o
    refine (RC C').eq_of_forall_lvl_eq 𝒪 π X xb xt G a _ _ fun m => ?_
    rw [key, hψ, (RC C).lvl_algebraMap, (RC C').lvl_algebraMap, GChain.resΓ_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map]

  have hsmul : ∀ (g : G) (r : R), Φ (g • r) = g • Φ r := by
    intro g r
    refine (RC C').eq_of_forall_lvl_eq 𝒪 π X xb xt G a _ _ fun m => ?_
    rw [key, hψ, ← (RC C).lvl_smul, ← (RC C').lvl_smul, key, hψ,
      GChain.appLE_resΓ X xt G a h (a m g⁻¹).hom (by rw [C.stable]) (by rw [C'.stable])]
  refine ⟨{ Φ with commutes' := hcomm }, hsmul, fun m r => ?_⟩
  exact key m r

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem chartRing_restrict_unique (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C)
    (C C' : GChain X xt G a) (h : ∀ m : ℕ, C'.W m ≤ C.W m) (res res' : (RC C).R →+* (RC C').R)
    (hres : ∀ (m : ℕ) (r : (RC C).R), (RC C').lvl m (Ideal.Quotient.mk _ (res r)) =
      (X m).presheaf.map (homOfLE (h m)).op ((RC C).lvl m (Ideal.Quotient.mk _ r)))
    (hres' : ∀ (m : ℕ) (r : (RC C).R), (RC C').lvl m (Ideal.Quotient.mk _ (res' r)) =
      (X m).presheaf.map (homOfLE (h m)).op ((RC C).lvl m (Ideal.Quotient.mk _ r))) :
    res = res' := by
  ext r
  exact (RC C').eq_of_forall_lvl_eq 𝒪 π X xb xt G a _ _ fun m => by rw [hres, hres']

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem exists_gchain_basicOpen (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C)
    (C : GChain X xt G a) (f : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C))) :
    ∃ Cf : GChain X xt G a, ∀ m : ℕ,
      Cf.W m = C.W m ⊓ (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R))) := by

  have hf : ∀ g : G, g • (f : (RC C).R) = f := f.2

  have hle : ∀ m : ℕ,
      (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R))) ≤ C.W m :=
    fun m => (X m).basicOpen_le _

  have key : ∀ (m : ℕ) (g' : G),
      C.W m ⊓ (a m g'⁻¹).hom ⁻¹ᵁ (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R))) =
        (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R))) := by
    intro m g'
    have e := congrArg (X m).basicOpen ((RC C).lvl_smul m g' (f : (RC C).R))
    rwa [Scheme.basicOpen_appLE, hf] at e

  have compat : ∀ m : ℕ,
      C.W m ⊓ (xt m) ⁻¹ᵁ (X (m + 1)).basicOpen ((RC C).lvl (m + 1) (Ideal.Quotient.mk _ (f : (RC C).R))) =
        (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R))) := by
    intro m
    have e := congrArg (X m).basicOpen ((RC C).lvl_compat m (f : (RC C).R))
    rwa [Scheme.basicOpen_appLE] at e
  refine ⟨{ W := fun m => C.W m ⊓ (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R)))
            affine := ?_, stable := ?_, compat := ?_ }, fun m => rfl⟩
  · intro m
    rw [inf_eq_right.mpr (hle m)]
    exact (C.affine m).basicOpen _
  · intro m g
    rw [inf_eq_right.mpr (hle m)]
    have h1 : (a m g).hom ⁻¹ᵁ (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R))) ≤ C.W m :=
      ((a m g).hom.preimage_mono (hle m)).trans (C.stable m g).le
    have h2 := key m g⁻¹
    rw [inv_inv] at h2
    exact (inf_eq_right.mpr h1).symm.trans h2
  · intro m
    rw [inf_eq_right.mpr (hle m), inf_eq_right.mpr (hle (m + 1))]
    have h1 : (xt m) ⁻¹ᵁ (X (m + 1)).basicOpen ((RC C).lvl (m + 1) (Ideal.Quotient.mk _ (f : (RC C).R))) ≤ C.W m :=
      ((xt m).preimage_mono (hle (m + 1))).trans (C.compat m).le
    exact (inf_eq_right.mpr h1).symm.trans (compat m)

section LevelLoc

variable (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C)
    (C Cf : GChain X xt G a) (f : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)))
    (hCf : ∀ m : ℕ, Cf.W m = C.W m ⊓ (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R))))
    (res : (RC C).R →ₐ[𝒪] (RC Cf).R)
    (hres_lvl : ∀ (m : ℕ) (r : (RC C).R), (RC Cf).lvl m (Ideal.Quotient.mk _ (res r)) =
      (X m).presheaf.map (homOfLE (by rw [hCf]; exact inf_le_left)).op ((RC C).lvl m (Ideal.Quotient.mk _ r)))

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
include hCf hres_lvl in

theorem level_localization (m : ℕ) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (RC Cf).R π ^ (m + 1)}) (res (f : (RC C).R))) ∧
    (∀ z : (RC Cf).R, ∃ (r : (RC C).R) (j : ℕ),
      res ((f : (RC C).R) ^ j) * z - res r ∈ Ideal.span {algebraMap 𝒪 (RC Cf).R π ^ (m + 1)}) ∧
    (∀ r : (RC C).R, res r ∈ Ideal.span {algebraMap 𝒪 (RC Cf).R π ^ (m + 1)} →
      ∃ j : ℕ, (f : (RC C).R) ^ j * r ∈ Ideal.span {algebraMap 𝒪 (RC C).R π ^ (m + 1)}) := by
  classical

  let s : Γ(X m, C.W m) := (RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R))
  have hle : Cf.W m ≤ C.W m := by rw [hCf]; exact inf_le_left
  have heq : Cf.W m = (X m).basicOpen s := by rw [hCf]; exact inf_eq_right.2 ((X m).basicOpen_le _)
  let ρ0 : Γ(X m, C.W m) →+* Γ(X m, Cf.W m) := ((X m).presheaf.map (homOfLE hle).op).hom
  letI alg : Algebra Γ(X m, C.W m) Γ(X m, Cf.W m) := ρ0.toAlgebra
  have H : IsLocalization.Away s Γ(X m, Cf.W m) := (C.affine m).isLocalization_of_eq_basicOpen s (homOfLE hle) heq
  have halg : ∀ y : Γ(X m, C.W m), algebraMap Γ(X m, C.W m) Γ(X m, Cf.W m) y = ρ0 y := fun _ => rfl
  let e1 := (RC C).lvl m
  let e2 := (RC Cf).lvl m
  have hcomm : ∀ r : (RC C).R, e2 (Ideal.Quotient.mk _ (res r)) = ρ0 (e1 (Ideal.Quotient.mk _ r)) := hres_lvl m
  have hpow : ∀ j : ℕ, ρ0 (s ^ j) = e2 (Ideal.Quotient.mk _ (res ((f : (RC C).R) ^ j))) := by
    intro j
    rw [hcomm]
    simp only [map_pow]
    rfl
  refine ⟨?_, ?_, ?_⟩
  ·
    have hu : IsUnit (algebraMap Γ(X m, C.W m) Γ(X m, Cf.W m) s) :=
      IsLocalization.map_units (M := Submonoid.powers s) Γ(X m, Cf.W m) ⟨s, Submonoid.mem_powers s⟩
    rw [halg, show s = s ^ 1 from (pow_one s).symm, hpow] at hu
    rw [pow_one] at hu
    exact (MulEquiv.isUnit_map e2).1 hu
  ·
    intro z
    obtain ⟨⟨y, c⟩, hyc⟩ := IsLocalization.surj (Submonoid.powers s) (e2 (Ideal.Quotient.mk _ z))
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
    obtain ⟨r, hr⟩ := (e1.surjective.comp Ideal.Quotient.mk_surjective) y
    refine ⟨r, j, ?_⟩
    rw [← Ideal.Quotient.eq, ← e2.injective.eq_iff]
    simp only [map_mul]
    rw [hcomm r, ← hpow, mul_comm]
    dsimp only at hyc
    simp only [halg] at hyc
    rw [← hj] at hyc
    rw [hyc, ← hr]
    rfl
  ·
    intro r hr
    have h0 : algebraMap Γ(X m, C.W m) Γ(X m, Cf.W m) (e1 (Ideal.Quotient.mk _ r)) =
        algebraMap Γ(X m, C.W m) Γ(X m, Cf.W m) 0 := by
      rw [halg, halg, map_zero, ← hcomm, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers s) h0
    obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).1 c.2
    refine ⟨j, ?_⟩
    rw [mul_zero, ← hj] at hc

    rw [← Ideal.Quotient.eq_zero_iff_mem, ← e1.injective.eq_iff]
    simp only [map_zero, map_mul, map_pow]
    exact hc

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
include hCf hres_lvl in
theorem level_unit (m : ℕ) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (RC Cf).R π ^ (m + 1)}) (res (f : (RC C).R))) :=
  (level_localization 𝒪 π X xb xt G a RC C Cf f hCf res hres_lvl m).1

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
include hCf hres_lvl in
theorem level_surj (m : ℕ) (z : (RC Cf).R) :
    ∃ (r : (RC C).R) (j : ℕ), res ((f : (RC C).R) ^ j) * z - res r ∈ Ideal.span {algebraMap 𝒪 (RC Cf).R π ^ (m + 1)} :=
  (level_localization 𝒪 π X xb xt G a RC C Cf f hCf res hres_lvl m).2.1 z

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
include hCf hres_lvl in
theorem level_ker (m : ℕ) (r : (RC C).R)
    (hr : res r ∈ Ideal.span {algebraMap 𝒪 (RC Cf).R π ^ (m + 1)}) :
    ∃ j : ℕ, (f : (RC C).R) ^ j * r ∈ Ideal.span {algebraMap 𝒪 (RC C).R π ^ (m + 1)} :=
  (level_localization 𝒪 π X xb xt G a RC C Cf f hCf res hres_lvl m).2.2 r hr

end LevelLoc
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12"

include hdvr hπ hcomplete in
omit hcart hproper hflat haff ha_over ha_xt hcov in

theorem isLocalizationAway_invariants_basicOpen (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C)
    (C Cf : GChain X xt G a) (f : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)))
    (hCf : ∀ m : ℕ, Cf.W m = C.W m ⊓ (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R))))
    (res : (RC C).R →ₐ[𝒪] (RC Cf).R) (hres_smul : ∀ (g : G) (r : (RC C).R), res (g • r) = g • res r)
    (hres_lvl : ∀ (m : ℕ) (r : (RC C).R), (RC Cf).lvl m (Ideal.Quotient.mk _ (res r)) =
      (X m).presheaf.map (homOfLE (by rw [hCf]; exact inf_le_left)).op ((RC C).lvl m (Ideal.Quotient.mk _ r)))
    (n : ℕ)
    (resA : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)) →+* ↥(ChartRing.A 𝒪 π X xb xt G a (RC Cf)))
    (hresA : ∀ x, (resA x : (RC Cf).R) = res (x : (RC C).R))
    (q : (↥(ChartRing.A 𝒪 π X xb xt G a (RC C)) ⧸ Ideal.span {algebraMap 𝒪 ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)) π ^ (n + 1)}) →+*
      (↥(ChartRing.A 𝒪 π X xb xt G a (RC Cf)) ⧸ Ideal.span {algebraMap 𝒪 ↥(ChartRing.A 𝒪 π X xb xt G a (RC Cf)) π ^ (n + 1)}))
    (hq : ∀ x, q (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (resA x)) :
    letI := q.toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk _ f :
      ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)) ⧸ Ideal.span {algebraMap 𝒪 ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)) π ^ (n + 1)})
      (↥(ChartRing.A 𝒪 π X xb xt G a (RC Cf)) ⧸ Ideal.span {algebraMap 𝒪 ↥(ChartRing.A 𝒪 π X xb xt G a (RC Cf)) π ^ (n + 1)}) := by

  obtain ⟨hN, hfin⟩ := isNoetherianRing_and_finite_fixedPoints 𝒪 hdvr π hπ hcomplete (RC C).R (RC C).complete (RC C).torsionFree
    (RC C).finiteType G
  haveI := hN
  haveI := hfin
  exact G2.isLocalizationAway_fixedPoints_quotient 𝒪 π G (RC C).R (RC Cf).R (RC C).torsionFree (RC Cf).torsionFree (RC Cf).complete
    res hres_smul f (level_unit 𝒪 π X xb xt G a RC C Cf f hCf res hres_lvl) (level_surj 𝒪 π X xb xt G a RC C Cf f hCf res hres_lvl)
    (level_ker 𝒪 π X xb xt G a RC C Cf f hCf res hres_lvl) n resA hresA q hq

omit hdvr hπ hcomplete hcart hproper in
theorem mem_basicOpen_prod {Z : Scheme.{0}} {U : Z.Opens} {ι : Type} [DecidableEq ι] (s : Finset ι) (t : ι → Γ(Z, U))
    (z : Z) (hz : z ∈ U) (h : ∀ i ∈ s, z ∈ Z.basicOpen (t i)) : z ∈ Z.basicOpen (∏ i ∈ s, t i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Scheme.basicOpen_one]; exact hz
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Scheme.basicOpen_mul]
    exact ⟨h i (Finset.mem_insert_self i s), ih fun j hj => h j (Finset.mem_insert_of_mem hj)⟩

omit hdvr hπ hcomplete hcart hproper in
theorem basicOpen_prod_le {Z : Scheme.{0}} {U : Z.Opens} {ι : Type} [DecidableEq ι] (s : Finset ι) (t : ι → Γ(Z, U))
    (i : ι) (hi : i ∈ s) : Z.basicOpen (∏ i ∈ s, t i) ≤ Z.basicOpen (t i) := by
  rw [← Finset.prod_erase_mul s t hi, Scheme.basicOpen_mul]
  exact inf_le_right

include hcart hproper in
omit hdvr hπ hcomplete hflat haff ha_over ha_xt hcov in

theorem exists_invariant_basicOpen_le (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C)
    (C C' : GChain X xt G a) (h : ∀ m : ℕ, C'.W m ≤ C.W m) (x : X 0) (hx : x ∈ C'.W 0) :
    ∃ f : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)),
      x ∈ (X 0).basicOpen ((RC C).lvl 0 (Ideal.Quotient.mk _ (f : (RC C).R))) ∧
      ∀ m : ℕ, C.W m ⊓ (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R))) ≤ C'.W m := by
  classical
  cases nonempty_fintype G
  have hW : IsAffineOpen (C.W 0) := C.affine 0
  have horbC' : ∀ g : G, (a 0 g).hom.base x ∈ C'.W 0 := fun g => by
    show x ∈ (a 0 g).hom ⁻¹ᵁ C'.W 0
    rw [C'.stable]
    exact hx
  have horb : ∀ g : G, (a 0 g).hom.base x ∈ C.W 0 := fun g => h 0 (horbC' g)

  let q : G → ↥(Spec Γ(X 0, C.W 0)) := fun g => hW.primeIdealOf ⟨(a 0 g).hom.base x, horb g⟩
  have hq : ∀ g : G, hW.fromSpec (q g) = (a 0 g).hom.base x := fun g => hW.fromSpec_primeIdealOf _

  let Z : Set ↥(Spec Γ(X 0, C.W 0)) := ((hW.fromSpec ⁻¹ᵁ (C'.W 0) : (Spec Γ(X 0, C.W 0)).Opens) : Set ↥(Spec Γ(X 0, C.W 0)))ᶜ
  have hZ : IsClosed Z := isClosed_compl_iff.2 (hW.fromSpec ⁻¹ᵁ (C'.W 0)).2
  let I : Ideal Γ(X 0, C.W 0) := PrimeSpectrum.vanishingIdeal Z
  have hqZ : ∀ g : G, q g ∉ Z := fun g => by
    simp only [Z, Set.mem_compl_iff, not_not]
    show hW.fromSpec (q g) ∈ C'.W 0
    rw [hq]
    exact horbC' g

  have havoid : ∃ s ∈ I, ∀ g : G, s ∉ (q g).asIdeal := by
    by_contra hcon
    push_neg at hcon
    have hsub : SetLike.coe I ⊆ ⋃ g ∈ (↑(Finset.univ : Finset G) : Set G), SetLike.coe (q g).asIdeal := by
      intro s hs
      obtain ⟨g, hg⟩ := hcon s hs
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ g)) hg
    obtain ⟨g, -, hle⟩ := (Ideal.subset_union_prime (1 : G) (1 : G) (fun g _ _ _ => (q g).isPrime)).1 hsub
    apply hqZ g
    have hmem : q g ∈ PrimeSpectrum.zeroLocus (SetLike.coe (PrimeSpectrum.vanishingIdeal Z)) :=
      (PrimeSpectrum.mem_zeroLocus _ _).2 hle
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure] at hmem
    exact hZ.closure_subset hmem
  obtain ⟨s, hsI, hsq⟩ := havoid

  have hDs : (X 0).basicOpen s ≤ C'.W 0 := by
    intro y hy
    have hyW : y ∈ C.W 0 := (X 0).basicOpen_le s hy
    have hy' : y ∈ Set.range hW.fromSpec := by rw [IsAffineOpen.range_fromSpec]; exact hyW
    obtain ⟨p, rfl⟩ := hy'
    have hp : p ∈ hW.fromSpec ⁻¹ᵁ (X 0).basicOpen s := hy
    rw [IsAffineOpen.fromSpec_preimage_basicOpen] at hp
    by_contra hp'
    exact ((PrimeSpectrum.mem_basicOpen _ _).1 hp) ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hsI p hp')
  have horbD : ∀ g : G, (a 0 g).hom.base x ∈ (X 0).basicOpen s := fun g => by
    rw [← hq]
    show q g ∈ hW.fromSpec ⁻¹ᵁ (X 0).basicOpen s
    rw [IsAffineOpen.fromSpec_preimage_basicOpen]
    exact (PrimeSpectrum.mem_basicOpen _ _).2 (hsq g)

  let ρ : (RC C).R →+* Γ(X 0, C.W 0) := ((RC C).lvl 0).toRingHom.comp (Ideal.Quotient.mk _)
  obtain ⟨r, hr⟩ : ∃ r, ρ r = s := (((RC C).lvl 0).surjective.comp Ideal.Quotient.mk_surjective) s
  let f : (RC C).R := ∏ g : G, g • r
  have hf : ∀ g' : G, g' • f = f := by
    intro g'
    have : (MulSemiringAction.toRingHom G (RC C).R g') f = f := by
      simp only [f, map_prod, MulSemiringAction.toRingHom_apply, smul_smul]
      exact Fintype.prod_equiv (Equiv.mulLeft g') _ _ (fun g => rfl)
    exact this
  have hρf : ρ f = ∏ g : G, (a 0 g⁻¹).hom.appLE (C.W 0) (C.W 0) (by rw [C.stable]) s := by
    simp only [f, map_prod]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [← hr]
    exact ((RC C).lvl_smul 0 g r).symm

  have hxD : x ∈ (X 0).basicOpen (ρ f) := by
    rw [hρf]
    apply mem_basicOpen_prod _ _ x (h 0 hx)
    intro g _
    rw [Scheme.basicOpen_appLE]
    exact ⟨h 0 hx, horbD g⁻¹⟩
  have hD0 : (X 0).basicOpen (ρ f) ≤ C'.W 0 := by
    rw [hρf]
    refine (basicOpen_prod_le _ _ (1 : G) (Finset.mem_univ _)).trans ?_
    rw [Scheme.basicOpen_appLE]
    exact inf_le_right.trans (((a 0 1⁻¹).hom.preimage_mono hDs).trans (C'.stable 0 1⁻¹).le)

  have hDm : ∀ m : ℕ, (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ f)) ≤ C'.W m := by
    intro m
    induction m with
    | zero => exact hD0
    | succ m ih =>
      intro y hy
      obtain ⟨y', rfl⟩ := (isHomeomorph_xt 𝒪 π X xb xt hcart m).surjective y
      have e := Scheme.basicOpen_appLE (xt m) (C.W m) (C.W (m + 1)) (by rw [C.compat])
        ((RC C).lvl (m + 1) (Ideal.Quotient.mk _ f))
      rw [(RC C).lvl_compat] at e
      have hy'W : y' ∈ C.W m := by
        have : y' ∈ (xt m) ⁻¹ᵁ C.W (m + 1) := (X (m + 1)).basicOpen_le _ hy
        rwa [C.compat] at this
      have hmem : y' ∈ (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ f)) := by
        rw [e]
        exact ⟨hy'W, hy⟩
      have : y' ∈ C'.W m := ih hmem
      rw [← C'.compat] at this
      exact this
  exact ⟨⟨f, hf⟩, hxD, fun m => inf_le_right.trans (hDm m)⟩

include hcart hproper in
omit hdvr hπ hcomplete hflat haff ha_over ha_xt hcov in

theorem exists_invariant_basicOpen_le_level (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C)
    (C C' : GChain X xt G a) (h : ∀ m : ℕ, C'.W m ≤ C.W m) (m : ℕ) (x : X m) (hx : x ∈ C'.W m) :
    ∃ f : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)),
      x ∈ (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R))) ∧
      ∀ k : ℕ, C.W k ⊓ (X k).basicOpen ((RC C).lvl k (Ideal.Quotient.mk _ (f : (RC C).R))) ≤ C'.W k := by
  induction m with
  | zero => exact exists_invariant_basicOpen_le 𝒪 π X xb xt hcart hproper G a RC C C' h x hx
  | succ m ih =>
    obtain ⟨y, rfl⟩ := (isHomeomorph_xt 𝒪 π X xb xt hcart m).surjective x
    have hy : y ∈ C'.W m := by
      rw [← C'.compat m]
      exact hx
    obtain ⟨f, hyf, hf⟩ := ih y hy
    refine ⟨f, ?_, hf⟩

    have e := Scheme.basicOpen_appLE (xt m) (C.W m) (C.W (m + 1)) (by rw [C.compat])
      ((RC C).lvl (m + 1) (Ideal.Quotient.mk _ (f : (RC C).R)))
    rw [(RC C).lvl_compat] at e
    rw [e] at hyf
    exact hyf.2

scoped instance GChain.instLE : LE (GChain X xt G a) := ⟨fun C' C => ∀ m : ℕ, C'.W m ≤ C.W m⟩

p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12 P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12.GChain"
scoped instance GChain.instPreorder : Preorder (GChain X xt G a) where
  le := fun C' C => ∀ m : ℕ, C'.W m ≤ C.W m
  le_refl := fun C m => le_rfl
  le_trans := fun C₁ C₂ C₃ h₁ h₂ m => (h₁ m).trans (h₂ m)

p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12 P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12.GChain"
omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
theorem GChain.le_def {C' C : GChain X xt G a} : C' ≤ C ↔ ∀ m : ℕ, C'.W m ≤ C.W m := Iff.rfl

noncomputable def chartRes (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) {C' C : GChain X xt G a} (h : C' ≤ C) :
    (RC C).R →ₐ[𝒪] (RC C').R :=
  (exists_chartRing_restrict 𝒪 π X xb xt G a RC C C' h).choose

theorem chartRes_smul (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) {C' C : GChain X xt G a} (h : C' ≤ C)
    (g : G) (r : (RC C).R) : chartRes 𝒪 π X xb xt G a RC h (g • r) = g • chartRes 𝒪 π X xb xt G a RC h r :=
  (exists_chartRing_restrict 𝒪 π X xb xt G a RC C C' h).choose_spec.1 g r

theorem lvl_chartRes (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) {C' C : GChain X xt G a} (h : C' ≤ C)
    (m : ℕ) (r : (RC C).R) :
    (RC C').lvl m (Ideal.Quotient.mk _ (chartRes 𝒪 π X xb xt G a RC h r)) =
      (X m).presheaf.map (homOfLE (h m)).op ((RC C).lvl m (Ideal.Quotient.mk _ r)) :=
  (exists_chartRing_restrict 𝒪 π X xb xt G a RC C C' h).choose_spec.2 m r

theorem chartRes_refl (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (C : GChain X xt G a) (r : (RC C).R) :
    chartRes 𝒪 π X xb xt G a RC (le_refl C) r = r := by
  refine (RC C).eq_of_forall_lvl_eq 𝒪 π X xb xt G a _ _ fun m => ?_
  rw [lvl_chartRes]
  have : (homOfLE (le_refl (C.W m))).op = 𝟙 _ := rfl
  rw [this, (X m).presheaf.map_id]
  rfl

theorem chartRes_trans (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) {C₁ C₂ C₃ : GChain X xt G a}
    (h₁ : C₁ ≤ C₂) (h₂ : C₂ ≤ C₃) (r : (RC C₃).R) :
    chartRes 𝒪 π X xb xt G a RC (h₁.trans h₂) r = chartRes 𝒪 π X xb xt G a RC h₁ (chartRes 𝒪 π X xb xt G a RC h₂ r) := by
  refine (RC C₁).eq_of_forall_lvl_eq 𝒪 π X xb xt G a _ _ fun m => ?_
  rw [lvl_chartRes, lvl_chartRes, lvl_chartRes, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

abbrev ChartRing.IA {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    Ideal ↥(FixedPoints.subalgebra 𝒪 RC.R G) :=
  Ideal.span {algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 RC.R G) π ^ (n + 1)}

noncomputable def chartResA (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) {C' C : GChain X xt G a} (h : C' ≤ C) :
    ↥(FixedPoints.subalgebra 𝒪 (RC C).R G) →ₐ[𝒪] ↥(FixedPoints.subalgebra 𝒪 (RC C').R G) :=
  ((chartRes 𝒪 π X xb xt G a RC h).comp (FixedPoints.subalgebra 𝒪 (RC C).R G).val).codRestrict
    (FixedPoints.subalgebra 𝒪 (RC C').R G) (fun x g => by
      show g • chartRes 𝒪 π X xb xt G a RC h (x : (RC C).R) = chartRes 𝒪 π X xb xt G a RC h (x : (RC C).R)
      rw [← chartRes_smul, x.2 g])

theorem chartResA_coe (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) {C' C : GChain X xt G a} (h : C' ≤ C)
    (x : ↥(FixedPoints.subalgebra 𝒪 (RC C).R G)) :
    (chartResA 𝒪 π X xb xt G a RC h x : (RC C').R) = chartRes 𝒪 π X xb xt G a RC h (x : (RC C).R) := rfl

noncomputable def chartResBar (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) {C' C : GChain X xt G a} (h : C' ≤ C)
    (n : ℕ) : (↥(FixedPoints.subalgebra 𝒪 (RC C).R G) ⧸ ChartRing.IA 𝒪 π X xb xt G a (RC C) n) →+*
      (↥(FixedPoints.subalgebra 𝒪 (RC C').R G) ⧸ ChartRing.IA 𝒪 π X xb xt G a (RC C') n) :=
  Ideal.quotientMap _ (chartResA 𝒪 π X xb xt G a RC h).toRingHom (by
    rw [ChartRing.IA, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    have : (chartResA 𝒪 π X xb xt G a RC h).toRingHom (algebraMap 𝒪 _ π ^ (n + 1)) = algebraMap 𝒪 _ π ^ (n + 1) := by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, AlgHom.commutes]
    rw [this]
    exact Ideal.subset_span rfl)

theorem chartResBar_mk (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) {C' C : GChain X xt G a} (h : C' ≤ C)
    (n : ℕ) (x : ↥(FixedPoints.subalgebra 𝒪 (RC C).R G)) :
    chartResBar 𝒪 π X xb xt G a RC h n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (chartResA 𝒪 π X xb xt G a RC h x) := rfl

theorem chartResBar_refl (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (C : GChain X xt G a) (n : ℕ) :
    chartResBar 𝒪 π X xb xt G a RC (le_refl C) n = RingHom.id _ := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
  simp only [RingHom.comp_apply, chartResBar_mk, RingHom.id_apply]
  congr 1
  exact Subtype.ext (chartRes_refl 𝒪 π X xb xt G a RC C x)

theorem chartResBar_trans (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) {C₁ C₂ C₃ : GChain X xt G a}
    (h₁ : C₁ ≤ C₂) (h₂ : C₂ ≤ C₃) (n : ℕ) :
    chartResBar 𝒪 π X xb xt G a RC (h₁.trans h₂) n =
      (chartResBar 𝒪 π X xb xt G a RC h₁ n).comp (chartResBar 𝒪 π X xb xt G a RC h₂ n) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
  simp only [RingHom.comp_apply, chartResBar_mk]
  congr 1
  exact Subtype.ext (chartRes_trans 𝒪 π X xb xt G a RC h₁ h₂ x)

noncomputable def glueFunctor (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    GChain X xt G a ⥤ Scheme.{0} where
  obj C := Spec (CommRingCat.of (↥(FixedPoints.subalgebra 𝒪 (RC C).R G) ⧸ ChartRing.IA 𝒪 π X xb xt G a (RC C) n))
  map {C' C} f := Spec.map (CommRingCat.ofHom (chartResBar 𝒪 π X xb xt G a RC f.le n))
  map_id C := by
    show Spec.map _ = _
    rw [show (𝟙 C : C ⟶ C).le = le_refl C from rfl, chartResBar_refl]
    exact Spec.map_id _
  map_comp {C₁ C₂ C₃} f g := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← chartResBar_trans]

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem ChartRing.span_pow_le_comap {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    Ideal.span {algebraMap 𝒪 (↥(ChartRing.A 𝒪 π X xb xt G a RC)) π ^ (n + 1)} ≤
      (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}).comap
        (algebraMap (↥(ChartRing.A 𝒪 π X xb xt G a RC)) RC.R) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow,
    ← IsScalarTower.algebraMap_apply 𝒪 (↥(ChartRing.A 𝒪 π X xb xt G a RC)) RC.R π]
  exact Ideal.subset_span rfl

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem ChartRing.smul_mem_span_pow {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) (n : ℕ)
    (g : G) (r : RC.R) (hr : r ∈ Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}) :
    g • r ∈ Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)} := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  have hgπ : g • (algebraMap 𝒪 RC.R π ^ (n + 1)) = algebraMap 𝒪 RC.R π ^ (n + 1) := by
    rw [smul_pow', Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]
  rw [smul_mul', hgπ]
  exact Ideal.mem_span_singleton'.2 ⟨g • c, rfl⟩

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem ChartRing.span_pow_le_comap_toRingHom {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C)
    (n : ℕ) (g : G) :
    Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)} ≤
      (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}).comap (MulSemiringAction.toRingHom G RC.R g) :=
  fun r hr => Ideal.mem_comap.mpr (by
    rw [MulSemiringAction.toRingHom_apply]
    exact ChartRing.smul_mem_span_pow 𝒪 π X xb xt G a RC n g r hr)

include hdvr hπ hcomplete in
omit hcart hproper hflat haff ha_over ha_xt hcov in

theorem ChartRing.quotientMap_algebraMap_injective {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C)
    (n : ℕ)
    (h : Ideal.span {algebraMap 𝒪 (↥(ChartRing.A 𝒪 π X xb xt G a RC)) π ^ (n + 1)} ≤
      (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}).comap
        (algebraMap (↥(ChartRing.A 𝒪 π X xb xt G a RC)) RC.R)) :
    Function.Injective
      (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)})
        (algebraMap (↥(ChartRing.A 𝒪 π X xb xt G a RC)) RC.R) h) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro z hz
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
  rw [Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨-, -, -, htors⟩ :=
    AlgebraicGeometry.AdmissibleAlgebra.fixedPoints_isAdicComplete_and_finite_and_finiteType 𝒪 hdvr π hπ
      hcomplete RC.R RC.complete RC.torsionFree RC.finiteType G
  exact htors (n + 1) x hz

include hdvr hπ hcomplete in
omit hcart hproper hflat haff ha_over ha_xt hcov in

theorem ChartRing.quotientMap_algebraMap_finite {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C)
    (n : ℕ)
    (h : Ideal.span {algebraMap 𝒪 (↥(ChartRing.A 𝒪 π X xb xt G a RC)) π ^ (n + 1)} ≤
      (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}).comap
        (algebraMap (↥(ChartRing.A 𝒪 π X xb xt G a RC)) RC.R)) :
    (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)})
        (algebraMap (↥(ChartRing.A 𝒪 π X xb xt G a RC)) RC.R) h).Finite := by
  obtain ⟨-, hfin, -, -⟩ :=
    AlgebraicGeometry.AdmissibleAlgebra.fixedPoints_isAdicComplete_and_finite_and_finiteType 𝒪 hdvr π hπ
      hcomplete RC.R RC.complete RC.torsionFree RC.finiteType G
  apply RingHom.Finite.of_comp_finite
    (f := Ideal.Quotient.mk (Ideal.span {algebraMap 𝒪 (↥(ChartRing.A 𝒪 π X xb xt G a RC)) π ^ (n + 1)}))
  rw [Ideal.quotientMap_comp_mk]
  refine RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective) ?_
  rw [RingHom.finite_algebraMap]
  exact hfin

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem ChartRing.quotientMap_toRingHom_mk {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C)
    (n : ℕ) (g : G)
    (hg : Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)} ≤
      (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}).comap (MulSemiringAction.toRingHom G RC.R g))
    (r : RC.R) :
    Ideal.quotientMap (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}) (MulSemiringAction.toRingHom G RC.R g) hg
        (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (g • r) := by
  rw [Ideal.quotientMap_mk, MulSemiringAction.toRingHom_apply]

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem ChartRing.quotientMap_toRingHom_quotientMap_algebraMap {C : GChain X xt G a}
    (RC : ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (g : G)
    (hg : Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)} ≤
      (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}).comap (MulSemiringAction.toRingHom G RC.R g))
    (h : Ideal.span {algebraMap 𝒪 (↥(ChartRing.A 𝒪 π X xb xt G a RC)) π ^ (n + 1)} ≤
      (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}).comap
        (algebraMap (↥(ChartRing.A 𝒪 π X xb xt G a RC)) RC.R))
    (z : ↥(ChartRing.A 𝒪 π X xb xt G a RC) ⧸
      Ideal.span {algebraMap 𝒪 (↥(ChartRing.A 𝒪 π X xb xt G a RC)) π ^ (n + 1)}) :
    Ideal.quotientMap (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}) (MulSemiringAction.toRingHom G RC.R g) hg
        (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)})
          (algebraMap (↥(ChartRing.A 𝒪 π X xb xt G a RC)) RC.R) h z) =
      Ideal.quotientMap (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)})
        (algebraMap (↥(ChartRing.A 𝒪 π X xb xt G a RC)) RC.R) h z := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Ideal.quotientMap_mk, ChartRing.quotientMap_toRingHom_mk 𝒪 π X xb xt G a RC n g hg]
  congr 1
  exact x.2 g

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem resLE_congr_hom' {X' Y' : Scheme.{0}} {f f' : X' ⟶ Y'} (h : f = f') (U : Y'.Opens) (V : X'.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ f' ⁻¹ᵁ U) : f.resLE U V e = f'.resLE U V e' := by
  subst h; rfl

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

noncomputable def ChartRing.isoSpec {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    (C.W n).toScheme ≅ Spec (CommRingCat.of (RC.R ⧸ Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)})) :=
  (C.affine n).isoSpec ≪≫ Scheme.Spec.mapIso (RC.lvl n).toCommRingCatIso.op

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
theorem ChartRing.isoSpec_hom {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    (ChartRing.isoSpec 𝒪 π X xb xt G a RC n).hom =
      (C.W n).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (RC.lvl n).toRingHom) := rfl

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem ChartRing.isoSpec_hom' {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    (ChartRing.isoSpec 𝒪 π X xb xt G a RC n).hom =
      (C.affine n).isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (RC.lvl n).toRingHom) := rfl

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
@[scoped simp]
theorem ChartRing.isoSpec_hom_comp_SpecMap_symm {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    (ChartRing.isoSpec 𝒪 π X xb xt G a RC n).hom ≫ Spec.map (CommRingCat.ofHom (RC.lvl n).symm.toRingHom) =
      (C.affine n).isoSpec.hom := by
  rw [ChartRing.isoSpec_hom', Category.assoc, ← Spec.map_comp]
  have : CommRingCat.ofHom (RC.lvl n).symm.toRingHom ≫ CommRingCat.ofHom (RC.lvl n).toRingHom = 𝟙 _ := by
    ext x; simp
  rw [this, Spec.map_id]
  exact Category.comp_id _

p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12 P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12.GChain P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12.ChartRing"
omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
@[scoped simp]
theorem ChartRing.isoSpec_inv {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    (ChartRing.isoSpec 𝒪 π X xb xt G a RC n).inv =
      Spec.map (CommRingCat.ofHom (RC.lvl n).symm.toRingHom) ≫ (C.affine n).isoSpec.inv := rfl

p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12 P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12.GChain P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12.ChartRing"
omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem ChartRing.resLE_comp_isoSpec_hom {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C)
    {m m' : ℕ} (f : X m ⟶ X m') (e : C.W m ≤ f ⁻¹ᵁ C.W m')
    (φ : (RC.R ⧸ Ideal.span {algebraMap 𝒪 RC.R π ^ (m' + 1)}) →+* (RC.R ⧸ Ideal.span {algebraMap 𝒪 RC.R π ^ (m + 1)}))
    (hφ : ∀ r : RC.R, f.appLE (C.W m') (C.W m) e (RC.lvl m' (Ideal.Quotient.mk _ r)) = RC.lvl m (φ (Ideal.Quotient.mk _ r))) :
    f.resLE (C.W m') (C.W m) e ≫ (ChartRing.isoSpec 𝒪 π X xb xt G a RC m').hom =
      (ChartRing.isoSpec 𝒪 π X xb xt G a RC m).hom ≫ Spec.map (CommRingCat.ofHom φ) := by
  have hring : CommRingCat.ofHom (RC.lvl m').toRingHom ≫ f.appLE (C.W m') (C.W m) e =
      CommRingCat.ofHom φ ≫ CommRingCat.ofHom (RC.lvl m).toRingHom := by
    ext r
    simpa using hφ r
  rw [ChartRing.isoSpec_hom, ChartRing.isoSpec_hom, ← Category.assoc,
    ← Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, hring]

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem ChartRing.resLE_xt_comp_isoSpec_hom {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    (xt n).resLE (C.W (n + 1)) (C.W n) (by rw [C.compat]) ≫ (ChartRing.isoSpec 𝒪 π X xb xt G a RC (n + 1)).hom =
      (ChartRing.isoSpec 𝒪 π X xb xt G a RC n).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 RC.R π) (Nat.le_succ (n + 1)))))) := by
  refine ChartRing.resLE_comp_isoSpec_hom 𝒪 π X xb xt G a RC (xt n) _ _ fun r => ?_
  rw [Ideal.Quotient.factor_mk]
  exact RC.lvl_compat n r

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem ChartRing.resLE_smul_inv_comp_isoSpec_hom {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C)
    (n : ℕ) (g : G)
    (hg : Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)} ≤
      (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}).comap (MulSemiringAction.toRingHom G RC.R g)) :
    (a n g⁻¹).hom.resLE (C.W n) (C.W n) (by rw [C.stable]) ≫ (ChartRing.isoSpec 𝒪 π X xb xt G a RC n).hom =
      (ChartRing.isoSpec 𝒪 π X xb xt G a RC n).hom ≫
        Spec.map (CommRingCat.ofHom
          (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}) (MulSemiringAction.toRingHom G RC.R g) hg)) := by
  refine ChartRing.resLE_comp_isoSpec_hom 𝒪 π X xb xt G a RC (a n g⁻¹).hom _ _ fun r => ?_
  rw [Ideal.quotientMap_mk, MulSemiringAction.toRingHom_apply]
  exact RC.lvl_smul n g r

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem ChartRing.resLE_smul_comp_isoSpec_hom {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C)
    (n : ℕ) (g : G)
    (hg : Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)} ≤
      (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}).comap (MulSemiringAction.toRingHom G RC.R g⁻¹)) :
    (a n g).hom.resLE (C.W n) (C.W n) (by rw [C.stable]) ≫ (ChartRing.isoSpec 𝒪 π X xb xt G a RC n).hom =
      (ChartRing.isoSpec 𝒪 π X xb xt G a RC n).hom ≫
        Spec.map (CommRingCat.ofHom
          (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}) (MulSemiringAction.toRingHom G RC.R g⁻¹) hg)) := by
  rw [resLE_congr_hom' (show (a n g).hom = (a n (g⁻¹)⁻¹).hom by rw [inv_inv]) (C.W n) (C.W n) _ (by rw [C.stable])]
  exact ChartRing.resLE_smul_inv_comp_isoSpec_hom 𝒪 π X xb xt G a RC n g⁻¹ hg

noncomputable def ChartRing.ιbar {C : GChain X xt G a} (RC : ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    (↥(FixedPoints.subalgebra 𝒪 RC.R G) ⧸ ChartRing.IA 𝒪 π X xb xt G a RC n) →+* (RC.R ⧸ Ideal.span {algebraMap 𝒪 RC.R π ^ (n + 1)}) :=
  Ideal.quotientMap _ (algebraMap _ RC.R) (ChartRing.span_pow_le_comap 𝒪 π X xb xt G a RC n)

noncomputable def qChart (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    (C.W n).toScheme ⟶ (glueFunctor 𝒪 π X xb xt G a RC n).obj C :=
  (ChartRing.isoSpec 𝒪 π X xb xt G a (RC C) n).hom ≫
    Spec.map (CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n))

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
theorem qChart_def (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    qChart 𝒪 π X xb xt G a RC n C = (ChartRing.isoSpec 𝒪 π X xb xt G a (RC C) n).hom ≫
      Spec.map (CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n)) := rfl

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem resLE_smul_comp_qChart (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a)
    (g : G) :
    (a n g).hom.resLE (C.W n) (C.W n) (by rw [C.stable]) ≫ qChart 𝒪 π X xb xt G a RC n C = qChart 𝒪 π X xb xt G a RC n C := by
  have hg := ChartRing.span_pow_le_comap_toRingHom 𝒪 π X xb xt G a (RC C) n g⁻¹
  have hι : CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n) ≫
      CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 (RC C).R π ^ (n + 1)})
        (MulSemiringAction.toRingHom G (RC C).R g⁻¹) hg) =
      CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n) := by
    ext x
    exact ChartRing.quotientMap_toRingHom_quotientMap_algebraMap 𝒪 π X xb xt G a (RC C) n g⁻¹ hg
      (ChartRing.span_pow_le_comap 𝒪 π X xb xt G a (RC C) n) (Ideal.Quotient.mk _ x)
  show (a n g).hom.resLE (C.W n) (C.W n) (by rw [C.stable]) ≫ (ChartRing.isoSpec 𝒪 π X xb xt G a (RC C) n).hom ≫
      Spec.map (CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n)) =
    (ChartRing.isoSpec 𝒪 π X xb xt G a (RC C) n).hom ≫ Spec.map (CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n))
  rw [← Category.assoc, ChartRing.resLE_smul_comp_isoSpec_hom 𝒪 π X xb xt G a (RC C) n g hg,
    Category.assoc, ← Spec.map_comp, hι]

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem qChart_apply_smul (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a)
    (g : G) (y : ↥(C.W n)) (hy : (a n g).hom.base y.1 ∈ C.W n) :
    (qChart 𝒪 π X xb xt G a RC n C).base ⟨(a n g).hom.base y.1, hy⟩ = (qChart 𝒪 π X xb xt G a RC n C).base y := by
  have e := congrArg (fun φ => φ.base y) (resLE_smul_comp_qChart 𝒪 π X xb xt G a RC n C g)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e
  rw [← e]
  congr 1
  apply Subtype.ext
  simp [Scheme.Hom.resLE]

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem homOfLE_comp_qChart (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ)
    {C' C : GChain X xt G a} (h : C' ≤ C) :
    (X n).homOfLE (h n) ≫ qChart 𝒪 π X xb xt G a RC n C =
      qChart 𝒪 π X xb xt G a RC n C' ≫ (glueFunctor 𝒪 π X xb xt G a RC n).map (homOfLE h) := by

  have hR : Ideal.span {algebraMap 𝒪 (RC C).R π ^ (n + 1)} ≤
      (Ideal.span {algebraMap 𝒪 (RC C').R π ^ (n + 1)}).comap (chartRes 𝒪 π X xb xt G a RC h).toRingHom := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap]
    have : (chartRes 𝒪 π X xb xt G a RC h).toRingHom (algebraMap 𝒪 _ π ^ (n + 1)) = algebraMap 𝒪 _ π ^ (n + 1) := by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, AlgHom.commutes]
    rw [this]
    exact Ideal.subset_span rfl

  have h1 : (X n).homOfLE (h n) ≫ (ChartRing.isoSpec 𝒪 π X xb xt G a (RC C) n).hom =
      (ChartRing.isoSpec 𝒪 π X xb xt G a (RC C') n).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (chartRes 𝒪 π X xb xt G a RC h).toRingHom hR)) := by
    have hring : CommRingCat.ofHom ((RC C).lvl n).toRingHom ≫ (X n).presheaf.map (homOfLE (h n)).op =
        CommRingCat.ofHom (Ideal.quotientMap _ (chartRes 𝒪 π X xb xt G a RC h).toRingHom hR) ≫
          CommRingCat.ofHom ((RC C').lvl n).toRingHom := by
      ext r
      simpa using (lvl_chartRes 𝒪 π X xb xt G a RC h n r).symm
    rw [ChartRing.isoSpec_hom, ChartRing.isoSpec_hom, ← Category.assoc,
      ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map (C'.W n) (C.W n) (h n), Category.assoc, Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp, hring]

  have h2 : CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n) ≫
      CommRingCat.ofHom (Ideal.quotientMap _ (chartRes 𝒪 π X xb xt G a RC h).toRingHom hR) =
      CommRingCat.ofHom (chartResBar 𝒪 π X xb xt G a RC h n) ≫ CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C') n) := by
    ext x
    rfl
  show (X n).homOfLE (h n) ≫ (ChartRing.isoSpec 𝒪 π X xb xt G a (RC C) n).hom ≫
      Spec.map (CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n)) =
    ((ChartRing.isoSpec 𝒪 π X xb xt G a (RC C') n).hom ≫
      Spec.map (CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C') n))) ≫
      Spec.map (CommRingCat.ofHom (chartResBar 𝒪 π X xb xt G a RC h n))
  rw [← Category.assoc, h1, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, h2]

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem glueFunctor_map_qChart_apply (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ)
    {C' C : GChain X xt G a} (h : C' ≤ C) (y : ↥(C'.W n)) :
    ((glueFunctor 𝒪 π X xb xt G a RC n).map (homOfLE h)).base ((qChart 𝒪 π X xb xt G a RC n C').base y) =
      (qChart 𝒪 π X xb xt G a RC n C).base ⟨y.1, h n y.2⟩ := by
  have e := congrArg (fun φ => φ.base y) (homOfLE_comp_qChart 𝒪 π X xb xt G a RC n h)
  simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e
  rw [← e]
  congr 1
  exact (X n).homOfLE_apply' (h n) y.1 y.2

include hdvr hπ hcomplete in
omit hcart hproper hflat haff ha_over ha_xt hcov in

theorem qChart_surjective (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    Function.Surjective (qChart 𝒪 π X xb xt G a RC n C).base := by
  let R := (RC C).R
  let A := ChartRing.A 𝒪 π X xb xt G a (RC C)
  haveI : Algebra.IsInvariant (↥A) R G := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  haveI : Algebra.IsIntegral (↥A) R := Algebra.IsInvariant.isIntegral (↥A) R G
  have hint : (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n).IsIntegral := by
    intro z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨p, hp, hpr⟩ := Algebra.IsIntegral.isIntegral (R := ↥A) r
    refine ⟨p.map (Ideal.Quotient.mk _), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, show (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n).comp (Ideal.Quotient.mk _) =
        (Ideal.Quotient.mk _).comp (algebraMap (↥A) R) from Ideal.quotientMap_comp_mk _,
      ← Polynomial.hom_eval₂, hpr, map_zero]
  have hinj : Function.Injective (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n) :=
    ChartRing.quotientMap_algebraMap_injective 𝒪 hdvr π hπ hcomplete X xb xt G a (RC C) n _
  intro x
  obtain ⟨y, hy⟩ := hint.comap_surjective hinj x
  obtain ⟨w, hw⟩ := (ChartRing.isoSpec 𝒪 π X xb xt G a (RC C) n).hom.surjective y
  refine ⟨w, ?_⟩
  change (Spec.map (CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n))).base
      ((ChartRing.isoSpec 𝒪 π X xb xt G a (RC C) n).hom.base w) = x
  rw [hw]
  exact hy

open scoped Pointwise in
omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem exists_smul_of_qChart_eq (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a)
    (y y' : ↥(C.W n)) (h : (qChart 𝒪 π X xb xt G a RC n C).base y = (qChart 𝒪 π X xb xt G a RC n C).base y') :
    ∃ g : G, (a n g).hom.base y.1 = y'.1 := by
  classical
  obtain ⟨x, hx⟩ := y
  obtain ⟨x', hx'⟩ := y'
  let R := (RC C).R
  let A := ChartRing.A 𝒪 π X xb xt G a (RC C)
  haveI : Algebra.IsInvariant (↥A) R G := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have hW : IsAffineOpen (C.W n) := C.affine n

  let ρ : R →+* Γ(X n, C.W n) := ((RC C).lvl n).toRingHom.comp (Ideal.Quotient.mk _)
  have hρ : Function.Surjective ρ := ((RC C).lvl n).surjective.comp Ideal.Quotient.mk_surjective

  let 𝔭 := hW.primeIdealOf ⟨x, hx⟩
  let 𝔭' := hW.primeIdealOf ⟨x', hx'⟩
  let Q : Ideal R := 𝔭.asIdeal.comap ρ
  let Q' : Ideal R := 𝔭'.asIdeal.comap ρ
  haveI : Q.IsPrime := Ideal.comap_isPrime ρ 𝔭.asIdeal
  haveI : Q'.IsPrime := Ideal.comap_isPrime ρ 𝔭'.asIdeal

  have hq : ∀ (z : X n) (hz : z ∈ C.W n),
      ((hW.primeIdealOf ⟨z, hz⟩).asIdeal.comap ρ).under (↥A) =
        ((qChart 𝒪 π X xb xt G a RC n C).base ⟨z, hz⟩).asIdeal.comap
          (Ideal.Quotient.mk (ChartRing.IA 𝒪 π X xb xt G a (RC C) n)) := by
    intro z hz
    have e : ((qChart 𝒪 π X xb xt G a RC n C).base ⟨z, hz⟩).asIdeal =
        ((hW.primeIdealOf ⟨z, hz⟩).asIdeal.comap ((RC C).lvl n).toRingHom).comap
          (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n) := rfl
    rw [e, Ideal.under_def, Ideal.comap_comap, Ideal.comap_comap, Ideal.comap_comap]
    congr 1
  have hQQ' : Q.under (↥A) = Q'.under (↥A) := by
    simp only [Q, Q', 𝔭, 𝔭', hq]
    simp only [h]
  haveI : SMulCommClass G (↥A) R := ⟨fun g b r => by
    change g • ((b : R) * r) = (b : R) * g • r
    rw [smul_mul', show g • (b : R) = b from b.2 g]⟩
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (↥A) R G Q Q' hQQ'
  refine ⟨g, ?_⟩

  have hgx : (a n g).hom.base x ∈ C.W n := by
    show x ∈ (a n g).hom ⁻¹ᵁ (C.W n); rw [C.stable]; exact hx
  have hsymm : ∀ r : R, ((MulSemiringAction.toRingAut G R) g).symm r = g⁻¹ • r := fun r => rfl
  have hsmul : (hW.primeIdealOf ⟨(a n g).hom.base x, hgx⟩).asIdeal.comap ρ = g • Q := by
    rw [← IsAffineOpen.comap_primeIdealOf_appLE (C.W n) hW (C.W n) hW (by rw [C.stable]) hx,
      PrimeSpectrum.comap_asIdeal, Ideal.comap_comap, Ideal.pointwise_smul_eq_comap]
    ext r
    have hl := (RC C).lvl_smul n g⁻¹ r
    simp only [inv_inv] at hl
    simp only [Ideal.mem_comap, Q, 𝔭, RingHom.coe_comp, Function.comp_apply, hsymm]
    exact Iff.of_eq (congrArg (fun s => s ∈ (hW.primeIdealOf ⟨x, hx⟩).asIdeal) hl)

  have key : hW.primeIdealOf ⟨(a n g).hom.base x, hgx⟩ = 𝔭' := by
    apply PrimeSpectrum.ext
    apply Ideal.comap_injective_of_surjective ρ hρ
    rw [hsmul, ← hg]
  have := congrArg hW.fromSpec key
  rwa [IsAffineOpen.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_primeIdealOf] at this

include hdvr hπ hcomplete hproper in
omit hcart hflat haff ha_over ha_xt hcov in

theorem isLocallyDirected_glueFunctor (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    ((glueFunctor 𝒪 π X xb xt G a RC n) ⋙ Scheme.forget).IsLocallyDirected := by
  constructor
  intro Ci Cj Ck fi fj xi xj hx
  simp only [Functor.comp_obj, Scheme.forget_obj, Functor.comp_map, Scheme.forget_map,
    ConcreteCategory.hom_ofHom] at hx

  obtain ⟨yi, rfl⟩ := qChart_surjective 𝒪 hdvr π hπ hcomplete X xb xt G a RC n Ci xi
  obtain ⟨yj, rfl⟩ := qChart_surjective 𝒪 hdvr π hπ hcomplete X xb xt G a RC n Cj xj
  have hi : Ci ≤ Ck := fi.le
  have hj : Cj ≤ Ck := fj.le

  have hik := glueFunctor_map_qChart_apply 𝒪 π X xb xt G a RC n hi yi
  have hjk := glueFunctor_map_qChart_apply 𝒪 π X xb xt G a RC n hj yj
  have hfi : fi = homOfLE hi := rfl
  have hfj : fj = homOfLE hj := rfl
  rw [hfi, hfj] at hx
  change ((glueFunctor 𝒪 π X xb xt G a RC n).map (homOfLE hi)).base ((qChart 𝒪 π X xb xt G a RC n Ci).base yi) =
    ((glueFunctor 𝒪 π X xb xt G a RC n).map (homOfLE hj)).base ((qChart 𝒪 π X xb xt G a RC n Cj).base yj) at hx
  rw [hik, hjk] at hx
  obtain ⟨g, hg⟩ := exists_smul_of_qChart_eq 𝒪 π X xb xt G a RC n Ck _ _ hx
  have hg' : (a n g).hom.base yi.1 = yj.1 := hg

  obtain ⟨Cl, hCl⟩ := gchain_inf 𝒪 π X xb xt hproper G a Ci Cj
  have hli : Cl ≤ Ci := fun m => (hCl m).le.trans inf_le_left
  have hlj : Cl ≤ Cj := fun m => (hCl m).le.trans inf_le_right
  have hyjWi : yj.1 ∈ Ci.W n := by
    have : (a n g).hom.base yi.1 ∈ Ci.W n := by
      show yi.1 ∈ (a n g).hom ⁻¹ᵁ (Ci.W n); rw [Ci.stable]; exact yi.2
    rwa [hg'] at this
  have hyjWl : yj.1 ∈ Cl.W n := by rw [hCl]; exact ⟨hyjWi, yj.2⟩
  refine ⟨Cl, homOfLE hli, homOfLE hlj, (qChart 𝒪 π X xb xt G a RC n Cl).base ⟨yj.1, hyjWl⟩, ?_, ?_⟩
  · show ((glueFunctor 𝒪 π X xb xt G a RC n).map (homOfLE hli)).base
        ((qChart 𝒪 π X xb xt G a RC n Cl).base ⟨yj.1, hyjWl⟩) = (qChart 𝒪 π X xb xt G a RC n Ci).base yi
    rw [glueFunctor_map_qChart_apply]
    have hmem : (a n g).hom.base yi.1 ∈ Ci.W n := by rw [hg']; exact hyjWi
    rw [← qChart_apply_smul 𝒪 π X xb xt G a RC n Ci g yi hmem]
    congr 1
    exact Subtype.ext hg'.symm
  · show ((glueFunctor 𝒪 π X xb xt G a RC n).map (homOfLE hlj)).base
        ((qChart 𝒪 π X xb xt G a RC n Cl).base ⟨yj.1, hyjWl⟩) = (qChart 𝒪 π X xb xt G a RC n Cj).base yj
    rw [glueFunctor_map_qChart_apply]
    congr 1

noncomputable def liftPt : (m : ℕ) → ↥(X 0) → ↥(X m)
  | 0 => fun x => x
  | m + 1 => fun x => (xt m).base (liftPt m x)

include hcart in
omit hdvr hπ hcomplete hproper hflat haff ha_over ha_xt hcov in
theorem liftPt_surjective (m : ℕ) : Function.Surjective (liftPt X xt m) := by
  induction m with
  | zero => exact Function.surjective_id
  | succ m ih => exact (isHomeomorph_xt 𝒪 π X xb xt hcart m).bijective.2.comp ih

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
theorem liftPt_mem_iff (C : GChain X xt G a) (m : ℕ) (x : ↥(X 0)) : liftPt X xt m x ∈ C.W m ↔ x ∈ C.W 0 := by
  induction m with
  | zero => exact Iff.rfl
  | succ m ih =>
    rw [← ih]
    show liftPt X xt m x ∈ (xt m) ⁻¹ᵁ C.W (m + 1) ↔ _
    rw [C.compat]

include hcart hproper in
omit hdvr hπ hcomplete hflat haff ha_over ha_xt hcov in

theorem exists_invariant_basicOpen_mem (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C)
    {C' C : GChain X xt G a} (h : C' ≤ C) (n : ℕ) (y : ↥(C'.W n)) :
    ∃ f : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)),
      y.1 ∈ (X n).basicOpen ((RC C).lvl n (Ideal.Quotient.mk _ (f : (RC C).R))) ∧
      ∀ m : ℕ, C.W m ⊓ (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R))) ≤ C'.W m := by
  obtain ⟨x, hx⟩ := liftPt_surjective 𝒪 π X xb xt hcart n y.1
  have hx0 : x ∈ C'.W 0 := (liftPt_mem_iff X xt G a C' n x).mp (hx.symm ▸ y.2)
  obtain ⟨f, hf0, hfle⟩ := exists_invariant_basicOpen_le 𝒪 π X xb xt hcart hproper G a RC C C' h x hx0
  obtain ⟨Cf, hCf⟩ := exists_gchain_basicOpen 𝒪 π X xb xt G a RC C f
  refine ⟨f, ?_, hfle⟩
  have hxf : x ∈ Cf.W 0 := by rw [hCf]; exact ⟨h 0 hx0, hf0⟩
  have := (liftPt_mem_iff X xt G a Cf n x).mpr hxf
  rw [hx, hCf] at this
  exact this.2

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem mem_basicOpen_iff_primeIdealOf_mem {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) (s : Γ(Y, U)) (y : ↥U) :
    (y : Y) ∈ Y.basicOpen s ↔ hU.primeIdealOf y ∈ PrimeSpectrum.basicOpen s := by
  rw [← hU.fromSpec_preimage_basicOpen]
  show _ ↔ hU.fromSpec.base (hU.primeIdealOf y) ∈ Y.basicOpen s
  rw [hU.fromSpec_primeIdealOf]

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem qChart_mem_basicOpen_iff (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a)
    (s : ↥(FixedPoints.subalgebra 𝒪 (RC C).R G)) (y : ↥(C.W n)) :
    (qChart 𝒪 π X xb xt G a RC n C).base y ∈ PrimeSpectrum.basicOpen (Ideal.Quotient.mk (ChartRing.IA 𝒪 π X xb xt G a (RC C) n) s) ↔
      y.1 ∈ (X n).basicOpen ((RC C).lvl n (Ideal.Quotient.mk _ (s : (RC C).R))) := by
  refine (PrimeSpectrum.mem_basicOpen _ _).trans ?_
  refine Iff.trans ?_ ((mem_basicOpen_iff_primeIdealOf_mem (C.affine n) _ y).trans (PrimeSpectrum.mem_basicOpen _ _)).symm
  exact Iff.rfl

include hdvr hπ hcomplete hcart hproper in
omit hflat haff ha_over ha_xt hcov in

theorem exists_basicChain_through (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ)
    {C' C : GChain X xt G a} (φ : C' ⟶ C) (y : ↥(C'.W n)) :
    ∃ (Cf : GChain X xt G a) (ψ : Cf ⟶ C'),
      IsOpenImmersion ((glueFunctor 𝒪 π X xb xt G a RC n).map ψ) ∧
      IsOpenImmersion ((glueFunctor 𝒪 π X xb xt G a RC n).map (ψ ≫ φ)) ∧
      (qChart 𝒪 π X xb xt G a RC n C').base y ∈ Set.range ((glueFunctor 𝒪 π X xb xt G a RC n).map ψ).base := by
  have h : C' ≤ C := φ.le
  obtain ⟨f, hyf, hfle⟩ := exists_invariant_basicOpen_mem 𝒪 π X xb xt hcart hproper G a RC h n y
  obtain ⟨Cf, hCf⟩ := exists_gchain_basicOpen 𝒪 π X xb xt G a RC C f
  have hCfC : Cf ≤ C := fun m => (hCf m).le.trans inf_le_left
  have hCfC' : Cf ≤ C' := fun m => (hCf m).le.trans (hfle m)

  let f' : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C')) := chartResA 𝒪 π X xb xt G a RC h f
  have hf' : ∀ m : ℕ, (X m).basicOpen ((RC C').lvl m (Ideal.Quotient.mk _ (f' : (RC C').R))) =
      C'.W m ⊓ (X m).basicOpen ((RC C).lvl m (Ideal.Quotient.mk _ (f : (RC C).R))) := by
    intro m
    rw [chartResA_coe, lvl_chartRes, Scheme.basicOpen_res]
  have hCf' : ∀ m : ℕ, Cf.W m = C'.W m ⊓ (X m).basicOpen ((RC C').lvl m (Ideal.Quotient.mk _ (f' : (RC C').R))) := by
    intro m
    rw [hf', ← inf_assoc, inf_idem, hCf]
    apply le_antisymm
    · exact le_inf (hfle m) inf_le_right
    · exact inf_le_inf_right _ (h m)

  have locC := isLocalizationAway_invariants_basicOpen 𝒪 hdvr π hπ hcomplete X xb xt G a RC C Cf f hCf
    (chartRes 𝒪 π X xb xt G a RC hCfC) (chartRes_smul 𝒪 π X xb xt G a RC hCfC) (lvl_chartRes 𝒪 π X xb xt G a RC hCfC) n
    (chartResA 𝒪 π X xb xt G a RC hCfC).toRingHom (chartResA_coe 𝒪 π X xb xt G a RC hCfC)
    (chartResBar 𝒪 π X xb xt G a RC hCfC n) (chartResBar_mk 𝒪 π X xb xt G a RC hCfC n)
  have locC' := isLocalizationAway_invariants_basicOpen 𝒪 hdvr π hπ hcomplete X xb xt G a RC C' Cf f' hCf'
    (chartRes 𝒪 π X xb xt G a RC hCfC') (chartRes_smul 𝒪 π X xb xt G a RC hCfC') (lvl_chartRes 𝒪 π X xb xt G a RC hCfC') n
    (chartResA 𝒪 π X xb xt G a RC hCfC').toRingHom (chartResA_coe 𝒪 π X xb xt G a RC hCfC')
    (chartResBar 𝒪 π X xb xt G a RC hCfC' n) (chartResBar_mk 𝒪 π X xb xt G a RC hCfC' n)
  refine ⟨Cf, homOfLE hCfC', ?_, ?_, ?_⟩
  · letI := (chartResBar 𝒪 π X xb xt G a RC hCfC' n).toAlgebra
    haveI := locC'
    exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk _ f')
  · letI := (chartResBar 𝒪 π X xb xt G a RC hCfC n).toAlgebra
    haveI := locC
    exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk _ f)
  · letI := (chartResBar 𝒪 π X xb xt G a RC hCfC' n).toAlgebra
    haveI := locC'
    have hrange : Set.range (PrimeSpectrum.comap (chartResBar 𝒪 π X xb xt G a RC hCfC' n)) =
        ((PrimeSpectrum.basicOpen (Ideal.Quotient.mk (ChartRing.IA 𝒪 π X xb xt G a (RC C') n) f') :
          TopologicalSpace.Opens (PrimeSpectrum _)) : Set (PrimeSpectrum _)) :=
      PrimeSpectrum.localization_away_comap_range _ (Ideal.Quotient.mk _ f')
    change (qChart 𝒪 π X xb xt G a RC n C').base y ∈ Set.range (PrimeSpectrum.comap (chartResBar 𝒪 π X xb xt G a RC hCfC' n))
    rw [hrange]
    show (qChart 𝒪 π X xb xt G a RC n C').base y ∈
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk (ChartRing.IA 𝒪 π X xb xt G a (RC C') n) f')
    rw [qChart_mem_basicOpen_iff, hf']
    exact ⟨y.2, hyf⟩

include hdvr hπ hcomplete hcart hproper in
omit hflat haff ha_over ha_xt hcov in

theorem isOpenImmersion_glueFunctor_map (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ)
    {C' C : GChain X xt G a} (f : C' ⟶ C) : IsOpenImmersion ((glueFunctor 𝒪 π X xb xt G a RC n).map f) := by
  have h : C' ≤ C := f.le
  have hf : f = homOfLE h := rfl

  haveI : ∀ p, IsIso (((glueFunctor 𝒪 π X xb xt G a RC n).map f).stalkMap p) := by
    intro p
    obtain ⟨y, rfl⟩ := qChart_surjective 𝒪 hdvr π hπ hcomplete X xb xt G a RC n C' p
    obtain ⟨Cf, ψ, h1, h2, ⟨q, hq⟩⟩ := exists_basicChain_through 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper G a RC n f y
    rw [← hq]
    have hOI : IsOpenImmersion ((glueFunctor 𝒪 π X xb xt G a RC n).map ψ ≫ (glueFunctor 𝒪 π X xb xt G a RC n).map f) := by
      rw [← Functor.map_comp]; exact h2
    haveI : IsIso (((glueFunctor 𝒪 π X xb xt G a RC n).map f).stalkMap (((glueFunctor 𝒪 π X xb xt G a RC n).map ψ).base q) ≫
        ((glueFunctor 𝒪 π X xb xt G a RC n).map ψ).stalkMap q) := by
      rw [← Scheme.Hom.stalkMap_comp]
      exact (IsOpenImmersion.iff_isIso_stalkMap.mp hOI).2 q
    exact IsIso.of_isIso_comp_right _ (((glueFunctor 𝒪 π X xb xt G a RC n).map ψ).stalkMap q)
  refine IsOpenImmersion.of_isIso_stalkMap _ ?_
  refine Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ((glueFunctor 𝒪 π X xb xt G a RC n).map f).continuous ?_ ?_
  ·
    intro p p' hpp'
    obtain ⟨y, rfl⟩ := qChart_surjective 𝒪 hdvr π hπ hcomplete X xb xt G a RC n C' p
    obtain ⟨y', rfl⟩ := qChart_surjective 𝒪 hdvr π hπ hcomplete X xb xt G a RC n C' p'
    change ((glueFunctor 𝒪 π X xb xt G a RC n).map f).base ((qChart 𝒪 π X xb xt G a RC n C').base y) =
      ((glueFunctor 𝒪 π X xb xt G a RC n).map f).base ((qChart 𝒪 π X xb xt G a RC n C').base y') at hpp'
    rw [hf, glueFunctor_map_qChart_apply, glueFunctor_map_qChart_apply] at hpp'
    obtain ⟨g₀, hg₀⟩ := exists_smul_of_qChart_eq 𝒪 π X xb xt G a RC n C _ _ hpp'
    have hg₀' : (a n g₀).hom.base y.1 = y'.1 := hg₀
    have hmem : (a n g₀).hom.base y.1 ∈ C'.W n := by rw [hg₀']; exact y'.2
    show (qChart 𝒪 π X xb xt G a RC n C').base y = (qChart 𝒪 π X xb xt G a RC n C').base y'
    rw [← qChart_apply_smul 𝒪 π X xb xt G a RC n C' g₀ y hmem]
    congr 1
    exact Subtype.ext hg₀'
  ·
    intro U hU
    rw [isOpen_iff_forall_mem_open]
    rintro _ ⟨p, hpU, rfl⟩
    obtain ⟨y, hy⟩ := qChart_surjective 𝒪 hdvr π hπ hcomplete X xb xt G a RC n C' p
    obtain ⟨Cf, ψ, h1, h2, ⟨q, hq⟩⟩ := exists_basicChain_through 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper G a RC n f y
    refine ⟨((glueFunctor 𝒪 π X xb xt G a RC n).map (ψ ≫ f)).base ''
        (((glueFunctor 𝒪 π X xb xt G a RC n).map ψ).base ⁻¹' U), ?_, ?_, ?_⟩
    · rintro _ ⟨q', hq'U, rfl⟩
      refine ⟨_, hq'U, ?_⟩
      rw [Functor.map_comp, Scheme.Hom.comp_base, TopCat.comp_app]
    · exact ((glueFunctor 𝒪 π X xb xt G a RC n).map (ψ ≫ f)).isOpenEmbedding.isOpenMap _
        (hU.preimage ((glueFunctor 𝒪 π X xb xt G a RC n).map ψ).continuous)
    · refine ⟨q, ?_, ?_⟩
      · show ((glueFunctor 𝒪 π X xb xt G a RC n).map ψ).base q ∈ U
        rw [hq, hy]; exact hpU
      · rw [Functor.map_comp, Scheme.Hom.comp_base, TopCat.comp_app, hq, hy]

variable [hOI : ∀ (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) {C' C : GChain X xt G a} (f : C' ⟶ C),
    IsOpenImmersion ((glueFunctor 𝒪 π X xb xt G a RC n).map f)]
  [hLD : ∀ (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ),
    ((glueFunctor 𝒪 π X xb xt G a RC n) ⋙ Scheme.forget).IsLocallyDirected]

noncomputable def Yglue (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) : Scheme.{0} :=
  Limits.colimit (glueFunctor 𝒪 π X xb xt G a RC n)

noncomputable def Yι (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    (glueFunctor 𝒪 π X xb xt G a RC n).obj C ⟶ Yglue 𝒪 π X xb xt G a RC n :=
  Limits.colimit.ι (glueFunctor 𝒪 π X xb xt G a RC n) C

theorem openCover_f (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    (Scheme.IsLocallyDirected.openCover (glueFunctor 𝒪 π X xb xt G a RC n)).f C = Yι 𝒪 π X xb xt G a RC n C := rfl

scoped instance (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    IsOpenImmersion (Yι 𝒪 π X xb xt G a RC n C) :=
  (Scheme.IsLocallyDirected.openCover (glueFunctor 𝒪 π X xb xt G a RC n)).map_prop C

theorem Yι_jointly_surjective (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (y : Yglue 𝒪 π X xb xt G a RC n) :
    ∃ (C : GChain X xt G a) (x : (glueFunctor 𝒪 π X xb xt G a RC n).obj C), (Yι 𝒪 π X xb xt G a RC n C).base x = y :=
  Scheme.IsLocallyDirected.ι_jointly_surjective _ y

noncomputable def YV (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    (Yglue 𝒪 π X xb xt G a RC n).Opens :=
  (Yι 𝒪 π X xb xt G a RC n C).opensRange

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
theorem YV_affine (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    IsAffineOpen (YV 𝒪 π X xb xt G a RC n C) :=
  haveI : IsAffine ((glueFunctor 𝒪 π X xb xt G a RC n).obj C) := by
    show IsAffine (Spec _); infer_instance
  isAffineOpen_opensRange _

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
theorem YV_cover (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (y : Yglue 𝒪 π X xb xt G a RC n) :
    ∃ C : GChain X xt G a, y ∈ YV 𝒪 π X xb xt G a RC n C := by
  obtain ⟨C, x, rfl⟩ := Yι_jointly_surjective 𝒪 π X xb xt G a RC n y
  exact ⟨C, ⟨x, rfl⟩⟩

noncomputable def Ychart (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    (↥(FixedPoints.subalgebra 𝒪 (RC C).R G) ⧸ ChartRing.IA 𝒪 π X xb xt G a (RC C) n) ≃+* Γ(Yglue 𝒪 π X xb xt G a RC n, YV 𝒪 π X xb xt G a RC n C) :=
  ((Scheme.ΓSpecIso (CommRingCat.of _)).symm ≪≫ ((Yι 𝒪 π X xb xt G a RC n C).appIso ⊤).symm ≪≫
    (Yglue 𝒪 π X xb xt G a RC n).presheaf.mapIso
      (eqToIso (Scheme.Hom.image_top_eq_opensRange (Yι 𝒪 π X xb xt G a RC n C)).symm).op).commRingCatIsoToRingEquiv

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem appLE_Ychart (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a)
    (z : ↥(FixedPoints.subalgebra 𝒪 (RC C).R G) ⧸ ChartRing.IA 𝒪 π X xb xt G a (RC C) n) :
    (Yι 𝒪 π X xb xt G a RC n C).appLE (YV 𝒪 π X xb xt G a RC n C) ⊤
        (by rw [YV, Scheme.Hom.preimage_opensRange])
      (Ychart 𝒪 π X xb xt G a RC n C z) = (Scheme.ΓSpecIso (CommRingCat.of _)).inv z := by
  have hY : Ychart 𝒪 π X xb xt G a RC n C z =
      ((Yglue 𝒪 π X xb xt G a RC n).presheaf.map (eqToHom (Scheme.Hom.image_top_eq_opensRange (Yι 𝒪 π X xb xt G a RC n C)).symm).op)
        (((Yι 𝒪 π X xb xt G a RC n C).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of _)).inv z)) := rfl
  have h1 := Scheme.Hom.map_appLE (Yι 𝒪 π X xb xt G a RC n C)
    (show (⊤ : ((glueFunctor 𝒪 π X xb xt G a RC n).obj C).Opens) ≤ (Yι 𝒪 π X xb xt G a RC n C) ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC n C) from
      by rw [YV, Scheme.Hom.preimage_opensRange])
    (eqToHom (Scheme.Hom.image_top_eq_opensRange (Yι 𝒪 π X xb xt G a RC n C)).symm).op
  have h2 : ((Yι 𝒪 π X xb xt G a RC n C).appIso ⊤).inv ≫
      (Yι 𝒪 π X xb xt G a RC n C).appLE ((Yι 𝒪 π X xb xt G a RC n C) ''ᵁ ⊤) ⊤
        (Scheme.Hom.preimage_image_eq _ ⊤).ge = 𝟙 _ := by
    rw [← Scheme.Hom.appIso_hom', Iso.inv_hom_id]
  rw [hY]
  change (((Yι 𝒪 π X xb xt G a RC n C).appIso ⊤).inv ≫
      ((Yglue 𝒪 π X xb xt G a RC n).presheaf.map (eqToHom (Scheme.Hom.image_top_eq_opensRange (Yι 𝒪 π X xb xt G a RC n C)).symm).op ≫
        (Yι 𝒪 π X xb xt G a RC n C).appLE (YV 𝒪 π X xb xt G a RC n C) ⊤ _)) ((Scheme.ΓSpecIso (CommRingCat.of _)).inv z) = _
  erw [h1]
  erw [h2]
  rfl

noncomputable def pChart (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    (↑(C.W n) : Scheme.{0}) ⟶ Yglue 𝒪 π X xb xt G a RC n :=
  (ChartRing.isoSpec 𝒪 π X xb xt G a (RC C) n).hom ≫ Spec.map (CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n)) ≫
    Yι 𝒪 π X xb xt G a RC n C

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem isOpenCover_W (hcov' : ∀ (n : ℕ) (x : X n), ∃ C : GChain X xt G a, x ∈ C.W n) (n : ℕ) :
    TopologicalSpace.IsOpenCover (fun C : GChain X xt G a => C.W n) := by
  refine TopologicalSpace.IsOpenCover.mk (top_le_iff.1 fun x _ => ?_)
  obtain ⟨C, hx⟩ := hcov' n x
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨C, hx⟩

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem exists_glue_of_compat (hcov' : ∀ (n : ℕ) (x : X n), ∃ C : GChain X xt G a, x ∈ C.W n)
    (hinf : ∀ C C' : GChain X xt G a, ∃ C'' : GChain X xt G a, ∀ m : ℕ, C''.W m = C.W m ⊓ C'.W m)
    (n : ℕ) {Y' : Scheme.{0}} (q : ∀ C : GChain X xt G a, (↑(C.W n) : Scheme.{0}) ⟶ Y')
    (hq : ∀ (C' C : GChain X xt G a) (h : C' ≤ C), (X n).homOfLE (h n) ≫ q C = q C') :
    ∃ p : X n ⟶ Y', ∀ C : GChain X xt G a, (C.W n).ι ≫ p = q C := by
  classical
  let 𝒲 := (X n).openCoverOfIsOpenCover (fun C : GChain X xt G a => C.W n) (isOpenCover_W X xt G a hcov' n)

  have key : ∀ (C C' : GChain X xt G a) {T : Scheme.{0}} (tC : T ⟶ ↑(C.W n)) (tC' : T ⟶ ↑(C'.W n)),
      tC ≫ (C.W n).ι = tC' ≫ (C'.W n).ι → tC ≫ q C = tC' ≫ q C' := by
    intro C C' T tC tC' htt
    obtain ⟨L, hL⟩ := hinf C C'
    have hLC : L ≤ C := fun m => (hL m).le.trans inf_le_left
    have hLC' : L ≤ C' := fun m => (hL m).le.trans inf_le_right
    have hrange : Set.range (tC ≫ (C.W n).ι).base ⊆ Set.range (L.W n).ι.base := by
      rintro x ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι, hL]
      refine ⟨?_, ?_⟩
      · show (C.W n).ι (tC z) ∈ C.W n
        rw [Scheme.Opens.ι_apply]; exact (tC z).2
      · have : (tC ≫ (C.W n).ι) z = (tC' ≫ (C'.W n).ι) z := by rw [htt]
        show ((tC ≫ (C.W n).ι) z) ∈ C'.W n
        rw [this, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
        exact (tC' z).2
    let tL : T ⟶ ↑(L.W n) := IsOpenImmersion.lift (L.W n).ι (tC ≫ (C.W n).ι) hrange
    have htL : tL ≫ (L.W n).ι = tC ≫ (C.W n).ι := IsOpenImmersion.lift_fac _ _ _
    have h1 : tC = tL ≫ (X n).homOfLE (hLC n) := by
      rw [← cancel_mono (C.W n).ι, Category.assoc, Scheme.homOfLE_ι, htL]
    have h2 : tC' = tL ≫ (X n).homOfLE (hLC' n) := by
      rw [← cancel_mono (C'.W n).ι, Category.assoc, Scheme.homOfLE_ι, htL, htt]
    rw [h1, h2, Category.assoc, Category.assoc, hq, hq]
  have hcompat : ∀ C C' : GChain X xt G a,
      Limits.pullback.fst (𝒲.f C) (𝒲.f C') ≫ q C = Limits.pullback.snd (𝒲.f C) (𝒲.f C') ≫ q C' :=
    fun C C' => key C C' _ _ Limits.pullback.condition
  refine ⟨𝒲.glueMorphisms q hcompat, fun C => ?_⟩
  exact Scheme.Cover.ι_glueMorphisms 𝒲 q hcompat C

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
theorem pChart_eq (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    pChart 𝒪 π X xb xt G a RC n C = qChart 𝒪 π X xb xt G a RC n C ≫ Yι 𝒪 π X xb xt G a RC n C :=
  (Category.assoc _ _ _).symm

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem pChart_homOfLE (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ)
    (C' C : GChain X xt G a) (h : C' ≤ C) :
    (X n).homOfLE (h n) ≫ pChart 𝒪 π X xb xt G a RC n C = pChart 𝒪 π X xb xt G a RC n C' := by
  rw [pChart_eq, pChart_eq, ← Category.assoc, homOfLE_comp_qChart 𝒪 π X xb xt G a RC n h, Category.assoc]
  congr 1
  exact Limits.colimit.w (glueFunctor 𝒪 π X xb xt G a RC n) (homOfLE h)

include hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem exists_p (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    ∃ p : X n ⟶ Yglue 𝒪 π X xb xt G a RC n, ∀ C : GChain X xt G a, (C.W n).ι ≫ p = pChart 𝒪 π X xb xt G a RC n C :=
  exists_glue_of_compat X xt G a (exists_gchain 𝒪 π hπ X xb xt hcart hflat G a ha_xt hcov) (gchain_inf 𝒪 π X xb xt hproper G a) n
    (pChart 𝒪 π X xb xt G a RC n) (fun C' C h => pChart_homOfLE 𝒪 π X xb xt G a RC n C' C h)

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem chartResBar_comp_quotientMap_algebraMap (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ)
    {C' C : GChain X xt G a} (h : C' ≤ C) :
    (chartResBar 𝒪 π X xb xt G a RC h n).comp
        (Ideal.quotientMap (ChartRing.IA 𝒪 π X xb xt G a (RC C) n) (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 (RC C).R G))
          (by rw [ChartRing.IA, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) =
      Ideal.quotientMap (ChartRing.IA 𝒪 π X xb xt G a (RC C') n) (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 (RC C').R G))
          (by rw [ChartRing.IA, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun o => ?_)
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk, chartResBar_mk]
  congr 1
  exact (chartResA 𝒪 π X xb xt G a RC h).commutes o

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem factor_comp_chartResBar (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ)
    {C' C : GChain X xt G a} (h : C' ≤ C) :
    (Ideal.Quotient.factor
        (show ChartRing.IA 𝒪 π X xb xt G a (RC C') (n + 1) ≤ ChartRing.IA 𝒪 π X xb xt G a (RC C') n from
          Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ (n + 1))))).comp
        (chartResBar 𝒪 π X xb xt G a RC h (n + 1)) =
      (chartResBar 𝒪 π X xb xt G a RC h n).comp (Ideal.Quotient.factor
        (show ChartRing.IA 𝒪 π X xb xt G a (RC C) (n + 1) ≤ ChartRing.IA 𝒪 π X xb xt G a (RC C) n from
          Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ (n + 1))))) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
  simp only [RingHom.comp_apply, Ideal.Quotient.factor_mk, chartResBar_mk]

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem exists_yb (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    ∃ yb : Yglue 𝒪 π X xb xt G a RC n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})),
      ∀ C : GChain X xt G a, Yι 𝒪 π X xb xt G a RC n C ≫ yb =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap (ChartRing.IA 𝒪 π X xb xt G a (RC C) n)
          (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 (RC C).R G))
          (by rw [ChartRing.IA, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) := by
  let c : Limits.Cocone (glueFunctor 𝒪 π X xb xt G a RC n) :=
    { pt := Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))
      ι :=
        { app := fun C => Spec.map (CommRingCat.ofHom (Ideal.quotientMap (ChartRing.IA 𝒪 π X xb xt G a (RC C) n)
            (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 (RC C).R G))
            (by rw [ChartRing.IA, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow];
                exact Ideal.subset_span rfl)))
          naturality := fun {C' C} f => by
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
            show Spec.map _ ≫ Spec.map _ = Spec.map _
            rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, chartResBar_comp_quotientMap_algebraMap] } }
  refine ⟨Limits.colimit.desc (glueFunctor 𝒪 π X xb xt G a RC n) c, fun C => ?_⟩
  unfold Yι
  exact Limits.colimit.ι_desc c C

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem exists_yt (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) :
    ∃ yt : Yglue 𝒪 π X xb xt G a RC n ⟶ Yglue 𝒪 π X xb xt G a RC (n + 1),
      ∀ C : GChain X xt G a, Yι 𝒪 π X xb xt G a RC n C ≫ yt =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
          (show ChartRing.IA 𝒪 π X xb xt G a (RC C) (n + 1) ≤ ChartRing.IA 𝒪 π X xb xt G a (RC C) n from
            Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ (n + 1)))))) ≫
          Yι 𝒪 π X xb xt G a RC (n + 1) C := by
  let c : Limits.Cocone (glueFunctor 𝒪 π X xb xt G a RC n) :=
    { pt := Yglue 𝒪 π X xb xt G a RC (n + 1)
      ι :=
        { app := fun C => Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
            (show ChartRing.IA 𝒪 π X xb xt G a (RC C) (n + 1) ≤ ChartRing.IA 𝒪 π X xb xt G a (RC C) n from
              Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ (n + 1)))))) ≫
            Yι 𝒪 π X xb xt G a RC (n + 1) C
          naturality := fun {C' C} f => by
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]

            unfold Yι
            rw [← Limits.colimit.w (glueFunctor 𝒪 π X xb xt G a RC (n + 1)) f]
            show Spec.map _ ≫ Spec.map _ ≫ Limits.colimit.ι (glueFunctor 𝒪 π X xb xt G a RC (n + 1)) C =
              Spec.map _ ≫ Spec.map _ ≫ Limits.colimit.ι (glueFunctor 𝒪 π X xb xt G a RC (n + 1)) C
            rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
              ← CommRingCat.ofHom_comp, factor_comp_chartResBar] } }
  refine ⟨Limits.colimit.desc (glueFunctor 𝒪 π X xb xt G a RC n) c, fun C => ?_⟩
  unfold Yι
  exact Limits.colimit.ι_desc c C

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
theorem top_le_preimage_YV (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    (⊤ : ((glueFunctor 𝒪 π X xb xt G a RC n).obj C).Opens) ≤ (Yι 𝒪 π X xb xt G a RC n C) ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC n C) :=
  fun y _ => ⟨y, rfl⟩

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem Yι_appLE_injective (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    Function.Injective ((Yι 𝒪 π X xb xt G a RC n C).appLE (YV 𝒪 π X xb xt G a RC n C) ⊤
      (top_le_preimage_YV 𝒪 π X xb xt G a RC n C)) := by
  intro s s' h
  obtain ⟨t, rfl⟩ := (Ychart 𝒪 π X xb xt G a RC n C).surjective s
  obtain ⟨t', rfl⟩ := (Ychart 𝒪 π X xb xt G a RC n C).surjective s'
  rw [appLE_Ychart, appLE_Ychart] at h
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of _)).hom h
  rw [CategoryTheory.Iso.inv_hom_id_apply, CategoryTheory.Iso.inv_hom_id_apply] at this
  rw [this]

noncomputable def redChart (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    (glueFunctor 𝒪 π X xb xt G a RC n).obj C ⟶ (glueFunctor 𝒪 π X xb xt G a RC (n + 1)).obj C :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
    (show ChartRing.IA 𝒪 π X xb xt G a (RC C) (n + 1) ≤ ChartRing.IA 𝒪 π X xb xt G a (RC C) n from
      Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ (n + 1))))))

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem redChart_appLE_ΓSpecIso_inv (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a)
    (x : ↥(FixedPoints.subalgebra 𝒪 (RC C).R G)) :
    (redChart 𝒪 π X xb xt G a RC n C).appLE ⊤ ⊤ le_top
        ((Scheme.ΓSpecIso (CommRingCat.of _)).inv (Ideal.Quotient.mk (ChartRing.IA 𝒪 π X xb xt G a (RC C) (n + 1)) x)) =
      (Scheme.ΓSpecIso (CommRingCat.of _)).inv (Ideal.Quotient.mk (ChartRing.IA 𝒪 π X xb xt G a (RC C) n) x) := by
  have hle : ChartRing.IA 𝒪 π X xb xt G a (RC C) (n + 1) ≤ ChartRing.IA 𝒪 π X xb xt G a (RC C) n :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ (n + 1)))
  have htop : (redChart 𝒪 π X xb xt G a RC n C).appLE ⊤ ⊤ le_top =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hle))).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [htop]
  have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.factor hle))
  have happ := congrArg (fun k => k.hom (Ideal.Quotient.mk _ x)) hnat
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Ideal.Quotient.factor_mk] at happ
  exact happ.symm

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem yt_appLE_comp_Yι_appLE (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a)
    (yt : Yglue 𝒪 π X xb xt G a RC n ⟶ Yglue 𝒪 π X xb xt G a RC (n + 1))
    (EV : YV 𝒪 π X xb xt G a RC n C ≤ yt ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC (n + 1) C)) :
    yt.appLE (YV 𝒪 π X xb xt G a RC (n + 1) C) (YV 𝒪 π X xb xt G a RC n C) EV ≫
      (Yι 𝒪 π X xb xt G a RC n C).appLE (YV 𝒪 π X xb xt G a RC n C) ⊤ (top_le_preimage_YV 𝒪 π X xb xt G a RC n C) =
      yt.app (YV 𝒪 π X xb xt G a RC (n + 1) C) ≫
        (Yι 𝒪 π X xb xt G a RC n C).appLE (yt ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC (n + 1) C)) ⊤
          ((top_le_preimage_YV 𝒪 π X xb xt G a RC n C).trans ((Yι 𝒪 π X xb xt G a RC n C).preimage_mono EV)) := by
  show (yt.app _ ≫ (Yglue 𝒪 π X xb xt G a RC n).presheaf.map (homOfLE EV).op) ≫ _ = _
  rw [Category.assoc, Scheme.Hom.map_appLE]

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem Yι_appLE_comp_redChart_appLE (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    (Yι 𝒪 π X xb xt G a RC (n + 1) C).appLE (YV 𝒪 π X xb xt G a RC (n + 1) C) ⊤ (top_le_preimage_YV 𝒪 π X xb xt G a RC (n + 1) C) ≫
      (redChart 𝒪 π X xb xt G a RC n C).appLE ⊤ ⊤ le_top =
      (Yι 𝒪 π X xb xt G a RC (n + 1) C).app (YV 𝒪 π X xb xt G a RC (n + 1) C) ≫
        (redChart 𝒪 π X xb xt G a RC n C).appLE ((Yι 𝒪 π X xb xt G a RC (n + 1) C) ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC (n + 1) C)) ⊤
          ((le_top).trans ((redChart 𝒪 π X xb xt G a RC n C).preimage_mono (top_le_preimage_YV 𝒪 π X xb xt G a RC (n + 1) C))) := by
  show ((Yι 𝒪 π X xb xt G a RC (n + 1) C).app _ ≫
    ((glueFunctor 𝒪 π X xb xt G a RC (n + 1)).obj C).presheaf.map (homOfLE (top_le_preimage_YV 𝒪 π X xb xt G a RC (n + 1) C)).op) ≫ _ = _
  rw [Category.assoc, Scheme.Hom.map_appLE]

omit 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat haff G a ha_over ha_xt hcov in

theorem comp_appLE_retype {X' Y' Z' : Scheme.{0}} (f : X' ⟶ Y') (g : Y' ⟶ Z') (U : Z'.Opens) (V : X'.Opens)
    (e : V ≤ (f ≫ g) ⁻¹ᵁ U) (e' : V ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U)) :
    (f ≫ g).appLE U V e = g.app U ≫ f.appLE (g ⁻¹ᵁ U) V e' :=
  Scheme.Hom.comp_appLE f g U V e

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem yt_app_comp_Yι_appLE (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a)
    (yt : Yglue 𝒪 π X xb xt G a RC n ⟶ Yglue 𝒪 π X xb xt G a RC (n + 1))
    (hytC : Yι 𝒪 π X xb xt G a RC n C ≫ yt = redChart 𝒪 π X xb xt G a RC n C ≫ Yι 𝒪 π X xb xt G a RC (n + 1) C)
    (EV : YV 𝒪 π X xb xt G a RC n C ≤ yt ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC (n + 1) C)) :
    yt.app (YV 𝒪 π X xb xt G a RC (n + 1) C) ≫
        (Yι 𝒪 π X xb xt G a RC n C).appLE (yt ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC (n + 1) C)) ⊤
          ((top_le_preimage_YV 𝒪 π X xb xt G a RC n C).trans ((Yι 𝒪 π X xb xt G a RC n C).preimage_mono EV)) =
      (Yι 𝒪 π X xb xt G a RC (n + 1) C).app (YV 𝒪 π X xb xt G a RC (n + 1) C) ≫
        (redChart 𝒪 π X xb xt G a RC n C).appLE ((Yι 𝒪 π X xb xt G a RC (n + 1) C) ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC (n + 1) C)) ⊤
          ((le_top).trans ((redChart 𝒪 π X xb xt G a RC n C).preimage_mono (top_le_preimage_YV 𝒪 π X xb xt G a RC (n + 1) C))) := by
  have E : (⊤ : ((glueFunctor 𝒪 π X xb xt G a RC n).obj C).Opens) ≤
      (Yι 𝒪 π X xb xt G a RC n C ≫ yt) ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC (n + 1) C) := by
    rw [Scheme.Hom.comp_preimage]
    exact (top_le_preimage_YV 𝒪 π X xb xt G a RC n C).trans ((Yι 𝒪 π X xb xt G a RC n C).preimage_mono EV)
  have E' : (⊤ : ((glueFunctor 𝒪 π X xb xt G a RC n).obj C).Opens) ≤
      (redChart 𝒪 π X xb xt G a RC n C ≫ Yι 𝒪 π X xb xt G a RC (n + 1) C) ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC (n + 1) C) := fun y _ => by
    rw [Scheme.Hom.comp_preimage]; exact ⟨_, rfl⟩
  have star := appLE_congr_hom hytC (YV 𝒪 π X xb xt G a RC (n + 1) C) ⊤ E E'
  rw [comp_appLE_retype _ _ _ _ E ((top_le_preimage_YV 𝒪 π X xb xt G a RC n C).trans ((Yι 𝒪 π X xb xt G a RC n C).preimage_mono EV)),
    comp_appLE_retype _ _ _ _ E' ((le_top).trans ((redChart 𝒪 π X xb xt G a RC n C).preimage_mono
      (top_le_preimage_YV 𝒪 π X xb xt G a RC (n + 1) C)))] at star
  exact star

section ReadOff

variable (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ)
  (p : ∀ n : ℕ, X n ⟶ Yglue 𝒪 π X xb xt G a RC n)
  (yb : ∀ n : ℕ, Yglue 𝒪 π X xb xt G a RC n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
  (yt : ∀ n : ℕ, Yglue 𝒪 π X xb xt G a RC n ⟶ Yglue 𝒪 π X xb xt G a RC (n + 1))
  (hp : ∀ (n : ℕ) (C : GChain X xt G a), (C.W n).ι ≫ p n = pChart 𝒪 π X xb xt G a RC n C)
  (hyb : ∀ (n : ℕ) (C : GChain X xt G a), Yι 𝒪 π X xb xt G a RC n C ≫ yb n =
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap (ChartRing.IA 𝒪 π X xb xt G a (RC C) n)
      (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 (RC C).R G))
      (by rw [ChartRing.IA, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))
  (hyt : ∀ (n : ℕ) (C : GChain X xt G a), Yι 𝒪 π X xb xt G a RC n C ≫ yt n =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (show ChartRing.IA 𝒪 π X xb xt G a (RC C) (n + 1) ≤ ChartRing.IA 𝒪 π X xb xt G a (RC C) n from
        Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ (n + 1)))))) ≫ Yι 𝒪 π X xb xt G a RC (n + 1) C)

include hπ hcart hflat ha_xt hcov hp hyb in
omit hdvr hcomplete hproper haff ha_over in

theorem ro_p_over : p n ≫ yb n = xb n := by
  let 𝒲 := (X n).openCoverOfIsOpenCover (fun C : GChain X xt G a => C.W n)
    (isOpenCover_W X xt G a (exists_gchain 𝒪 π hπ X xb xt hcart hflat G a ha_xt hcov) n)
  refine Scheme.Cover.hom_ext 𝒲 _ _ fun C => ?_
  change (C.W n).ι ≫ p n ≫ yb n = (C.W n).ι ≫ xb n
  rw [reassoc_of% (hp n C), pChart, Category.assoc, Category.assoc]
  erw [hyb n C]
  rw [← Spec.map_comp, ChartRing.isoSpec_hom', Category.assoc, ← Spec.map_comp]
  apply eq_of_secOf_eq
  intro x
  obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [secOf_comp_SpecMap, secOf_isoSpec_hom, secOf_ι_comp, ← (RC C).lvl_algebraMap n o]
  rfl

include hπ hcart hflat ha_xt hcov hp hyt in
omit hdvr hcomplete hproper haff ha_over in

theorem ro_p_xt : xt n ≫ p (n + 1) = p n ≫ yt n := by
  let 𝒲 := (X n).openCoverOfIsOpenCover (fun C : GChain X xt G a => C.W n)
    (isOpenCover_W X xt G a (exists_gchain 𝒪 π hπ X xb xt hcart hflat G a ha_xt hcov) n)
  refine Scheme.Cover.hom_ext 𝒲 _ _ fun C => ?_
  change (C.W n).ι ≫ xt n ≫ p (n + 1) = (C.W n).ι ≫ p n ≫ yt n
  have e1 : (C.W n).ι ≫ xt n = (xt n).resLE (C.W (n + 1)) (C.W n) (by rw [C.compat]) ≫ (C.W (n + 1)).ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  rw [reassoc_of% e1, hp (n + 1) C, reassoc_of% (hp n C), pChart, pChart,
    reassoc_of% (ChartRing.resLE_xt_comp_isoSpec_hom 𝒪 π X xb xt G a (RC C) n), Category.assoc, Category.assoc]
  erw [hyt n C]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  have hring : ∀ (h2 : ChartRing.IA 𝒪 π X xb xt G a (RC C) (n + 1) ≤ ChartRing.IA 𝒪 π X xb xt G a (RC C) n)
      (h3 : Ideal.span {algebraMap 𝒪 (RC C).R π ^ (n + 1 + 1)} ≤ Ideal.span {algebraMap 𝒪 (RC C).R π ^ (n + 1)}),
      CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) (n + 1)) ≫ CommRingCat.ofHom (Ideal.Quotient.factor h3) =
      CommRingCat.ofHom (Ideal.Quotient.factor h2) ≫ CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n) := by
    intro h2 h3
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_))
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, ChartRing.ιbar, Ideal.quotientMap_mk,
      Ideal.Quotient.factor_mk]
  rw [hring]

include hπ hcart hflat ha_xt hcov hp in
omit hdvr hcomplete hproper haff ha_over in

theorem ro_p_inv (g : G) : (a n g).hom ≫ p n = p n := by
  let 𝒲 := (X n).openCoverOfIsOpenCover (fun C : GChain X xt G a => C.W n)
    (isOpenCover_W X xt G a (exists_gchain 𝒪 π hπ X xb xt hcart hflat G a ha_xt hcov) n)
  refine Scheme.Cover.hom_ext 𝒲 _ _ fun C => ?_
  change (C.W n).ι ≫ (a n g).hom ≫ p n = (C.W n).ι ≫ p n
  have e1 : (C.W n).ι ≫ (a n g).hom = (a n g).hom.resLE (C.W n) (C.W n) (by rw [C.stable]) ≫ (C.W n).ι :=
    (Scheme.Hom.resLE_comp_ι _ _).symm
  rw [reassoc_of% e1, hp, pChart, ← Category.assoc,
    ChartRing.resLE_smul_comp_isoSpec_hom 𝒪 π X xb xt G a (RC C) n g
      (ChartRing.span_pow_le_comap_toRingHom 𝒪 π X xb xt G a (RC C) n g⁻¹),
    Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp]
  have hring : CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n) ≫
      CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {algebraMap 𝒪 (RC C).R π ^ (n + 1)})
        (MulSemiringAction.toRingHom G (RC C).R g⁻¹) (ChartRing.span_pow_le_comap_toRingHom 𝒪 π X xb xt G a (RC C) n g⁻¹)) =
      CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n) := by
    refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, ChartRing.ιbar]
    exact ChartRing.quotientMap_toRingHom_quotientMap_algebraMap 𝒪 π X xb xt G a (RC C) n g⁻¹ _ _ z
  rw [hring]

include hyb hyt in
omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov hp in

theorem ro_yt_over : yt n ≫ yb (n + 1) =
    yb n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1)))))) := by
  apply Limits.colimit.hom_ext
  intro C
  change Yι 𝒪 π X xb xt G a RC n C ≫ yt n ≫ yb (n + 1) = Yι 𝒪 π X xb xt G a RC n C ≫ yb n ≫ _
  rw [reassoc_of% (hyt n C), reassoc_of% (hyb n C)]
  erw [Category.assoc, hyb (n + 1) C, ← Spec.map_comp, ← Spec.map_comp]
  have hring : ∀ (h1 : Ideal.span {π ^ (n + 1 + 1)} ≤ (ChartRing.IA 𝒪 π X xb xt G a (RC C) (n + 1)).comap
        (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 (RC C).R G)))
      (h2 : ChartRing.IA 𝒪 π X xb xt G a (RC C) (n + 1) ≤ ChartRing.IA 𝒪 π X xb xt G a (RC C) n)
      (h3 : Ideal.span {π ^ (n + 1 + 1)} ≤ Ideal.span {π ^ (n + 1)})
      (h4 : Ideal.span {π ^ (n + 1)} ≤ (ChartRing.IA 𝒪 π X xb xt G a (RC C) n).comap
        (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 (RC C).R G))),
      CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 (RC C).R G)) h1) ≫
        CommRingCat.ofHom (Ideal.Quotient.factor h2) =
      CommRingCat.ofHom (Ideal.Quotient.factor h3) ≫
        CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 (RC C).R G)) h4) := by
    intro h1 h2 h3 h4
    refine CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun o => ?_))
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Ideal.quotientMap_mk,
      Ideal.Quotient.factor_mk]
  rw [hring]

include hdvr hπ hcomplete hcart hproper hflat ha_xt hcov hp in
omit haff ha_over in

theorem ro_V_pre (C : GChain X xt G a) : (p n) ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC n C) = C.W n := by
  classical

  have hpt : ∀ (C' : GChain X xt G a) (y : ↥(C'.W n)),
      (p n).base y.1 = (Yι 𝒪 π X xb xt G a RC n C').base ((qChart 𝒪 π X xb xt G a RC n C').base y) := by
    intro C' y
    have := congrArg (fun f : (↑(C'.W n) : Scheme.{0}) ⟶ Yglue 𝒪 π X xb xt G a RC n => f.base y) (hp n C')
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    rw [pChart_eq] at this
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at this
    exact this
  ext x
  constructor
  · intro hx

    obtain ⟨z, hz⟩ : ∃ z, (Yι 𝒪 π X xb xt G a RC n C).base z = (p n).base x := hx
    obtain ⟨C', hxC'⟩ := exists_gchain 𝒪 π hπ X xb xt hcart hflat G a ha_xt hcov n x
    have h1 : (Yι 𝒪 π X xb xt G a RC n C).base z =
        (Yι 𝒪 π X xb xt G a RC n C').base ((qChart 𝒪 π X xb xt G a RC n C').base ⟨x, hxC'⟩) := by
      rw [hz]; exact hpt C' ⟨x, hxC'⟩
    obtain ⟨k, fC, fC', w, hw1, hw2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (glueFunctor 𝒪 π X xb xt G a RC n)).1 h1
    obtain ⟨y, hy⟩ := qChart_surjective 𝒪 hdvr π hπ hcomplete X xb xt G a RC n k w
    have hkC' : k ≤ C' := fC'.le
    have hkC : k ≤ C := fC.le
    have h2 : (qChart 𝒪 π X xb xt G a RC n C').base ⟨y.1, hkC' n y.2⟩ =
        (qChart 𝒪 π X xb xt G a RC n C').base ⟨x, hxC'⟩ := by
      rw [← glueFunctor_map_qChart_apply 𝒪 π X xb xt G a RC n hkC', hy]
      have : (homOfLE hkC' : k ⟶ C') = fC' := Subsingleton.elim _ _
      rw [this, hw2]
    obtain ⟨g, hg⟩ := exists_smul_of_qChart_eq 𝒪 π X xb xt G a RC n C' ⟨y.1, hkC' n y.2⟩ ⟨x, hxC'⟩ h2

    have hyC : (a n g).hom.base y.1 ∈ C.W n := by
      have : y.1 ∈ (a n g).hom ⁻¹ᵁ C.W n := by rw [C.stable]; exact hkC n y.2
      exact this
    simp only [hg] at hyC
    exact hyC
  · intro hx
    show (p n).base x ∈ YV 𝒪 π X xb xt G a RC n C
    rw [hpt C ⟨x, hx⟩]
    exact ⟨_, rfl⟩

include hyt in
omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov hp hyb in

theorem ro_V_compat (C : GChain X xt G a) :
    (yt n) ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC (n + 1) C) = YV 𝒪 π X xb xt G a RC n C := by
  classical

  let hle : ∀ C' : GChain X xt G a, ChartRing.IA 𝒪 π X xb xt G a (RC C') (n + 1) ≤ ChartRing.IA 𝒪 π X xb xt G a (RC C') n :=
    fun C' => Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ (n + 1)))
  let φ : ∀ C' : GChain X xt G a, (glueFunctor 𝒪 π X xb xt G a RC n).obj C' ⟶ (glueFunctor 𝒪 π X xb xt G a RC (n + 1)).obj C' := fun C' =>
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hle C')))
  have hyt' : ∀ C' : GChain X xt G a, Yι 𝒪 π X xb xt G a RC n C' ≫ yt n = φ C' ≫ Yι 𝒪 π X xb xt G a RC (n + 1) C' := hyt n

  have hnat : ∀ {C₁ C₂ : GChain X xt G a} (f : C₁ ⟶ C₂), (glueFunctor 𝒪 π X xb xt G a RC n).map f ≫ φ C₂ = φ C₁ ≫ (glueFunctor 𝒪 π X xb xt G a RC (n + 1)).map f := by
    intro C₁ C₂ f
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, factor_comp_chartResBar]

  have hφinj : ∀ C' : GChain X xt G a, Function.Injective (φ C').base := fun C' =>
    PrimeSpectrum.comap_injective_of_surjective _ (Ideal.Quotient.factor_surjective (hle C'))
  have hφsurj : ∀ C' : GChain X xt G a, Function.Surjective (φ C').base := by
    intro C' q
    have hq : q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor (hle C'))) := by
      rw [range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective (hle C'))]
      refine (PrimeSpectrum.mem_zeroLocus _ _).2 fun x hx => ?_
      rw [SetLike.mem_coe, RingHom.mem_ker] at hx
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hx' : x ∈ ChartRing.IA 𝒪 π X xb xt G a (RC C') n := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]; rwa [Ideal.Quotient.factor_mk] at hx
      apply q.2.mem_of_pow_mem 2
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2]
      · exact q.asIdeal.zero_mem
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
      refine Ideal.mem_span_singleton'.2 ⟨c * c * algebraMap 𝒪 _ π ^ n, ?_⟩
      ring
    obtain ⟨x, hx⟩ := hq
    exact ⟨x, hx⟩
  ext y
  constructor
  · intro hy
    obtain ⟨w, hw⟩ : ∃ w, (Yι 𝒪 π X xb xt G a RC (n + 1) C).base w = (yt n).base y := hy
    obtain ⟨C', z', rfl⟩ := Yι_jointly_surjective 𝒪 π X xb xt G a RC n y
    have h1 : (Yι 𝒪 π X xb xt G a RC (n + 1) C).base w = (Yι 𝒪 π X xb xt G a RC (n + 1) C').base ((φ C').base z') := by
      rw [hw, ← Scheme.Hom.comp_apply, hyt', Scheme.Hom.comp_apply]
    obtain ⟨k, fC, fC', u, hu1, hu2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (glueFunctor 𝒪 π X xb xt G a RC (n + 1))).1 h1
    obtain ⟨v, rfl⟩ := hφsurj k u
    have h2 : ((glueFunctor 𝒪 π X xb xt G a RC n).map fC').base v = z' := by
      apply hφinj C'
      rw [← Scheme.Hom.comp_apply, hnat, Scheme.Hom.comp_apply, hu2]
    refine ⟨((glueFunctor 𝒪 π X xb xt G a RC n).map fC).base v, ?_⟩
    have w1 : (glueFunctor 𝒪 π X xb xt G a RC n).map fC ≫ Yι 𝒪 π X xb xt G a RC n C = Yι 𝒪 π X xb xt G a RC n k :=
      Limits.colimit.w (glueFunctor 𝒪 π X xb xt G a RC n) fC
    have w2 : (glueFunctor 𝒪 π X xb xt G a RC n).map fC' ≫ Yι 𝒪 π X xb xt G a RC n C' = Yι 𝒪 π X xb xt G a RC n k :=
      Limits.colimit.w (glueFunctor 𝒪 π X xb xt G a RC n) fC'
    show (Yι 𝒪 π X xb xt G a RC n C).base (((glueFunctor 𝒪 π X xb xt G a RC n).map fC).base v) = (Yι 𝒪 π X xb xt G a RC n C').base z'
    rw [← h2, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, w1, w2]
  · rintro ⟨z, hz⟩
    refine ⟨(φ C).base z, ?_⟩
    show (Yι 𝒪 π X xb xt G a RC (n + 1) C).base ((φ C).base z) = (yt n).base y
    rw [← hz, ← Scheme.Hom.comp_apply, ← hyt', Scheme.Hom.comp_apply]

omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in

theorem appLE_Yι_injective (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) (C : GChain X xt G a) :
    Function.Injective ((Yι 𝒪 π X xb xt G a RC n C).appLE (YV 𝒪 π X xb xt G a RC n C) ⊤
      (by rw [YV, Scheme.Hom.preimage_opensRange])) := by
  intro s t hst

  have hs : s = Ychart 𝒪 π X xb xt G a RC n C ((Ychart 𝒪 π X xb xt G a RC n C).symm s) := ((Ychart _ _ _ _ _ _ _ RC n C).apply_symm_apply s).symm
  have ht : t = Ychart 𝒪 π X xb xt G a RC n C ((Ychart 𝒪 π X xb xt G a RC n C).symm t) := ((Ychart _ _ _ _ _ _ _ RC n C).apply_symm_apply t).symm
  rw [hs, ht, appLE_Ychart, appLE_Ychart] at hst
  have := (Scheme.ΓSpecIso (CommRingCat.of _)).symm.commRingCatIsoToRingEquiv.injective hst
  rw [hs, ht, this]

include hp in
omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov hyb hyt in

theorem ro_chart_p (hVpre : ∀ (C : GChain X xt G a) (n : ℕ), (p n) ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC n C) = C.W n)
    (C : GChain X xt G a) (x : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C))) :
    (p n).appLE (YV 𝒪 π X xb xt G a RC n C) (C.W n) (by rw [hVpre]) (Ychart 𝒪 π X xb xt G a RC n C (Ideal.Quotient.mk _ x)) =
      (RC C).lvl n (Ideal.Quotient.mk _ (x : (RC C).R)) := by
  have e₂ : (⊤ : (↑(C.W n) : Scheme.{0}).Opens) ≤ (C.W n).ι ⁻¹ᵁ (C.W n) := fun y _ => y.2
  have hle : (⊤ : ((glueFunctor 𝒪 π X xb xt G a RC n).obj C).Opens) ≤
      (Yι 𝒪 π X xb xt G a RC n C) ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC n C) := by
    rw [YV, Scheme.Hom.preimage_opensRange]
  have hle' : (⊤ : (↑(C.W n) : Scheme.{0}).Opens) ≤
      (qChart 𝒪 π X xb xt G a RC n C ≫ Yι 𝒪 π X xb xt G a RC n C) ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC n C) :=
    fun y _ => ⟨(qChart 𝒪 π X xb xt G a RC n C).base y, rfl⟩

  have nat : ∀ {R S : CommRingCat.{0}} (φ : R ⟶ S) (r : R),
      (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) := by
    intro R S φ r
    change ((Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop) r = (φ ≫ (Scheme.ΓSpecIso S).inv) r
    rw [Scheme.ΓSpecIso_inv_naturality]

  have hT : (C.W n).ι.appLE (C.W n) ⊤ e₂ = (C.W n).topIso.inv := by
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl

  have h1 : (C.W n).topIso.inv ((p n).appLE (YV 𝒪 π X xb xt G a RC n C) (C.W n) (by rw [hVpre])
        (Ychart 𝒪 π X xb xt G a RC n C (Ideal.Quotient.mk _ x))) =
      (qChart 𝒪 π X xb xt G a RC n C).appLE ⊤ ⊤ le_top
        ((Yι 𝒪 π X xb xt G a RC n C).appLE (YV 𝒪 π X xb xt G a RC n C) ⊤ hle
          (Ychart 𝒪 π X xb xt G a RC n C (Ideal.Quotient.mk _ x))) := by
    rw [← hT]
    change ((p n).appLE (YV 𝒪 π X xb xt G a RC n C) (C.W n) (by rw [hVpre]) ≫ (C.W n).ι.appLE (C.W n) ⊤ e₂)
        (Ychart 𝒪 π X xb xt G a RC n C (Ideal.Quotient.mk _ x)) =
      ((Yι 𝒪 π X xb xt G a RC n C).appLE (YV 𝒪 π X xb xt G a RC n C) ⊤ hle ≫
        (qChart 𝒪 π X xb xt G a RC n C).appLE ⊤ ⊤ le_top) (Ychart 𝒪 π X xb xt G a RC n C (Ideal.Quotient.mk _ x))
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom ((hp n C).trans (pChart_eq 𝒪 π X xb xt G a RC n C)) (YV 𝒪 π X xb xt G a RC n C) ⊤ _ hle']

  have h2 : (qChart 𝒪 π X xb xt G a RC n C).appLE ⊤ ⊤ le_top
        ((Yι 𝒪 π X xb xt G a RC n C).appLE (YV 𝒪 π X xb xt G a RC n C) ⊤ hle
          (Ychart 𝒪 π X xb xt G a RC n C (Ideal.Quotient.mk _ x))) =
      (C.W n).topIso.inv ((RC C).lvl n (Ideal.Quotient.mk _ (x : (RC C).R))) := by
    rw [appLE_Ychart]
    have hD : (qChart 𝒪 π X xb xt G a RC n C).appLE ⊤ ⊤ le_top = (qChart 𝒪 π X xb xt G a RC n C).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    rw [hD]
    change (C.W n).toSpecΓ.appTop
        ((Spec.map (CommRingCat.ofHom ((RC C).lvl n).toRingHom)).appTop
          ((Spec.map (CommRingCat.ofHom (ChartRing.ιbar 𝒪 π X xb xt G a (RC C) n))).appTop
            ((Scheme.ΓSpecIso (CommRingCat.of _)).inv (Ideal.Quotient.mk _ x)))) = _
    rw [Scheme.Opens.toSpecΓ_appTop, nat, nat]
    change (C.W n).topIso.inv (((Scheme.ΓSpecIso Γ(X n, C.W n)).inv ≫ (Scheme.ΓSpecIso Γ(X n, C.W n)).hom) _) = _
    rw [Iso.inv_hom_id]
    rfl

  exact (ConcreteCategory.injective_of_mono_of_preservesPullback (C.W n).topIso.inv) (h1.trans h2)

include hyt in
omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov hp hyb in

theorem ro_chart_yt (hVcompat : ∀ (C : GChain X xt G a) (n : ℕ),
      (yt n) ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC (n + 1) C) = YV 𝒪 π X xb xt G a RC n C)
    (C : GChain X xt G a) (x : ↥(ChartRing.A 𝒪 π X xb xt G a (RC C))) :
    (yt n).appLE (YV 𝒪 π X xb xt G a RC (n + 1) C) (YV 𝒪 π X xb xt G a RC n C) (by rw [hVcompat])
      (Ychart 𝒪 π X xb xt G a RC (n + 1) C (Ideal.Quotient.mk _ x)) = Ychart 𝒪 π X xb xt G a RC n C (Ideal.Quotient.mk _ x) := by
  have EV : YV 𝒪 π X xb xt G a RC n C ≤ (yt n) ⁻¹ᵁ (YV 𝒪 π X xb xt G a RC (n + 1) C) := by rw [hVcompat]
  have hytC : Yι 𝒪 π X xb xt G a RC n C ≫ yt n = redChart 𝒪 π X xb xt G a RC n C ≫ Yι 𝒪 π X xb xt G a RC (n + 1) C :=
    hyt n C
  have hmor := (yt_appLE_comp_Yι_appLE 𝒪 π X xb xt G a RC n C (yt n) EV).trans
    ((yt_app_comp_Yι_appLE 𝒪 π X xb xt G a RC n C (yt n) hytC EV).trans
      (Yι_appLE_comp_redChart_appLE 𝒪 π X xb xt G a RC n C).symm)
  apply Yι_appLE_injective 𝒪 π X xb xt G a RC n C
  rw [appLE_Ychart, ← CommRingCat.comp_apply, hmor, CommRingCat.comp_apply, appLE_Ychart]
  exact redChart_appLE_ΓSpecIso_inv 𝒪 π X xb xt G a RC n C x

include hyb in
omit hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov hp hyt in

theorem ro_chart_yb (C : GChain X xt G a) (o : 𝒪) :
    Ychart 𝒪 π X xb xt G a RC n C (Ideal.Quotient.mk _ (algebraMap 𝒪 ↥(ChartRing.A 𝒪 π X xb xt G a (RC C)) o)) =
      (yb n).appLE ⊤ (YV 𝒪 π X xb xt G a RC n C) le_top
        ((Scheme.ΓSpecIso (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))).inv (Ideal.Quotient.mk _ o)) := by
  apply appLE_Yι_injective 𝒪 π X xb xt G a RC n C
  rw [appLE_Ychart, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  rw [appLE_congr_hom (hyb n C) ⊤ ⊤ _ le_top, Fib7.appLE_top_top, ← CommRingCat.comp_apply]
  erw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

end ReadOff
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12 P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12.GChain P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12.ChartRing"

include hdvr hπ hcomplete hcart hproper hflat haff ha_over ha_xt hcov in
omit hOI hLD in

theorem nonempty_pieces (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) :
    Nonempty (Pieces 𝒪 π X xb xt G a RC) := by
  classical
  haveI hOI : ∀ (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ) {C' C : GChain X xt G a} (f : C' ⟶ C),
      IsOpenImmersion ((glueFunctor 𝒪 π X xb xt G a RC n).map f) :=
    fun RC n C' C f => isOpenImmersion_glueFunctor_map 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper G a RC n f
  haveI hLD : ∀ (RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C) (n : ℕ),
      ((glueFunctor 𝒪 π X xb xt G a RC n) ⋙ Scheme.forget).IsLocallyDirected :=
    fun RC n => isLocallyDirected_glueFunctor 𝒪 hdvr π hπ hcomplete X xb xt hproper G a RC n
  choose p hp using fun n => exists_p 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat haff G a ha_over ha_xt hcov RC n
  choose yb hyb using fun n => exists_yb 𝒪 π X xb xt G a RC n
  choose yt hyt using fun n => exists_yt 𝒪 π X xb xt G a RC n
  have hVpre := fun (C : GChain X xt G a) (n : ℕ) =>
    ro_V_pre 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat G a ha_xt hcov RC n p hp C
  have hVcompat := fun (C : GChain X xt G a) (n : ℕ) => ro_V_compat 𝒪 π X xb xt G a RC n yt hyt C
  exact ⟨{
    Y := Yglue 𝒪 π X xb xt G a RC
    yb := yb
    yt := yt
    p := p
    p_over := fun n => ro_p_over 𝒪 π hπ X xb xt hcart hflat G a ha_xt hcov RC n p yb hp hyb
    p_xt := fun n => ro_p_xt 𝒪 π hπ X xb xt hcart hflat G a ha_xt hcov RC n p yt hp hyt
    p_inv := fun n g => ro_p_inv 𝒪 π hπ X xb xt hcart hflat G a ha_xt hcov RC n p hp g
    yt_over := fun n => ro_yt_over 𝒪 π X xb xt G a RC n yb yt hyb hyt
    V := fun C n => YV 𝒪 π X xb xt G a RC n C
    V_affine := fun C n => YV_affine 𝒪 π X xb xt G a RC n C
    V_pre := hVpre
    V_compat := hVcompat
    V_cover := fun n y => YV_cover 𝒪 π X xb xt G a RC n y
    chart := fun C n => Ychart 𝒪 π X xb xt G a RC n C
    chart_p := fun C n x => ro_chart_p 𝒪 π X xb xt G a RC n p hp hVpre C x
    chart_yt := fun C n x => ro_chart_yt 𝒪 π X xb xt G a RC n yt hyt hVcompat C x
    chart_yb := fun C n o => ro_chart_yb 𝒪 π X xb xt G a RC n yb hyb C o }⟩

end Charts
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12 P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12.GChain P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12.ChartRing"

end F4Cover12
p2m_reactivate "P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12 P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12.GChain P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen.F4Cover12.ChartRing"

open F4Cover12 in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hproper : ∀ n : ℕ, IsProper (xb n)) (hflat : ∀ n : ℕ, Flat (xb n))
    (haff : ∀ (n : ℕ) (S : Set (X n)), S.Finite → ∃ U : (X n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (X n)))
    (G : Type) [Group G] [Finite G] (a : ∀ n : ℕ, G →* Aut (X n))
    (ha_over : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (hcov : ∀ x : X 0, ∃ U : (X 0).Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (a 0 g).hom ⁻¹ᵁ U = U) :
    Nonempty (TowerQuotientDatum 𝒪 π X xb xt G a) := by
  classical

  have RC : ∀ C : GChain X xt G a, ChartRing 𝒪 π X xb xt G a C := fun C =>
    (nonempty_chartRing 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat G a ha_over ha_xt C).some
  obtain ⟨P⟩ := nonempty_pieces 𝒪 hdvr π hπ hcomplete X xb xt hcart hproper hflat haff G a ha_over ha_xt hcov RC
  exact ⟨{
    Y := P.Y, yb := P.yb, yt := P.yt,
    yt_isPullback := yt_isPullback_of 𝒪 π X xb xt G a P,
    yb_isProper := yb_isProper_of 𝒪 hdvr π hπ hcomplete X xb xt hproper G a P,
    yb_flat := yb_flat_of 𝒪 hdvr π hπ X xb xt G a P,
    p := P.p, p_over := P.p_over, p_xt := P.p_xt,
    p_isPullback := p_isPullback_of 𝒪 π X xb xt hcart G a P,
    p_inv := P.p_inv,
    p_isFinite := p_isFinite_of 𝒪 hdvr π hπ hcomplete X xb xt G a P,
    p_surjective := p_surjective_of 𝒪 hdvr π hπ hcomplete X xb xt G a P,
    p_epi_loc := p_epi_loc_of 𝒪 hdvr π hπ hcomplete X xb xt G a P,
    univ_loc := univ_loc_of 𝒪 hdvr π hπ hcomplete X xb xt G a P,
    fib := fib_of 𝒪 hdvr π hπ hcomplete X xb xt G a P,
    adicFib := adicFib_of 𝒪 hdvr π hπ hcomplete X xb xt G a P }⟩

end S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_nonempty_towerQuotientDatum_of_isProper_of_flat_of_forall_exists_isAffineOpen (solution)
