-- Prove2me | solution 1 for AlgebraicGeometry.Smooth.smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/64b3c9f9-15d7-5460-b8d1-dcb48cca34e2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.AlgebraicGeometry TrivSqZeroExt"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsOpenImmersion.lift Surjective Spec.map_comp_assoc SmoothOfRelativeDimension Scheme.Hom Smooth.exists_isStandardSmooth range_eq_range_of_surjective IsAffineOpen.SpecMap_appLE_fromSpec LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Smooth IsOpenImmersion Spec.map_injective Scheme.Hom.finiteType_appLE Spec.preimage isAffineOpen_top IsAffineOpen IsOpenImmersion.lift_fac Scheme.Hom.comp_apply Scheme.ΓSpecIso"
namespace Dim1PosChar
p2m_open "AlgebraicGeometry"

theorem isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hP0 : P = ⊥
  · subst hP0
    refine le_antisymm ?_ bot_le
    intro n hn
    rw [Ideal.mem_bot]
    by_contra hne
    obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes (n.natAbs + 1)
    have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).irreducible
    have hmem : n ∈ Ideal.span {(p : ℤ)} := by
      have := (Ideal.mem_sInf.mp hn) (show Ideal.span {(p : ℤ)} ∈ {J : Ideal ℤ | ⊥ ≤ J ∧ J.IsMaximal} from ⟨bot_le, hmax⟩)
      exact this
    rw [Ideal.mem_span_singleton] at hmem
    have h1 : (p : ℤ).natAbs ∣ n.natAbs := Int.natAbs_dvd_natAbs.mpr hmem
    rw [Int.natAbs_natCast] at h1
    have h2 : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hne
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero h2) h1
    omega
  · have hmax : P.IsMaximal := hP.isMaximal hP0
    refine le_antisymm (sInf_le ⟨le_rfl, hmax⟩) ?_
    exact le_sInf fun J hJ => hJ.1

theorem exists_prime_charP_of_finiteType {K : Type u} [Field K] (ψ : ℤ →+* K) (hψ : ψ.FiniteType) :
    ∃ p : ℕ, p.Prime ∧ CharP K p := by
  haveI := isJacobsonRing_int
  obtain ⟨p, hp⟩ := CharP.exists K
  refine ⟨p, ?_, hp⟩
  rcases CharP.char_is_prime_or_zero K p with h | h
  · exact h
  · exfalso
    subst h
    haveI : CharZero K := CharP.charP_to_charZero K
    have hψ' : ψ = algebraMap ℤ K := RingHom.ext_int ψ _
    have hfin : (algebraMap ℤ K).Finite := by
      rw [← hψ']; exact RingHom.finite_iff_finiteType_of_isJacobsonRing.mpr hψ
    have hint : Algebra.IsIntegral ℤ K := by
      have : Module.Finite ℤ K := RingHom.finite_algebraMap.mp hfin
      exact Algebra.IsIntegral.of_finite ℤ K
    have h2 : _root_.IsIntegral ℤ ((algebraMap ℚ K) (2⁻¹ : ℚ)) := hint.isIntegral _
    rw [isIntegral_algebraMap_iff (algebraMap ℚ K).injective] at h2
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp h2
    have : (2 : ℚ) * (y : ℚ) = 1 := by
      rw [show ((y : ℤ) : ℚ) = 2⁻¹ from hy]; norm_num
    have h2y : (2 * y : ℤ) = 1 := by exact_mod_cast this
    omega

theorem subsingleton_and_nonempty_of_line {ι k : Type*} [Field k] (v : ι → k)
    (h : ∀ w : ι → k, ∃! c : k, w = c • v) : Subsingleton ι ∧ Nonempty ι := by
  classical
  constructor
  · by_contra hι
    rw [not_subsingleton_iff_nontrivial] at hι
    obtain ⟨i, j, hij⟩ := hι
    by_cases hv : v = 0
    · obtain ⟨c, hc, -⟩ := h (fun _ => 1)
      have := congr_fun hc i
      simp [hv] at this
    · obtain ⟨l, hl⟩ : ∃ l, v l ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hv (funext hall)
      obtain ⟨i', hi'⟩ : ∃ i', i' ≠ l := by
        by_cases hil : i = l
        · exact ⟨j, fun h => hij (hil.trans h.symm)⟩
        · exact ⟨i, hil⟩
      obtain ⟨c, hc, -⟩ := h (v + Pi.single i' 1)
      have h1 := congr_fun hc l
      have h2 := congr_fun hc i'
      simp only [Pi.add_apply, Pi.single_eq_of_ne hi'.symm, add_zero, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_same] at h1 h2
      have hc1 : c = 1 := by
        have : (c - 1) * v l = 0 := by rw [sub_mul, one_mul, ← h1, sub_self]
        rcases mul_eq_zero.mp this with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hl
      rw [hc1, one_mul] at h2
      simp at h2
  · by_contra hι
    rw [not_nonempty_iff] at hι
    obtain ⟨c, -, huniq⟩ := h v
    have h0 : (0 : k) = c := huniq 0 (funext fun i => (IsEmpty.false i).elim)
    have h1 : (1 : k) = c := huniq 1 (funext fun i => (IsEmpty.false i).elim)
    exact zero_ne_one (h0.trans h1.symm)

private abbrev _root_.AlgebraicGeometry.Dim1PosChar.scale (k : Type u) [Field k] (c : k) : DualNumber k →+* DualNumber k :=
  (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom

p2m_export "AlgebraicGeometry.Dim1PosChar" "scale"
section Ring

variable {R A k : Type u} [CommRing R] [CommRing A] [Algebra R A] [Field k] [Algebra A k]

structure IsTangent (R : Type u) [CommRing R] [Algebra R A] (τ : A →+* DualNumber k) : Prop where
  fst_apply : ∀ a, (τ a).fst = algebraMap A k a
  base : ∀ r, τ (algebraMap R A r) = inl (algebraMap A k (algebraMap R A r))

theorem IsTangent.scale {τ : A →+* DualNumber k} (hτ : IsTangent R τ) (c : k) :
    IsTangent R ((scale k c).comp τ) := by
  refine ⟨fun a => ?_, fun r => ?_⟩
  · simp [hτ.fst_apply a]
  · rw [RingHom.comp_apply, hτ.base r]
    ext <;> simp

variable [Algebra R k] [IsScalarTower R A k]

noncomputable def IsTangent.deriv {τ : A →+* DualNumber k} (hτ : IsTangent R τ) : Derivation R A k where
  toFun a := (τ a).snd
  map_add' a b := by simp
  map_smul' r a := by
    show (τ (r • a)).snd = r • (τ a).snd
    rw [Algebra.smul_def, map_mul, snd_mul, hτ.base r, hτ.fst_apply]
    simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  map_one_eq_zero' := by
    show (τ 1).snd = 0
    simp
  leibniz' a b := by
    show (τ (a * b)).snd = a • (τ b).snd + b • (τ a).snd
    rw [map_mul, snd_mul, hτ.fst_apply, hτ.fst_apply]
    simp [Algebra.smul_def, mul_comm]

@[scoped simp] theorem IsTangent.deriv_apply {τ : A →+* DualNumber k} (hτ : IsTangent R τ) (a : A) :
    hτ.deriv a = (τ a).snd := rfl

p2m_reactivate "P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.AlgebraicGeometry.Dim1PosChar.IsTangent"

noncomputable def ofDeriv (D : Derivation R A k) : A →+* DualNumber k where
  toFun a := (algebraMap A k a, D a)
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [map_mul, Derivation.leibniz, snd_mk, snd_mul, fst_mk, smul_eq_mul, Algebra.smul_def]
      simp [MulOpposite.smul_eq_mul_unop, mul_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp

omit [IsScalarTower R A k] in
theorem isTangent_ofDeriv (D : Derivation R A k) : IsTangent R (ofDeriv D) := by
  refine ⟨fun a => rfl, fun r => ?_⟩
  ext
  · rfl
  · show D (algebraMap R A r) = 0
    exact D.map_algebraMap r

theorem deriv_ofDeriv (D : Derivation R A k) : (isTangent_ofDeriv D).deriv = D := by
  ext a; rfl

omit [Algebra R k] [IsScalarTower R A k] in
theorem eq_of_snd_eq {τ τ' : A →+* DualNumber k} (hτ : IsTangent R τ) (hτ' : IsTangent R τ')
    (h : ∀ a, (τ a).snd = (τ' a).snd) : τ = τ' := by
  refine RingHom.ext fun a => ?_
  ext
  · rw [hτ.fst_apply, hτ'.fst_apply]
  · exact h a

variable {ι : Type*} (b : Module.Basis ι A Ω[A⁄R])

noncomputable def coord {τ : A →+* DualNumber k} (hτ : IsTangent R τ) : ι → k :=
  fun i => hτ.deriv.liftKaehlerDifferential (b i)

noncomputable def mulLeftLinear (c : k) : k →ₗ[A] k where
  toFun m := c * m
  map_add' m m' := mul_add c m m'
  map_smul' a m := by simp [Algebra.smul_def, mul_left_comm]

theorem coord_scale {τ : A →+* DualNumber k} (hτ : IsTangent R τ) (c : k) :
    coord b (hτ.scale c) = c • coord b hτ := by
  have key : (hτ.scale c).deriv.liftKaehlerDifferential =
      (mulLeftLinear (A := A) c).comp hτ.deriv.liftKaehlerDifferential := by
    refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun a => ?_)
    change (hτ.scale c).deriv.liftKaehlerDifferential (KaehlerDifferential.D R A a) =
      c * hτ.deriv.liftKaehlerDifferential (KaehlerDifferential.D R A a)
    rw [Derivation.liftKaehlerDifferential_comp_D, Derivation.liftKaehlerDifferential_comp_D]
    simp only [IsTangent.deriv_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
      Function.comp_apply, TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_eq_mul]
  funext i
  exact congrArg (fun f => f (b i)) key

theorem coord_injective {τ τ' : A →+* DualNumber k} (hτ : IsTangent R τ) (hτ' : IsTangent R τ')
    (h : coord b hτ = coord b hτ') : τ = τ' := by
  apply eq_of_snd_eq hτ hτ'
  have : hτ.deriv.liftKaehlerDifferential = hτ'.deriv.liftKaehlerDifferential :=
    b.ext fun i => congr_fun h i
  intro a
  rw [← hτ.deriv_apply, ← hτ'.deriv_apply, ← Derivation.liftKaehlerDifferential_comp_D hτ.deriv a, this,
    Derivation.liftKaehlerDifferential_comp_D]

theorem coord_surjective (w : ι → k) : ∃ (τ : A →+* DualNumber k) (hτ : IsTangent R τ), coord b hτ = w := by
  let g : Ω[A⁄R] →ₗ[A] k := b.constr ℕ w
  let D : Derivation R A k := g.compDer (KaehlerDifferential.D R A)
  refine ⟨ofDeriv D, isTangent_ofDeriv D, ?_⟩
  have key : (isTangent_ofDeriv D).deriv.liftKaehlerDifferential = g := by
    apply Derivation.liftKaehlerDifferential_unique
    rw [Derivation.liftKaehlerDifferential_comp, deriv_ofDeriv]
  funext i
  simp only [coord, key, g, Module.Basis.constr_basis]

theorem line_coord {ν : A →+* DualNumber k} (hν : IsTangent R ν)
    (hline : ∀ τ : A →+* DualNumber k, IsTangent R τ → ∃! c : k, τ = (scale k c).comp ν) :
    ∀ w : ι → k, ∃! c : k, w = c • coord b hν := by
  intro w
  obtain ⟨τ, hτ, rfl⟩ := coord_surjective (R := R) b w
  obtain ⟨c, hc, huniq⟩ := hline τ hτ
  refine ⟨c, ?_, fun c' hc' => ?_⟩
  · subst hc
    exact (coord_scale b hν c)
  · apply huniq c'
    apply coord_injective b hτ (hν.scale c')
    rw [hc', coord_scale]

end Ring
p2m_reactivate "P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.AlgebraicGeometry.Dim1PosChar.IsTangent"

section SchemeLevel

theorem subsingleton_primeSpectrum_dualNumber (k : Type u) [Field k] :
    Subsingleton (PrimeSpectrum (DualNumber k)) := by
  refine ⟨fun P Q => ?_⟩
  have key : ∀ (P : PrimeSpectrum (DualNumber k)) (x : DualNumber k), x ∈ P.asIdeal ↔ x.fst = 0 := by
    intro P x
    constructor
    · intro hx
      by_contra h
      have hu : IsUnit x := isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr h)
      exact P.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)
    · intro hx
      have hsq : x * x = 0 := by
        ext
        · simp [hx]
        · simp [snd_mul, hx]
      have : x * x ∈ P.asIdeal := by rw [hsq]; exact zero_mem _
      exact (P.2.mem_or_mem this).elim id id
  ext x
  rw [key P, key Q]

theorem surjective_specMap_fstHom (k : Type u) [Field k] :
    Function.Surjective (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) := by
  intro P
  exact ⟨(⊥ : PrimeSpectrum k), (subsingleton_primeSpectrum_dualNumber k).elim _ _⟩

variable {X : Scheme.{u}} {V : X.Opens} (hV : IsAffineOpen V)

noncomputable abbrev pt {B : Type u} [CommRing B] (τ : Γ(X, V) →+* B) : Spec (CommRingCat.of B) ⟶ X :=
  Spec.map (CommRingCat.ofHom τ) ≫ hV.fromSpec

theorem pt_injective {B : Type u} [CommRing B] {τ τ' : Γ(X, V) →+* B} (h : pt hV τ = pt hV τ') : τ = τ' := by
  have h1 : Spec.map (CommRingCat.ofHom τ) = Spec.map (CommRingCat.ofHom τ') := (cancel_mono hV.fromSpec).mp h
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  simpa using h2

theorem pt_comp {B C : Type u} [CommRing B] [CommRing C] (τ : Γ(X, V) →+* B) (σ : B →+* C) :
    pt hV (σ.comp τ) = Spec.map (CommRingCat.ofHom σ) ≫ pt hV τ := by
  simp only [pt, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U) (e : V ≤ f ⁻¹ᵁ U)
  [Algebra Γ(Y, U) Γ(X, V)] (halg : algebraMap Γ(Y, U) Γ(X, V) = (f.appLE U V e).hom)
  {k : Type u} [Field k] [Algebra Γ(X, V) k]

include hU halg in

theorem pt_mem_tangent {τ : Γ(X, V) →+* DualNumber k} (hτ : IsTangent Γ(Y, U) τ) :
    pt hV τ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ pt hV (algebraMap Γ(X, V) k) ≫ f ∧
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ pt hV τ = pt hV (algebraMap Γ(X, V) k) := by
  constructor
  · have key : f.appLE U V e ≫ CommRingCat.ofHom τ =
        f.appLE U V e ≫ CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp (algebraMap Γ(X, V) k)) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      change τ ((f.appLE U V e).hom r) = algebraMap k (DualNumber k) (algebraMap Γ(X, V) k ((f.appLE U V e).hom r))
      rw [← halg, hτ.base r, TrivSqZeroExt.algebraMap_eq_inl]
    have hVf : hV.fromSpec ≫ f = Spec.map (f.appLE U V e) ≫ hU.fromSpec :=
      (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e).symm
    calc pt hV τ ≫ f = Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (f.appLE U V e) ≫ hU.fromSpec := by
          rw [pt, Category.assoc, hVf]
      _ = Spec.map (f.appLE U V e ≫ CommRingCat.ofHom τ) ≫ hU.fromSpec := by rw [Spec.map_comp_assoc]
      _ = Spec.map (f.appLE U V e ≫ CommRingCat.ofHom
            ((algebraMap k (DualNumber k)).comp (algebraMap Γ(X, V) k))) ≫ hU.fromSpec := by rw [key]
      _ = Spec.map (CommRingCat.ofHom ((algebraMap k (DualNumber k)).comp (algebraMap Γ(X, V) k))) ≫
            hV.fromSpec ≫ f := by rw [Spec.map_comp_assoc, hVf]
      _ = pt hV ((algebraMap k (DualNumber k)).comp (algebraMap Γ(X, V) k)) ≫ f := by rw [pt, Category.assoc]
      _ = _ := by rw [pt_comp, Category.assoc]
  · rw [← pt_comp]
    congr 1
    exact RingHom.ext hτ.fst_apply

include hU halg in

theorem exists_isTangent_of_tangent (t : Spec (CommRingCat.of (DualNumber k)) ⟶ X)
    (ht : t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ pt hV (algebraMap Γ(X, V) k) ≫ f)
    (htx : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ t = pt hV (algebraMap Γ(X, V) k)) :
    ∃ (τ : Γ(X, V) →+* DualNumber k), IsTangent Γ(Y, U) τ ∧ pt hV τ = t := by

  have hrange : Set.range t ⊆ Set.range hV.fromSpec := by
    haveI : Surjective (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) :=
      ⟨surjective_specMap_fstHom k⟩
    rw [← range_eq_range_of_surjective (pt hV (algebraMap Γ(X, V) k)) t _ htx]
    rintro _ ⟨p, rfl⟩
    exact ⟨_, (Scheme.Hom.comp_apply _ _ p).symm⟩
  let t' := IsOpenImmersion.lift hV.fromSpec t hrange
  have ht' : t' ≫ hV.fromSpec = t := IsOpenImmersion.lift_fac _ _ _
  let τ : Γ(X, V) →+* DualNumber k := (Spec.preimage t').hom
  have hτ : Spec.map (CommRingCat.ofHom τ) = t' := by simp [τ]
  have hpt : pt hV τ = t := by rw [pt, hτ, ht']
  refine ⟨τ, ⟨fun a => ?_, fun r => ?_⟩, hpt⟩
  ·
    have h1 : pt hV ((TrivSqZeroExt.fstHom k k k).toRingHom.comp τ) = pt hV (algebraMap Γ(X, V) k) := by
      rw [pt_comp, hpt, htx]
    exact RingHom.congr_fun (pt_injective hV h1) a
  ·
    have hVf : hV.fromSpec ≫ f = Spec.map (f.appLE U V e) ≫ hU.fromSpec :=
      (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e).symm
    have h1 : Spec.map (f.appLE U V e ≫ CommRingCat.ofHom τ) ≫ hU.fromSpec =
        Spec.map (f.appLE U V e ≫ CommRingCat.ofHom
          ((algebraMap k (DualNumber k)).comp (algebraMap Γ(X, V) k))) ≫ hU.fromSpec := by
      rw [Spec.map_comp_assoc, Spec.map_comp_assoc, ← hVf]
      change pt hV τ ≫ f = pt hV ((algebraMap k (DualNumber k)).comp (algebraMap Γ(X, V) k)) ≫ f
      rw [hpt, ht, pt_comp, Category.assoc]
      rfl
    rw [cancel_mono] at h1
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    have h3 := RingHom.congr_fun h2 r
    change τ ((f.appLE U V e).hom r) = algebraMap k (DualNumber k) (algebraMap Γ(X, V) k ((f.appLE U V e).hom r)) at h3
    rw [← halg] at h3
    rw [h3, TrivSqZeroExt.algebraMap_eq_inl]

end SchemeLevel
p2m_reactivate "P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.AlgebraicGeometry.Dim1PosChar.IsTangent"

end AlgebraicGeometry.Dim1PosChar
p2m_reactivate "P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.AlgebraicGeometry.Dim1PosChar.IsTangent P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.AlgebraicGeometry.Dim1PosChar"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.AlgebraicGeometry.Dim1PosChar.IsTangent P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int.AlgebraicGeometry"

open AlgebraicGeometry.Dim1PosChar in
theorem solution

    (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] [Smooth f]

    (H : ∀ (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (x : Spec (CommRingCat.of k) ⟶ X),
      ∃ v : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
        v ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ x ≫ f ∧
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ v = x ∧
        ∀ t : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
          t ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫ x ≫ f →
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ t = x →
          ∃! c : k, t = Spec.map (CommRingCat.ofHom
            (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).toRingHom) ≫ v) :
    SmoothOfRelativeDimension 1 f := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hU, V, hV, hxV, e, hst⟩ := Smooth.exists_isStandardSmooth f x
  refine ⟨U, hU, V, hV, hxV, e, ?_⟩

  algebraize [(f.appLE U V e).hom]
  have halg : algebraMap Γ(Spec (CommRingCat.of R), U) Γ(X, V) = (f.appLE U V e).hom := rfl
  have hp : PrimeSpectrum Γ(X, V) := hV.primeIdealOf ⟨x, hxV⟩
  haveI : Nontrivial Γ(X, V) := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨hp⟩
  show Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Spec (CommRingCat.of R), U) Γ(X, V)
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  let b := Module.Free.chooseBasis Γ(X, V) Ω[Γ(X, V)⁄Γ(Spec (CommRingCat.of R), U)]
  rw [← b.mk_eq_rank'']

  have hft : ((f.appLE U V e).hom.comp
      ((((𝟙 (Spec (CommRingCat.of R)) : _ ⟶ _).appLE ⊤ U le_top).hom.comp
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap ℤ R))))).FiniteType := by
    refine RingHom.FiniteType.comp (Scheme.Hom.finiteType_appLE f hU hV e) ?_
    refine RingHom.FiniteType.comp ?_ ?_
    · exact Scheme.Hom.finiteType_appLE (𝟙 _) (isAffineOpen_top _) hU le_top
    refine RingHom.FiniteType.comp ?_ ?_
    · exact RingHom.FiniteType.of_surjective _ (fun y => ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y, by
        rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]⟩)
    · exact RingHom.finiteType_algebraMap.mpr inferInstance

  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(X, V)
  letI := Ideal.Quotient.field m
  obtain ⟨p, hpp, hchar⟩ := exists_prime_charP_of_finiteType ((Ideal.Quotient.mk m).comp _)
    (RingHom.FiniteType.comp (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective) hft)
  haveI := hchar
  haveI : Fact p.Prime := ⟨hpp⟩
  let k := AlgebraicClosure (Γ(X, V) ⧸ m)

  obtain ⟨v, hv, hvx, hall⟩ := H k p (pt hV (algebraMap Γ(X, V) k))
  obtain ⟨ν, hν, rfl⟩ := exists_isTangent_of_tangent hV f hU e halg v hv hvx
  have hline : ∀ τ : Γ(X, V) →+* DualNumber k, IsTangent Γ(Spec (CommRingCat.of R), U) τ →
      ∃! c : k, τ = (scale k c).comp ν := by
    intro τ hτ
    obtain ⟨hτ1, hτ2⟩ := pt_mem_tangent hV f hU e halg hτ
    obtain ⟨c, hc, huniq⟩ := hall (pt hV τ) hτ1 hτ2
    refine ⟨c, ?_, fun c' hc' => huniq c' ?_⟩
    · apply pt_injective hV
      rw [hc]
      exact (pt_comp hV ν (scale k c)).symm
    · have hc'' : τ = (scale k c').comp ν := hc'
      show pt hV τ = Spec.map _ ≫ pt hV ν
      rw [hc'']
      exact pt_comp hV ν (scale k c')

  obtain ⟨hs, hn⟩ := subsingleton_and_nonempty_of_line (coord b hν) (line_coord b hν hline)
  exact Cardinal.mk_eq_one _

end S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int
end P2MW
export P2MW.S_AlgebraicGeometry_Smooth_smoothOfRelativeDimension_one_of_forall_charP_exists_forall_existsUnique_eq_comp_of_finiteType_int (solution)
