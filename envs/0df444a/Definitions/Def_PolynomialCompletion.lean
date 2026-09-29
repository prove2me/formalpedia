-- Prove2me | Definitions.Def_PolynomialCompletion
-- name    : PolynomialCompletion
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/c10cb631-c7ee-5c24-82cc-8989bf6b5ade
-- title:
--   Adic completions: levelwise isomorphisms, localisation at a maximal ideal, power series
-- statement:
--   The first part transfers adic completions along compatible families of truncation isomorphisms. For ideals $I \subseteq R$ and $J \subseteq S$, [`AdicCompletion.factorPow_evalₐ`](../def/PolynomialCompletion.html#L12) records that the level-$n$ evaluation maps $\mathrm{AdicCompletion}\,I\,R \to R/I^n$ commute with the transition maps $R/I^n \to R/I^m$ for $m \le n$. Given ring isomorphisms $e_n : R/I^n \simeq S/J^n$ commuting with those transition maps, [`AdicCompletion.levelwiseHom`](../def/PolynomialCompletion.html#L33) is the induced ring homomorphism $\mathrm{AdicCompletion}\,I\,R \to \mathrm{AdicCompletion}\,J\,S$ characterised by $\mathrm{eval}_n \circ f = e_n \circ \mathrm{eval}_n$, and [`AdicCompletion.ofLevelwiseEquiv`](../def/PolynomialCompletion.html#L47) is the resulting ring isomorphism of completions, its inverse coming from the family $(e_n^{-1})$; `ofLevelwiseEquiv_of` says that it sends the image of $x \in R$ to the image of $y \in S$ whenever $e_n$ carries the class of $x$ to the class of $y$ at every level.
--
--   The second part treats a maximal ideal $q$ of a commutative ring $R$ and the local ring $R_q$ with maximal ideal $\mathfrak m$. It is shown that $\mathfrak m^n$ contracts to $q^n$ along $R \to R_q$, that the induced map `quotientPowMap` $: R/q^n \to R_q/\mathfrak m^n$ is bijective (surjectivity using that for $s \notin q$ there are $a$ and $c \in q^n$ with $as + c = 1$), giving the isomorphism `quotientPowEquiv` compatible with the transition maps, and hence [`AdicCompletion.localizationEquiv`](../def/PolynomialCompletion.html#L161), an isomorphism between the $q$-adic completion of $R$ and the $\mathfrak m$-adic completion of $R_q$ compatible with the maps from $R$.
--
--   Finally, for a field $k$, `idealOfVars σ k` is identified with the kernel of `constantCoeff`, hence is maximal, and is the only maximal ideal of $\mathrm{MvPolynomial}\,σ\,k$ containing all the variables. For finite $σ$ and such a maximal ideal $q$, `adicCompletionRingEquivMvPowerSeries` and its $k$-algebra refinement `adicCompletionAlgEquivMvPowerSeries` identify the $\mathfrak m$-adic completion of the local ring at $q$ with $\mathrm{MvPowerSeries}\,σ\,k$, sending the image of a polynomial to that polynomial viewed as a power series, in particular $X_i \mapsto X_i$.
--
--   **Relation to Mathlib.** Built on Mathlib's `AdicCompletion` together with its level maps and lifting lemmas, Mathlib's `MvPolynomial.idealOfVars` and Mathlib's identification `MvPowerSeries.toAdicCompletionAlgEquiv` of the completion of a polynomial ring at the ideal of the variables with a power series ring; the transfer along a levelwise family of isomorphisms and the comparison with the completion of the localisation at a maximal ideal are added here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PolynomialCompletion.lean

import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Localization.AtPrime.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AdicCompletion

section Levelwise

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)

theorem factorPow_evalₐ {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (evalₐ I n x) = evalₐ I m x := by
  induction x using AdicCompletion.induction_on with
  | _ a =>
    rw [evalₐ_mk, evalₐ_mk]
    simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    exact Ideal.mk_eq_mk I h a

variable (e : ∀ n, R ⧸ I ^ n ≃+* S ⧸ J ^ n)
  (he : ∀ {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n),
    Ideal.Quotient.factorPow J h (e n x) = e m (Ideal.Quotient.factorPow I h x))

include he in
theorem levelwise_compat {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp ((e n).toRingHom.comp (evalₐ I n).toRingHom)
      = (e m).toRingHom.comp (evalₐ I m).toRingHom := by
  ext x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  rw [he, factorPow_evalₐ]

noncomputable def levelwiseHom : AdicCompletion I R →+* AdicCompletion J S :=
  liftRingHom J (fun n => (e n).toRingHom.comp (evalₐ I n).toRingHom) (levelwise_compat I J e he)

@[simp] theorem evalₐ_levelwiseHom (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (levelwiseHom I J e he x) = e n (evalₐ I n x) :=
  evalₐ_liftRingHom J (fun n => (e n).toRingHom.comp (evalₐ I n).toRingHom)
    (levelwise_compat I J e he) n x

include he in
theorem he_symm {m n : ℕ} (h : m ≤ n) (y : S ⧸ J ^ n) :
    Ideal.Quotient.factorPow I h ((e n).symm y) = (e m).symm (Ideal.Quotient.factorPow J h y) := by
  apply (e m).injective
  rw [RingEquiv.apply_symm_apply, ← he, RingEquiv.apply_symm_apply]

noncomputable def ofLevelwiseEquiv : AdicCompletion I R ≃+* AdicCompletion J S :=
  RingEquiv.ofRingHom (levelwiseHom I J e he)
    (levelwiseHom J I (fun n => (e n).symm) (he_symm I J e he))
    (RingHom.ext fun y => ext_evalₐ fun n => by simp)
    (RingHom.ext fun x => ext_evalₐ fun n => by simp)

@[simp] theorem evalₐ_ofLevelwiseEquiv (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (ofLevelwiseEquiv I J e he x) = e n (evalₐ I n x) :=
  evalₐ_levelwiseHom I J e he n x

@[simp] theorem evalₐ_ofLevelwiseEquiv_symm (n : ℕ) (y : AdicCompletion J S) :
    evalₐ I n ((ofLevelwiseEquiv I J e he).symm y) = (e n).symm (evalₐ J n y) :=
  evalₐ_levelwiseHom J I (fun n => (e n).symm) (he_symm I J e he) n y

theorem ofLevelwiseEquiv_of (x : R) (y : S) (hxy : ∀ n, e n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ y) :
    ofLevelwiseEquiv I J e he (of I R x) = of J S y := by
  refine ext_evalₐ fun n => ?_
  rw [evalₐ_ofLevelwiseEquiv, evalₐ_of, evalₐ_of, hxy]

end Levelwise

end AdicCompletion

namespace Localization.AtPrime

variable {R : Type*} [CommRing R] (q : Ideal R) [hq : q.IsMaximal]

open IsLocalRing

theorem pow_le_comap_maximalIdeal_pow (n : ℕ) :
    q ^ n ≤ ((maximalIdeal (Localization.AtPrime q)) ^ n).comap
      (algebraMap R (Localization.AtPrime q)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
  exact Ideal.le_comap_map

theorem comap_maximalIdeal_pow (n : ℕ) :
    ((maximalIdeal (Localization.AtPrime q)) ^ n).comap (algebraMap R (Localization.AtPrime q))
      = q ^ n := by
  rcases n with _ | n
  · simp
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
  refine IsLocalization.under_map_of_isPrimary_disjoint q.primeCompl (Localization.AtPrime q)
    (Ideal.isPrimary_of_isMaximal_radical ?_) ?_
  · rw [Ideal.radical_pow _ n.succ_ne_zero, hq.isPrime.radical]
    exact hq
  · exact Set.disjoint_left.mpr fun x hx hx' => hx (Ideal.pow_le_self n.succ_ne_zero hx')

def quotientPowMap (n : ℕ) :
    R ⧸ q ^ n →+* Localization.AtPrime q ⧸ (maximalIdeal (Localization.AtPrime q)) ^ n :=
  Ideal.quotientMap _ (algebraMap R (Localization.AtPrime q)) (pow_le_comap_maximalIdeal_pow q n)

theorem quotientPowMap_mk (n : ℕ) (x : R) :
    quotientPowMap q n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap R _ x) :=
  Ideal.quotientMap_mk

theorem exists_mul_add_eq_one_of_notMem (n : ℕ) {s : R} (hs : s ∉ q) :
    ∃ a, ∃ c ∈ q ^ n, a * s + c = 1 := by
  have htop : q ⊔ Ideal.span {s} = ⊤ := by
    obtain ⟨y, i, hi, h⟩ := hq.exists_inv hs
    rw [Ideal.eq_top_iff_one, ← h, sup_comm]
    exact Submodule.add_mem_sup (Ideal.mem_span_singleton'.mpr ⟨y, rfl⟩) hi
  have h1 : (1 : R) ∈ q ^ n ⊔ Ideal.span {s} := by
    rw [Ideal.pow_sup_eq_top htop]; trivial
  obtain ⟨c, hc, z, hz, hcz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  exact ⟨a, c, hc, by rw [add_comm, hcz]⟩

theorem quotientPowMap_bijective (n : ℕ) : Function.Bijective (quotientPowMap q n) := by
  constructor
  · exact Ideal.quotientMap_injective' (comap_maximalIdeal_pow q n).le
  · intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨a, c, hc, hac⟩ := exists_mul_add_eq_one_of_notMem q n (s := (s : R)) s.prop
    refine ⟨Ideal.Quotient.mk _ (r * a), ?_⟩
    rw [quotientPowMap_mk, Ideal.Quotient.eq]
    have hs : (algebraMap R (Localization.AtPrime q)) (s : R) * IsLocalization.mk' _ r s
        = algebraMap R _ r := IsLocalization.mk'_spec' _ r s
    have : algebraMap R (Localization.AtPrime q) (r * a) - IsLocalization.mk' _ r s
        = - (IsLocalization.mk' (Localization.AtPrime q) r s * algebraMap R _ c) := by
      have hc' : algebraMap R (Localization.AtPrime q) (a * s) = 1 - algebraMap R _ c := by
        rw [eq_sub_iff_add_eq, ← map_add, hac, map_one]
      rw [map_mul, ← hs, mul_comm (algebraMap R _ (s : R)), mul_assoc, ← map_mul,
        mul_comm (s : R), hc']
      ring
    rw [this]
    refine neg_mem (Ideal.mul_mem_left _ _ ?_)
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hc

noncomputable def quotientPowEquiv (n : ℕ) :
    R ⧸ q ^ n ≃+* Localization.AtPrime q ⧸ (maximalIdeal (Localization.AtPrime q)) ^ n :=
  RingEquiv.ofBijective _ (quotientPowMap_bijective q n)

@[simp] theorem quotientPowEquiv_mk (n : ℕ) (x : R) :
    quotientPowEquiv q n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap R _ x) :=
  quotientPowMap_mk q n x

theorem factorPow_quotientPowEquiv {m n : ℕ} (h : m ≤ n) (x : R ⧸ q ^ n) :
    Ideal.Quotient.factorPow _ h (quotientPowEquiv q n x)
      = quotientPowEquiv q m (Ideal.Quotient.factorPow q h x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  show Ideal.Quotient.factor _ (quotientPowEquiv q n (Ideal.Quotient.mk _ x))
    = quotientPowEquiv q m (Ideal.Quotient.factor _ (Ideal.Quotient.mk _ x))
  rw [quotientPowEquiv_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, quotientPowEquiv_mk]

end Localization.AtPrime

namespace AdicCompletion

variable {R : Type*} [CommRing R] (q : Ideal R) [q.IsMaximal]

open IsLocalRing

noncomputable def localizationEquiv :
    AdicCompletion q R ≃+*
      AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) :=
  ofLevelwiseEquiv q _ (Localization.AtPrime.quotientPowEquiv q)
    (Localization.AtPrime.factorPow_quotientPowEquiv q)

@[simp] theorem localizationEquiv_of (x : R) :
    localizationEquiv q (of q R x) = of _ _ (algebraMap R (Localization.AtPrime q) x) :=
  ofLevelwiseEquiv_of _ _ _ _ x _ fun n => Localization.AtPrime.quotientPowEquiv_mk q n x

end AdicCompletion

namespace MvPolynomial

variable {σ : Type*} {k : Type*} [Field k]

theorem idealOfVars_eq_ker_constantCoeff :
    idealOfVars σ k = RingHom.ker (constantCoeff : MvPolynomial σ k →+* k) := by
  apply le_antisymm
  · rw [idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact constantCoeff_X k i
  · intro p hp
    rw [idealOfVars, ← Set.image_univ, mem_ideal_span_X_image]
    intro m hm
    by_contra! h
    have : m = 0 := Finsupp.ext fun i => h i (Set.mem_univ i)
    subst this
    exact (mem_support_iff.mp hm) hp

theorem idealOfVars_isMaximal : (idealOfVars σ k).IsMaximal := by
  rw [idealOfVars_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, constantCoeff_C σ a⟩

theorem eq_idealOfVars_of_X_mem (q : Ideal (MvPolynomial σ k)) [hq : q.IsMaximal] (hX : ∀ i, X i ∈ q) :
    q = idealOfVars σ k := by
  refine ((idealOfVars_isMaximal (σ := σ) (k := k)).eq_of_le hq.ne_top ?_).symm
  rw [idealOfVars, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact hX i

variable [Finite σ] (q : Ideal (MvPolynomial σ k)) [hq : q.IsMaximal] (hX : ∀ i, X i ∈ q)

open IsLocalRing

noncomputable def adicCompletionRingEquivMvPowerSeries :
    AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
      ≃+* MvPowerSeries σ k := by
  have h := eq_idealOfVars_of_X_mem q hX
  subst h
  exact (AdicCompletion.localizationEquiv (idealOfVars σ k)).symm.trans
    (MvPowerSeries.toAdicCompletionAlgEquiv σ k).toRingEquiv.symm

theorem adicCompletionRingEquivMvPowerSeries_of (p : MvPolynomial σ k) :
    adicCompletionRingEquivMvPowerSeries q hX
      (AdicCompletion.of _ _ (algebraMap _ (Localization.AtPrime q) p)) = (p : MvPowerSeries σ k) := by
  have h := eq_idealOfVars_of_X_mem q hX
  subst h
  simp only [adicCompletionRingEquivMvPowerSeries, RingEquiv.trans_apply]
  rw [← AdicCompletion.localizationEquiv_of, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_eq,
    AlgEquiv.coe_ringEquiv, MvPowerSeries.toAdicCompletionAlgEquiv_apply,
    MvPowerSeries.toAdicCompletion_coe]

noncomputable def adicCompletionAlgEquivMvPowerSeries :
    AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
      ≃ₐ[k] MvPowerSeries σ k :=
  AlgEquiv.ofRingEquiv (f := adicCompletionRingEquivMvPowerSeries q hX) fun x => by
    rw [AdicCompletion.algebraMap_apply, IsScalarTower.algebraMap_apply k (MvPolynomial σ k)
      (Localization.AtPrime q), adicCompletionRingEquivMvPowerSeries_of, algebraMap_eq, coe_C]
    rfl

theorem adicCompletionAlgEquivMvPowerSeries_of (p : MvPolynomial σ k) :
    adicCompletionAlgEquivMvPowerSeries q hX
      (AdicCompletion.of _ _ (algebraMap _ (Localization.AtPrime q) p)) = (p : MvPowerSeries σ k) :=
  adicCompletionRingEquivMvPowerSeries_of q hX p

theorem adicCompletionAlgEquivMvPowerSeries_X (i : σ) :
    adicCompletionAlgEquivMvPowerSeries q hX
      (AdicCompletion.of _ _ (algebraMap _ (Localization.AtPrime q) (X i : MvPolynomial σ k)))
        = MvPowerSeries.X i := by
  rw [adicCompletionAlgEquivMvPowerSeries_of, coe_X]

end MvPolynomial

#print axioms AdicCompletion.ofLevelwiseEquiv
#print axioms Localization.AtPrime.quotientPowEquiv
#print axioms AdicCompletion.localizationEquiv
#print axioms MvPolynomial.adicCompletionAlgEquivMvPowerSeries
#print axioms MvPolynomial.adicCompletionAlgEquivMvPowerSeries_of


