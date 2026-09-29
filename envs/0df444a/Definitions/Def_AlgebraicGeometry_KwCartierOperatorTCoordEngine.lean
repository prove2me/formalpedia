-- Prove2me | Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine
-- name    : AlgebraicGeometry_KwCartierOperatorTCoordEngine
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/484b5ac5-b5e6-5378-b1df-953cea664f4a
-- title:
--   Cartier operator in a t-coordinate on Kähler differentials
-- statement:
--   Throughout, $F$ is a field of characteristic a prime $\ell$, algebra over a field $K$, and $F^{\ell} \subseteq F$ denotes the subfield `kw_pke_pthPowers F ℓ`, the range of the Frobenius endomorphism, i.e. the subfield of $\ell$-th powers. The first group of results records the basic facts about $\ell$-th powers and differentials: $d(g^{\ell}) = 0$ in $\Omega_{F/K}$ for every $g$ (`kw_cart_d_pow_zero`); if $dt \neq 0$ then $t \notin F^{\ell}$ (`kw_cart_not_pthPower`); and, for such $t$, the minimal polynomial of $t$ over $F^{\ell}$ has degree exactly $\ell$ (`kw_cart_minpoly_natDegree_eq`), proved by showing that the minimal polynomial becomes $(X-t)^{d}$ after base change to $F$ and that a degree $d < \ell$ would force $t \in F^{\ell}$ through the coefficient of $X^{d-1}$. Auxiliary lemmas state that associated monic polynomials over a field coincide, that a nonzero vector spans a one-dimensional module, and hence (`kw_cart_hspan_of_isCurveOver`) that under [`AlgebraicCurve.IsCurveOver K F`](../def/AlgebraicCurve_IsCurveOver.html#L15), whose field `kaehler_free_rank_one` asserts freeness and $\operatorname{rank}_F \Omega_{F/K} = 1$, any $t$ with $dt \neq 0$ gives $\Omega_{F/K} = F\cdot dt$.
--
--   The coordinate machinery follows. Assuming that every element of $F$ is separable over the subfield underlying $F^{\ell}(t)$ and that $\deg \operatorname{minpoly}_{F^{\ell}}(t) = \ell$, each $u \in F$ has a unique expansion $u = \sum_{i<\ell} c_i t^{i}$ with $c_i \in F^{\ell}$ (`kw_cart_exists_repr`, resting on the $F^{\ell}$-independence of $1,t,\dots,t^{\ell-1}$ in `kw_cart_pow_family_indep`); `kw_cart_repr` names the coefficient family, which is additive and satisfies $\operatorname{repr}(a^{\ell}u)_i = a^{\ell}\operatorname{repr}(u)_i$. `kw_cart_root` is the inverse of Frobenius on $F^{\ell}$, the unique $\ell$-th root of an element of that subfield, additive with $\operatorname{root}(a^{\ell}p) = a\operatorname{root}(p)$. Given $dt \neq 0$ and $\Omega_{F/K} = F\cdot dt$, `kw_cart_dtCoord` extracts the unique $w \in F$ with $\omega = w\,dt$, and is additive and $F$-homogeneous. Finally `kw_cart_C`, which takes the hypotheses $dt \neq 0$, the spanning property, separability and the degree equality as arguments, is defined by
--   $$C(\omega) = \sqrt[\ell]{c_{\ell-1}}\; dt, \qquad c = \operatorname{repr}\bigl(\operatorname{dtCoord}(\omega)\bigr),$$
--   and is shown to be additive (`kw_cart_C_add`) and $\ell^{-1}$-semilinear: $C(a^{\ell}\omega) = a\,C(\omega)$ (`kw_cart_C_semilinear`). `kw_cart_axiomAnchor` is a trivial auxiliary asserting `True`.
--
--   **Relation to Mathlib.** The differentials are Mathlib's `KaehlerDifferential` module $\Omega_{F/K}$; Mathlib has no Cartier operator, and the operator here is the project's own, defined relative to a chosen element $t$ with $dt \neq 0$ rather than intrinsically.
--
--   **Where it is used.** The operator is built for the analysis of differentials on a curve $F/K$ in characteristic $\ell$, in the form needed for Hasse–Witt and logarithmic-derivative arguments about $\ell$-power torsion in the divisor class group of the curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_KwPthPowerKerDExpansionEngine
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial IntermediateField AlgebraicCurve.KwPke

noncomputable section

namespace AlgebraicCurve.KwCart

theorem kw_cart_axiomAnchor : True :=
  have _h₁ : True = True := propext Iff.rfl
  have _h₂ : ℕ := Classical.choice ⟨0⟩
  have _h₃ : Quot.mk (fun (_ _ : ℕ) => True) 0 = Quot.mk (fun (_ _ : ℕ) => True) 1 :=
    Quot.sound trivial
  trivial

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP F ℓ]

omit hℓ in

theorem kw_cart_d_pow_zero (g : F) :
    KaehlerDifferential.D K F (g ^ ℓ) = 0 := by
  have _ := kw_cart_axiomAnchor
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero F ℓ, zero_smul]

theorem kw_cart_not_pthPower {t : F} (hdt : KaehlerDifferential.D K F t ≠ 0) :
    t ∉ kw_pke_pthPowers F ℓ := by
  have _ := kw_cart_axiomAnchor
  intro hmem
  obtain ⟨g, hg⟩ := (kw_pke_mem_pthPowers_iff F ℓ).mp hmem
  exact hdt (by rw [← hg]; exact kw_cart_d_pow_zero g)

theorem kw_cart_monic_eq_of_associated {p q : Polynomial F} (hp : p.Monic) (hq : q.Monic)
    (h : Associated p q) : p = q := by
  have _ := kw_cart_axiomAnchor
  obtain ⟨u, hu⟩ := h
  obtain ⟨c, hc, hCc⟩ := Polynomial.isUnit_iff.mp u.isUnit
  have hu' : p * C c = q := by rw [hCc, hu]
  have hlc : (p * C c).leadingCoeff = q.leadingCoeff := by rw [hu']
  rw [leadingCoeff_mul, hp.leadingCoeff, hq.leadingCoeff, one_mul, leadingCoeff_C] at hlc
  rw [← hu', hlc, map_one, mul_one]

theorem kw_cart_minpoly_natDegree_eq {t : F}
    (hdt : KaehlerDifferential.D K F t ≠ 0) :
    (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ := by
  have _ := kw_cart_axiomAnchor
  have hPmem : t ^ ℓ ∈ kw_pke_pthPowers F ℓ := (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨t, rfl⟩
  set d := (minpoly (kw_pke_pthPowers F ℓ) t).natDegree with hd
  have hint : IsIntegral (kw_pke_pthPowers F ℓ) t := kw_pke_isIntegral_gen t
  have hdle : d ≤ ℓ := kw_pke_minpoly_natDegree_le t
  have hdpos : 0 < d := minpoly.natDegree_pos hint

  have hmap_monic : ((minpoly (kw_pke_pthPowers F ℓ) t).map (algebraMap (kw_pke_pthPowers F ℓ) F)).Monic :=
    (minpoly.monic hint).map _
  have hmap_dvd : (minpoly (kw_pke_pthPowers F ℓ) t).map (algebraMap (kw_pke_pthPowers F ℓ) F) ∣ (X - C t) ^ ℓ := by
    have hcoe : (algebraMap (kw_pke_pthPowers F ℓ) F)
        (⟨t ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨t, rfl⟩⟩ : kw_pke_pthPowers F ℓ) = t ^ ℓ := rfl
    have hdvd : minpoly (kw_pke_pthPowers F ℓ) t ∣ X ^ ℓ - C (⟨t ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr
        ⟨t, rfl⟩⟩ : kw_pke_pthPowers F ℓ) :=
      minpoly.dvd _ t (by simp [Polynomial.aeval_def, Polynomial.eval₂_sub, hcoe])
    have h2 : (X - C t : Polynomial F) ^ ℓ = X ^ ℓ - C (t ^ ℓ) := by
      have h := sub_pow_char (X : Polynomial F) (C t)
      rwa [← map_pow] at h
    have h1 : (X ^ ℓ - C (⟨t ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨t, rfl⟩⟩ :
        kw_pke_pthPowers F ℓ) : Polynomial (kw_pke_pthPowers F ℓ)).map (algebraMap (kw_pke_pthPowers F ℓ) F)
        = X ^ ℓ - C (t ^ ℓ) := by
      simp [Polynomial.map_sub, Polynomial.map_pow, hcoe]
    rw [h2, ← h1]
    exact Polynomial.map_dvd _ hdvd
  have hprime : Prime (X - C t : Polynomial F) := Polynomial.prime_X_sub_C t
  obtain ⟨k, hkle, hassoc⟩ := (dvd_prime_pow hprime ℓ).mp hmap_dvd
  have hmap_eq : (minpoly (kw_pke_pthPowers F ℓ) t).map (algebraMap (kw_pke_pthPowers F ℓ) F) = (X - C t) ^ k :=
    kw_cart_monic_eq_of_associated hmap_monic ((monic_X_sub_C t).pow k) hassoc
  have hkd : k = d := by
    have h1 : ((minpoly (kw_pke_pthPowers F ℓ) t).map (algebraMap (kw_pke_pthPowers F ℓ) F)).natDegree = d := natDegree_map _
    rw [hmap_eq] at h1
    rw [← h1, natDegree_pow, natDegree_X_sub_C, mul_one]

  by_contra hne
  have hdlt : d < ℓ := lt_of_le_of_ne hdle hne
  have hcoeff_mem : ((minpoly (kw_pke_pthPowers F ℓ) t).map (algebraMap (kw_pke_pthPowers F ℓ) F)).coeff (d - 1)
      ∈ kw_pke_pthPowers F ℓ := by
    rw [Polynomial.coeff_map]
    exact ((minpoly (kw_pke_pthPowers F ℓ) t).coeff (d - 1)).2
  rw [hmap_eq, hkd] at hcoeff_mem

  have hcomp : ((X - C t : Polynomial F) ^ d).coeff (d - 1) = (d : F) * (-t) := by
    have h0 : (X - C t : Polynomial F) = X + C (-t) := by rw [map_neg, sub_eq_add_neg]
    rw [h0, coeff_X_add_C_pow]
    have h1 : d - (d - 1) = 1 := by omega
    have h2 : d.choose (d - 1) = d := by
      rw [Nat.choose_symm (by omega : 1 ≤ d), Nat.choose_one_right]
    rw [h1, h2, pow_one]
    ring
  rw [hcomp] at hcoeff_mem

  have hdcast : ((d : ℕ) : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F ℓ]
    exact fun hdvd => absurd (Nat.le_of_dvd hdpos hdvd) (not_le.mpr hdlt)
  have hdP : ((d : ℕ) : F) ∈ kw_pke_pthPowers F ℓ := kw_pke_prime_field_pow F ℓ d
  have htP : t ∈ kw_pke_pthPowers F ℓ := by
    have hneg : (-(((d : ℕ) : F) * t)) ∈ kw_pke_pthPowers F ℓ := by
      have : ((d : ℕ) : F) * (-t) = -(((d : ℕ) : F) * t) := by ring
      rwa [this] at hcoeff_mem
    have hmul : ((d : ℕ) : F) * t ∈ kw_pke_pthPowers F ℓ := by
      have := neg_mem hneg
      rwa [neg_neg] at this
    have hinv : (((d : ℕ) : F))⁻¹ ∈ kw_pke_pthPowers F ℓ := inv_mem hdP
    have := mul_mem hinv hmul
    rwa [← mul_assoc, inv_mul_cancel₀ hdcast, one_mul] at this
  exact kw_cart_not_pthPower hdt htP

theorem kw_cart_span_singleton_eq_top_of_finrank_one
    {M : Type*} [AddCommGroup M] [Module F M]
    (h1 : Module.finrank F M = 1) {v : M} (hv : v ≠ 0) :
    Submodule.span F {v} = ⊤ := by
  have _ := kw_cart_axiomAnchor
  haveI : FiniteDimensional F M := .of_finrank_eq_succ h1
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [finrank_span_singleton hv, h1]

theorem kw_cart_hspan_of_isCurveOver [AlgebraicCurve.IsCurveOver K F] {t : F}
    (hdt : KaehlerDifferential.D K F t ≠ 0) :
    Submodule.span F {KaehlerDifferential.D K F t} = ⊤ := by
  have _ := kw_cart_axiomAnchor
  exact kw_cart_span_singleton_eq_top_of_finrank_one
    (AlgebraicCurve.IsCurveOver.kaehler_free_rank_one (K := K) (F := F)).2 hdt

section Repr

variable (t : F)

theorem kw_cart_pow_family_indep
    (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (c : Fin ℓ → kw_pke_pthPowers F ℓ)
    (h : (∑ i : Fin ℓ, ((c i : F)) * t ^ (i : ℕ)) = 0) :
    ∀ i, c i = 0 := by
  have _ := kw_cart_axiomAnchor
  classical
  set q : Polynomial (kw_pke_pthPowers F ℓ) :=
    ∑ i : Fin ℓ, Polynomial.monomial (i : ℕ) (c i) with hq
  have hqcoeff : ∀ i : Fin ℓ, q.coeff (i : ℕ) = c i := by
    intro i
    rw [hq, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single i]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro j _ hji
      rw [Polynomial.coeff_monomial, if_neg (fun hj => hji (Fin.ext hj))]
    · intro hni
      exact absurd (Finset.mem_univ i) hni
  have hqaeval : Polynomial.aeval t q = 0 := by
    rw [hq, map_sum]
    have hterm : ∀ i : Fin ℓ, Polynomial.aeval t (Polynomial.monomial (i : ℕ) (c i))
        = ((c i : F)) * t ^ (i : ℕ) := fun i => by
      rw [Polynomial.aeval_monomial]
      rfl
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    exact h
  have hqzero : q = 0 := by
    by_contra hqne
    have hdvd := minpoly.dvd (kw_pke_pthPowers F ℓ) t hqaeval
    have hdeg_le := Polynomial.natDegree_le_of_dvd hdvd hqne
    have hqdeg : q.natDegree < ℓ := by
      rw [hq]
      refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
      rw [Finset.fold_max_lt]
      refine ⟨hℓ.out.pos, fun i _ => ?_⟩
      exact lt_of_le_of_lt (Polynomial.natDegree_monomial_le _) i.2
    rw [hdeg] at hdeg_le
    omega
  intro i
  rw [← hqcoeff i, hqzero, Polynomial.coeff_zero]

theorem kw_cart_exists_repr
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (u : F) :
    ∃! c : Fin ℓ → kw_pke_pthPowers F ℓ,
      u = ∑ i : Fin ℓ, ((c i : F)) * t ^ (i : ℕ) := by
  have _ := kw_cart_axiomAnchor
  classical
  have hint : IsIntegral (kw_pke_pthPowers F ℓ) t := kw_pke_isIntegral_gen t

  have hmem : u ∈ (kw_pke_expansionField (ℓ := ℓ) t).toSubfield :=
    kw_pke_mem_expansionField t hsep u
  have hmem2 : u ∈ Algebra.adjoin (kw_pke_pthPowers F ℓ) ({t} : Set F) := by
    have h1 : u ∈ (IntermediateField.adjoin (kw_pke_pthPowers F ℓ) ({t} : Set F)).toSubalgebra := hmem
    rwa [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
      at h1
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem2
  obtain ⟨q0, hq0⟩ := hmem2
  have hq0' : Polynomial.aeval t q0 = u := hq0

  set m := minpoly (kw_pke_pthPowers F ℓ) t with hm
  have hm_monic : m.Monic := minpoly.monic hint
  set q := q0 %ₘ m with hqdef
  have hq_aeval : Polynomial.aeval t q = u := by
    rw [hqdef, Polynomial.aeval_modByMonic_eq_self_of_root
      (minpoly.aeval (kw_pke_pthPowers F ℓ) t), hq0']
  have hq_deg : q.natDegree < ℓ := by
    by_cases hqz : q = 0
    · rw [hqz, Polynomial.natDegree_zero]
      exact hℓ.out.pos
    · have h1 : q.degree < m.degree := Polynomial.degree_modByMonic_lt q0 hm_monic
      have h4 := Polynomial.natDegree_lt_natDegree hqz h1
      have h2 : m.natDegree = ℓ := hdeg
      omega

  have hrep : u = ∑ j : Fin ℓ, ((q.coeff (j : ℕ) : F)) * t ^ (j : ℕ) := by
    have hsum : (∑ i ∈ Finset.range (q.natDegree + 1),
        (algebraMap (kw_pke_pthPowers F ℓ) F) (q.coeff i) * t ^ i)
        = ∑ i ∈ Finset.range ℓ, (algebraMap (kw_pke_pthPowers F ℓ) F) (q.coeff i) * t ^ i := by
      refine Finset.sum_subset ?_ ?_
      · intro k hk
        rw [Finset.mem_range] at hk ⊢
        omega
      · intro k _ hnk
        rw [Finset.mem_range] at hnk
        have hklt : q.natDegree < k := by omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hklt, map_zero, zero_mul]
    calc u = Polynomial.aeval t q := hq_aeval.symm
      _ = ∑ i ∈ Finset.range (q.natDegree + 1), (algebraMap (kw_pke_pthPowers F ℓ) F) (q.coeff i) * t ^ i := by
          rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range]
      _ = ∑ i ∈ Finset.range ℓ, (algebraMap (kw_pke_pthPowers F ℓ) F) (q.coeff i) * t ^ i := hsum
      _ = ∑ j : Fin ℓ, ((q.coeff (j : ℕ) : F)) * t ^ (j : ℕ) :=
          (Fin.sum_univ_eq_sum_range (fun i => ((q.coeff i : F)) * t ^ i) ℓ).symm
  refine ⟨fun i => q.coeff (i : ℕ), hrep, ?_⟩
  intro c' hc'
  funext i
  have hdiff : (∑ j : Fin ℓ, (((c' j - q.coeff (j : ℕ)) : kw_pke_pthPowers F ℓ) : F) * t ^ (j : ℕ)) = 0 := by
    have h1 : (∑ j : Fin ℓ, ((c' j : F)) * t ^ (j : ℕ))
        - (∑ j : Fin ℓ, ((q.coeff (j : ℕ) : F)) * t ^ (j : ℕ)) = 0 := by
      rw [← hc', ← hrep, sub_self]
    rw [← h1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hz := kw_cart_pow_family_indep t hdeg _ hdiff i
  exact sub_eq_zero.mp hz

variable (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
variable (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)

def kw_cart_repr (u : F) : Fin ℓ → kw_pke_pthPowers F ℓ :=
  (kw_cart_exists_repr t hsep hdeg u).exists.choose

theorem kw_cart_repr_spec (u : F) :
    u = ∑ i : Fin ℓ, ((kw_cart_repr t hsep hdeg u i : F)) * t ^ (i : ℕ) :=
  (kw_cart_exists_repr t hsep hdeg u).exists.choose_spec

theorem kw_cart_repr_unique {u : F} {c : Fin ℓ → kw_pke_pthPowers F ℓ}
    (hc : u = ∑ i : Fin ℓ, ((c i : F)) * t ^ (i : ℕ)) :
    kw_cart_repr t hsep hdeg u = c := by
  have _ := kw_cart_axiomAnchor
  exact (kw_cart_exists_repr t hsep hdeg u).unique
    (kw_cart_repr_spec t hsep hdeg u) hc

theorem kw_cart_repr_add (u v : F) :
    kw_cart_repr t hsep hdeg (u + v)
      = kw_cart_repr t hsep hdeg u + kw_cart_repr t hsep hdeg v := by
  have _ := kw_cart_axiomAnchor
  refine kw_cart_repr_unique t hsep hdeg ?_
  have hu := kw_cart_repr_spec t hsep hdeg u
  have hv := kw_cart_repr_spec t hsep hdeg v
  calc u + v
      = (∑ i : Fin ℓ, ((kw_cart_repr t hsep hdeg u i : F)) * t ^ (i : ℕ))
        + ∑ i : Fin ℓ, ((kw_cart_repr t hsep hdeg v i : F)) * t ^ (i : ℕ) := by
        rw [← hu, ← hv]
    _ = ∑ i : Fin ℓ,
          (((kw_cart_repr t hsep hdeg u + kw_cart_repr t hsep hdeg v) i : F))
            * t ^ (i : ℕ) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.add_apply]
        push_cast
        ring

theorem kw_cart_repr_pow_smul (a : F) (u : F) :
    kw_cart_repr t hsep hdeg (a ^ ℓ * u)
      = fun i => ⟨a ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨a, rfl⟩⟩
          * kw_cart_repr t hsep hdeg u i := by
  have _ := kw_cart_axiomAnchor
  refine kw_cart_repr_unique t hsep hdeg ?_
  have hu := kw_cart_repr_spec t hsep hdeg u
  calc a ^ ℓ * u
      = a ^ ℓ * ∑ i : Fin ℓ, ((kw_cart_repr t hsep hdeg u i : F)) * t ^ (i : ℕ) := by
        rw [← hu]
    _ = ∑ i : Fin ℓ,
          (((fun i => (⟨a ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨a, rfl⟩⟩ :
              kw_pke_pthPowers F ℓ) * kw_cart_repr t hsep hdeg u i) i : F))
            * t ^ (i : ℕ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring

end Repr

section Root

def kw_cart_root (p : kw_pke_pthPowers F ℓ) : F :=
  ((kw_pke_mem_pthPowers_iff F ℓ).mp p.2).choose

theorem kw_cart_root_pow (p : kw_pke_pthPowers F ℓ) :
    (kw_cart_root p) ^ ℓ = (p : F) :=
  ((kw_pke_mem_pthPowers_iff F ℓ).mp p.2).choose_spec

theorem kw_cart_root_unique {p : kw_pke_pthPowers F ℓ} {g : F}
    (hg : g ^ ℓ = (p : F)) : kw_cart_root p = g := by
  have _ := kw_cart_axiomAnchor
  have h1 : (kw_cart_root p) ^ ℓ = g ^ ℓ := by rw [kw_cart_root_pow, hg]
  have hfrob : Function.Injective (frobenius F ℓ) := frobenius_inj F ℓ
  exact hfrob (by simpa [frobenius_def] using h1)

theorem kw_cart_root_add (p q : kw_pke_pthPowers F ℓ) :
    kw_cart_root (p + q) = kw_cart_root p + kw_cart_root q := by
  have _ := kw_cart_axiomAnchor
  refine kw_cart_root_unique ?_
  rw [add_pow_char, kw_cart_root_pow, kw_cart_root_pow]
  rfl

theorem kw_cart_root_pow_mul (a : F) (p : kw_pke_pthPowers F ℓ) :
    kw_cart_root (⟨a ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨a, rfl⟩⟩ * p)
      = a * kw_cart_root p := by
  have _ := kw_cart_axiomAnchor
  refine kw_cart_root_unique ?_
  rw [mul_pow, kw_cart_root_pow]
  rfl

end Root

section Cartier

theorem kw_cart_exists_dtCoord (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (ω : Ω[F⁄K]) : ∃! w : F, ω = w • KaehlerDifferential.D K F t := by
  have _ := kw_cart_axiomAnchor
  have hmem : ω ∈ Submodule.span F {KaehlerDifferential.D K F t} := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨w, hw⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨w, hw.symm, ?_⟩
  intro w' hw'
  have h0 : (w' - w) • KaehlerDifferential.D K F t = 0 := by
    rw [sub_smul, ← hw', hw, sub_self]
  rcases smul_eq_zero.mp h0 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hdt

def kw_cart_dtCoord (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤) (ω : Ω[F⁄K]) : F :=
  (kw_cart_exists_dtCoord (K := K) t hdt hspan ω).exists.choose

theorem kw_cart_dtCoord_spec (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤) (ω : Ω[F⁄K]) :
    ω = kw_cart_dtCoord t hdt hspan ω • KaehlerDifferential.D K F t :=
  (kw_cart_exists_dtCoord (K := K) t hdt hspan ω).exists.choose_spec

theorem kw_cart_dtCoord_unique (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤) {ω : Ω[F⁄K]} {w : F}
    (hw : ω = w • KaehlerDifferential.D K F t) :
    kw_cart_dtCoord t hdt hspan ω = w := by
  have _ := kw_cart_axiomAnchor
  have h1 := kw_cart_dtCoord_spec t hdt hspan ω
  have h0 : (kw_cart_dtCoord t hdt hspan ω - w) • KaehlerDifferential.D K F t = 0 := by
    rw [sub_smul, ← h1, ← hw, sub_self]
  rcases smul_eq_zero.mp h0 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hdt

theorem kw_cart_dtCoord_add (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤) (ω ω' : Ω[F⁄K]) :
    kw_cart_dtCoord t hdt hspan (ω + ω')
      = kw_cart_dtCoord t hdt hspan ω + kw_cart_dtCoord t hdt hspan ω' := by
  have _ := kw_cart_axiomAnchor
  refine kw_cart_dtCoord_unique t hdt hspan ?_
  rw [add_smul]
  nth_rewrite 1 [kw_cart_dtCoord_spec t hdt hspan ω]
  nth_rewrite 1 [kw_cart_dtCoord_spec t hdt hspan ω']
  rfl

theorem kw_cart_dtCoord_smul (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤) (a : F) (ω : Ω[F⁄K]) :
    kw_cart_dtCoord t hdt hspan (a • ω) = a * kw_cart_dtCoord t hdt hspan ω := by
  have _ := kw_cart_axiomAnchor
  refine kw_cart_dtCoord_unique t hdt hspan ?_
  rw [mul_smul]
  nth_rewrite 1 [kw_cart_dtCoord_spec t hdt hspan ω]
  rfl

def kw_cart_C (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (ω : Ω[F⁄K]) : Ω[F⁄K] :=
  (kw_cart_root (kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω)
    ⟨ℓ - 1, by have := hℓ.out.pos; omega⟩)) • KaehlerDifferential.D K F t

theorem kw_cart_C_add (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (ω ω' : Ω[F⁄K]) :
    kw_cart_C (K := K) t hdt hspan hsep hdeg (ω + ω')
      = kw_cart_C (K := K) t hdt hspan hsep hdeg ω
        + kw_cart_C (K := K) t hdt hspan hsep hdeg ω' := by
  have _ := kw_cart_axiomAnchor
  rw [kw_cart_C, kw_cart_C, kw_cart_C, kw_cart_dtCoord_add,
    kw_cart_repr_add]
  have h1 : ∀ i, (kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω)
      + kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω')) i
      = kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω) i
        + kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω') i := fun _ => rfl
  rw [h1, kw_cart_root_add, add_smul]

theorem kw_cart_C_semilinear (t : F) (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (a : F) (ω : Ω[F⁄K]) :
    kw_cart_C (K := K) t hdt hspan hsep hdeg (a ^ ℓ • ω)
      = a • kw_cart_C (K := K) t hdt hspan hsep hdeg ω := by
  have _ := kw_cart_axiomAnchor
  rw [kw_cart_C, kw_cart_C, kw_cart_dtCoord_smul]
  have h2 : a ^ ℓ * kw_cart_dtCoord t hdt hspan ω
      = a ^ ℓ * kw_cart_dtCoord t hdt hspan ω := rfl
  rw [kw_cart_repr_pow_smul]
  have h3 : (fun i => (⟨a ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨a, rfl⟩⟩ :
      kw_pke_pthPowers F ℓ)
      * kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω) i)
      ⟨ℓ - 1, by have := hℓ.out.pos; omega⟩
      = ⟨a ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨a, rfl⟩⟩
        * kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω)
          ⟨ℓ - 1, by have := hℓ.out.pos; omega⟩ := rfl
  rw [h3, kw_cart_root_pow_mul, mul_smul]

end Cartier

end AlgebraicCurve.KwCart

end

section Audits

/-- info: 'AlgebraicCurve.KwCart.kw_cart_axiomAnchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_axiomAnchor

/-- info: 'AlgebraicCurve.KwCart.kw_cart_d_pow_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_d_pow_zero

/-- info: 'AlgebraicCurve.KwCart.kw_cart_not_pthPower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_not_pthPower

/-- info: 'AlgebraicCurve.KwCart.kw_cart_monic_eq_of_associated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_monic_eq_of_associated

/-- info: 'AlgebraicCurve.KwCart.kw_cart_minpoly_natDegree_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_minpoly_natDegree_eq

/-- info: 'AlgebraicCurve.KwCart.kw_cart_span_singleton_eq_top_of_finrank_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_span_singleton_eq_top_of_finrank_one

/-- info: 'AlgebraicCurve.KwCart.kw_cart_hspan_of_isCurveOver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_hspan_of_isCurveOver

/-- info: 'AlgebraicCurve.KwCart.kw_cart_pow_family_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_pow_family_indep

/-- info: 'AlgebraicCurve.KwCart.kw_cart_exists_repr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_exists_repr

/-- info: 'AlgebraicCurve.KwCart.kw_cart_repr_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_repr_spec

/-- info: 'AlgebraicCurve.KwCart.kw_cart_repr_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_repr_unique

/-- info: 'AlgebraicCurve.KwCart.kw_cart_repr_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_repr_add

/-- info: 'AlgebraicCurve.KwCart.kw_cart_repr_pow_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_repr_pow_smul

/-- info: 'AlgebraicCurve.KwCart.kw_cart_root_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_root_pow

/-- info: 'AlgebraicCurve.KwCart.kw_cart_root_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_root_unique

/-- info: 'AlgebraicCurve.KwCart.kw_cart_root_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_root_add

/-- info: 'AlgebraicCurve.KwCart.kw_cart_root_pow_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_root_pow_mul

/-- info: 'AlgebraicCurve.KwCart.kw_cart_exists_dtCoord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_exists_dtCoord

/-- info: 'AlgebraicCurve.KwCart.kw_cart_dtCoord_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_dtCoord_spec

/-- info: 'AlgebraicCurve.KwCart.kw_cart_dtCoord_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_dtCoord_unique

/-- info: 'AlgebraicCurve.KwCart.kw_cart_dtCoord_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_dtCoord_add

/-- info: 'AlgebraicCurve.KwCart.kw_cart_dtCoord_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_dtCoord_smul

/-- info: 'AlgebraicCurve.KwCart.kw_cart_C_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_C_add

/-- info: 'AlgebraicCurve.KwCart.kw_cart_C_semilinear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCart.kw_cart_C_semilinear

end Audits


