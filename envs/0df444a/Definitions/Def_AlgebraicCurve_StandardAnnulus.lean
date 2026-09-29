-- Prove2me | Definitions.Def_AlgebraicCurve_StandardAnnulus
-- name    : AlgebraicCurve_StandardAnnulus
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/4e138121-f54f-558a-9a89-d811f687c27c
-- title:
--   Gauss valuation, rational-function reduction, admissible points, standard annulus
-- statement:
--   Fix a field $K$ with a valuation subring $A$. For $P \in K[X]$, `gaussVal A P` is the supremum, over the support of $P$, of `A.valuation` of the coefficients of $P$; it is shown to be multiplicative (Gauss's lemma) and submultiplicative for sums, hence assembles into a valuation `gaussValuationPoly` on $K[X]$ with values in `A.ValueGroup`. Since it is nonzero on nonzero polynomials it extends, via `Valuation.extendToLocalization`, to a valuation `gaussValuation` on `RatFunc K`, whose valuation subring is `gaussIntegers A`. The ring homomorphisms `constToGauss : A →+* gaussIntegers A` (a local homomorphism), `xGauss` and `polyToGauss : A[X] →+* gaussIntegers A` feed an injective map `psiPoly` from $k[X]$, $k$ the residue field of $A$, into the residue field of `gaussIntegers A`; it is extended to `psiRatFunc` on `RatFunc k` and proved surjective, giving a ring isomorphism `psiEquiv : RatFunc k ≃+* ResidueField (gaussIntegers A)` and hence a reduction map `gaussResidue : gaussIntegers A →+* RatFunc k` with kernel the maximal ideal; every nonzero $f$ becomes, after scaling by a constant, an element with nonzero reduction. Over algebraically closed $K$, `exists_factored_rep` writes a polynomial of Gauss value $1$ as a unit constant times linear factors at its roots in $A$ times factors $1 - r^{-1}X$ at its roots outside, and reads off the reduction.
--
--   For a modulus $\pi \in A$, `Admissible A π a` means $v(\pi) < v(a) < 1$ for $v =$ `A.valuation`; `innerCount A p` counts, with multiplicity, the roots of $p$ of valuation $< 1$, and is identified with the multiplicity of $0$ in the reduction. Together with order computations at the places `placeOfPoint K a` ($\operatorname{ord}$ of a polynomial $=$ its root multiplicity at $a$) these build `standardAnnulus`, an `Annulus A (RatFunc K)` with parameter $X$, modulus $\pi$ and domain the places of admissible points. Finally `ComponentChart.ofConstantReductionNodes` turns a pointwise constant reduction, a finite set of nodes and a divisor-existence hypothesis into a `ComponentChart` whose domain is the complement of the fibres of the nodes.
--
--   **Relation to Mathlib.** The Gauss valuation is assembled here from Mathlib's `Valuation`, `ValuationSubring`, `Valuation.extendToLocalization` and `RatFunc`; the surrounding notions `Place`, `Annulus` and `ComponentChart`, and the reduction data attached to them, are the project's own.
--
--   **Where it is used.** The Gauss reduction of `RatFunc K` supplies the component chart of a rational component in a semistable reduction, and the standard annulus models the neighbourhood of a node; these are the local charts used in the analysis of the reduction of modular curves at a finite place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_StandardAnnulus.lean

import Definitions.Def_ModularCurve_FinitePlaceLift
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve.GaussReduction

open Polynomial

variable {K : Type*} [Field K] (A : ValuationSubring K)

noncomputable def gaussVal (P : K[X]) : A.ValueGroup :=
  P.support.sup fun i => A.valuation (P.coeff i)

theorem gaussVal_zero : gaussVal A (0 : K[X]) = 0 := by
  simp only [gaussVal, Polynomial.support_zero, Finset.sup_empty]
  exact bot_eq_zero

theorem valuation_coeff_le_gaussVal (P : K[X]) (i : ℕ) :
    A.valuation (P.coeff i) ≤ gaussVal A P := by
  by_cases hi : i ∈ P.support
  · exact Finset.le_sup (f := fun i => A.valuation (P.coeff i)) hi
  · rw [Polynomial.notMem_support_iff.mp hi, map_zero]
    exact zero_le'

theorem exists_gaussVal_eq (P : K[X]) (hP : P ≠ 0) :
    ∃ i ∈ P.support, A.valuation (P.coeff i) = gaussVal A P := by
  obtain ⟨i, hi, hv⟩ := Finset.exists_mem_eq_sup P.support
    (Polynomial.support_nonempty.mpr hP) fun i => A.valuation (P.coeff i)
  exact ⟨i, hi, hv.symm⟩

theorem gaussVal_ne_zero (P : K[X]) (hP : P ≠ 0) : gaussVal A P ≠ 0 := by
  obtain ⟨i, hi, hv⟩ := exists_gaussVal_eq A P hP
  rw [← hv]
  simpa using Polynomial.mem_support_iff.mp hi

theorem gaussVal_C (c : K) : gaussVal A (C c : K[X]) = A.valuation c := by
  by_cases hc : c = 0
  · simp [hc, gaussVal_zero]
  · rw [gaussVal]
    rw [Polynomial.support_C hc]
    simp

theorem gaussVal_one : gaussVal A (1 : K[X]) = 1 := by
  rw [show (1 : K[X]) = C 1 from (map_one C).symm, gaussVal_C, map_one]

theorem gaussVal_add_le (P Q : K[X]) :
    gaussVal A (P + Q) ≤ max (gaussVal A P) (gaussVal A Q) := by
  rw [gaussVal]
  refine Finset.sup_le fun i _ => ?_
  rw [Polynomial.coeff_add]
  exact le_trans (Valuation.map_add _ _ _)
    (max_le_max (valuation_coeff_le_gaussVal A P i) (valuation_coeff_le_gaussVal A Q i))

theorem gaussVal_mul (P Q : K[X]) :
    gaussVal A (P * Q) = gaussVal A P * gaussVal A Q := by
  by_cases hP : P = 0
  · simp [hP, gaussVal_zero]
  by_cases hQ : Q = 0
  · simp [hQ, gaussVal_zero]
  have hgP := gaussVal_ne_zero A P hP
  have hgQ := gaussVal_ne_zero A Q hQ

  have hSP : (P.support.filter fun i => A.valuation (P.coeff i) = gaussVal A P).Nonempty := by
    obtain ⟨i, hi, hv⟩ := exists_gaussVal_eq A P hP
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hv⟩⟩
  have hSQ : (Q.support.filter fun i => A.valuation (Q.coeff i) = gaussVal A Q).Nonempty := by
    obtain ⟨j, hj, hv⟩ := exists_gaussVal_eq A Q hQ
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, hv⟩⟩
  set i₀ := (P.support.filter fun i => A.valuation (P.coeff i) = gaussVal A P).max' hSP with hi₀def
  set j₀ := (Q.support.filter fun j => A.valuation (Q.coeff j) = gaussVal A Q).max' hSQ with hj₀def
  have hi₀ : A.valuation (P.coeff i₀) = gaussVal A P :=
    (Finset.mem_filter.mp ((P.support.filter _).max'_mem hSP)).2
  have hj₀ : A.valuation (Q.coeff j₀) = gaussVal A Q :=
    (Finset.mem_filter.mp ((Q.support.filter _).max'_mem hSQ)).2
  have hPlt : ∀ i, i₀ < i → A.valuation (P.coeff i) < gaussVal A P := by
    intro i hi
    rcases lt_or_eq_of_le (valuation_coeff_le_gaussVal A P i) with h | h
    · exact h
    · exfalso
      have hmem : i ∈ P.support := by
        rw [Polynomial.mem_support_iff]
        intro h0
        rw [h0, map_zero] at h
        exact hgP h.symm
      have : i ≤ i₀ := Finset.le_max' _ i (Finset.mem_filter.mpr ⟨hmem, h⟩)
      omega
  have hQlt : ∀ j, j₀ < j → A.valuation (Q.coeff j) < gaussVal A Q := by
    intro j hj
    rcases lt_or_eq_of_le (valuation_coeff_le_gaussVal A Q j) with h | h
    · exact h
    · exfalso
      have hmem : j ∈ Q.support := by
        rw [Polynomial.mem_support_iff]
        intro h0
        rw [h0, map_zero] at h
        exact hgQ h.symm
      have : j ≤ j₀ := Finset.le_max' _ j (Finset.mem_filter.mpr ⟨hmem, h⟩)
      omega

  refine le_antisymm ?_ ?_
  · refine Finset.sup_le fun n _ => ?_
    rw [Polynomial.coeff_mul]
    refine Valuation.map_sum_le _ fun x _ => ?_
    rw [map_mul]
    exact mul_le_mul' (valuation_coeff_le_gaussVal A P x.1)
      (valuation_coeff_le_gaussVal A Q x.2)
  ·
    have hmain : A.valuation (P.coeff i₀ * Q.coeff j₀) = gaussVal A P * gaussVal A Q := by
      rw [map_mul, hi₀, hj₀]
    have hmainne : gaussVal A P * gaussVal A Q ≠ 0 := mul_ne_zero hgP hgQ
    have hrest : A.valuation
        (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2)
        < gaussVal A P * gaussVal A Q := by
      refine Valuation.map_sum_lt _ hmainne fun x hx => ?_
      obtain ⟨hxne, hxmem⟩ := Finset.mem_erase.mp hx
      have hxsum : x.1 + x.2 = i₀ + j₀ := Finset.HasAntidiagonal.mem_antidiagonal.mp hxmem
      rw [map_mul]
      rcases Nat.lt_or_ge i₀ x.1 with hgt | hle
      · calc A.valuation (P.coeff x.1) * A.valuation (Q.coeff x.2)
            ≤ A.valuation (P.coeff x.1) * gaussVal A Q :=
              mul_le_mul_right (valuation_coeff_le_gaussVal A Q x.2) _
          _ < gaussVal A P * gaussVal A Q :=
              mul_lt_mul_of_pos_right (hPlt x.1 hgt) (zero_lt_iff.mpr hgQ)
      · have hx1 : x.1 < i₀ ∨ x.1 = i₀ := lt_or_eq_of_le hle
        rcases hx1 with hlt | heq
        · have hx2 : j₀ < x.2 := by omega
          calc A.valuation (P.coeff x.1) * A.valuation (Q.coeff x.2)
              ≤ gaussVal A P * A.valuation (Q.coeff x.2) :=
                mul_le_mul_left (valuation_coeff_le_gaussVal A P x.1) _
            _ < gaussVal A P * gaussVal A Q :=
                mul_lt_mul_of_pos_left (hQlt x.2 hx2) (zero_lt_iff.mpr hgP)
        · exfalso
          have : x.2 = j₀ := by omega
          exact hxne (Prod.ext heq this)
    have hcoeff : A.valuation ((P * Q).coeff (i₀ + j₀))
        = gaussVal A P * gaussVal A Q := by
      rw [Polynomial.coeff_mul]
      rw [← Finset.sum_erase_add _ _
        (show ((i₀, j₀) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (i₀ + j₀) from
          Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl)]
      rw [Valuation.map_add_eq_of_lt_right _ (by rw [hmain]; exact hrest)]
      exact hmain
    rw [← hcoeff]
    exact valuation_coeff_le_gaussVal A (P * Q) (i₀ + j₀)

noncomputable def gaussValuationPoly : Valuation K[X] A.ValueGroup where
  toFun := gaussVal A
  map_zero' := gaussVal_zero A
  map_one' := gaussVal_one A
  map_mul' := gaussVal_mul A
  map_add_le_max' := gaussVal_add_le A

theorem nonZeroDivisors_le_primeCompl :
    nonZeroDivisors K[X] ≤ (gaussValuationPoly A).supp.primeCompl := by
  intro P hP
  have hP0 : P ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hP
  show P ∉ (gaussValuationPoly A).supp
  rw [Valuation.mem_supp_iff]
  exact gaussVal_ne_zero A P hP0

noncomputable def gaussValuation : Valuation (RatFunc K) A.ValueGroup :=
  (gaussValuationPoly A).extendToLocalization (nonZeroDivisors_le_primeCompl A) (RatFunc K)

theorem gaussValuation_algebraMap_poly (P : K[X]) :
    gaussValuation A (algebraMap K[X] (RatFunc K) P) = gaussVal A P :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ _

noncomputable def gaussIntegers : ValuationSubring (RatFunc K) :=
  (gaussValuation A).valuationSubring

theorem mem_gaussIntegers_iff (f : RatFunc K) :
    f ∈ gaussIntegers A ↔ gaussValuation A f ≤ 1 := Iff.rfl

theorem gaussValuation_algebraMap_const (c : K) :
    gaussValuation A (algebraMap K (RatFunc K) c) = A.valuation c := by
  rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K) c, Polynomial.algebraMap_eq,
    gaussValuation_algebraMap_poly, gaussVal_C]

theorem gaussVal_X : gaussVal A (Polynomial.X : K[X]) = 1 := by
  rw [gaussVal, Polynomial.support_X]
  simp only [Finset.sup_singleton, Polynomial.coeff_X_one, map_one]

theorem isUnit_gauss_iff (x : ↥(gaussIntegers A)) :
    IsUnit x ↔ gaussValuation A (x : RatFunc K) = 1 := by
  constructor
  · intro hu
    obtain ⟨y, hy1, _⟩ := isUnit_iff_exists.mp hu
    have hv : gaussValuation A (x : RatFunc K) * gaussValuation A (y : RatFunc K) = 1 := by
      rw [← map_mul, ← Subring.coe_mul, hy1, OneMemClass.coe_one, map_one]
    have hle : gaussValuation A (x : RatFunc K) ≤ 1 := x.2
    have hle' : gaussValuation A (y : RatFunc K) ≤ 1 := y.2
    by_contra hne
    have hlt : gaussValuation A (x : RatFunc K) < 1 := lt_of_le_of_ne hle hne
    have hprod : gaussValuation A (x : RatFunc K) * gaussValuation A (y : RatFunc K) < 1 := by
      calc gaussValuation A (x : RatFunc K) * gaussValuation A (y : RatFunc K)
          ≤ gaussValuation A (x : RatFunc K) * 1 := mul_le_mul_right hle' _
        _ < 1 := by rwa [mul_one]
    rw [hv] at hprod
    exact lt_irrefl _ hprod
  · intro hv
    have hx0 : (x : RatFunc K) ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hv
      exact zero_ne_one hv
    have hinv : (x : RatFunc K)⁻¹ ∈ gaussIntegers A := by
      rw [mem_gaussIntegers_iff, map_inv₀, hv, inv_one]
    refine ⟨⟨x, ⟨(x : RatFunc K)⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
    · exact Subtype.ext (by simp [mul_inv_cancel₀ hx0])
    · exact Subtype.ext (by simp [inv_mul_cancel₀ hx0])

theorem not_isUnit_gauss_iff (x : ↥(gaussIntegers A)) :
    ¬IsUnit x ↔ gaussValuation A (x : RatFunc K) < 1 := by
  rw [isUnit_gauss_iff]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => ne_of_lt h⟩

noncomputable def constToGauss : ↥A →+* ↥(gaussIntegers A) where
  toFun c := ⟨algebraMap K (RatFunc K) (c : K), by
    rw [mem_gaussIntegers_iff, gaussValuation_algebraMap_const]
    exact A.valuation_le_one c⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[simp] theorem constToGauss_coe (c : ↥A) :
    ((constToGauss A c : ↥(gaussIntegers A)) : RatFunc K) = algebraMap K (RatFunc K) (c : K) :=
  rfl

instance isLocalHom_constToGauss : IsLocalHom (constToGauss A) := by
  constructor
  intro a ha
  by_contra hnu
  have hlt : A.valuation (a : K) < 1 := by
    rcases lt_or_eq_of_le (A.valuation_le_one a) with h | h
    · exact h
    · exact absurd ((A.valuation_eq_one_iff a).mpr h) hnu
  have : gaussValuation A ((constToGauss A a : ↥(gaussIntegers A)) : RatFunc K) < 1 := by
    rw [constToGauss_coe, gaussValuation_algebraMap_const]
    exact hlt
  exact (not_isUnit_gauss_iff A _).mpr this ha

noncomputable def xGauss : ↥(gaussIntegers A) :=
  ⟨algebraMap K[X] (RatFunc K) Polynomial.X, by
    rw [mem_gaussIntegers_iff, gaussValuation_algebraMap_poly, gaussVal_X]⟩

noncomputable def polyToGauss : Polynomial ↥A →+* ↥(gaussIntegers A) :=
  Polynomial.eval₂RingHom (constToGauss A) (xGauss A)

theorem polyToGauss_coe (P : Polynomial ↥A) :
    ((polyToGauss A P : ↥(gaussIntegers A)) : RatFunc K)
      = algebraMap K[X] (RatFunc K) (P.map A.subtype) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Polynomial.map_add, map_add, Subring.coe_add, hp, hq]
  | monomial n a =>
    have h1 : ((polyToGauss A (Polynomial.monomial n a) : ↥(gaussIntegers A)) : RatFunc K)
        = algebraMap K (RatFunc K) (a : K) * (algebraMap K[X] (RatFunc K) Polynomial.X) ^ n := by
      show ((Polynomial.eval₂RingHom (constToGauss A) (xGauss A)) (Polynomial.monomial n a)
        : ↥(gaussIntegers A)).1 = _
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, Subring.coe_mul,
        SubmonoidClass.coe_pow, constToGauss_coe]
      rfl
    rw [h1, Polynomial.map_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    congr 1

theorem valuation_eq_one_of_isUnit {a : ↥A} (ha : IsUnit a) : A.valuation (a : K) = 1 :=
  (A.valuation_eq_one_iff a).mp ha

theorem residue_polyToGauss_ne_zero (P : Polynomial ↥A) (h : ∃ n, IsUnit (P.coeff n)) :
    IsLocalRing.residue ↥(gaussIntegers A) (polyToGauss A P) ≠ 0 := by
  obtain ⟨n, hn⟩ := h
  rw [Ne, IsLocalRing.residue_eq_zero_iff, (IsLocalRing.mem_maximalIdeal _)]
  intro hm
  have hlt : gaussValuation A ((polyToGauss A P : ↥(gaussIntegers A)) : RatFunc K) < 1 :=
    (not_isUnit_gauss_iff A _).mp (mem_nonunits_iff.mp hm)
  have hge : (1 : A.ValueGroup) ≤ gaussValuation A ((polyToGauss A P : ↥(gaussIntegers A)) : RatFunc K) := by
    rw [polyToGauss_coe, gaussValuation_algebraMap_poly]
    have := valuation_coeff_le_gaussVal A (P.map A.subtype) n
    rw [Polynomial.coeff_map] at this
    rw [← valuation_eq_one_of_isUnit A hn]
    exact this
  exact absurd (lt_of_le_of_lt hge hlt) (lt_irrefl _)

noncomputable def residueConstHom :
    IsLocalRing.ResidueField ↥A →+* IsLocalRing.ResidueField ↥(gaussIntegers A) :=
  IsLocalRing.ResidueField.map (constToGauss A)

noncomputable def psiPoly :
    Polynomial (IsLocalRing.ResidueField ↥A) →+* IsLocalRing.ResidueField ↥(gaussIntegers A) :=
  Polynomial.eval₂RingHom (residueConstHom A)
    (IsLocalRing.residue ↥(gaussIntegers A) (xGauss A))

theorem psiPoly_map_residue (P : Polynomial ↥A) :
    psiPoly A (P.map (IsLocalRing.residue ↥A))
      = IsLocalRing.residue ↥(gaussIntegers A) (polyToGauss A P) := by
  have h : (psiPoly A).comp (Polynomial.mapRingHom (IsLocalRing.residue ↥A))
      = (IsLocalRing.residue ↥(gaussIntegers A)).comp (polyToGauss A) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C]
      rw [psiPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        residueConstHom, IsLocalRing.ResidueField.map_residue,
        polyToGauss, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X]
      rw [psiPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
        polyToGauss, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  exact DFunLike.congr_fun h P

theorem exists_lift_of_residue (p : Polynomial (IsLocalRing.ResidueField ↥A)) :
    ∃ P : Polynomial ↥A, P.map (IsLocalRing.residue ↥A) = p ∧
      ∀ n, p.coeff n ≠ 0 → IsUnit (P.coeff n) := by
  classical
  set ℓ : IsLocalRing.ResidueField ↥A → ↥A :=
    Function.surjInv IsLocalRing.residue_surjective with hℓdef
  have hℓ : ∀ c, IsLocalRing.residue ↥A (ℓ c) = c :=
    fun c => Function.surjInv_eq IsLocalRing.residue_surjective c
  refine ⟨p.sum fun n c => Polynomial.monomial n (ℓ c), ?_, ?_⟩
  · ext m
    rw [Polynomial.coeff_map]
    rw [Polynomial.sum, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' p.support m fun n => ℓ (p.coeff n)]
    by_cases hm : m ∈ p.support
    · rw [if_pos hm, hℓ]
    · rw [if_neg hm, map_zero, eq_comm]
      exact Polynomial.notMem_support_iff.mp hm
  · intro n hn
    have hmem : n ∈ p.support := Polynomial.mem_support_iff.mpr hn
    rw [Polynomial.sum, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' p.support n fun m => ℓ (p.coeff m), if_pos hmem]
    by_contra hnu
    have : ℓ (p.coeff n) ∈ IsLocalRing.maximalIdeal ↥A :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have h0 : IsLocalRing.residue ↥A (ℓ (p.coeff n)) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr this
    rw [hℓ] at h0
    exact hn h0

theorem psiPoly_injective : Function.Injective (psiPoly A) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hne
  obtain ⟨P, hmap, hunit⟩ := exists_lift_of_residue A p
  obtain ⟨n, hn⟩ : ∃ n, p.coeff n ≠ 0 := by
    by_contra hall
    refine hne (Polynomial.ext fun n => ?_)
    rw [Polynomial.coeff_zero]
    by_contra h0
    exact hall ⟨n, h0⟩
  have := psiPoly_map_residue A P
  rw [hmap, hp] at this
  exact residue_polyToGauss_ne_zero A P ⟨n, hunit n hn⟩ this.symm

noncomputable def psiRatFunc :
    RatFunc (IsLocalRing.ResidueField ↥A) →+* IsLocalRing.ResidueField ↥(gaussIntegers A) :=
  IsFractionRing.lift (psiPoly_injective A)

theorem psiRatFunc_algebraMap (p : Polynomial (IsLocalRing.ResidueField ↥A)) :
    psiRatFunc A (algebraMap _ _ p) = psiPoly A p :=
  IsFractionRing.lift_algebraMap _ _

theorem psiRatFunc_surjective : Function.Surjective (psiRatFunc A) := by
  intro g
  obtain ⟨f, rfl⟩ := IsLocalRing.residue_surjective (R := ↥(gaussIntegers A)) g

  obtain ⟨P, Q, hQ0, hPQ⟩ : ∃ (P Q : K[X]), Q ≠ 0 ∧
      (f : RatFunc K) = algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q :=
    ⟨RatFunc.num (f : RatFunc K), RatFunc.denom (f : RatFunc K),
      RatFunc.denom_ne_zero _, (RatFunc.num_div_denom _).symm⟩

  obtain ⟨i₀, hi₀mem, hi₀⟩ := exists_gaussVal_eq A Q hQ0
  set c := Q.coeff i₀ with hcdef
  have hc0 : c ≠ 0 := Polynomial.mem_support_iff.mp hi₀mem
  set P' := Polynomial.C c⁻¹ * P with hP'def
  set Q' := Polynomial.C c⁻¹ * Q with hQ'def
  have hQ'0 : Q' ≠ 0 := mul_ne_zero (by simpa using inv_ne_zero hc0) hQ0
  have hgQ' : gaussVal A Q' = 1 := by
    rw [hQ'def, gaussVal_mul, gaussVal_C, map_inv₀, hi₀, inv_mul_cancel₀]
    exact gaussVal_ne_zero A Q hQ0
  have hPQ' : (f : RatFunc K) = algebraMap K[X] (RatFunc K) P' / algebraMap K[X] (RatFunc K) Q' := by
    rw [hP'def, hQ'def, map_mul, map_mul, mul_div_mul_left, hPQ]
    intro h
    exact inv_ne_zero hc0 (Polynomial.C_eq_zero.mp
      ((map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mp h))
  have hfQP : (f : RatFunc K) * algebraMap K[X] (RatFunc K) Q' = algebraMap K[X] (RatFunc K) P' := by
    rw [hPQ', div_mul_cancel₀]
    intro h
    exact hQ'0 ((map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mp h)

  have hgP' : gaussVal A P' ≤ 1 := by
    have hval : gaussValuation A (f : RatFunc K) * gaussVal A Q' = gaussVal A P' := by
      rw [← gaussValuation_algebraMap_poly A Q', ← gaussValuation_algebraMap_poly A P',
        ← map_mul, hfQP]
    rw [← hval, hgQ', mul_one]
    exact f.2

  have hPcoef : (↑P'.coeffs : Set K) ⊆ (A.toSubring : Set K) := by
    intro x hx
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    exact (A.valuation_le_one_iff _).mp ((valuation_coeff_le_gaussVal A P' n).trans hgP')
  have hQcoef : (↑Q'.coeffs : Set K) ⊆ (A.toSubring : Set K) := by
    intro x hx
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    exact (A.valuation_le_one_iff _).mp
      ((valuation_coeff_le_gaussVal A Q' n).trans (le_of_eq hgQ'))
  set PA := P'.toSubring A.toSubring hPcoef with hPAdef
  set QA := Q'.toSubring A.toSubring hQcoef with hQAdef
  have hPAmap : PA.map A.subtype = P' := by
    ext n
    rw [Polynomial.coeff_map]
    exact Polynomial.coeff_toSubring P' A.toSubring hPcoef
  have hQAmap : QA.map A.subtype = Q' := by
    ext n
    rw [Polynomial.coeff_map]
    exact Polynomial.coeff_toSubring Q' A.toSubring hQcoef

  have hQunit : ∃ n, IsUnit (QA.coeff n) := by
    refine ⟨i₀, ?_⟩
    have hco : (QA.coeff i₀ : K) = Q'.coeff i₀ := Polynomial.coeff_toSubring _ _ hQcoef
    have hval1 : A.valuation (QA.coeff i₀ : K) = 1 := by
      rw [hco, hQ'def]
      rw [Polynomial.coeff_C_mul, map_mul, map_inv₀, ← hcdef, hi₀]
      exact inv_mul_cancel₀ (gaussVal_ne_zero A Q hQ0)
    exact (A.valuation_eq_one_iff _).mpr hval1

  have hfmul : IsLocalRing.residue ↥(gaussIntegers A) f
      * IsLocalRing.residue ↥(gaussIntegers A) (polyToGauss A QA)
      = IsLocalRing.residue ↥(gaussIntegers A) (polyToGauss A PA) := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    rw [Subring.coe_mul, polyToGauss_coe, polyToGauss_coe, hPAmap, hQAmap]
    exact hfQP
  have hQne : IsLocalRing.residue ↥(gaussIntegers A) (polyToGauss A QA) ≠ 0 :=
    residue_polyToGauss_ne_zero A QA hQunit
  refine ⟨algebraMap _ _ (PA.map (IsLocalRing.residue ↥A))
    / algebraMap _ _ (QA.map (IsLocalRing.residue ↥A)), ?_⟩
  rw [map_div₀, psiRatFunc_algebraMap, psiRatFunc_algebraMap,
    psiPoly_map_residue, psiPoly_map_residue]
  rw [eq_comm, eq_div_iff hQne]
  exact hfmul

noncomputable def psiEquiv :
    RatFunc (IsLocalRing.ResidueField ↥A) ≃+* IsLocalRing.ResidueField ↥(gaussIntegers A) :=
  RingEquiv.ofBijective (psiRatFunc A) ⟨(psiRatFunc A).injective, psiRatFunc_surjective A⟩

noncomputable def gaussResidue :
    ↥(gaussIntegers A) →+* RatFunc (IsLocalRing.ResidueField ↥A) :=
  ((psiEquiv A).symm : IsLocalRing.ResidueField ↥(gaussIntegers A) →+* _).comp
    (IsLocalRing.residue ↥(gaussIntegers A))

theorem ker_gaussResidue :
    RingHom.ker (gaussResidue A) = IsLocalRing.maximalIdeal ↥(gaussIntegers A) := by
  ext x
  rw [RingHom.mem_ker, gaussResidue, RingHom.comp_apply]
  constructor
  · intro h
    have h0 : IsLocalRing.residue ↥(gaussIntegers A) x = 0 :=
      (psiEquiv A).symm.injective
        (show (psiEquiv A).symm _ = (psiEquiv A).symm 0 by rw [map_zero]; exact h)
    exact (IsLocalRing.residue_eq_zero_iff _).mp h0
  · intro h
    have h0 : IsLocalRing.residue ↥(gaussIntegers A) x = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr h
    show (psiEquiv A).symm _ = 0
    rw [h0, map_zero]

theorem gaussValuation_smul (c : K) (f : RatFunc K) :
    gaussValuation A (c • f) = A.valuation c * gaussValuation A f := by
  rw [Algebra.smul_def, map_mul, gaussValuation_algebraMap_const]

theorem exists_smul_gaussResidue_ne_zero (f : RatFunc K) (hf : f ≠ 0) :
    ∃ c : K, ∃ h : c • f ∈ gaussIntegers A, gaussResidue A ⟨c • f, h⟩ ≠ 0 := by
  obtain ⟨c, hc⟩ := A.valuation_surjective (gaussValuation A f)⁻¹
  have hf0 : gaussValuation A f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  have hval : gaussValuation A (c • f) = 1 := by
    rw [gaussValuation_smul, hc, inv_mul_cancel₀ hf0]
  have hmem : c • f ∈ gaussIntegers A := by rw [mem_gaussIntegers_iff, hval]
  refine ⟨c, hmem, fun h0 => ?_⟩
  have hres0 : IsLocalRing.residue ↥(gaussIntegers A) ⟨c • f, hmem⟩ = 0 := by
    refine (psiEquiv A).symm.injective ?_
    show (psiEquiv A).symm _ = (psiEquiv A).symm 0
    rw [map_zero]
    exact h0
  have hm := (IsLocalRing.residue_eq_zero_iff _).mp hres0
  have hlt := (not_isUnit_gauss_iff A _).mp
    (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hm))
  rw [show ((⟨c • f, hmem⟩ : ↥(gaussIntegers A)) : RatFunc K) = c • f from rfl, hval] at hlt
  exact lt_irrefl _ hlt

section PlaceMap

open RationalFunctionField
open scoped Classical

variable [IsAlgClosed K]

omit [IsAlgClosed K] in
theorem gaussVal_eq_one_of_coeffs (p : K[X]) (hle : ∀ n, A.valuation (p.coeff n) ≤ 1)
    (hex : ∃ n, A.valuation (p.coeff n) = 1) : gaussVal A p = 1 := by
  obtain ⟨n, hn⟩ := hex
  refine le_antisymm (Finset.sup_le fun i _ => hle i) ?_
  rw [← hn]
  exact valuation_coeff_le_gaussVal A p n

omit [IsAlgClosed K] in
theorem gaussVal_X_sub_C_of_le (a : K) (ha : A.valuation a ≤ 1) :
    gaussVal A (Polynomial.X - Polynomial.C a) = 1 := by
  refine gaussVal_eq_one_of_coeffs A _ (fun n => ?_) ⟨1, ?_⟩
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    rcases eq_or_ne n 0 with rfl | h0
    · rw [if_neg one_ne_zero, if_pos rfl, zero_sub, Valuation.map_neg]
      exact ha
    · rcases eq_or_ne n 1 with rfl | h1
      · rw [if_pos rfl, if_neg one_ne_zero, sub_zero, map_one]
      · rw [if_neg (fun h => h1 h.symm), if_neg h0, sub_zero, map_zero]
        exact zero_le'
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C,
      if_neg one_ne_zero, sub_zero, map_one]

omit [IsAlgClosed K] in
theorem gaussVal_one_sub_C_mul_X (b : K) (hb : A.valuation b ≤ 1) :
    gaussVal A (1 - Polynomial.C b * Polynomial.X) = 1 := by
  refine gaussVal_eq_one_of_coeffs A _ (fun n => ?_) ⟨0, ?_⟩
  · rw [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul, Polynomial.coeff_X]
    rcases eq_or_ne n 0 with rfl | h0
    · rw [if_pos rfl, if_neg one_ne_zero, mul_zero, sub_zero, map_one]
    · rcases eq_or_ne n 1 with rfl | h1
      · rw [if_neg one_ne_zero, if_pos rfl, mul_one, zero_sub, Valuation.map_neg]
        exact hb
      · rw [if_neg h0, if_neg (fun h => h1 h.symm), mul_zero, sub_zero, map_zero]
        exact zero_le'
  · rw [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, if_pos rfl, if_neg one_ne_zero, mul_zero, sub_zero, map_one]

omit [IsAlgClosed K] in

theorem X_sub_C_eq_of_ne_zero (r : K) (hr : r ≠ 0) :
    Polynomial.X - Polynomial.C r
      = Polynomial.C (-r) * (1 - Polynomial.C r⁻¹ * Polynomial.X) := by
  rw [mul_sub, mul_one, ← mul_assoc, ← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ hr,
    Polynomial.C_neg, Polynomial.C_neg, Polynomial.C_1, neg_one_mul, sub_neg_eq_add]
  ring

theorem exists_factored_rep (pA : Polynomial ↥A)
    (h1 : gaussVal A (pA.map A.subtype) = 1) :
    ∃ (c : ↥A) (sInt : Multiset ↥A) (sNon : Multiset K),
      IsUnit c ∧
      (pA.map A.subtype).roots = sInt.map Subtype.val + sNon ∧
      (∀ r ∈ sNon, ¬ A.valuation r ≤ 1) ∧
      pA.map (IsLocalRing.residue ↥A)
        = Polynomial.C (IsLocalRing.residue ↥A c)
          * ((sInt.map fun a =>
              Polynomial.X - Polynomial.C (IsLocalRing.residue ↥A a)).prod) := by
  classical
  set p := pA.map A.subtype with hpdef
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, gaussVal_zero] at h1
    exact zero_ne_one h1

  set liftA : K → ↥A := fun r => if h : r ∈ A then ⟨r, h⟩ else 1 with hliftA
  set sInt : Multiset ↥A := (p.roots.filter (fun r => A.valuation r ≤ 1)).map liftA with hsInt
  set sNon := p.roots.filter (fun r => ¬ A.valuation r ≤ 1) with hsNon
  have hsplit : p.roots.filter (fun r => A.valuation r ≤ 1) + sNon = p.roots :=
    Multiset.filter_add_not _ _
  have hsIntcoe : sInt.map Subtype.val = p.roots.filter (fun r => A.valuation r ≤ 1) := by
    rw [hsInt, Multiset.map_map]
    calc (p.roots.filter (fun r => A.valuation r ≤ 1)).map (Subtype.val ∘ liftA)
        = (p.roots.filter (fun r => A.valuation r ≤ 1)).map id := by
          refine Multiset.map_congr rfl fun r hr => ?_
          have hrA : r ∈ A :=
            (A.valuation_le_one_iff r).mp (Multiset.mem_filter.mp hr).2
          simp [hliftA, dif_pos hrA]
      _ = _ := Multiset.map_id _

  have hsplits : p = Polynomial.C p.leadingCoeff
      * (p.roots.map fun a => Polynomial.X - Polynomial.C a).prod :=
    (IsAlgClosed.splits p).eq_prod_roots

  have hsNonmem : ∀ r ∈ sNon, ¬ A.valuation r ≤ 1 := by
    intro r hr
    rw [hsNon] at hr
    exact (Multiset.mem_filter.mp hr).2
  have hsNon0 : ∀ r ∈ sNon, r ≠ 0 := by
    intro r hr h0
    exact hsNonmem r hr (by rw [h0, map_zero]; exact zero_le')
  have hsNoninv : ∀ r ∈ sNon, A.valuation r⁻¹ < 1 := by
    intro r hr
    have hgt : 1 < A.valuation r := lt_of_not_ge (hsNonmem r hr)
    have hne : A.valuation r ≠ 0 := fun h => by
      rw [h] at hgt
      exact absurd hgt (by simp)
    rw [map_inv₀]
    rw [inv_lt_one₀ (zero_lt_iff.mpr hne)]
    exact hgt

  set c'' : K := p.leadingCoeff * (sNon.map fun r => -r).prod with hc''def

  have hKfac : p = Polynomial.C c''
      * ((sInt.map Subtype.val).map fun a => Polynomial.X - Polynomial.C a).prod
      * ((sNon.map fun r => 1 - Polynomial.C r⁻¹ * Polynomial.X)).prod := by
    have hroots : p.roots = sInt.map Subtype.val + sNon := by
      rw [hsIntcoe]
      exact hsplit.symm
    rw [hsplits, hroots, Multiset.map_add, Multiset.prod_add]
    have hNonfac : ((sNon.map fun a => Polynomial.X - Polynomial.C a)).prod
        = Polynomial.C ((sNon.map fun r => -r).prod)
          * ((sNon.map fun r => 1 - Polynomial.C r⁻¹ * Polynomial.X)).prod := by
      have h1 : (sNon.map fun a => Polynomial.X - Polynomial.C a)
          = sNon.map fun r => Polynomial.C (-r)
            * (1 - Polynomial.C r⁻¹ * Polynomial.X) := by
        refine Multiset.map_congr rfl fun r hr => ?_
        exact X_sub_C_eq_of_ne_zero r (hsNon0 r hr)
      rw [h1, Multiset.prod_map_mul]
      congr 1
      rw [show (sNon.map fun r => Polynomial.C (-r))
          = ((sNon.map fun r => -r).map ⇑Polynomial.C) from
        (Multiset.map_map _ _ _).symm]
      rw [← map_multiset_prod Polynomial.C]
    rw [hNonfac, hc''def, map_mul]
    ring

  have hgInt : gaussVal A (((sInt.map Subtype.val).map
      fun a => Polynomial.X - Polynomial.C a).prod) = 1 := by
    rw [show gaussVal A = ⇑(gaussValuationPoly A) from rfl, map_multiset_prod]
    rw [Multiset.map_map]
    have : ((sInt.map Subtype.val).map
        ((⇑(gaussValuationPoly A)) ∘ fun a => Polynomial.X - Polynomial.C a))
        = (sInt.map Subtype.val).map (fun _ => (1 : A.ValueGroup)) := by
      refine Multiset.map_congr rfl fun r hr => ?_
      have hrle : A.valuation r ≤ 1 := by
        rw [hsIntcoe] at hr
        exact (Multiset.mem_filter.mp hr).2
      exact gaussVal_X_sub_C_of_le A r hrle
    rw [this, Multiset.map_const', Multiset.prod_replicate, one_pow]
  have hgNon : gaussVal A (((sNon.map
      fun r => 1 - Polynomial.C r⁻¹ * Polynomial.X)).prod) = 1 := by
    rw [show gaussVal A = ⇑(gaussValuationPoly A) from rfl, map_multiset_prod]
    rw [Multiset.map_map]
    have : (sNon.map ((⇑(gaussValuationPoly A))
        ∘ fun r => 1 - Polynomial.C r⁻¹ * Polynomial.X))
        = sNon.map (fun _ => (1 : A.ValueGroup)) := by
      refine Multiset.map_congr rfl fun r hr => ?_
      exact gaussVal_one_sub_C_mul_X A r⁻¹ (le_of_lt (hsNoninv r hr))
    rw [this, Multiset.map_const', Multiset.prod_replicate, one_pow]
  have hvc : A.valuation c'' = 1 := by
    have := h1
    rw [hKfac] at this
    rw [gaussVal_mul, gaussVal_mul, gaussVal_C, hgInt, hgNon, mul_one, mul_one] at this
    exact this
  have hcmem : c'' ∈ A := (A.valuation_le_one_iff _).mp (le_of_eq hvc)
  set cA : ↥A := ⟨c'', hcmem⟩ with hcA
  have hcunit : IsUnit cA := (A.valuation_eq_one_iff cA).mpr hvc

  set liftInv : K → ↥A := fun r => if h : r⁻¹ ∈ A then ⟨r⁻¹, h⟩ else 0 with hliftInv
  have hliftInvmem : ∀ r ∈ sNon, ((liftInv r : ↥A) : K) = r⁻¹ := by
    intro r hr
    have : r⁻¹ ∈ A := (A.valuation_le_one_iff _).mp (le_of_lt (hsNoninv r hr))
    simp [hliftInv, dif_pos this]
  have hliftInvres : ∀ r ∈ sNon, IsLocalRing.residue ↥A (liftInv r) = 0 := by
    intro r hr
    refine (IsLocalRing.residue_eq_zero_iff _).mpr ?_
    rw [(IsLocalRing.mem_maximalIdeal _)]
    rw [mem_nonunits_iff]
    intro hu
    have := valuation_eq_one_of_isUnit A hu
    rw [hliftInvmem r hr] at this
    exact absurd this (ne_of_lt (hsNoninv r hr))

  set PA' : Polynomial ↥A := Polynomial.C cA
      * ((sInt.map fun a => Polynomial.X - Polynomial.C a)).prod
      * ((sNon.map fun r =>
          1 - Polynomial.C (liftInv r) * Polynomial.X)).prod with hPA'
  have hmapprodK : ∀ (m : Multiset (Polynomial ↥A)),
      (m.prod).map A.subtype = (m.map (Polynomial.map A.subtype)).prod := fun m => by
    rw [← Polynomial.coe_mapRingHom]
    exact map_multiset_prod (Polynomial.mapRingHom A.subtype) m
  have hmapprodR : ∀ (m : Multiset (Polynomial ↥A)),
      (m.prod).map (IsLocalRing.residue ↥A)
        = (m.map (Polynomial.map (IsLocalRing.residue ↥A))).prod := fun m => by
    rw [← Polynomial.coe_mapRingHom]
    exact map_multiset_prod (Polynomial.mapRingHom (IsLocalRing.residue ↥A)) m
  have hmapPA' : PA'.map A.subtype = p := by
    rw [hPA', Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C]
    rw [hKfac]
    congr 1
    · congr 1
      · rw [hmapprodK, Multiset.map_map]
        congr 1
        conv_rhs => rw [Multiset.map_map]
        refine Multiset.map_congr rfl fun a _ => ?_
        simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X,
          Polynomial.map_C]
        rfl
    · rw [hmapprodK, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun r hr => ?_
      simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_one,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
      rw [show (A.subtype (liftInv r)) = r⁻¹ from hliftInvmem r hr]
  have hpAeq : pA = PA' :=
    Polynomial.map_injective A.subtype Subtype.coe_injective (by rw [hmapPA', hpdef])
  refine ⟨cA, sInt, sNon, hcunit, ?_, hsNonmem, ?_⟩
  · rw [hsIntcoe]
    exact hsplit.symm
  · rw [hpAeq, hPA', Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C]
    have hNon1 : (((sNon.map fun r =>
        1 - Polynomial.C (liftInv r) * Polynomial.X)).prod).map
          (IsLocalRing.residue ↥A) = 1 := by
      rw [hmapprodR, Multiset.map_map]
      have hcongr : sNon.map ((Polynomial.map (IsLocalRing.residue ↥A))
          ∘ fun r => 1 - Polynomial.C (liftInv r) * Polynomial.X)
          = sNon.map (fun _ => (1 : Polynomial (IsLocalRing.ResidueField ↥A))) := by
        refine Multiset.map_congr rfl fun r hr => ?_
        simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_one,
          Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
          hliftInvres r hr, Polynomial.C_0, zero_mul, sub_zero]
      rw [hcongr, Multiset.map_const', Multiset.prod_replicate, one_pow]
    rw [hNon1, mul_one]
    congr 1
    rw [hmapprodR, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]

omit [IsAlgClosed K] in
theorem gaussResidue_polyToGauss (PA : Polynomial ↥A) :
    gaussResidue A (polyToGauss A PA)
      = algebraMap (Polynomial (IsLocalRing.ResidueField ↥A))
          (RatFunc (IsLocalRing.ResidueField ↥A)) (PA.map (IsLocalRing.residue ↥A)) := by
  rw [gaussResidue, RingHom.comp_apply, ← psiPoly_map_residue, ← psiRatFunc_algebraMap]
  show (psiEquiv A).symm ((psiEquiv A) _) = _
  rw [RingEquiv.symm_apply_apply]

omit [IsAlgClosed K] in
theorem map_residue_ne_zero_of_gaussVal_one (pA : Polynomial ↥A)
    (h1 : gaussVal A (pA.map A.subtype) = 1) :
    gaussResidue A (polyToGauss A pA) ≠ 0 := by
  have hp0 : pA.map A.subtype ≠ 0 := fun h => by
    rw [h, gaussVal_zero] at h1
    exact zero_ne_one h1
  obtain ⟨i, himem, hival⟩ := exists_gaussVal_eq A _ hp0
  have hunit : ∃ n, IsUnit (pA.coeff n) := by
    refine ⟨i, (A.valuation_eq_one_iff _).mpr ?_⟩
    have : A.valuation ((pA.map A.subtype).coeff i) = 1 := by rw [hival, h1]
    rwa [Polynomial.coeff_map] at this
  intro h0
  have : IsLocalRing.residue ↥(gaussIntegers A) (polyToGauss A pA) = 0 := by
    refine (psiEquiv A).symm.injective ?_
    show (psiEquiv A).symm _ = (psiEquiv A).symm 0
    rw [map_zero]
    exact h0
  exact residue_polyToGauss_ne_zero A pA hunit this

end PlaceMap

section PlaceHelpers

variable {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']

theorem ord_nonneg_of_mem_gen (v : Place K' F') {f : F'}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) : 0 ≤ v.ord f := by
  have h1 : v.adicValuation f ≤ 1 := by
    have h := v.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : v.toValuationSubring) : F') = f from rfl] at h
    rw [h]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  rcases v.adicValuation_le_one_iff.mp h1 with h | h
  · exact absurd h hf0
  · exact h

theorem ord_pos_of_residue_eq_zero (v : Place K' F') {f : F'}
    (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0)
    (h : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ = 0) : 0 < v.ord f := by
  have hm : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.residue_eq_zero_iff _).mp h
  have hlt' : v.adicValuation f < 1 := (v.mem_maximalIdeal_iff_adicValuation_lt_one _).mp hm
  have hge := ord_nonneg_of_mem_gen v hf hf0
  rcases lt_or_eq_of_le hge with h' | h'
  · exact h'
  · exact absurd ((v.ord_eq_zero_iff_adicValuation_eq_one hf0).mp h'.symm) (ne_of_lt hlt')

theorem mem_of_ord_nonneg_gen (v : Place K' F') {f : F'} (hf0 : f ≠ 0)
    (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  rw [v.mem_iff_adicValuation_le_one]
  by_contra hgt
  rw [not_le] at hgt
  have hinv : f⁻¹ ∈ v.toValuationSubring := by
    rw [v.mem_iff_adicValuation_le_one, map_inv₀]
    exact le_of_lt
      ((inv_lt_one₀ (zero_lt_iff.mpr (v.adicValuation_ne_zero hf0))).mpr hgt)
  have h2 := ord_nonneg_of_mem_gen v hinv (inv_ne_zero hf0)
  rw [v.ord_inv] at h2
  have h3 : v.ord f = 0 := by omega
  exact absurd ((v.ord_eq_zero_iff_adicValuation_eq_one hf0).mp h3) (ne_of_gt hgt)

theorem isRational_of_deg_eq_one_gen [IsAlgClosed K'] (v : Place K' F')
    (h : v.deg = 1) : v.IsRational := by
  haveI : Module.Finite K' v.ResidueField :=
    Module.finite_of_finrank_eq_succ (n := 0) (h : Module.finrank K' v.ResidueField = 1)
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K')).2

theorem evalAt_mul_of_mem (v : Place K' F') (hv : v.IsRational) {f g : F'}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

theorem evalAt_sub_of_mem (v : Place K' F') (hv : v.IsRational) {f g : F'}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv (sub_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem evalAt_algebraMap_const (v : Place K' F') (hv : v.IsRational) (c : K') :
    v.evalAt (algebraMap K' F' c) = c := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (v.algebraMap_mem' c)]
  rfl

end PlaceHelpers

section PointwiseGauss

open RationalFunctionField
open scoped Classical

variable [IsAlgClosed K]

end PointwiseGauss

end AlgebraicCurve.GaussReduction

namespace AlgebraicCurve.RationalFunctionField

open Polynomial

variable {K : Type*} [Field K]

private theorem ord_placeOfPoint_algebraMap_eq_mul (a : K) {q : K[X]} (hq : q ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q)
      = (rootMultiplicity a q : ℤ)
          * (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) := by

  obtain ⟨r, hr⟩ := pow_rootMultiplicity_dvd q a
  set m : ℕ := rootMultiplicity a q with hm
  have hXa : (X : K[X]) - C a ≠ 0 := X_sub_C_ne_zero a
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hq (by simpa using hr)

  have hndvd : ¬((X : K[X]) - C a) ∣ r := by
    intro ⟨s, hs⟩
    have : (X - C a) ^ (m + 1) ∣ q := ⟨s, by rw [hr, hs]; ring⟩
    have := (le_rootMultiplicity_iff hq).mpr this
    omega

  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hr0' : algebraMap K[X] (RatFunc K) r ≠ 0 := (map_ne_zero_iff _ hinj).mpr hr0
  have hpow' : algebraMap K[X] (RatFunc K) ((X - C a) ^ m) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (pow_ne_zero m hXa)

  have hordr : (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) r) = 0 := by
    by_contra hcon
    apply hndvd
    have hmem := (Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K)
      (heightOneSpectrumOfIrreducible K (irreducible_X_sub_C a)) hr0).mp hcon
    rw [heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton] at hmem
    exact hmem

  calc (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q)
      = (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) ((X - C a) ^ m)
          * algebraMap K[X] (RatFunc K) r) := by rw [← map_mul, ← hr]
    _ = (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) ((X - C a) ^ m))
          + (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) r) :=
        (placeOfPoint K a).ord_mul hpow' hr0'
    _ = (placeOfPoint K a).ord ((algebraMap K[X] (RatFunc K) (X - C a)) ^ (m : ℤ)) := by
        rw [hordr, add_zero, map_pow, ← zpow_natCast]
    _ = (m : ℤ) * (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) :=
        (placeOfPoint K a).ord_zpow _ _

private theorem dvd_ord_placeOfPoint (a : K) {f : RatFunc K} (hf : f ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) ∣ (placeOfPoint K a).ord f := by
  have hinj := IsFractionRing.injective K[X] (RatFunc K)
  have hnum : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hden : f.denom ≠ 0 := f.denom_ne_zero
  have hnum' : algebraMap K[X] (RatFunc K) f.num ≠ 0 := (map_ne_zero_iff _ hinj).mpr hnum
  have hden' : algebraMap K[X] (RatFunc K) f.denom ≠ 0 := (map_ne_zero_iff _ hinj).mpr hden
  have hsplit : f = algebraMap K[X] (RatFunc K) f.num
      * (algebraMap K[X] (RatFunc K) f.denom)⁻¹ := by
    rw [← div_eq_mul_inv, f.num_div_denom]
  rw [hsplit, (placeOfPoint K a).ord_mul hnum' (inv_ne_zero hden'), Place.ord_inv,
    ord_placeOfPoint_algebraMap_eq_mul a hnum, ord_placeOfPoint_algebraMap_eq_mul a hden]
  exact dvd_add (Dvd.intro_left _ rfl) ((Dvd.intro_left _ rfl).neg_right)

private theorem ord_placeOfPoint_X_sub_C (a : K) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) = 1 := by
  set v := placeOfPoint K a with hv
  set n : ℤ := v.ord (algebraMap K[X] (RatFunc K) (X - C a)) with hn

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπ0 : (π : RatFunc K) ≠ 0 := by
    simpa using hπ.ne_zero
  have h1 : v.ord (π : RatFunc K) = 1 := v.ord_coe_irreducible hπ

  have hdvd : n ∣ 1 := h1 ▸ dvd_ord_placeOfPoint a hπ0

  have hXa : algebraMap K[X] (RatFunc K) (X - C a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr (X_sub_C_ne_zero a)
  have hmem : algebraMap K[X] (RatFunc K) (X - C a) ∈ v.toValuationSubring := by
    rw [hv, placeOfPoint_eq_ofHeightOneSpectrum]
    exact algebraMap_mem_ofHeightOneSpectrum K _ _
  have hnonneg : 0 ≤ n := GaussReduction.ord_nonneg_of_mem_gen v hmem hXa

  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd) with h | h
  · exact h
  · omega

private theorem ord_placeOfPoint_algebraMap (a : K) {q : K[X]} (hq : q ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) q) = rootMultiplicity a q := by
  rw [ord_placeOfPoint_algebraMap_eq_mul a hq, ord_placeOfPoint_X_sub_C a, mul_one]

end AlgebraicCurve.RationalFunctionField

namespace AlgebraicCurve

open IsLocalRing

namespace ComponentChart

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

noncomputable def ofConstantReductionNodes (R : ConstantReduction A F Fbar) (hR : R.IsPointwise)
    (nodes : Finset (Place (ResidueField A) Fbar))
    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 → ∃ D : Divisor L F, ∀ P, D P = P.ord (f : F)) :
    ComponentChart A F Fbar where
  integers := R.integers
  residue := R.residue
  dom := {P | R.placeMap P ∉ nodes}
  nodes := nodes
  placeMap := R.placeMap
  algebraMap_mem_iff := R.algebraMap_mem_iff
  residue_surjective := R.residue_surjective
  ker_residue := R.ker_residue
  residue_algebraMap := R.residue_algebraMap
  exists_smul_mem := R.exists_smul_mem
  placeMap_not_mem_nodes := fun _ h => h
  pointwise := fun P hPdom hP f hf hfib =>
    hR P hP f hf (fun w hw => hfib w (show R.placeMap w ∉ nodes by rw [hw]; exact hPdom) hw)
  mapDomain_placeMap := fun f hf D hDdom hDoff Q hQ => by
    classical
    obtain ⟨Dfull, hDfull⟩ := hdiv f hf
    have hD : D = Dfull.filter (fun P => R.placeMap P ∉ nodes) := by
      ext P
      rw [Finsupp.filter_apply]
      by_cases h : R.placeMap P ∈ nodes
      · rw [if_neg (fun hn => hn h)]
        exact hDoff P (fun hn => hn h)
      · rw [if_pos h]
        exact (hDdom P h).trans (hDfull P).symm
    have hsplit : Dfull = D + Dfull.filter (fun P => ¬ (R.placeMap P ∉ nodes)) := by
      rw [hD]
      exact (Finsupp.filter_add_filter_not Dfull (fun P => R.placeMap P ∉ nodes)).symm
    have hfull := R.mapDomain_placeMap f hf Dfull hDfull Q
    rw [hsplit, Finsupp.mapDomain_add, Finsupp.add_apply] at hfull
    have hzero : Finsupp.mapDomain R.placeMap
        (Dfull.filter (fun P => ¬ (R.placeMap P ∉ nodes))) Q = 0 := by
      rw [← Finsupp.notMem_support_iff]
      intro hmem
      have himg := Finsupp.mapDomain_support hmem
      rw [Finset.mem_image] at himg
      obtain ⟨P, hP, hPQ⟩ := himg
      have hP' := Finsupp.mem_support_iff.mp hP
      rw [Finsupp.filter_apply] at hP'
      by_cases h : R.placeMap P ∈ nodes
      · rw [hPQ] at h
        exact hQ h
      · rw [if_neg (fun hc => hc h)] at hP'
        exact hP' rfl
    rw [hzero, add_zero] at hfull
    exact hfull

@[simp] theorem ofConstantReductionNodes_integers (R : ConstantReduction A F Fbar) (hR : R.IsPointwise)
    (nodes : Finset (Place (ResidueField A) Fbar))
    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 → ∃ D : Divisor L F, ∀ P, D P = P.ord (f : F)) :
    (ofConstantReductionNodes R hR nodes hdiv).integers = R.integers := rfl

@[simp] theorem ofConstantReductionNodes_dom (R : ConstantReduction A F Fbar) (hR : R.IsPointwise)
    (nodes : Finset (Place (ResidueField A) Fbar))
    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 → ∃ D : Divisor L F, ∀ P, D P = P.ord (f : F)) :
    (ofConstantReductionNodes R hR nodes hdiv).dom = {P | R.placeMap P ∉ nodes} := rfl

@[simp] theorem ofConstantReductionNodes_nodes (R : ConstantReduction A F Fbar) (hR : R.IsPointwise)
    (nodes : Finset (Place (ResidueField A) Fbar))
    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 → ∃ D : Divisor L F, ∀ P, D P = P.ord (f : F)) :
    (ofConstantReductionNodes R hR nodes hdiv).nodes = nodes := rfl

@[simp] theorem ofConstantReductionNodes_placeMap (R : ConstantReduction A F Fbar) (hR : R.IsPointwise)
    (nodes : Finset (Place (ResidueField A) Fbar))
    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 → ∃ D : Divisor L F, ∀ P, D P = P.ord (f : F)) :
    (ofConstantReductionNodes R hR nodes hdiv).placeMap = R.placeMap := rfl

@[simp] theorem ofConstantReductionNodes_residue (R : ConstantReduction A F Fbar) (hR : R.IsPointwise)
    (nodes : Finset (Place (ResidueField A) Fbar))
    (hdiv : ∀ f : R.integers, R.residue f ≠ 0 → ∃ D : Divisor L F, ∀ P, D P = P.ord (f : F)) :
    (ofConstantReductionNodes R hR nodes hdiv).residue = R.residue := rfl

end ComponentChart

namespace StandardAnnulus

open Polynomial RationalFunctionField GaussReduction

section PointPlaces

variable {K : Type*} [Field K]

theorem ord_placeOfPoint_X_sub_C (a b : K) [DecidableEq K] :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C b)) = if a = b then 1 else 0 := by
  rw [ord_placeOfPoint_algebraMap a (X_sub_C_ne_zero b), rootMultiplicity_X_sub_C]
  split_ifs <;> rfl

theorem ord_placeOfPoint_X_sub_C_self (a : K) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (X - C a)) = 1 := by
  classical
  rw [ord_placeOfPoint_X_sub_C, if_pos rfl]

theorem ord_placeOfPoint_C (a : K) {c : K} (hc : c ≠ 0) :
    (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) (C c)) = 0 := by
  rw [ord_placeOfPoint_algebraMap a (by simpa using hc), rootMultiplicity_C]
  rfl

theorem algebraMap_mem_placeOfPoint (a : K) (p : K[X]) :
    algebraMap K[X] (RatFunc K) p ∈ (placeOfPoint K a).toValuationSubring := by
  by_cases hp : p = 0
  · rw [hp, map_zero]
    exact zero_mem _
  · apply mem_of_ord_nonneg_gen _ (fun h => hp ((map_eq_zero_iff _
      (IsFractionRing.injective K[X] (RatFunc K))).mp h))
    rw [ord_placeOfPoint_algebraMap a hp]
    exact Int.natCast_nonneg _

theorem X_mem_placeOfPoint (a : K) : (RatFunc.X : RatFunc K) ∈ (placeOfPoint K a).toValuationSubring := by
  rw [← RatFunc.algebraMap_X]
  exact algebraMap_mem_placeOfPoint a X

theorem ord_placeOfPoint_X_sub (a : K) :
    (placeOfPoint K a).ord (RatFunc.X - algebraMap K (RatFunc K) a) = 1 := by
  rw [← RatFunc.algebraMap_X, show algebraMap K (RatFunc K) a = algebraMap K[X] (RatFunc K) (C a) by
    rw [RatFunc.algebraMap_C]; rfl, ← map_sub, ord_placeOfPoint_X_sub_C_self]

section EvalHelpers

variable {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']

theorem evalAt_eq_zero_of_ord_pos (v : Place K' F') {f : F'} (hf0 : f ≠ 0) (h : 0 < v.ord f) :
    v.evalAt f = 0 := by
  have hmem : f ∈ v.toValuationSubring := mem_of_ord_nonneg_gen v hf0 h.le
  rw [v.evalAt_of_mem hmem]
  have hne : v.adicValuation f ≠ 1 := fun h1 =>
    absurd ((v.ord_eq_zero_iff_adicValuation_eq_one hf0).mpr h1) (ne_of_gt h)
  have hlt : v.adicValuation f < 1 := lt_of_le_of_ne (v.mem_iff_adicValuation_le_one.mp hmem) hne
  have hmax : (⟨f, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (v.mem_maximalIdeal_iff_adicValuation_lt_one _).mpr hlt
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hmem⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  rw [hres, ← map_zero (algebraMap K' v.ResidueField), v.residueInv_algebraMap]

theorem evalAt_ne_zero_of_ord_eq_zero (v : Place K' F') (hv : v.IsRational) {f : F'} (hf0 : f ≠ 0)
    (h : v.ord f = 0) : v.evalAt f ≠ 0 := by
  have hmem : f ∈ v.toValuationSubring := mem_of_ord_nonneg_gen v hf0 h.ge
  intro h0
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hmem⟩ = 0 := by
    have h1 := v.algebraMap_evalAt hv hmem
    rw [h0, map_zero] at h1
    exact h1.symm
  have hpos := ord_pos_of_residue_eq_zero v hmem hf0 hres
  omega

theorem evalAt_inv_of_ord_eq_zero (v : Place K' F') (hv : v.IsRational) {f : F'} (hf0 : f ≠ 0)
    (h : v.ord f = 0) : v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hmem : f ∈ v.toValuationSubring := mem_of_ord_nonneg_gen v hf0 h.ge
  have hmem' : f⁻¹ ∈ v.toValuationSubring :=
    mem_of_ord_nonneg_gen v (inv_ne_zero hf0) (by rw [v.ord_inv]; omega)
  have hne := evalAt_ne_zero_of_ord_eq_zero v hv hf0 h
  have hmul : v.evalAt f⁻¹ * v.evalAt f = 1 := by
    rw [← evalAt_mul_of_mem v hv hmem' hmem, inv_mul_cancel₀ hf0, v.evalAt_one]
  exact eq_inv_of_mul_eq_one_left hmul

end EvalHelpers

variable [IsAlgClosed K]

theorem isRational_placeOfPoint (a : K) : (placeOfPoint K a).IsRational :=
  isRational_of_deg_eq_one_gen _ (deg_placeOfPoint K a)

theorem evalAt_placeOfPoint_algebraMap (a : K) (p : K[X]) :
    (placeOfPoint K a).evalAt (algebraMap K[X] (RatFunc K) p) = p.eval a := by
  classical
  have hP := isRational_placeOfPoint (K := K) a

  obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := a) (p := p)
  have hmem := algebraMap_mem_placeOfPoint (K := K) a p
  have hmemC := algebraMap_mem_placeOfPoint (K := K) a (C (p.eval a))
  have hsub : (placeOfPoint K a).evalAt (algebraMap K[X] (RatFunc K) (p - C (p.eval a))) = 0 := by
    by_cases hq0 : q = 0
    · rw [hq, hq0, mul_zero, map_zero, (placeOfPoint K a).evalAt_of_mem (zero_mem _)]
      rw [show (⟨(0 : RatFunc K), zero_mem _⟩ : (placeOfPoint K a).toValuationSubring) = 0 from
        Subtype.ext rfl, map_zero, ← map_zero (algebraMap K (placeOfPoint K a).ResidueField),
        (placeOfPoint K a).residueInv_algebraMap]
    · apply evalAt_eq_zero_of_ord_pos
      · intro h
        have h' := (map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mp h
        rw [hq] at h'
        exact hq0 ((mul_eq_zero.mp h').resolve_left (X_sub_C_ne_zero a))
      · rw [hq, map_mul, (placeOfPoint K a).ord_mul
          (fun h => X_sub_C_ne_zero a ((map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mp h))
          (fun h => hq0 ((map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mp h)),
          ord_placeOfPoint_X_sub_C_self, ord_placeOfPoint_algebraMap a hq0]
        have : (0 : ℤ) ≤ (rootMultiplicity a q : ℤ) := Int.natCast_nonneg _
        omega
  rw [map_sub, evalAt_sub_of_mem _ hP hmem hmemC, RatFunc.algebraMap_C,
    show (RatFunc.C (p.eval a) : RatFunc K) = algebraMap K (RatFunc K) (p.eval a) from rfl,
    evalAt_algebraMap_const _ hP] at hsub
  exact sub_eq_zero.mp hsub

theorem evalAt_placeOfPoint_X (a : K) : (placeOfPoint K a).evalAt (RatFunc.X : RatFunc K) = a := by
  rw [← RatFunc.algebraMap_X, evalAt_placeOfPoint_algebraMap, eval_X]

end PointPlaces

section Admissible

variable {K : Type*} [Field K] (A : ValuationSubring K)

def Admissible (π : A) (a : K) : Prop :=
  A.valuation (π : K) < A.valuation a ∧ A.valuation a < 1

variable {A}

theorem Admissible.ne_zero {π : A} {a : K} (h : Admissible A π a) : a ≠ 0 := by
  intro h0
  have h1 := h.1
  rw [h0, map_zero] at h1
  exact not_lt_of_ge zero_le' h1

theorem Admissible.mem {π : A} {a : K} (h : Admissible A π a) : a ∈ A :=
  (A.valuation_le_one_iff a).mp h.2.le

theorem Admissible.mem_maximalIdeal {π : A} {a : K} (h : Admissible A π a) :
    (⟨a, h.mem⟩ : A) ∈ maximalIdeal A :=
  (A.valuation_lt_one_iff _).mpr h.2

theorem Admissible.exists_eq_mul {π : A} {a : K} (h : Admissible A π a) :
    ∃ m ∈ maximalIdeal A, (π : K) = a * m := by
  have ha0 := h.ne_zero
  have hva0 : A.valuation a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
  have hvm : A.valuation ((π : K) * a⁻¹) < 1 := by
    rw [map_mul, map_inv₀]
    calc A.valuation (π : K) * (A.valuation a)⁻¹
        < A.valuation a * (A.valuation a)⁻¹ := mul_lt_mul_of_pos_right h.1 (inv_pos_of_pos (zero_lt_iff.mpr hva0))
      _ = 1 := mul_inv_cancel₀ hva0
  have hmem : (π : K) * a⁻¹ ∈ A := (A.valuation_le_one_iff _).mp hvm.le
  refine ⟨⟨_, hmem⟩, (A.valuation_lt_one_iff _).mpr hvm, ?_⟩
  show (π : K) = a * ((π : K) * a⁻¹)
  field_simp

theorem admissible_of (π : A) (c : A) (hc : c ∈ maximalIdeal A) (hc0 : (c : K) ≠ 0)
    (hm : ∃ m ∈ maximalIdeal A, (π : K) = c * m) : Admissible A π c := by
  obtain ⟨m, hmmax, hπ⟩ := hm
  refine ⟨?_, (A.valuation_lt_one_iff _).mp hc⟩
  rw [hπ, map_mul]
  have hvc0 : 0 < A.valuation (c : K) := zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hc0)
  calc A.valuation (c : K) * A.valuation (m : K) < A.valuation (c : K) * 1 :=
        mul_lt_mul_of_pos_left ((A.valuation_lt_one_iff _).mp hmmax) hvc0
    _ = A.valuation (c : K) := mul_one _

theorem exists_admissible [IsAlgClosed K] (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : (π : K) ≠ 0) :
    ∃ a : K, Admissible A π a := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self (π : K)
  have hvπ : A.valuation (π : K) = A.valuation s * A.valuation s := by rw [hs, map_mul]
  have hvs0 : A.valuation s ≠ 0 := by
    intro h
    rw [h, mul_zero] at hvπ
    exact hπ0 ((Valuation.zero_iff _).mp hvπ)
  have hvs1 : A.valuation s < 1 := by
    by_contra hge
    rw [not_lt] at hge
    have : 1 ≤ A.valuation (π : K) := by
      rw [hvπ]
      calc (1 : A.ValueGroup) = 1 * 1 := (mul_one _).symm
        _ ≤ A.valuation s * A.valuation s := mul_le_mul' hge hge
    exact absurd ((A.valuation_lt_one_iff _).mp hπ) (not_lt_of_ge this)
  refine ⟨s, ?_, hvs1⟩
  rw [hvπ]
  calc A.valuation s * A.valuation s < A.valuation s * 1 :=
        mul_lt_mul_of_pos_left hvs1 (zero_lt_iff.mpr hvs0)
    _ = A.valuation s := mul_one _

end Admissible

section Poly

variable {K : Type*} [Field K] (A : ValuationSubring K)

noncomputable def innerCount (p : K[X]) : ℕ :=
  Multiset.card (p.roots.filter fun r => A.valuation r < 1)

theorem gaussVal_X_sub_C (r : K) : gaussVal A (X - C r) = max 1 (A.valuation r) := by
  by_cases h : A.valuation r ≤ 1
  · rw [gaussVal_X_sub_C_of_le A r h, max_eq_left h]
  · have hlt : 1 < A.valuation r := lt_of_not_ge h
    have hr0 : r ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hlt
      exact not_lt_of_ge zero_le' hlt
    have hinv : A.valuation r⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ hlt.le
    rw [X_sub_C_eq_of_ne_zero r hr0, gaussVal_mul, gaussVal_C, Valuation.map_neg,
      gaussVal_one_sub_C_mul_X A r⁻¹ hinv, mul_one, max_eq_right hlt.le]

theorem gaussVal_prod_X_sub_C (s : Multiset K) :
    gaussVal A ((s.map fun r => X - C r).prod) = (s.map fun r => max 1 (A.valuation r)).prod := by
  rw [show gaussVal A = ⇑(gaussValuationPoly A) from rfl, map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun r _ => ?_
  exact gaussVal_X_sub_C A r

omit A in
theorem eval_prod_X_sub_C (s : Multiset K) (a : K) :
    ((s.map fun r => X - C r).prod).eval a = (s.map fun r => a - r).prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun r _ => ?_
  simp

variable {A}

theorem valuation_sub_root {π : A} {a r : K} (ha : Admissible A π a) (hr : ¬ Admissible A π r) :
    A.valuation (a - r) = max 1 (A.valuation r) * (if A.valuation r < 1 then A.valuation a else 1) := by
  by_cases h : A.valuation r < 1
  · have hle : A.valuation r ≤ A.valuation (π : K) := by
      by_contra hlt
      rw [not_le] at hlt
      exact hr ⟨hlt, h⟩
    have hlt : A.valuation r < A.valuation a := lt_of_le_of_lt hle ha.1
    rw [if_pos h, max_eq_left h.le, one_mul]
    exact Valuation.map_sub_eq_of_lt_left _ hlt
  · rw [not_lt] at h
    have hlt : A.valuation a < A.valuation r := lt_of_lt_of_le ha.2 h
    rw [if_neg (not_lt.mpr h), max_eq_right h, mul_one]
    exact Valuation.map_sub_eq_of_lt_right _ hlt

theorem prod_valuation_sub_roots {π : A} {a : K} (ha : Admissible A π a) (s : Multiset K)
    (hs : ∀ r ∈ s, ¬ Admissible A π r) :
    (s.map fun r => A.valuation (a - r)).prod
      = (s.map fun r => max 1 (A.valuation r)).prod
        * A.valuation a ^ Multiset.card (s.filter fun r => A.valuation r < 1) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have hr := hs r (Multiset.mem_cons_self _ _)
    have hs' : ∀ x ∈ s, ¬ Admissible A π x := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, ih hs',
      valuation_sub_root ha hr]
    by_cases h : A.valuation r < 1
    · rw [if_pos h, Multiset.filter_cons_of_pos (p := fun r => A.valuation r < 1) s h, Multiset.card_cons, pow_succ]
      ac_rfl
    · rw [if_neg h, Multiset.filter_cons_of_neg (p := fun r => A.valuation r < 1) s h, mul_one]
      ac_rfl

theorem valuation_eval_eq_pow [IsAlgClosed K] {π : A} (p : K[X]) (hp : gaussVal A p = 1)
    (hroots : ∀ r, Admissible A π r → ¬ p.IsRoot r) {a : K} (ha : Admissible A π a) :
    A.valuation (p.eval a) = A.valuation a ^ innerCount A p := by
  have hp0 : p ≠ 0 := fun h => by
    rw [h, gaussVal_zero] at hp
    exact zero_ne_one hp
  have hsplit : p = C p.leadingCoeff * (p.roots.map fun r => X - C r).prod :=
    (IsAlgClosed.splits p).eq_prod_roots
  have hs : ∀ r ∈ p.roots, ¬ Admissible A π r :=
    fun r hr hadm => hroots r hadm ((mem_roots hp0).mp hr)
  have heval : p.eval a = p.leadingCoeff * (p.roots.map fun r => a - r).prod := by
    conv_lhs => rw [hsplit]
    rw [eval_mul, eval_C, eval_prod_X_sub_C]
  have hgauss : gaussVal A p = A.valuation p.leadingCoeff * (p.roots.map fun r => max 1 (A.valuation r)).prod := by
    conv_lhs => rw [hsplit]
    rw [gaussVal_mul, gaussVal_C, gaussVal_prod_X_sub_C]
  rw [heval, map_mul, map_multiset_prod, Multiset.map_map,
    show (p.roots.map (⇑A.valuation ∘ fun r => a - r)) = p.roots.map fun r => A.valuation (a - r) from rfl,
    prod_valuation_sub_roots ha p.roots hs, ← mul_assoc, ← hgauss, hp, one_mul]
  rfl

theorem not_isRoot_of_isCoprime {p q : K[X]} (h : IsCoprime p q) {r : K} (hp : p.IsRoot r) :
    ¬ q.IsRoot r := by
  intro hq
  obtain ⟨u, v, huv⟩ := h
  have h1 := congrArg (eval r) huv
  rw [eval_add, eval_mul, eval_mul, hp.eq_zero, hq.eq_zero, mul_zero, mul_zero, add_zero, eval_one] at h1
  exact zero_ne_one h1

theorem rootMultiplicity_zero_map_residue [IsAlgClosed K] (pA : Polynomial ↥A)
    (h1 : gaussVal A (pA.map A.subtype) = 1) :
    rootMultiplicity 0 (pA.map (IsLocalRing.residue ↥A)) = innerCount A (pA.map A.subtype) := by
  classical
  obtain ⟨c, sInt, sNon, hcunit, hroots, hsNon, hres⟩ := exists_factored_rep A pA h1
  have hc0 : IsLocalRing.residue ↥A c ≠ 0 := by
    intro h0
    have hm := (IsLocalRing.residue_eq_zero_iff _).mp h0
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hm)) hcunit
  have hmm : (sInt.map fun a => X - C (IsLocalRing.residue ↥A a))
      = (sInt.map (IsLocalRing.residue ↥A)).map (fun b => X - C b) := by
    rw [Multiset.map_map]
    rfl
  rw [hres, ← count_roots, roots_C_mul _ hc0, hmm, roots_multiset_prod_X_sub_C, Multiset.count_map]
  unfold innerCount
  rw [hroots, Multiset.filter_add, Multiset.card_add]
  have hNon : (sNon.filter fun r => A.valuation r < 1) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro r hr hlt
    exact hsNon r hr hlt.le
  rw [hNon, Multiset.card_zero, add_zero, Multiset.filter_map, Multiset.card_map]
  congr 1
  refine Multiset.filter_congr fun a _ => ?_
  rw [Function.comp_apply, eq_comm, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]

theorem exists_coprime_unit_repr (f : ↥(gaussIntegers A))
    (hu : gaussValuation A (f : RatFunc K) = 1) :
    ∃ PA QA : Polynomial ↥A,
      gaussVal A (QA.map A.subtype) = 1 ∧ gaussVal A (PA.map A.subtype) = 1 ∧
      IsCoprime (PA.map A.subtype) (QA.map A.subtype) ∧
      (f : RatFunc K) * algebraMap K[X] (RatFunc K) (QA.map A.subtype)
        = algebraMap K[X] (RatFunc K) (PA.map A.subtype) := by
  classical
  obtain ⟨P, Q, hQ0, hPQ, hcop⟩ : ∃ (P Q : K[X]), Q ≠ 0 ∧
      (f : RatFunc K) = algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q ∧ IsCoprime P Q :=
    ⟨RatFunc.num (f : RatFunc K), RatFunc.denom (f : RatFunc K),
      RatFunc.denom_ne_zero _, (RatFunc.num_div_denom _).symm, RatFunc.isCoprime_num_denom _⟩
  obtain ⟨i₀, hi₀mem, hi₀⟩ := exists_gaussVal_eq A Q hQ0
  set c := Q.coeff i₀ with hcdef
  have hc0 : c ≠ 0 := Polynomial.mem_support_iff.mp hi₀mem
  set P' := Polynomial.C c⁻¹ * P with hP'def
  set Q' := Polynomial.C c⁻¹ * Q with hQ'def
  have hQ'0 : Q' ≠ 0 := mul_ne_zero (by simpa using inv_ne_zero hc0) hQ0
  have hcop' : IsCoprime P' Q' := by
    rw [hP'def, hQ'def]
    exact (isCoprime_mul_unit_left (Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero hc0))) P Q).mpr hcop
  have hgQ' : gaussVal A Q' = 1 := by
    rw [hQ'def, gaussVal_mul, gaussVal_C, map_inv₀, hi₀, inv_mul_cancel₀]
    exact gaussVal_ne_zero A Q hQ0
  have hPQ' : (f : RatFunc K)
      = algebraMap K[X] (RatFunc K) P' / algebraMap K[X] (RatFunc K) Q' := by
    rw [hP'def, hQ'def, map_mul, map_mul, mul_div_mul_left, hPQ]
    intro h
    exact inv_ne_zero hc0 (Polynomial.C_eq_zero.mp
      ((map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mp h))
  have hfQP : (f : RatFunc K) * algebraMap K[X] (RatFunc K) Q'
      = algebraMap K[X] (RatFunc K) P' := by
    rw [hPQ', div_mul_cancel₀]
    intro h
    exact hQ'0 ((map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mp h)
  have hgP' : gaussVal A P' = 1 := by
    have hval : gaussValuation A (f : RatFunc K) * gaussVal A Q' = gaussVal A P' := by
      rw [← gaussValuation_algebraMap_poly A Q', ← gaussValuation_algebraMap_poly A P',
        ← map_mul, hfQP]
    rw [← hval, hu, hgQ', mul_one]
  have hPcoef : (↑P'.coeffs : Set K) ⊆ (A.toSubring : Set K) := by
    intro x hx
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    exact (A.valuation_le_one_iff _).mp
      ((valuation_coeff_le_gaussVal A P' n).trans (le_of_eq hgP'))
  have hQcoef : (↑Q'.coeffs : Set K) ⊆ (A.toSubring : Set K) := by
    intro x hx
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
    exact (A.valuation_le_one_iff _).mp
      ((valuation_coeff_le_gaussVal A Q' n).trans (le_of_eq hgQ'))
  refine ⟨P'.toSubring A.toSubring hPcoef, Q'.toSubring A.toSubring hQcoef, ?_, ?_, ?_, ?_⟩
  · have hmap : (Q'.toSubring A.toSubring hQcoef).map A.subtype = Q' := by
      ext n
      rw [Polynomial.coeff_map]
      exact Polynomial.coeff_toSubring Q' A.toSubring hQcoef
    rw [hmap, hgQ']
  · have hmap : (P'.toSubring A.toSubring hPcoef).map A.subtype = P' := by
      ext n
      rw [Polynomial.coeff_map]
      exact Polynomial.coeff_toSubring P' A.toSubring hPcoef
    rw [hmap, hgP']
  · have hmapP : (P'.toSubring A.toSubring hPcoef).map A.subtype = P' := by
      ext n
      rw [Polynomial.coeff_map]
      exact Polynomial.coeff_toSubring P' A.toSubring hPcoef
    have hmapQ : (Q'.toSubring A.toSubring hQcoef).map A.subtype = Q' := by
      ext n
      rw [Polynomial.coeff_map]
      exact Polynomial.coeff_toSubring Q' A.toSubring hQcoef
    rw [hmapP, hmapQ]
    exact hcop'
  · have hmapP : (P'.toSubring A.toSubring hPcoef).map A.subtype = P' := by
      ext n
      rw [Polynomial.coeff_map]
      exact Polynomial.coeff_toSubring P' A.toSubring hPcoef
    have hmapQ : (Q'.toSubring A.toSubring hQcoef).map A.subtype = Q' := by
      ext n
      rw [Polynomial.coeff_map]
      exact Polynomial.coeff_toSubring Q' A.toSubring hQcoef
    rw [hmapP, hmapQ]
    exact hfQP

end Poly

section Core

variable {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K)

theorem ord_algebraMap_eq_zero {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F'] (v : Place K' F')
    {c : K'} (hc : c ≠ 0) : v.ord (algebraMap K' F' c) = 0 := by
  have h0 : algebraMap K' F' c ≠ 0 := (_root_.map_ne_zero _).mpr hc
  have h1 := ord_nonneg_of_mem_gen v (v.algebraMap_mem' c) h0
  have h2 := ord_nonneg_of_mem_gen v (v.algebraMap_mem' c⁻¹) ((_root_.map_ne_zero _).mpr (inv_ne_zero hc))
  rw [map_inv₀, v.ord_inv] at h2
  omega

omit [IsAlgClosed K] in

theorem gaussValuation_eq_one_of_residue_ne_zero' (f : ↥(gaussIntegers A)) (hf : gaussResidue A f ≠ 0) :
    gaussValuation A (f : RatFunc K) = 1 := by
  rw [← isUnit_gauss_iff]
  by_contra hnu
  have hm : f ∈ maximalIdeal ↥(gaussIntegers A) := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
  have hker : f ∈ RingHom.ker (gaussResidue A) := by
    rw [ker_gaussResidue]
    exact hm
  exact hf hker

omit [IsAlgClosed K] in

theorem exists_isUnit_of_valuation_eq_one {x : K} (hx : A.valuation x = 1) :
    ∃ h : x ∈ A, IsUnit (⟨x, h⟩ : A) :=
  ⟨(A.valuation_le_one_iff x).mp hx.le, (A.valuation_eq_one_iff _).mpr hx⟩

theorem valuation_evalAt_eq_zpow (π : A) (g : ↥(gaussIntegers A)) (hres : gaussResidue A g ≠ 0)
    (hord : ∀ a : K, Admissible A π a → (placeOfPoint K a).ord (g : RatFunc K) = 0)
    {a : K} (ha : Admissible A π a) :
    A.valuation ((placeOfPoint K a).evalAt (g : RatFunc K))
      = A.valuation a ^ (placeOfPoint (ResidueField ↥A) 0).ord (gaussResidue A g) := by
  classical
  have hu := gaussValuation_eq_one_of_residue_ne_zero' A g hres
  obtain ⟨PA, QA, hgQ, hgP, hcop, hid⟩ := exists_coprime_unit_repr g hu
  set P := PA.map A.subtype with hPdef
  set Q := QA.map A.subtype with hQdef
  have hP0 : P ≠ 0 := fun h => by
    rw [h, gaussVal_zero] at hgP
    exact zero_ne_one hgP
  have hQ0 : Q ≠ 0 := fun h => by
    rw [h, gaussVal_zero] at hgQ
    exact zero_ne_one hgQ
  have halgP0 : algebraMap K[X] (RatFunc K) P ≠ 0 := fun h =>
    hP0 ((map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mp h)
  have halgQ0 : algebraMap K[X] (RatFunc K) Q ≠ 0 := fun h =>
    hQ0 ((map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mp h)
  have hg0 : (g : RatFunc K) ≠ 0 := fun h => by
    rw [h, map_zero] at hu
    exact zero_ne_one hu

  have hordPQ : ∀ b : K, (placeOfPoint K b).ord (g : RatFunc K)
      = (rootMultiplicity b P : ℤ) - rootMultiplicity b Q := by
    intro b
    have h := congrArg ((placeOfPoint K b).ord) hid
    rw [(placeOfPoint K b).ord_mul hg0 halgQ0, ord_placeOfPoint_algebraMap b hQ0,
      ord_placeOfPoint_algebraMap b hP0] at h
    omega
  have hrootQ : ∀ r, Admissible A π r → ¬ Q.IsRoot r := by
    intro r hr hQr
    have hPr : ¬ P.IsRoot r := fun hPr => not_isRoot_of_isCoprime hcop hPr hQr
    have h := hordPQ r
    rw [hord r hr, rootMultiplicity_eq_zero hPr] at h
    have hpos : 0 < rootMultiplicity r Q := (rootMultiplicity_pos hQ0).mpr hQr
    omega
  have hrootP : ∀ r, Admissible A π r → ¬ P.IsRoot r := by
    intro r hr hPr
    have hQr : ¬ Q.IsRoot r := not_isRoot_of_isCoprime hcop hPr
    have h := hordPQ r
    rw [hord r hr, rootMultiplicity_eq_zero hQr] at h
    have hpos : 0 < rootMultiplicity r P := (rootMultiplicity_pos hP0).mpr hPr
    omega

  have hPl := isRational_placeOfPoint (K := K) a
  have hQa0 : Q.eval a ≠ 0 := fun h => hrootQ a ha h
  have hordQa : (placeOfPoint K a).ord (algebraMap K[X] (RatFunc K) Q) = 0 := by
    rw [ord_placeOfPoint_algebraMap a hQ0, rootMultiplicity_eq_zero (fun h => hrootQ a ha h)]
    rfl
  have hQinvmem : (algebraMap K[X] (RatFunc K) Q)⁻¹ ∈ (placeOfPoint K a).toValuationSubring :=
    mem_of_ord_nonneg_gen _ (inv_ne_zero halgQ0) (by rw [(placeOfPoint K a).ord_inv, hordQa]; norm_num)
  have hgeq : (g : RatFunc K) = algebraMap K[X] (RatFunc K) P * (algebraMap K[X] (RatFunc K) Q)⁻¹ := by
    rw [← hid, mul_assoc, mul_inv_cancel₀ halgQ0, mul_one]
  have heval : (placeOfPoint K a).evalAt (g : RatFunc K) = P.eval a * (Q.eval a)⁻¹ := by
    rw [hgeq, evalAt_mul_of_mem _ hPl (algebraMap_mem_placeOfPoint a P) hQinvmem,
      evalAt_inv_of_ord_eq_zero _ hPl halgQ0 hordQa, evalAt_placeOfPoint_algebraMap,
      evalAt_placeOfPoint_algebraMap]

  have hsubQ : (⟨(g : RatFunc K), g.2⟩ : ↥(gaussIntegers A)) * polyToGauss A QA = polyToGauss A PA := by
    apply Subtype.ext
    rw [Subring.coe_mul, polyToGauss_coe, polyToGauss_coe]
    exact hid
  have hresQ : gaussResidue A (polyToGauss A QA) ≠ 0 := map_residue_ne_zero_of_gaussVal_one A QA hgQ
  have hresP : gaussResidue A (polyToGauss A PA) ≠ 0 := map_residue_ne_zero_of_gaussVal_one A PA hgP
  have hmapQ0 : QA.map (IsLocalRing.residue ↥A) ≠ 0 := by
    intro h
    apply hresQ
    rw [gaussResidue_polyToGauss, h, map_zero]
  have hmapP0 : PA.map (IsLocalRing.residue ↥A) ≠ 0 := by
    intro h
    apply hresP
    rw [gaussResidue_polyToGauss, h, map_zero]
  have hordbar : (placeOfPoint (ResidueField ↥A) 0).ord (gaussResidue A g)
      = (innerCount A P : ℤ) - innerCount A Q := by
    have h := congrArg (gaussResidue A) hsubQ
    rw [map_mul, show (⟨(g : RatFunc K), g.2⟩ : ↥(gaussIntegers A)) = g from Subtype.ext rfl] at h
    have h2 := congrArg ((placeOfPoint (ResidueField ↥A) 0).ord) h
    rw [(placeOfPoint (ResidueField ↥A) 0).ord_mul hres hresQ, gaussResidue_polyToGauss,
      gaussResidue_polyToGauss, ord_placeOfPoint_algebraMap 0 hmapQ0,
      ord_placeOfPoint_algebraMap 0 hmapP0, rootMultiplicity_zero_map_residue QA hgQ,
      rootMultiplicity_zero_map_residue PA hgP] at h2
    rw [hPdef, hQdef]
    omega

  have hva0 : A.valuation a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha.ne_zero
  rw [heval, map_mul, map_inv₀, valuation_eval_eq_pow P hgP hrootP ha, valuation_eval_eq_pow Q hgQ hrootQ ha,
    hordbar, zpow_sub₀ hva0, zpow_natCast, zpow_natCast, div_eq_mul_inv]

theorem exists_isUnit_evalAt_mul_zpow (π : A) (g : ↥(gaussIntegers A)) (hres : gaussResidue A g ≠ 0)
    (hord : ∀ a : K, Admissible A π a → (placeOfPoint K a).ord (g : RatFunc K) = 0)
    {a : K} (ha : Admissible A π a) :
    ∃ h : (placeOfPoint K a).evalAt (g : RatFunc K)
        * ((placeOfPoint K a).evalAt (RatFunc.X : RatFunc K))
            ^ (-(placeOfPoint (ResidueField ↥A) 0).ord (gaussResidue A g)) ∈ A,
      IsUnit (⟨_, h⟩ : A) := by
  apply exists_isUnit_of_valuation_eq_one
  have hva0 : A.valuation a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha.ne_zero
  rw [evalAt_placeOfPoint_X, map_mul, map_zpow₀, valuation_evalAt_eq_zpow A π g hres hord ha, zpow_neg,
    mul_inv_cancel₀ (zpow_ne_zero _ hva0)]

end Core

section TheAnnulus

variable {K : Type*} [Field K] [IsAlgClosed K] (A : ValuationSubring K)

noncomputable def standardAnnulus (π : A) (hπ : π ∈ maximalIdeal A) : Annulus A (RatFunc K) where
  dom := {P | ∃ a : K, Admissible A π a ∧ P = placeOfPoint K a}
  param := RatFunc.X
  modulus := π
  modulus_mem := hπ
  mem_dom := by
    rintro P ⟨a, ha, rfl⟩
    refine ⟨isRational_placeOfPoint a, X_mem_placeOfPoint a, ?_, ?_, ?_⟩
    · rw [evalAt_placeOfPoint_X]
      exact ⟨ha.mem, ha.mem_maximalIdeal⟩
    · rw [evalAt_placeOfPoint_X]
      exact ha.ne_zero
    · rw [evalAt_placeOfPoint_X]
      exact ha.exists_eq_mul
  existsUnique_evalAt_eq := by
    intro c hc hc0 hm
    have hadm : Admissible A π c := admissible_of π c hc hc0 hm
    refine ⟨placeOfPoint K c, ⟨⟨c, hadm, rfl⟩, evalAt_placeOfPoint_X (c : K)⟩, ?_⟩
    rintro P ⟨⟨a, ha, rfl⟩, hPa⟩
    rw [evalAt_placeOfPoint_X] at hPa
    rw [hPa]
  ord_param_sub := by
    rintro P ⟨a, ha, rfl⟩
    rw [evalAt_placeOfPoint_X, ord_placeOfPoint_X_sub]
  unit_principle := by
    intro f hf0 hordf
    obtain ⟨c, hcg, hres⟩ := exists_smul_gaussResidue_ne_zero A f hf0
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hres
      have h0 : (⟨(0 : K) • f, hcg⟩ : ↥(gaussIntegers A)) = 0 := Subtype.ext (zero_smul K f)
      rw [h0, map_zero]
    have hordg : ∀ a : K, Admissible A π a → (placeOfPoint K a).ord (c • f) = 0 := by
      intro a ha
      rw [Algebra.smul_def, (placeOfPoint K a).ord_mul ((_root_.map_ne_zero _).mpr hc0) hf0,
        ord_algebraMap_eq_zero _ hc0, hordf (placeOfPoint K a) ⟨a, ha, rfl⟩, add_zero]
    refine ⟨(placeOfPoint (ResidueField ↥A) 0).ord (gaussResidue A ⟨c • f, hcg⟩), c⁻¹, inv_ne_zero hc0, ?_⟩
    rintro P ⟨a, ha, rfl⟩
    have hcore := exists_isUnit_evalAt_mul_zpow A π ⟨c • f, hcg⟩ hres hordg ha
    have hPl := isRational_placeOfPoint (K := K) a
    have hfmem : f ∈ (placeOfPoint K a).toValuationSubring :=
      mem_of_ord_nonneg_gen _ hf0 (by rw [hordf (placeOfPoint K a) ⟨a, ha, rfl⟩])
    have hsmul : (placeOfPoint K a).evalAt ((⟨c • f, hcg⟩ : ↥(gaussIntegers A)) : RatFunc K)
        = (placeOfPoint K a).evalAt f * c⁻¹⁻¹ := by
      rw [inv_inv, show (((⟨c • f, hcg⟩ : ↥(gaussIntegers A)) : RatFunc K)) = c • f from rfl, Algebra.smul_def,
        evalAt_mul_of_mem _ hPl ((placeOfPoint K a).algebraMap_mem' c) hfmem, evalAt_algebraMap_const _ hPl, mul_comm]
    rw [hsmul] at hcore
    exact hcore

theorem standardAnnulus_dom (π : A) (hπ : π ∈ maximalIdeal A) :
    (standardAnnulus A π hπ).dom = {P | ∃ a : K, Admissible A π a ∧ P = placeOfPoint K a} := rfl

theorem standardAnnulus_param (π : A) (hπ : π ∈ maximalIdeal A) :
    (standardAnnulus A π hπ).param = RatFunc.X := rfl

theorem standardAnnulus_dom_nonempty (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : (π : K) ≠ 0) :
    (standardAnnulus A π hπ).dom.Nonempty := by
  obtain ⟨a, ha⟩ := exists_admissible π hπ hπ0
  exact ⟨placeOfPoint K a, a, ha, rfl⟩

end TheAnnulus

section Degenerate

variable {K : Type*} [Field K]

theorem not_admissible_top (π : ↥(⊤ : ValuationSubring K)) (a : K) :
    ¬ Admissible (⊤ : ValuationSubring K) π a := by
  rintro ⟨h1, h2⟩
  have hmem : (⟨a, ValuationSubring.mem_top a⟩ : ↥(⊤ : ValuationSubring K))
      ∈ maximalIdeal ↥(⊤ : ValuationSubring K) :=
    (ValuationSubring.valuation_lt_one_iff _ _).mpr h2
  rw [Annulus.maximalIdeal_top_eq_bot' K, Ideal.mem_bot] at hmem
  have ha : a = 0 := congrArg Subtype.val hmem
  rw [ha, map_zero] at h1
  exact not_lt_of_ge zero_le' h1

theorem standardAnnulus_top_dom [IsAlgClosed K] (π : ↥(⊤ : ValuationSubring K))
    (hπ : π ∈ maximalIdeal ↥(⊤ : ValuationSubring K)) :
    (standardAnnulus (⊤ : ValuationSubring K) π hπ).dom = ∅ := by
  ext P
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, ha, -⟩
  exact not_admissible_top π a ha

attribute [local instance] ConstantReduction.ofTopAlgebra in

noncomputable def _root_.AlgebraicCurve.ComponentChart.ofConstantReductionNodesSelf (L : Type*) [Field L]
    (nodes : Finset (Place (ResidueField ↥(⊤ : ValuationSubring L)) L)) :
    ComponentChart (⊤ : ValuationSubring L) L L :=
  ComponentChart.ofConstantReductionNodes (ConstantReduction.ofTop L L)
    (ConstantReduction.isPointwise_ofTop L L) nodes
    (fun _ _ => ⟨0, fun P => (ConstantReduction.isEmpty_place_self L).elim P⟩)

end Degenerate

end StandardAnnulus

end AlgebraicCurve


