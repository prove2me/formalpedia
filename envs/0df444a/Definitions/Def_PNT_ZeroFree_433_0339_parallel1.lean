-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0339_parallel1
-- name    : PNT_ZeroFree_433_0339_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:15:08.647665+00:00
-- url     : https://prove2.me/theorems/8119d97c-cea3-4ee4-b603-7267c5e54374
-- title:
--   Zero-free region foundations: CubicSieve.Poisson, CubicSieve.Initial [0339_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.CubicSieve.Poisson
--   - OAI.NumberTheory.DirichletL.CubicSieve.Initial
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/Poisson.lean#L12-L355
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/Initial.lean#L13-L344

import Definitions.Def_PNT_ZeroFree_433_0004
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0010
import Definitions.Def_PNT_ZeroFree_433_0013
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0032
import Definitions.Def_PNT_ZeroFree_433_0037_1
import Definitions.Def_PNT_ZeroFree_433_0038
import Definitions.Def_PNT_ZeroFree_433_0038_1
import Definitions.Def_PNT_ZeroFree_433_0039
import Definitions.Def_PNT_ZeroFree_433_0040
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0042
import Definitions.Def_PNT_ZeroFree_433_0043
import Definitions.Def_PNT_ZeroFree_433_0043_1
import Definitions.Def_PNT_ZeroFree_433_0051
import Definitions.Def_PNT_ZeroFree_433_0052
import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/Poisson.lean#L12-L355
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/CubicSieve/Initial.lean#L13-L344
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.Poisson
section
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson QuadraticInitialBound
open CompletedGauss ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem canonical_finite_prime_gauss_transform_scalar_of_nontrivial
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      (finiteSexticQuotientRow P hc hgood j h)⁻¹ *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  exact IdealGaussCRT.gauss_transform_finite_crt_scalar (fun i => O ⧸ P i)
    (IdealGaussCRT.quotientProdEquivPi P hc)
    (fun i => actualSextic (P i) (hgood i) ^ j i) ψ
    hχ h

theorem canonical_finite_prime_gauss_transform_conj_of_nontrivial
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hc : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (ψ : AddChar (O ⧸ ∏ i, P i) ℂ) (h : O ⧸ ∏ i, P i) :
    (∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ (h * x)) =
      star (finiteSexticQuotientRow P hc hgood j h) *
        ∑ x : O ⧸ ∏ i, P i, finiteSexticQuotientRow P hc hgood j x * ψ x := by
  rw [canonical_finite_prime_gauss_transform_scalar_of_nontrivial P hc hgood j hχ ψ,
    finiteSexticQuotientRow_inv_eq_star P hc hgood j h]

theorem canonical_principal_gauss_transform_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    [Fintype (O ⧸ ∏ i, P i)] [∀ i, Fintype (O ⧸ P i)]
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i)
    [Fintype (O ⧸ Ideal.span {c})]
    (ψ : AddChar (O ⧸ Ideal.span {c}) ℂ) (h : O ⧸ Ideal.span {c}) :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ (h * r)) =
      star (principalSexticRow P hcop hgood j c hc h) *
        ∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r * ψ r := by
  let e := Ideal.quotEquivOfEq hc
  let row := finiteSexticQuotientRow P hcop hgood j
  let φ : AddChar (O ⧸ ∏ i, P i) ℂ := ψ.compAddMonoidHom e.symm.toAddMonoidHom
  have hleft :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ (e h * x) := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ (e h * x))]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ (h * r) = row (e r) * ψ (e.symm (e h * e r))
    rw [← map_mul, e.symm_apply_apply]
  have hbase :
      (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r) =
        ∑ x : O ⧸ ∏ i, P i, row x * φ x := by
    rw [← Equiv.sum_comp e.toEquiv (fun x => row x * φ x)]
    apply Finset.sum_congr rfl
    intro r _
    change row (e r) * ψ r = row (e r) * ψ (e.symm (e r))
    rw [e.symm_apply_apply]
  change (∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ (h * r)) =
    star (row (e h)) * ∑ r : O ⧸ Ideal.span {c}, row (e r) * ψ r
  rw [hleft, hbase]
  exact canonical_finite_prime_gauss_transform_conj_of_nontrivial P hcop hgood j hχ φ (e h)

theorem canonical_radial_poisson_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    let hc0 := finitePrimeModulus_ne_zero P
    let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
    let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
    let ψ := eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc0
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (span_finitePrimeModulus P)
  let : Fintype (O ⧸ ∏ i, P i) := Fintype.ofEquiv (O ⧸ Ideal.span {c}) e.toEquiv
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let row := principalSexticRow P hcop hgood j c (span_finitePrimeModulus P)
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  have ht (h : O) :
      (∑ r : O ⧸ Ideal.span {c}, row r * ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) =
        star (finiteSexticRow P hgood j h) * (∑ r, row r * ψ r) := by
    rw [canonical_principal_gauss_transform_of_nontrivial P hcop hgood j hχ c
      (span_finitePrimeModulus P) ψ,
      principalSexticRow_mk P hcop hgood j c (span_finitePrimeModulus P) h]
  have hp := actual_radial_paper_poisson_trace W scale hscale c hc0 row
  change (∑' z : O, row (Ideal.Quotient.mk (Ideal.span {c}) z) *
    W (‖eisEmbedding z‖ ^ 2 / scale)) =
      (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
        (∑ r : O ⧸ Ideal.span {c}, row r *
          ψ (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [ht] at hp
  simpa only [row, principalSexticRow_mk P hcop hgood j c
    (span_finitePrimeModulus P)] using hp

theorem canonical_radial_poisson_normalized_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    let c := finitePrimeModulus P
    (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss P hcop hgood j / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, star (finiteSexticRow P hgood j h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  classical
  let c := finitePrimeModulus P
  let G := canonicalGaussSum P hcop hgood j
  let F : O → ℂ := fun h => star (finiteSexticRow P hgood j h) *
    paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)
  have hp := canonical_radial_poisson_of_nontrivial P hcop hgood j hχ W scale hscale
  change (∑' z : O, finiteSexticRow P hgood j z * W (‖eisEmbedding z‖ ^ 2 / scale)) =
    (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
      (star (finiteSexticRow P hgood j h) * G) *
        paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  have hsum : (∑' h : O, (star (finiteSexticRow P hgood j h) * G) *
      paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)) =
      G * ∑' h : O, F h := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    dsimp [F]
    ring
  rw [hsum] at hp
  rw [hp]
  change ((scale / ‖eisEmbedding c‖ ^ 2 : ℝ) : ℂ) * (G * ∑' h : O, F h) =
    ((scale : ℂ) * (G / (‖eisEmbedding c‖ : ℂ)) / (‖eisEmbedding c‖ : ℂ)) *
      ∑' h : O, F h
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P)))
  push_cast
  field_simp

theorem norm_canonicalGaussSum_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1) :
    ‖canonicalGaussSum P hcop hgood j‖ = ‖eisEmbedding (finitePrimeModulus P)‖ := by
  classical
  let c := finitePrimeModulus P
  have hc0 : c ≠ 0 := finitePrimeModulus_ne_zero P
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ P i) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
  let e : (O ⧸ Ideal.span {c}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq (span_finitePrimeModulus P)).trans
      (IdealGaussCRT.quotientProdEquivPi P hcop)
  let χ : ∀ i, MulChar (O ⧸ P i) ℂ := fun i => actualSextic (P i) (hgood i) ^ j i
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc0
  have hψ : ψ.IsPrimitive := GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc0
  have hnormsq := IdealGaussCRT.norm_gauss_finite_crt_sq (fun i => O ⧸ P i)
    e χ ψ hχ (fun i => IdealGaussCRT.coordinateAddChar_isPrimitive
      (fun i => O ⧸ P i) e ψ hψ i)
  change ‖canonicalGaussSum P hcop hgood j‖ ^ 2 =
    (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) at hnormsq
  have hcard : (Fintype.card (O ⧸ Ideal.span {c}) : ℝ) = ‖eisEmbedding c‖ ^ 2 := by
    symm
    simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] using
      eisEmbedding_norm_sq_eq_absNorm_span c
  rw [hcard] at hnormsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hnormsq

theorem norm_canonicalNormalizedGauss_of_nontrivial {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, goodLambda ∉ P i)
    (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hgood i) ^ j i ≠ 1) :
    ‖canonicalNormalizedGauss P hcop hgood j‖ = 1 := by
  have hn : ‖eisEmbedding (finitePrimeModulus P)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  change ‖canonicalGaussSum P hcop hgood j /
    (‖eisEmbedding (finitePrimeModulus P)‖ : ℂ)‖ = 1
  rw [norm_div,
    norm_canonicalGaussSum_of_nontrivial P hcop hgood j hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), div_self hn]

theorem canonical_polya_vinogradov_of_nontrivial {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (P i) (hg i) ^ j i ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, finiteSexticRow P hg j z * W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      pvControl W * ‖eisEmbedding (finitePrimeModulus P)‖ := by
  let c := finitePrimeModulus P
  let q := ‖eisEmbedding c‖
  have hq : 0 < q := norm_pos_iff.mpr (eisEmbedding_ne_zero (finitePrimeModulus_ne_zero P))
  let t := M / q ^ 2
  have ht : 0 < t := div_pos hM (sq_pos_of_pos hq)
  let F : O → ℂ := fun h => star (finiteSexticRow P hg j h) *
    paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)
  have hF (h : O) : ‖F h‖ ≤ ‖paperRadialFourier W (t * ‖eisEmbedding h‖ ^ 2)‖ := by
    dsimp only [F]
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (finiteSexticRow_norm_le_one P hg j h)
  have hs := paperRadialFourier_lattice_summable_norm W t ht
  have hFs : Summable (fun h : O => ‖F h‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF hs
  have hzero : F 0 = 0 := by simp only [F, finiteSexticRow_zero P hg j, star_zero, zero_mul]
  have heq : (∑' h : O, F h) = ∑' h : {h : O // h ≠ 0}, F h := by
    symm
    apply tsum_subtype_eq_of_support_subset
    intro h hh hz
    subst h
    exact hh hzero
  have hn : ‖∑' h : O, F h‖ ≤
      ∑' h : {h : O // h ≠ 0}, ‖paperRadialFourier W (t * ‖eisEmbedding h.val‖ ^ 2)‖ := by
    rw [heq]
    exact (norm_tsum_le_tsum_norm (hFs.subtype _)).trans
      ((hFs.subtype _).tsum_le_tsum (fun h => hF h) (hs.subtype _))
  have hbound : t * ‖∑' h : O, F h‖ ≤ pvControl W :=
    (mul_le_mul_of_nonneg_left hn ht.le).trans (pv_lattice_bound W t ht)
  rw [canonical_radial_poisson_normalized_of_nontrivial P hcop hg j hχ W M hM]
  have hargs (h : O) : M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2 =
      t * ‖eisEmbedding h‖ ^ 2 := by dsimp [t, q]; ring
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) *
    ∑' h : O, star (finiteSexticRow P hg j h) *
      paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2)‖ ≤ _
  simp_rw [hargs]
  change ‖((M : ℂ) * canonicalNormalizedGauss P hcop hg j / (q : ℂ)) * ∑' h : O, F h‖ ≤ _
  rw [norm_mul, norm_div, norm_mul, norm_canonicalNormalizedGauss_of_nontrivial P hcop hg j hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq]
  change M / q * ‖∑' h : O, F h‖ ≤ pvControl W * q
  calc
    _ = q * (t * ‖∑' h : O, F h‖) := by dsimp [t]; field_simp
    _ ≤ q * pvControl W := mul_le_mul_of_nonneg_left hbound hq.le
    _ = _ := mul_comm _ _

theorem canonical_masked_polya_vinogradov_of_nontrivial
    {α ι : Type*} [DecidableEq α] [Fintype ι] [Nonempty ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (S : Finset α) (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hg : ∀ i, goodLambda ∉ Q i) (j : ι → ℕ)
    (hχ : ∀ i, actualSextic (Q i) (hg i) ^ j i ≠ 1)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, rowCoprimeMask P S z * finiteSexticRow Q hg j z *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ S.card * (pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖) := by
  rw [canonical_masked_radial_dilations P hinj S Q hcop hg j W M hM]
  calc
    _ ≤ ∑ E ∈ S.powerset, ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
        finiteSexticRow Q hg j (primeSubsetGenerator P E) *
        ∑' z : O, finiteSexticRow Q hg j z *
          W (‖eisEmbedding z‖ ^ 2 / (M / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _E ∈ S.powerset, pvControl W * ‖eisEmbedding (finitePrimeModulus Q)‖ := by
      apply Finset.sum_le_sum
      intro E hE
      rw [norm_mul, norm_mul]
      have hp := canonical_polya_vinogradov_of_nontrivial Q hcop hg j hχ W _
        (primeSubset_reducedScale_pos P E hM)
      have hmul : ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ)‖ *
          ‖finiteSexticRow Q hg j (primeSubsetGenerator P E)‖ ≤ 1 := by
        calc
          _ ≤ 1 * 1 := mul_le_mul (norm_ideal_moebius_le_one _)
            (finiteSexticRow_norm_le_one Q hg j _) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul _
      exact (mul_le_of_le_one_left (norm_nonneg _) hmul).trans hp
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

def cubicExponent (negative : Bool) : ℕ := if negative then 4 else 2

theorem cubicExponent_nonprincipal (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (negative : Bool) :
    actualSextic P hg ^ cubicExponent negative ≠ 1 := by
  let χ := actualSextic P hg ^ 2
  have hχ : χ ≠ 1 := by
    dsimp [χ]
    rw [canonicalSextic_pow_two P hg]
    exact (MulChar.ringHomComp_ne_one_iff eisEmbedding_injective).mpr (cubicChar_ne_one P hg)
  have h3 : χ ^ 3 = 1 := by
    dsimp [χ]
    rw [canonicalSextic_pow_two P hg, MulChar.ringHomComp_pow, cubicChar_pow_three P hg, MulChar.ringHomComp_one]
  have h2 : χ ^ 2 ≠ 1 := by
    intro h
    apply hχ
    calc
      χ = χ ^ 2 * χ := by rw [h, one_mul]
      _ = χ ^ 3 := (pow_succ χ 2).symm
      _ = 1 := h3
  cases negative with
  | false => simpa only [cubicExponent, Bool.false_eq_true, ite_false,
      ] using hχ
  | true =>
      have he : actualSextic P hg ^ 4 = χ ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul]
      simpa only [cubicExponent, ite_true, he] using h2

theorem cubic_radial_poisson {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (negative : ι → Bool)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, finiteSexticRow P hg (fun i => cubicExponent (negative i)) z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * canonicalNormalizedGauss P hcop hg
        (fun i => cubicExponent (negative i)) / (‖eisEmbedding (finitePrimeModulus P)‖ : ℂ)) *
      ∑' h : O, star (finiteSexticRow P hg (fun i => cubicExponent (negative i)) h) *
        paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (finitePrimeModulus P)‖ ^ 2) :=
  canonical_radial_poisson_normalized_of_nontrivial P hcop hg _
    (fun i => cubicExponent_nonprincipal (P i) (hg i) (negative i)) W scale hscale

theorem cubic_polya_vinogradov {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hg : ∀ i, goodLambda ∉ P i) (negative : ι → Bool)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    ‖∑' z : O, finiteSexticRow P hg (fun i => cubicExponent (negative i)) z *
      W (‖eisEmbedding z‖ ^ 2 / scale)‖ ≤
        pvControl W * ‖eisEmbedding (finitePrimeModulus P)‖ :=
  canonical_polya_vinogradov_of_nontrivial P hcop hg _
    (fun i => cubicExponent_nonprincipal (P i) (hg i) (negative i)) W scale hscale

end
end SevenEighths.CubicSieve

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.CubicSieve.Initial
section
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CompletedGauss ConcretePrimeRowBridge ShortDraftHeckeBridge QuadraticInitialBound
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicFiniteRow {α : Type*} (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α) (z : O) : ℂ :=
  (finiteSquarefreeRow P hg S z) ^ 2

theorem cubicFiniteRow_eq_canonical {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α) (z : O) :
    cubicFiniteRow P hg S z =
      finiteSexticRow (fun i : S => P i.val) (fun i => hg i.val) (fun _ => 2) z := by
  simp only [cubicFiniteRow, finiteSexticRow, finiteSquarefreeRow,
    MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0), Finset.prod_pow]
  rw [Finset.prod_coe_sort (s := S) (f := fun i => actualSextic (P i) (hg i) (Ideal.Quotient.mk (P i) z))]

def activeCubicExponent {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : ℕ :=
  if i.val ∈ S \ T then 4 else 2

theorem activeCubicExponent_nonprincipal {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (i : activeSupport S T) :
    actualSextic (P i.val) (hg i.val) ^ activeCubicExponent S T i ≠ 1 := by
  have h := cubicExponent_nonprincipal (P i.val) (hg i.val)
    (decide (i.val ∈ S \ T))
  simpa only [cubicExponent, activeCubicExponent, decide_eq_true_eq] using h

theorem cubicFiniteRow_pair_kernel {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S T : Finset α) (z : O) :
    star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z =
      rowCoprimeMask P (S ∩ T) z *
        finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
          (activeCubicExponent S T) z := by
  have h := congrArg (fun v : ℂ => v ^ 2) (finiteSquarefreeRow_pair_activeSupport P hg S T z)
  have hm : rowCoprimeMask P (S ∩ T) z ^ 2 = rowCoprimeMask P (S ∩ T) z := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  have hrow : finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
        (activeExponent S T) z ^ 2 =
      finiteSexticRow (activePrimes P S T) (fun i => hg i.val)
        (activeCubicExponent S T) z := by
    unfold finiteSexticRow
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    have h6 : actualSextic (P i.val) (hg i.val) ^ 6 = 1 :=
      (pow_mul _ 2 3).trans <|
        (congrArg (fun φ : MulChar (O ⧸ P i.val) ℂ => φ ^ 3)
          (canonicalSextic_pow_two (P i.val) (hg i.val))).trans <|
            (MulChar.ringHomComp_pow _ _ _).trans <|
              (congrArg (fun φ : MulChar (O ⧸ P i.val) O => φ.ringHomComp eisEmbedding)
                (cubicChar_pow_three (P i.val) (hg i.val))).trans
                  (MulChar.ringHomComp_one eisEmbedding)
    rw [← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0)]
    apply congrArg (fun χ : MulChar (O ⧸ P i.val) ℂ => χ (Ideal.Quotient.mk (P i.val) z))
    change (actualSextic (P i.val) (hg i.val) ^ activeExponent S T i) ^ 2 = _
    unfold activeExponent activeCubicExponent
    split_ifs
    · rw [← pow_mul, show (5 * 2 : ℕ) = 4 + 6 by decide, pow_add, h6, mul_one]
    · simp
  simpa only [mul_pow, ← star_pow, hm, hrow, cubicFiniteRow] using h

theorem cubic_gram_offdiagonal {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (hne : S ≠ T) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤
      (2 : ℝ) ^ (S ∩ T).card *
        (pvControl W * ‖eisEmbedding (finitePrimeModulus (activePrimes P S T))‖) := by
  let : Nonempty (activeSupport S T) := (activeSupport_nonempty_of_ne hne).to_subtype
  simp_rw [cubicFiniteRow_pair_kernel P hg S T]
  exact canonical_masked_polya_vinogradov_of_nontrivial P hinj (S ∩ T) (activePrimes P S T)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val)
    (activeCubicExponent S T) (activeCubicExponent_nonprincipal P hg S T) W M hM

theorem cubic_gram_offdiagonal_of_norm_le {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (S T : Finset α) (hne : S ≠ T) (N : ℝ) (hN : 0 ≤ N)
    (hS : supportNorm P S ≤ N) (hT : supportNorm P T ≤ N)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ pvControl W * N := by
  apply (cubic_gram_offdiagonal P hinj hg S T hne W M hM).trans
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (divisor_conductor_bound P S T N hN hS hT)
    (pvControl_nonneg W)

theorem cubicFiniteRow_norm_le_one {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α) (z : O) :
    ‖cubicFiniteRow P hg S z‖ ≤ 1 := by
  rw [cubicFiniteRow_eq_canonical]
  exact finiteSexticRow_norm_le_one _ _ _ _

theorem cubic_pair_summable {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S T : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg T z) *
      W (‖eisEmbedding z‖ ^ 2 / M)) := by
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hM)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hW
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (cubicFiniteRow_norm_le_one P hg S z) (cubicFiniteRow_norm_le_one P hg T z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

theorem cubic_gram_diagonal {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, (star (cubicFiniteRow P hg S z) * cubicFiniteRow P hg S z) *
        W (‖eisEmbedding z‖ ^ 2 / M)‖ ≤ diagonalControl W * M := by
  have hMp : 0 < M := by linarith
  have hs := (cubic_pair_summable P hg S S W M hMp).norm
  have hW : Summable (fun z : O => ‖W (‖eisEmbedding z‖ ^ 2 / M)‖) := by
    simpa only [scaledRadialTest_apply] using
      actual_eisenstein_summable_norm (scaledRadialTest W M hMp)
  refine (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum ?_ hW).trans
    (radial_weight_lattice_bound W M hM))
  intro z
  rw [norm_mul, norm_mul, norm_star]
  exact mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_mul (cubicFiniteRow_norm_le_one P hg S z) (cubicFiniteRow_norm_le_one P hg S z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

private theorem norm_sq_finite_sum {β : Type*} (C : Finset β) (a r : β → ℂ) :
    (↑(‖∑ n ∈ C, a n * r n‖ ^ 2) : ℂ) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) * (star (r n) * r m) := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [map_sum, map_mul, starRingEnd_apply]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem cubic_mean_summable {α β : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (fun z : O => W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ)) := by
  have hs := summable_sum (s := C) (fun n hn => summable_sum (s := C) (fun m hm =>
    (cubic_pair_summable P hg (support n) (support m) W M hM).mul_left (star (a n) * a m)))
  apply hs.congr
  intro z
  rw [norm_sq_finite_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  ring

theorem cubic_mean_expand {α β : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (C : Finset β) (support : β → Finset α) (a : β → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ)) =
      ∑ n ∈ C, ∑ m ∈ C, (star (a n) * a m) *
        ∑' z : O, (star (cubicFiniteRow P hg (support n) z) * cubicFiniteRow P hg (support m) z) *
          W (‖eisEmbedding z‖ ^ 2 / M) := by
  let f : β → β → O → ℂ := fun n m z => (star (a n) * a m) *
    ((star (cubicFiniteRow P hg (support n) z) * cubicFiniteRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M))
  have hf (n m : β) : Summable (f n m) :=
    (cubic_pair_summable P hg (support n) (support m) W M hM).mul_left _
  have heq (z : O) : W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ) =
        ∑ n ∈ C, ∑ m ∈ C, f n m z := by
    rw [norm_sq_finite_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro m hm
    dsimp [f]
    ring
  rw [tsum_congr heq, Summable.tsum_finsetSum (fun n hn => summable_sum (fun m hm => hf n m))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Summable.tsum_finsetSum (fun m hm => hf n m)]
  apply Finset.sum_congr rfl
  intro m hm
  exact tsum_mul_left

theorem cubic_initial_mean_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (C : Finset β) (support : β → Finset α)
    (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 1 ≤ M) :
    ‖∑' z : O, W (‖eisEmbedding z‖ ^ 2 / M) *
      (↑(‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) : ℂ)‖ ≤
        (diagonalControl W * M + pvControl W * N * C.card) * ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let D := diagonalControl W * M
  let B := pvControl W * N
  have hB : 0 ≤ B := mul_nonneg (pvControl_nonneg W) hN
  let K : β → β → ℂ := fun n m => ∑' z : O,
    (star (cubicFiniteRow P hg (support n) z) * cubicFiniteRow P hg (support m) z) *
      W (‖eisEmbedding z‖ ^ 2 / M)
  have hK (n : β) (hn : n ∈ C) (m : β) (hm : m ∈ C) :
      ‖K n m‖ ≤ (if n = m then D else 0) + B := by
    by_cases hnm : n = m
    · subst m
      simp only [ite_true]
      exact (cubic_gram_diagonal P hg (support n) W M hM).trans (le_add_of_nonneg_right hB)
    · simp only [hnm, ite_false, zero_add]
      exact cubic_gram_offdiagonal_of_norm_le P hinj hg _ _
        (fun h => hnm (hsupp hn hm h)) N hN (hNorm n hn) (hNorm m hm) W M hMp
  have heq (n : β) (hn : n ∈ C) :
      (∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
        D * ‖a n‖ ^ 2 + B * ‖a n‖ * ∑ m ∈ C, ‖a m‖ := by
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    simp only [Finset.sum_ite_eq, hn, ite_true]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hcalc : (∑ n ∈ C, ∑ m ∈ C,
      ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B)) =
      D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := by
    rw [Finset.sum_congr rfl heq]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [cubic_mean_expand P hg C support a W M hMp]
  calc
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖(star (a n) * a m) * K n m‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ n ∈ C, ∑ m ∈ C, ‖a n‖ * ‖a m‖ * ((if n = m then D else 0) + B) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_left (hK n hn m hm) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * (∑ n ∈ C, ‖a n‖) ^ 2 := hcalc
    _ ≤ D * (∑ n ∈ C, ‖a n‖ ^ 2) + B * ((C.card : ℝ) * ∑ n ∈ C, ‖a n‖ ^ 2) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_left _ hB
      simpa only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, mul_comm] using
        Finset.sum_mul_sq_le_sq_mul_sq C (fun n => ‖a n‖) (fun _ => (1 : ℝ))
    _ = _ := by dsimp [D, B]; ring

theorem cubic_initial_finite_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ i, goodLambda ∉ P i)
    (C : Finset β) (support : β → Finset α) (hsupp : Set.InjOn support (↑C : Set β))
    (N : ℝ) (hN : 0 ≤ N) (hNorm : ∀ n ∈ C, supportNorm P (support n) ≤ N)
    (a : β → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2) ≤
      (diagonalControl sieveCutoff * M + pvControl sieveCutoff * N * C.card) *
        ∑ n ∈ C, ‖a n‖ ^ 2 := by
  have hMp : 0 < M := by linarith
  let E : O → ℝ := fun z => ‖∑ n ∈ C, a n * cubicFiniteRow P hg (support n) z‖ ^ 2
  let F : O → ℝ := fun z => sieveBump (‖eisEmbedding z‖ ^ 2 / M) * E z
  let H : O → ℂ := fun z => sieveCutoff (‖eisEmbedding z‖ ^ 2 / M) * (E z : ℂ)
  have hF (z : O) : 0 ≤ F z := mul_nonneg sieveBump.nonneg (sq_nonneg _)
  have hH (z : O) : H z = (F z : ℂ) := by
    simp only [H, F, sieveCutoff_apply, Complex.ofReal_mul]
  have hHs : Summable H := cubic_mean_summable P hg C support a sieveCutoff M hMp
  have hFs : Summable F := hHs.norm.congr (fun z => by
    rw [hH, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF z)])
  have hsum : ‖∑' z : O, H z‖ = ∑' z : O, F z := by
    rw [tsum_congr hH, ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg hF)]
  calc
    _ = ∑ z ∈ R, F z := by
      apply Finset.sum_congr rfl
      intro z hz
      have ht0 : 0 ≤ ‖eisEmbedding z‖ ^ 2 / M := div_nonneg (sq_nonneg _) hMp.le
      have ht1 : ‖eisEmbedding z‖ ^ 2 / M ≤ 1 := (div_le_one hMp).mpr (hR z hz)
      simp only [F, sieveBump_eq_one ht0 ht1, one_mul, E]
    _ ≤ ∑' z : O, F z := hFs.sum_le_tsum R (fun z _ => hF z)
    _ = ‖∑' z : O, H z‖ := hsum.symm
    _ ≤ _ := cubic_initial_mean_bound P hinj hg C support hsupp N hN hNorm
      a sieveCutoff M hM

theorem ideal_initial_cubic_sieve
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F, ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (hsq : ∀ I ∈ F, Squarefree I)
    (N : ℕ) (hN : 1 ≤ N) (hnorm : ∀ I ∈ F, Ideal.absNorm I ≤ N)
    (a : Ideal O → ℂ) (M : ℝ) (hM : 1 ≤ M) (R : Finset O)
    (hR : ∀ z ∈ R, ‖eisEmbedding z‖ ^ 2 ≤ M) :
    (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 2‖ ^ 2) ≤
      initialSieveConstant * (M + (N : ℝ) ^ 2) * ∑ I ∈ F, ‖a I‖ ^ 2 := by
  let : ∀ i : primePool F, (i.val).IsMaximal := primePool_maximal F hFpos
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsupp : Set.InjOn (idealSupport F) (↑F : Set (Ideal O)) := by
    intro I hI J hJ h
    exact idealSupport_injective_on_squarefree F hI hJ (hsq I hI) (hsq J hJ) h
  have hNorm (I : Ideal O) (hI : I ∈ F) :
      supportNorm (fun i : primePool F => i.val) (idealSupport F I) ≤ (N : ℝ) := by
    unfold supportNorm
    rw [idealSupport_product_eq F hI (hsq I hI)]
    exact_mod_cast hnorm I hI
  have hb := cubic_initial_finite_bound (fun i : primePool F => i.val)
    Subtype.val_injective (primePool_good F hFgood) F (idealSupport F) hsupp
    (N : ℝ) (by positivity) hNorm a M hM R hR
  change (∑ z ∈ R, ‖∑ I ∈ F, a I * (idealSexticRow F hFpos hFgood I z) ^ 2‖ ^ 2) ≤
    (diagonalControl sieveCutoff * M + pvControl sieveCutoff * (N : ℝ) * F.card) *
      ∑ I ∈ F, ‖a I‖ ^ 2 at hb
  have hsub : F ⊆ idealsUpTo N := by
    intro I hI
    apply mem_idealsUpTo.mpr
    constructor
    · apply Nat.one_le_iff_ne_zero.mpr
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]
      exact hFpos I hI
    · exact hnorm I hI
  have hcardNat : F.card ≤ 64 * (N + 1) :=
    (Finset.card_le_card hsub).trans (CompactScaleBridge.idealsUpTo_card_le N)
  have hcard : (F.card : ℝ) ≤ 128 * (N : ℝ) := by
    have hh : (F.card : ℝ) ≤ 64 * ((N : ℝ) + 1) := by exact_mod_cast hcardNat
    linarith
  refine hb.trans (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hdiag := diagonalControl_nonneg sieveCutoff
  have hpv := pvControl_nonneg sieveCutoff
  have hmul := mul_le_mul_of_nonneg_left hcard (mul_nonneg hpv (by positivity : (0 : ℝ) ≤ N))
  unfold initialSieveConstant
  nlinarith [mul_nonneg hdiag (sq_nonneg (N : ℝ)),
    mul_nonneg hpv (show 0 ≤ M by linarith)]

end
end SevenEighths.CubicSieve

end OAI

end


