-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0332_parallel1
-- name    : PNT_ZeroFree_433_0332_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T10:54:55.536285+00:00
-- url     : https://prove2.me/theorems/48f3f9ed-8d3b-4566-befd-888d6d2fa50f
-- title:
--   Zero-free region foundations: PrimeNumberTheoremAnd.Wiener [0332_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - PrimeNumberTheoremAnd.Wiener
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/Wiener.lean#L3050-L3691

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Definitions.Def_PNT_ZeroFree_433_0086
import Definitions.Def_PNT_ZeroFree_433_0130_parallel1
import Definitions.Def_PNT_ZeroFree_433_0158_parallel1
import Definitions.Def_PNT_ZeroFree_433_0188_parallel1
import Definitions.Def_PNT_ZeroFree_433_0218_parallel1
import Definitions.Def_PNT_ZeroFree_433_0228_parallel1_1
import Definitions.Def_PNT_ZeroFree_433_0260_parallel1
import Definitions.Def_PNT_ZeroFree_433_0262_parallel1
import Definitions.Def_PNT_ZeroFree_433_0303_parallel1
import Definitions.Def_PNT_ZeroFree_433_0329_parallel1
import Definitions.Def_PNT_ZeroFree_433_0330_parallel1

/- Supporting zero-free-region lemmas, grouped by independent dependencies.
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/c39a751132c88b6e8080b74c74023fd95b3d8be0/PrimeNumberTheoremAnd/Wiener.lean
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
/- Original source header, including license and authors:

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Topology.EMetricSpace.BoundedVariation
import PrimeNumberTheoremAnd.Mathlib.Analysis.Asymptotics.Asymptotics
import PrimeNumberTheoremAnd.Fourier
import PrimeNumberTheoremAnd.SmoothExistence
import Mathlib.Analysis.Convolution


-/
set_option lang.lemmaCmd true
set_option linter.style.header false

-- note: the opening of ArithmeticFunction introduces a notation σ that seems
-- impossible to hide, and hence parameters that are traditionally called σ will
-- have to be called σ' instead in this file.

open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate

variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]

/-
The Fourier transform of an absolutely integrable function $\psi: \R \to \C$ is defined by the
formula $$ \hat \psi(u) := \int_\R e(-tu) \psi(t)\ dt$$ where $e(\theta) := e^{2\pi i \theta}$.

Let $f: \N \to \C$ be an arithmetic function such that $\sum_{n=1}^\infty \frac{|f(n)|}{n^\sigma} <
\infty$ for all $\sigma>1$.  Then the Dirichlet series
$$ F(s) := \sum_{n=1}^\infty \frac{f(n)}{n^s}$$
is absolutely convergent for $\sigma>1$.
-/


-- TODO - add to mathlib
attribute [fun_prop] Real.continuous_fourierChar


attribute [fun_prop] measurable_coe_nnreal_ennreal


/-
Now let $A \in \C$, and suppose that there is a continuous function $G(s)$ defined on
$\mathrm{Re} s \geq 1$ such that $G(s) = F(s) - \frac{A}{s-1}$ whenever $\mathrm{Re} s > 1$.
We also make the Chebyshev-type hypothesis
\begin{equation}\label{cheby}
\sum_{n \leq x} |f(n)| \ll x
\end{equation}
for all $x \geq 1$ (this hypothesis is not strictly necessary, but simplifies the arguments and
can be obtained fairly easily in applications).
-/


-- Here compact support is used but perhaps it is not necessary


/- Should this be a gcongr lemma? -/


-- just the surjectivity is stated here, as this is all that is needed for the current
-- application, but perhaps one should state and prove bijectivity instead


/-
Now we add the hypothesis that $f(n) \geq 0$ for all $n$.

-/


-- TODO with `Ico`


/- A version of the *Wiener-Ikehara Tauberian Theorem*: If `f` is a nonnegative arithmetic
function whose L-series has a simple pole at `s = 1` with residue `A` and otherwise extends
continuously to the closed half-plane `re s ≥ 1`, then `∑ n < N, f n` is asymptotic to `A*N`. -/


/-
\section{Weak PNT}

-/

-- Proof extracted from the `EulerProducts` project so we can adapt it to the
-- version of the Wiener-Ikehara theorem proved above (with the `cheby`
-- hypothesis)


-- #print axioms WeakPNT

section auto_cheby

variable {f : ℕ → ℝ}


/-
\section{Removing the Chebyshev hypothesis}

In this section we do *not* assume the bound \eqref{cheby}, but instead derive it from the other hypotheses.

-/


lemma norm_integrand_le_K_mul_norm_psi
    {x K : ℝ}
    (hx : 0 < x)
    (hK : ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K) :
    ∀ t : ℝ,
      ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ ≤ K * ‖ψ t‖ := by
  intro t
  by_cases ht : t ∈ Function.support ψ
  · have hxnorm : ‖((x : ℂ) ^ (t * Complex.I))‖ = 1 := norm_x_cpow_it x t hx
    calc
      ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
          = ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ * ‖((x : ℂ) ^ (t * Complex.I))‖ := by
              simp [mul_left_comm, mul_comm]
      _   = ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ * 1 := by simp [hxnorm]
      _   ≤ K * ‖ψ t‖ := by
            have hGle : ‖G (1 + t * Complex.I)‖ ≤ K := hK t ht
            have : ‖G (1 + t * Complex.I)‖ * ‖ψ t‖ ≤ K * ‖ψ t‖ :=
              mul_le_mul_of_nonneg_right hGle (norm_nonneg _)
            simpa [mul_assoc, mul_left_comm, mul_comm] using this
  · have hψ0 : ψ t = 0 := by
      by_contra hψ0
      exact ht (by simpa [Function.support] using hψ0)
    simp [hψ0, mul_comm]


lemma norm_error_integral_le
    (ψ : ℝ → ℂ) (x K : ℝ)
    (hGline_meas : Measurable (fun t : ℝ => G (1 + t * I)))
    (hψ_meas : AEStronglyMeasurable ψ)
    (hx : 0 < x)
    (hK : ∀ t : ℝ, t ∈ Function.support ψ → ‖G (1 + t * Complex.I)‖ ≤ K)
    (hψ : Integrable (fun t : ℝ => ‖ψ t‖) ) :
    ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
      ≤ K * (∫ t : ℝ, ‖ψ t‖) := by
  have h1 : ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
        ≤ ∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ := by
    simpa using (norm_integral_le_integral_norm
        (f := fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))))
  have hmeas_main : AEStronglyMeasurable
        (fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))) := by
    have hG' : AEMeasurable fun t : ℝ => G (1 + t * Complex.I) := hGline_meas.aemeasurable
    have hψ_meas' : AEMeasurable ψ := hψ_meas.aemeasurable
    have hx_ne : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
    have hx_ne' : NeZero (x : ℂ) := ⟨hx_ne⟩
    have hxpow_meas : AEMeasurable fun t : ℝ => ((x : ℂ) ^ (t * Complex.I)) := by
      have hcontℂ : Continuous fun z : ℂ => ((x : ℂ) ^ z) :=
        continuous_const_cpow (z := (x : ℂ))
      have hcont : Continuous fun t : ℝ => ((x : ℂ) ^ ((t : ℂ) * Complex.I)) :=
        hcontℂ.comp (by
          have h : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by
            simpa using! (continuous_ofReal.mul continuous_const)
          simpa [mul_comm] using h)
      exact hcont.measurable.aemeasurable
    have hGψ_meas : AEMeasurable fun t : ℝ => (G (1 + t * Complex.I)) * (ψ t) := hG'.mul hψ_meas'
    have htotal : AEMeasurable (fun t : ℝ =>
            (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))) :=
      hGψ_meas.mul hxpow_meas
    exact htotal.aestronglyMeasurable
  have hpt : (fun t : ℝ =>
          ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖)
        ≤ᵐ[volume] (fun t : ℝ => K * ‖ψ t‖) := by
    refine Eventually.of_forall ?_
    intro t
    exact norm_integrand_le_K_mul_norm_psi (hx := hx) (hK := hK) t
  have hR : Integrable (fun t : ℝ => K * ‖ψ t‖) := hψ.const_mul K
  have hL : Integrable (fun t : ℝ =>
        ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖) := by
      have hpt_norm :
          (fun t : ℝ => ‖‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖‖)
            ≤ᵐ[volume] (fun t : ℝ => K * ‖ψ t‖) := hpt.mono (by
          intro t ht
          simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using ht)
      exact hR.mono' hmeas_main.norm hpt_norm
  have h2 : (∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖)
        ≤ ∫ t : ℝ, K * ‖ψ t‖ := integral_mono_ae (μ := (volume : Measure ℝ)) hL hR hpt
  have h3 : (∫ t : ℝ, K * ‖ψ t‖) = K * (∫ t : ℝ, ‖ψ t‖) := by
    simp [integral_const_mul]
  calc
    ‖∫ t : ℝ, (G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖
        ≤ ∫ t : ℝ, ‖(G (1 + t * Complex.I)) * (ψ t) * ((x : ℂ) ^ (t * Complex.I))‖ := h1
    _   ≤ ∫ t : ℝ, K * ‖ψ t‖ := h2
    _   = K * (∫ t : ℝ, ‖ψ t‖) := h3


set_option backward.isDefEq.respectTransparency false in
lemma Real.fourierIntegral_convolution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume) = 𝓕 f * 𝓕 g := by
  ext y
  simp only [Pi.mul_apply, FourierTransform.fourier, MeasureTheory.convolution,
    VectorFourier.fourierIntegral, ContinuousLinearMap.mul_apply']
  have h_int : Integrable (fun p : ℝ × ℝ ↦ 𝐞 (-(y * p.1)) • (f p.2 * g (p.1 - p.2))) := by
    simp only [Circle.smul_def, smul_eq_mul]
    refine (Integrable.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hf hg).bdd_mul
      (c := 1) ?_ ?_
    · exact (by continuity : Continuous _).aestronglyMeasurable
    · filter_upwards with p; simp
  calc ∫ v, 𝐞 (-(y * v)) • ∫ t, f t * g (v - t)
      = ∫ v, ∫ t, 𝐞 (-(y * v)) • (f t * g (v - t)) := by
        simp only [Circle.smul_def, smul_eq_mul, ← integral_const_mul]
    _ = ∫ t, ∫ v, 𝐞 (-(y * v)) • (f t * g (v - t)) := integral_integral_swap h_int
    _ = ∫ t, f t • ∫ v, 𝐞 (-(y * v)) • g (v - t) := by
        simp only [Circle.smul_def, smul_eq_mul, mul_left_comm, integral_const_mul]
    _ = ∫ t, f t • ∫ u, 𝐞 (-(y * (u + t))) • g u := by
        congr 1; ext t
        rw [← integral_add_right_eq_self (fun v ↦ 𝐞 (-(y * v)) • g (v - t)) t]; simp
    _ = ∫ t, f t • ∫ u, (𝐞 (-(y * t)) * 𝐞 (-(y * u))) • g u := by
        congr 2 with t; congr 1
        simp only [mul_add, neg_add, mul_comm, Real.fourierChar.map_add_eq_mul]
    _ = ∫ t, 𝐞 (-(y * t)) • f t • ∫ u, 𝐞 (-(y * u)) • g u := by
        congr 1; ext t
        simp only [mul_smul, Circle.smul_def, smul_eq_mul, integral_const_mul]; ring
    _ = (∫ t, 𝐞 (-(y * t)) • f t) * ∫ u, 𝐞 (-(y * u)) • g u := by
        simp only [Circle.smul_def, smul_eq_mul, ← mul_assoc, integral_mul_const]

lemma Real.fourierIntegral_conj_neg {f : ℝ → ℂ} (y : ℝ) :
    𝓕 (fun x ↦ conj (f (-x))) y = conj (𝓕 f y) := by
  simp only [fourier_real_eq]
  have h_conj : ∀ x, 𝐞 (-(x * y)) • conj (f (-x)) = conj (𝐞 (x * y) • f (-x)) := fun x ↦ by
    simp only [Circle.smul_def, Real.fourierChar_apply, map_mul, smul_eq_mul, neg_mul,
      Complex.ofReal_neg, mul_neg]
    congr 1
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, mul_neg]
  calc ∫ x, 𝐞 (-(x * y)) • conj (f (-x))
      = ∫ x, conj (𝐞 (x * y) • f (-x)) := by congr 1; ext x; exact h_conj x
    _ = conj (∫ x, 𝐞 (x * y) • f (-x)) := integral_conj
    _ = conj (∫ x, 𝐞 (-(x * y)) • f x) := by
        rw [← integral_neg_eq_self (fun x => 𝐞 (-(x * y)) • f x)]
        congr 2 with x; ring_nf

/- Smooth compactly supported function with non-negative Fourier transform via self-convolution. -/


/- The series `∑ f(n)/n · 𝓕ψ(log(n/x)/(2π))` is summable for `x ≥ 1`. -/


/- Short interval bound from global filtered bound: if `∑ f(n)/n · 𝓕ψ(log(n/x)) ≤ B`,
then `∑_{(1-ε)x < n ≤ x} f(n) ≤ Cx` for some `ε, C > 0`. -/


/- Bootstraps short interval bounds to global Chebyshev bound via strong induction.
If `∑_{(1-ε)x < n ≤ x} f(n) ≤ Cx` for all `x ≥ 1`, then `∑_{n ≤ x} f(n) = O(x)`. -/


end auto_cheby

/-
\section{The prime number theorem in arithmetic progressions}
-/


theorem WeakPNT_character
    {q a : ℕ} (hq : q ≥ 1) (ha : Nat.Coprime a q) (ha' : a < q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ if n % q = a then Λ n else 0) s =
      - (∑' χ : DirichletCharacter ℂ q,
          ((starRingEnd ℂ) (χ a) * ((deriv (LSeries (fun n:ℕ ↦ χ n)) s)) /
          (LSeries (fun n:ℕ ↦ χ n) s))) / (Nat.totient q : ℂ) := by
  have : NeZero q := ⟨by omega⟩
  convert! vonMangoldt.LSeries_residueClass_eq ((ZMod.isUnit_iff_coprime a q).mpr ha) hs using 1
  · congr with n
    have : n % q = a ↔ (n : ZMod q) = a := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha']
    simp [this]
    split_ifs <;> simp [*]
  · rw [div_eq_inv_mul, neg_mul_comm, tsum_fintype]
    congr 3 with χ
    rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hs,
      DirichletCharacter.LFunction_eq_LSeries _ hs, mul_div]
    congr 2
    rw [starRingEnd_apply, MulChar.star_apply', MulChar.inv_apply_eq_inv',
      ← ZMod.coe_unitOfCoprime a ha, ZMod.inv_coe_unit, map_units_inv]


theorem WeakPNT_AP_prelim {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : Nat.Coprime a q) (ha' : a < q) :
    ∃ G: ℂ → ℂ, (ContinuousOn G {s | 1 ≤ s.re}) ∧
    (Set.EqOn G (fun s ↦ LSeries (fun n ↦ if n % q = a then Λ n else 0) s - 1 /
      ((Nat.totient q) * (s - 1))) {s | 1 < s.re}) := by
  have : NeZero q := NeZero.of_pos hq
  have hG : ∃ G : ℂ → ℂ, ContinuousOn G {s | 1 ≤ s.re} ∧ Set.EqOn G
      (fun s ↦ LSeries (fun n ↦ if (n : ZMod q) = a then Λ n else 0) s - (q.totient : ℂ)⁻¹ / (s - 1)) {s | 1 < s.re} := by
    use vonMangoldt.LFunctionResidueClassAux (a : ZMod q), vonMangoldt.continuousOn_LFunctionResidueClassAux (q := q) (a := a)
    have := vonMangoldt.eqOn_LFunctionResidueClassAux ((ZMod.isUnit_iff_coprime a q).mpr ha)
    convert! this using 6; split <;> simp_all
  convert! hG using 6
  · simp [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha']
  · rw [inv_eq_one_div, div_div]

/- The von Mangoldt function divided by `n ^ s` is summable for `s > 1`. -/
lemma summable_vonMangoldt_div_rpow {s : ℝ} (hs : 1 < s) : Summable (fun n ↦ Λ n / n ^ s) := by
  have h_log_bound : ∀ n : ℕ, (Λ n : ℝ) ≤ Real.log n := fun n ↦ vonMangoldt_le_log
  suffices h_log_sum : Summable fun n : ℕ ↦ Real.log n / (n : ℝ) ^ s by
    exact .of_nonneg_of_le (fun n ↦ div_nonneg vonMangoldt_nonneg (by positivity))
      (fun n ↦ div_le_div_of_nonneg_right (h_log_bound n) (by positivity)) h_log_sum
  have h_log_le_n_eps : ∀ ε > 0, ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n / (n : ℝ) ^ s ≤ C * (n : ℝ) ^ (ε - s) := by
    intro ε hε_pos
    obtain ⟨C, hC_pos, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n ≤ C * (n : ℝ) ^ ε := by
      refine ⟨1 / ε, by positivity, fun n hn ↦ ?_⟩
      have := log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) ^ ε)
      rw [log_rpow (by positivity)] at this
      nlinarith [rpow_pos_of_pos (by positivity : 0 < (n : ℝ)) ε, mul_div_cancel₀ 1 hε_pos.ne']
    refine ⟨C, hC_pos, fun n hn ↦ ?_⟩
    rw [rpow_sub (by positivity)]
    exact le_trans (div_le_div_of_nonneg_right (hC n hn) (by positivity)) (by rw [div_eq_mul_inv]; ring_nf; norm_num)
  obtain ⟨C, _, hC⟩ : ∃ C > 0, ∀ n : ℕ, n ≥ 2 → Real.log n / (n : ℝ) ^ s ≤ C * (n : ℝ) ^ ((s - 1) / 2 - s) :=
    h_log_le_n_eps ((s - 1) / 2) (by linarith)
  rw [← summable_nat_add_iff 2]
  exact Summable.of_nonneg_of_le (fun n ↦ div_nonneg (log_nonneg (by norm_cast; omega))
    (rpow_nonneg (by positivity) _)) (fun n ↦ hC _ (by omega)) (Summable.mul_left _ <| by
      simpa using summable_nat_add_iff 2 |>.2 <| summable_nat_rpow.2 <| by linarith)


/-
\section{The Chebotarev density theorem: the case of cyclotomic extensions}

Throughout this section, $K$ is a number field, $m \geq 1$ is a fixed integer,
$L = K(\mu_m)$, and $G = \mathrm{Gal}(L/K)$.  (In particular $G$ is abelian, and for
$K=\mathbb{Q}$ one recovers $G \cong (\mathbb{Z}/m\mathbb{Z})^\times$.)
Write $\zeta_K$ and $\zeta_L$ for the Dedekind zeta functions of $K$ and $L$, and for
an abelian character $\chi : G \to \mathbb{C}^\times$ write $L(\chi,s)$ for the associated
Artin $L$-function (equivalently, the Hecke $L$-function of the ideal character attached to
$\chi$; cf.\ Notation~7.1.17 and Proposition~7.1.18 of
\url{https://www.math.ucla.edu/~sharifi/algnum.pdf}).

The goal of this section is to prove the Chebotarev density theorem in the cyclotomic case
(Proposition~\ref{Chebotarev-cyclotomic-density} below), following the classical argument via
Artin $L$-functions as in Sharifi, Propositions~7.1.16--7.1.19 and Proposition~7.2.1.  The
abelian and general cases are then reduced to this one in the subsequent sections.
-/

/-
\begin{lemma}[Artin $L$-function as Euler product]\label{Artin-L-euler}
Let $\chi : G \to \mathbb{C}^\times$ be an abelian character.  For $\Re(s) > 1$ one has
\[
L(\chi,s) \;=\; \prod_{\mathfrak{p}} \bigl(1 - \chi(\mathfrak{p})\, N\mathfrak{p}^{-s}\bigr)^{-1}
\;=\; \sum_{\mathfrak{a} \subseteq \mathcal{O}_K} \chi(\mathfrak{a})\, N\mathfrak{a}^{-s},
\]
where the product runs over nonzero prime ideals of $\mathcal{O}_K$, with the convention
$\chi(\mathfrak{p}) = 0$ if $\mathfrak{p}$ ramifies in the fixed field of $\ker\chi$.
\end{lemma}
-/

/-
\begin{proof}
This is the specialisation of the Artin Euler product (Definition~7.1.15 of Sharifi) to
abelian characters; see Proposition~7.1.18 of
\url{https://www.math.ucla.edu/~sharifi/algnum.pdf}.  Absolute convergence for $\Re(s)>1$
follows from comparison with $\zeta_K(s)$.
\end{proof}
-/

/-
\begin{lemma}[Dedekind-factor]\label{Dedekind-factor}
For $\Re(s) > 1$ one has
\[
\zeta_L(s) \;=\; \prod_{\chi : G \to \mathbb{C}^\times} L(\chi,s),
\]
where the product runs over all (necessarily one-dimensional) irreducible characters of $G$.
\end{lemma}
-/

/-
\begin{proof}\uses{Artin-L-euler}
In general, for a Galois extension $L/K$ and characters $\chi$ of irreducible representations of
$\mathrm{Gal}(L/K)$, Proposition~7.1.16 of
\url{https://www.math.ucla.edu/~sharifi/algnum.pdf} gives
$\zeta_L(s) = \prod_\chi L(\chi,s)^{\chi(1)}$ for $\Re(s)>1$.  In the present abelian
(cyclotomic) setting every irreducible character is one-dimensional, so $\chi(1)=1$ and the
exponents disappear.  Alternatively, comparing Euler factors at an unramified prime
$\mathfrak{p}$: the primes of $L$ above $\mathfrak{p}$ contribute the factor
$(1 - N\mathfrak{p}^{-fs})^{-g}$ to $\zeta_L$, while the Artin factors multiply to the same
quantity by the usual identity $\prod_\chi (1 - \chi(\varphi_{\mathfrak{p}}) X) = 1 - X^f$
(with $X = N\mathfrak{p}^{-s}$ and $f$ the residue degree).
\end{proof}
-/

/-
\begin{lemma}[Simple pole]\label{Dedekind-pole}
The Dedekind zeta function $\zeta_L$ admits a meromorphic continuation to a neighbourhood of
the line $\Re(s)=1$ with a single simple pole at $s=1$ (and is otherwise holomorphic and
nonvanishing on that line after removing the pole).  In particular
$\log \zeta_L(s) \sim \log(s-1)^{-1}$ as $s \to 1^+$.
\end{lemma}
-/

/-
\begin{proof}
This is the standard analytic continuation of Dedekind zeta (Theorem~7.1.12 of
\url{https://www.math.ucla.edu/~sharifi/algnum.pdf}): absolute convergence of the ideal
Dirichlet series and Euler product for $\Re(s)>1$, meromorphic continuation across
$\Re(s)>1-[L:\mathbb{Q}]^{-1}$, and a simple pole at $s=1$.  The logarithmic asymptotic is
immediate from the simple pole.
\end{proof}
-/

/-
\begin{lemma}[Continuation of nontrivial Artin $L$-functions]\label{Artin-L-continuation}
Let $\chi : G \to \mathbb{C}^\times$ be a nontrivial character.  Then $L(\chi,s)$ extends to an
analytic function on the half-plane $\Re(s) > 1 - [K:\mathbb{Q}]^{-1}$, and in particular is
holomorphic at $s=1$.
\end{lemma}
-/

/-
\begin{proof}
Following Proposition~7.1.19 of \url{https://www.math.ucla.edu/~sharifi/algnum.pdf}: let $n$
be the order of $\chi$.  Geometry of numbers supplies the estimate that, for each $n$th root of
unity $\zeta$, the number of ideals $\mathfrak{a}$ with $N\mathfrak{a} \leq N$ and
$\chi(\mathfrak{a})=\zeta$ is $CN + O\bigl(N^{1-[K:\mathbb{Q}]^{-1}}\bigr)$ with $C$ independent of
$\zeta$.  Summing against $\zeta$ cancels the main terms, so
$\sum_{N\mathfrak{a}\leq N} \chi(\mathfrak{a}) = O\bigl(N^{1-[K:\mathbb{Q}]^{-1}}\bigr)$.
Lemma~7.1.5 of Sharifi then yields absolute uniform convergence of
$\sum_{\mathfrak{a}} \chi(\mathfrak{a})\, N\mathfrak{a}^{-s}$ on compact subsets of
$\Re(s) > 1 - [K:\mathbb{Q}]^{-1}$.
\end{proof}
-/

/-
\begin{lemma}[Dedekind-nonvanishing]\label{Dedekind-nonvanishing}
For any nontrivial character $\chi$ of $G = \mathrm{Gal}(L/K)$, one has $L(\chi,1) \neq 0$.
Moreover $L(\chi,s)$ does not vanish for $\Re(s)=1$.
\end{lemma}
-/

/-
\begin{proof}\uses{Dedekind-factor, Dedekind-pole, Artin-L-continuation}
For the value at $s=1$: write $\log\zeta_L(t) = \sum_\chi \log L(\chi,t)$ for real $t>1$.
As $t\to 1^+$, the left side is $\sim \log(t-1)^{-1}$ by Lemma~\ref{Dedekind-pole}.  If some
nontrivial $L(\chi,\cdot)$ had a zero of order $m_\chi \geq 1$ at $s=1$, the right side would
behave like $\bigl(1 - \sum_\chi m_\chi\bigr)\log(t-1)^{-1}$ up to a bounded error
(the trivial character contributes the pole of $\zeta_K$, absorbed into the factorisation),
forcing $1-\sum m_\chi \leq 0$, a contradiction.  Hence $L(\chi,1)\neq 0$ for all nontrivial
$\chi$ (Sharifi, Proposition~7.1.19).

For the rest of the line $\Re(s)=1$, $s\neq 1$: adapt the classical nonvanishing argument for
Dirichlet $L$-functions (comparison of $\zeta_L(s)$, $\zeta_L(s)^3\,|L(\chi,s)|^4$, or the
$3+4\operatorname{Re}$ inequality) using the Euler product of Lemma~\ref{Artin-L-euler} and the
absence of poles of nontrivial $L(\chi,\cdot)$ on $\Re(s)=1$ from
Lemma~\ref{Artin-L-continuation}.
\end{proof}
-/

/-
\begin{lemma}[Orthogonality for Frobenius classes]\label{Chebotarev-orthogonality}
Fix $\sigma \in G$.  For every prime ideal $\mathfrak{p}$ of $\mathcal{O}_K$ unramified in $L$,
\[
\sum_{\chi : G \to \mathbb{C}^\times} \chi(\sigma)^{-1}\,\chi(\varphi_{\mathfrak{p}})
\;=\;
\begin{cases}
|G| & \text{if }\varphi_{\mathfrak{p}} = \sigma,\\
0 & \text{otherwise.}
\end{cases}
\]
Equivalently, if $\sigma(\zeta_m) = \zeta_m^a$ with $\gcd(a,m)=1$, the sum equals $|G|$
precisely when $N\mathfrak{p} \equiv a \pmod{m}$.
\end{lemma}
-/

/-
\begin{proof}
Standard character orthogonality on the finite abelian group $G$.  The reformulation in terms
of $N\mathfrak{p} \bmod m$ uses that $\varphi_{\mathfrak{p}}(\zeta_m) = \zeta_m^{N\mathfrak{p}}$
for the cyclotomic character.
\end{proof}
-/

/-
\begin{proposition}[Cyclotomic Chebotarev density]\label{Chebotarev-cyclotomic-density}
For every $\sigma \in G$, the set of prime ideals $\mathfrak{p}$ of $K$ unramified in $L$ with
Frobenius $\varphi_{\mathfrak{p}} = \sigma$ has Dirichlet density $1/|G|$.
\end{proposition}
-/

/-
\begin{proof}\uses{Dedekind-factor, Dedekind-pole, Dedekind-nonvanishing, Artin-L-euler,
Chebotarev-orthogonality}
This is Proposition~7.2.1 of \url{https://www.math.ucla.edu/~sharifi/algnum.pdf}.  For
$\Re(s)>1$ one has $\log L(\chi,s) \sim \sum_{\mathfrak{p}} \chi(\mathfrak{p})\, N\mathfrak{p}^{-s}$.
Summing against $\chi(\sigma)^{-1}$ and applying Lemma~\ref{Chebotarev-orthogonality} yields
\[
\sum_{\chi} \chi(\sigma)^{-1} \log L(\chi,s)
\;\sim\;
|G| \sum_{\varphi_{\mathfrak{p}}=\sigma} N\mathfrak{p}^{-s}.
\]
On the other hand, by Lemmas~\ref{Dedekind-factor} and~\ref{Dedekind-nonvanishing} the left
side is $\sim \log\zeta_K(s) \sim \log(s-1)^{-1}$ as $s\to 1^+$ (only the trivial character
contributes a pole).  Comparing the two asymptotics gives the asserted Dirichlet density.
\end{proof}
-/

/-
\begin{lemma}[PNT for one character]\label{Dedekind-PNT}
For any nontrivial character $\chi$ of $G$,
\[
\sum_{N\mathfrak{p} \leq x} \chi(\mathfrak{p})\, \log N\mathfrak{p} \;=\; o(x)
\qquad(x\to\infty).
\]
(Equivalently, writing $\Lambda_\chi$ for the von Mangoldt-type coefficients of $-\frac{L'}{L}(\chi,s)$,
one has $\sum_{n\leq x} \Lambda_\chi(n) = o(x)$.)
\end{lemma}

\emph{Remark on prime powers.}
Expanding $-\frac{L'}{L}(\chi,s)$ as a Dirichlet series selects coefficients supported on
prime powers $\mathfrak{p}^j$ with weight $\chi(\varphi_{\mathfrak{p}})^j\log N\mathfrak{p}$.
Thus an \emph{exact} identity expressing $-\sum_\chi \chi(\sigma)^{-1}\frac{L'}{L}(\chi,s)$ as a
sum over primes with Frobenius $\sigma$ should use the condition $\varphi_{\mathfrak{p}}^j=\sigma$
rather than $\varphi_{\mathfrak{p}}=\sigma$.  For the density statement in
Proposition~\ref{Chebotarev-cyclotomic-density} this distinction is immaterial: the $j=1$ terms
agree with the Frobenius condition, while the $j\geq 2$ terms converge absolutely for
$\Re(s)>1/2$ and do not affect the residue at $s=1$.
-/

/-
\begin{proof}\uses{Dedekind-nonvanishing, Artin-L-continuation}
By Lemmas~\ref{Artin-L-continuation} and~\ref{Dedekind-nonvanishing}, $L(\chi,s)$ is holomorphic
and nonvanishing on $\Re(s)\geq 1$, so $-\frac{L'}{L}(\chi,s)$ extends continuously to
$\Re(s)\geq 1$.  The claimed prime-sum estimate then follows by the same Wiener--Ikehara /
Ingham contour argument used for Dirichlet $L$-functions in the prime-number theorem in
arithmetic progressions (cf.\ the material already formalised for Dirichlet $L$-functions
earlier in this file).  Passing through $\Lambda_\chi$ (rather than the bare prime sum) makes
the $j\geq 2$ prime-power contributions explicit and shows they are $O(x^{1/2}\log x)$,
hence absorbable in the $o(x)$ error; cf.\ the remark after the statement.
\end{proof}
-/

/-
\section{The Chebotarev density theorem: the case of abelian extensions}

Now let $L/K$ be an arbitrary finite abelian extension with Galois group $G$, and fix
$\sigma \in G$.  The goal is to show that the primes of $K$ with Frobenius $\sigma$ still have
Dirichlet density $1/|G|$, by reducing to the cyclotomic case already treated.
(Cf.\ Theorem~7.2.2, Step~2, of \url{https://www.math.ucla.edu/~sharifi/algnum.pdf}; cyclic
extensions already suffice for the later reduction to the general case.)
-/

/-
\begin{lemma}[Cyclotomic crossing]\label{Chebotarev-abelian-crossing}
Choose an integer $m\geq 1$ not dividing the discriminant of $L/K$, large enough that
$H := \mathrm{Gal}(L(\mu_m)/L) \cong (\mathbb{Z}/m\mathbb{Z})^\times$ via the cyclotomic character
and $\mathrm{Gal}(L(\mu_m)/K) \cong G \times H$.  For $\sigma\in G$ and $\tau\in H$ write
$S_{\sigma,\tau}$ for the set of primes of $K$ unramified in $L(\mu_m)$ with Frobenius
$(\sigma,\tau)\in G\times H$, and $S_\sigma$ for the set of primes of $K$ unramified in $L$
with Frobenius $\sigma$ in $G$.  Then
\[
\delta_{\mathrm{inf}}(S_\sigma) \;=\; \sum_{\tau\in H} \delta_{\mathrm{inf}}(S_{\sigma,\tau}).
\]
\end{lemma}
-/

/-
\begin{proof}
Every prime counted in $S_\sigma$ lifts to primes in the various $S_{\sigma,\tau}$ according to
the Frobenius in the cyclotomic layer; the identity of lower densities is the usual additivity
of Dirichlet densities over a finite partition (up to the finitely many ramified primes).
\end{proof}
-/

/-
\begin{lemma}[Density after cyclotomic crossing]\label{Chebotarev-abelian-density}
In the notation of Lemma~\ref{Chebotarev-abelian-crossing}, if the order of $\tau\in H$ is
divisible by $|G|$, then $\langle(\sigma,\tau)\rangle \cap (G\times\{1\}) = \{1\}$, so
$L(\mu_m)$ is obtained by adjoining $\mu_m$ to the fixed field
$F := L(\mu_m)^{\langle(\sigma,\tau)\rangle}$.  Applying Proposition~\ref{Chebotarev-cyclotomic-density}
to the cyclotomic extension $F(\mu_m)/F$ and transporting densities as in the reduction step
of Theorem~7.2.2 yields $\delta(S_{\sigma,\tau}) = 1/(|G|\,|H|)$.
\end{lemma}
-/

/-
\begin{proof}\uses{Chebotarev-cyclotomic-density, Chebotarev-abelian-crossing}
See Sharifi, Theorem~7.2.2, Step~2 (display after ``Now suppose that $|G|$ divides the order of
$\tau$'').
\end{proof}
-/

/-
\begin{proposition}[Abelian Chebotarev]\label{Chebotarev-abelian}
Let $L/K$ be finite abelian with Galois group $G$.  For every $\sigma\in G$, the Dirichlet
density of primes of $K$ with Frobenius $\sigma$ exists and equals $1/|G|$.
\end{proposition}
-/

/-
\begin{proof}\uses{Chebotarev-abelian-crossing, Chebotarev-abelian-density,
Chebotarev-cyclotomic-density}
Let $H_n \subset H$ be the set of elements whose order is divisible by $n$.  Summing the
densities of Lemma~\ref{Chebotarev-abelian-density} over $\tau\in H_n$ gives
$\delta_{\mathrm{inf}}(S_\sigma) \geq |H_n|/(|G|\,|H|)$.  Choosing $m$ so that $|H_n|/|H|$ is
arbitrarily close to $1$ (possible since there are primes $m\equiv 1\pmod{n^j}$ by the
cyclotomic case already proved, and $|H_n|/|H|$ tends to $1$ as $j\to\infty$), one obtains
$\delta_{\mathrm{inf}}(S_\sigma) \geq 1/|G|$.  Summing over $\sigma\in G$ forces equality
throughout, so each density exists and equals $1/|G|$.
\end{proof}
-/

/-
\section{The Chebotarev density theorem: the general case}

Finally let $L/K$ be an arbitrary finite Galois extension with group $G$, and let $C\subset G$
be a conjugacy class.  The theorem reduces to the abelian (indeed cyclic) case already proved,
by passing to the fixed field of an element of $C$.
-/

/-
\begin{lemma}[Reduction to a cyclic subextension]\label{Chebotarev-reduction}
Fix $\sigma\in C$ and let $E$ be the fixed field of $\langle\sigma\rangle$, so $L/E$ is cyclic of
degree $f = |\langle\sigma\rangle|$.  Write $S$ for the set of primes of $K$ unramified in $L$
whose Frobenius class equals $C$, and $T_\sigma$ for the set of primes $\mathfrak{P}$ of $E$
unramified in $L$ (and lying over $K$) with Frobenius equal to $\sigma$.  Then
\[
\delta(S) \;=\; \frac{f\,|C|}{|G|}\,\delta(T_\sigma),
\]
whenever either density exists.  In particular, the Chebotarev statement for $L/K$ and $C$
follows from the abelian statement for the cyclic extension $L/E$ and the element $\sigma$.
\end{lemma}
-/

/-
\begin{proof}
If $\mathfrak{P}\in T_\sigma$, then $\varphi_{\mathfrak{P}}=\sigma$ fixes $E$, so $\mathfrak{P}$ has
residue degree one over $K$.  There are exactly $|G|/f$ primes of $L$ over $\mathfrak{P}\cap K$,
and their Frobenii are equidistributed among the $|C|$ elements of the conjugacy class $C$;
exactly $|G|/(f\,|C|)$ of them have Frobenius $\sigma$.  Comparing the Dirichlet series
$\sum N\mathfrak{p}^{-s}$ over $S$ with $\sum N\mathfrak{P}^{-s}$ over $T_\sigma$ (and using
$\sum_{\mathfrak{p}} N\mathfrak{p}^{-s} \sim \sum_{\mathfrak{P}} N\mathfrak{P}^{-s}$) yields the
displayed identity.  See Sharifi, Theorem~7.2.2, Step~1.
\end{proof}
-/

/-
\begin{theorem}[Chebotarev density theorem]\label{Chebotarev-general}
Let $L/K$ be a finite Galois extension of number fields with Galois group $G$, and let
$C\subset G$ be a conjugacy class.  The set of prime ideals $\mathfrak{p}$ of $K$ unramified in
$L$ whose Frobenius conjugacy class equals $C$ has Dirichlet density $|C|/|G|$.
\end{theorem}
-/

/-
\begin{proof}\uses{Chebotarev-reduction, Chebotarev-abelian}
Combine Lemma~\ref{Chebotarev-reduction} with Proposition~\ref{Chebotarev-abelian} applied to
the cyclic extension $L/E$: the latter gives $\delta(T_\sigma) = 1/f$, whence
$\delta(S) = |C|/|G|$.
\end{proof}
-/

end


