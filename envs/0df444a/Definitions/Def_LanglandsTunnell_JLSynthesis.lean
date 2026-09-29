-- Prove2me | Definitions.Def_LanglandsTunnell_JLSynthesis
-- name    : LanglandsTunnell_JLSynthesis
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/e9e059ce-f80b-5d0f-b6b0-9967229d2d3b
-- title:
--   Cusp synthesis from Jacquet–Langlands converse data
-- statement:
--   Throughout, $K$ is a number field, $S$ a finite set of finite places of $K$ and $m : S \to \mathbb{N}$ a family of exponents. `kZeroSet S m` is the set of $g \in \mathrm{GL}_2(\mathbb{A}_K)$ such that for each $v \in S$ the predicate `MemZK0At` holds at $v$ with exponent $m_v$, i.e. the matrix $g_v = (g_{ij})$ over the completion $K_v$ obtained from the finite part of $g$ satisfies: $|g_{11}| \neq 0$, $|g_{00}| = |g_{11}|$, $|g_{01}| \le |g_{11}|$ and $|g_{10}| \le |g_{11}| \, q_v^{-m_v}$ in the valuation $\mathrm{Valued.v}$ on $K_v$ (so the condition is invariant under the local centre and cuts out a congruence condition of depth $m_v$ in the lower-left entry); `mem_kZeroSet_iff` is the membership unfolding. The main theorem `kZeroSet_meets` asserts that every left coset of $\mathrm{GL}_2(K)$ meets this set: for each $g$ there is $\gamma \in \mathrm{GL}_2(K)$ with $\gamma g \in$ `kZeroSet S m`. Auxiliary results prove the required weak approximation (given targets in $K$, resp. in the completions $K_v$ for $v \in S$, and exponents, a single element of $K$ approximates all of them to prescribed accuracy), the multiplicativity of the local component map on $\mathrm{GL}_2(\mathbb{A}_K)$, and an entrywise valuation bound for products of $2 \times 2$ matrices over $K_v$.
--
--   On the archimedean side, `archNormFactor g` is the product over infinite places $w$ of $(\sqrt{|\det g_w|})^{-1}$ at real $w$ and $\lVert \det g_w \rVert^{-1}$ at complex $w$, where $g_w$ is the real or complex component of $g$; `archW'` multiplies the product `archW` of the Whittaker functions of the given real and complex archimedean data by this factor. Given $S$-data $d$ (with coefficients `d.a`, character `d.epsChar` and exponents `d.m`), archimedean parameters and data, and a finite Whittaker datum $d_F$ for a Hecke eigensystem $\Pi$, `jlSeries'` is the Whittaker series $g \mapsto \sum_{\alpha \in K^{\times}} a(\alpha)\,\varepsilon(g)\,W_{\infty}(\mathrm{diag}(\alpha,1)g)\,W_f(\mathrm{diag}(\alpha,1)g)$ formed with `archW'`, and `theForm` is its extension along rational translates into `kZeroSet S d.m`, i.e. $g \mapsto$ `jlSeries'`$(\gamma_g\, g)$ for a chosen $\gamma_g \in \mathrm{GL}_2(K)$ with $\gamma_g g$ in that set; `theForm_eq` restates this. `pinsOf c u d₁ d₂ T` packages the analytic data as the production carrier pins of $K$: Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, full central subgroup, level groups $N \mapsto$ `levelOne` $N \sqcap$ the finite adelic subgroup, the standard Hecke generators, and the conditional adelic additive Haar measure on the adelic box, with window the union over $x \in T$ of the right translates by $x$ of the centre-cut Siegel set with numerics $(c,u,d_1,d_2)$. Finally `translateSum` forms the finite combinations $g \mapsto \sum_i c_i\,$`theForm`$(g k_i)$ of right translates of `theForm`.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, the valuations on adic completions with density of $K$ in them, the Dedekind-domain approximation lemma used for the weak approximation statements, and Haar measure; the congruence condition `MemZK0At`, the Whittaker series, the carrier pins structure and the Siegel-set windows are the project's own notions.
--
--   **Where it is used.** These constructions synthesise a candidate automorphic form on $\mathrm{GL}_2(\mathbb{A}_K)$ out of the Whittaker data produced by a converse theorem, the step by which a Hecke eigensystem with the requisite functional equations is realised by an automorphic form. This is the analytic input to Langlands–Tunnell, which supplies the modularity of the mod $3$ representation attached to a Frey curve in the Fermat argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_JLSynthesis.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel
open LanglandsTunnell.Converse

noncomputable section

namespace LanglandsTunnell.Converse.CuspSynthesis

open AutomorphicForm.SmoothCusp

variable {K : Type} [Field K] [NumberField K]

def kZeroSet (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ↥S → ℕ) :
    Set (AdelicGL2 (𝓞 K) K) :=
  {g | ∀ v : ↥S, MemZK0At v.1 (m v) g}

theorem mem_kZeroSet_iff (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ↥S → ℕ) (g : AdelicGL2 (𝓞 K) K) :
    g ∈ kZeroSet S m ↔ ∀ v : ↥S, MemZK0At v.1 (m v) g :=
  Iff.rfl

section WeakApproximation

open scoped WithZero

private theorem exists_forall_valuation_sub_lt (S : Finset (HeightOneSpectrum (𝓞 K))) (s : ↥S → K)
    (e : ↥S → ℤ) : ∃ x : K, ∀ v : ↥S, v.1.valuation K (s v - x) < WithZero.exp (e v) := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) (Finset.univ : Finset ↥S) s
  choose a ha using fun v : ↥S => hb v (Finset.mem_univ v)
  have hb0 : ((b : 𝓞 K) : K) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (𝓞 K) K), (IsFractionRing.injective (𝓞 K) K).eq_iff]
    exact nonZeroDivisors.coe_ne_zero b
  have hnb : ∀ v : ↥S, ∃ n : ℕ, v.1.intValuation (b : 𝓞 K) = WithZero.exp (-(n : ℤ)) := by
    intro v
    have h0 := v.1.intValuation_ne_zero' b
    have h1 := v.1.intValuation_le_one (b : 𝓞 K)
    refine ⟨(-WithZero.log (v.1.intValuation (b : 𝓞 K))).toNat, ?_⟩
    rw [Int.toNat_of_nonneg, neg_neg, WithZero.exp_log h0]
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega
  choose nb hnb using hnb
  set E : HeightOneSpectrum (𝓞 K) → ℕ := fun w => if hw : w ∈ S then ((nb ⟨w, hw⟩ : ℤ) - e ⟨w, hw⟩ + 1).toNat else 0
    with hE
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun w => w.asIdeal) E
    (fun w _ => w.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) fun v => a ⟨v.1, v.2⟩
  refine ⟨(y : K) / (b : 𝓞 K), fun v => ?_⟩
  have hsv : s v = (a v : K) / (b : 𝓞 K) := by
    rw [eq_div_iff hb0, mul_comm]
    have := ha v
    rw [Algebra.smul_def] at this
    exact this.symm
  have hEv : E v.1 = ((nb v : ℤ) - e v + 1).toNat := by
    simp only [hE, dif_pos v.2]
  have hmem : a v - y ∈ v.1.asIdeal ^ E v.1 := by
    rw [← Ideal.neg_mem_iff, neg_sub]
    exact hy v.1 v.2
  rw [hsv, ← sub_div, ← map_sub, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, hnb v]
  have ha' := (v.1.intValuation_le_pow_iff_mem (a v - y) (E v.1)).mpr hmem
  have hq : v.1.intValuation (a v - y) / WithZero.exp (-(nb v : ℤ)) ≤
      WithZero.exp (-(E v.1 : ℤ)) * WithZero.exp (nb v : ℤ) := by
    rw [div_eq_mul_inv, ← WithZero.exp_neg, neg_neg]
    exact mul_le_mul' ha' le_rfl
  refine lt_of_le_of_lt hq ?_
  rw [← WithZero.exp_add, WithZero.exp_lt_exp, hEv]
  omega

private theorem exists_forall_valued_sub_lt (S : Finset (HeightOneSpectrum (𝓞 K)))
    (t : ∀ v : ↥S, v.1.adicCompletion K) (r : ↥S → ℤ) :
    ∃ x : K, ∀ v : ↥S, Valued.v (t v - algebraMap K (v.1.adicCompletion K) x) < WithZero.exp (r v) := by
  have hs : ∀ v : ↥S, ∃ s : K, Valued.v (t v - algebraMap K (v.1.adicCompletion K) s) < WithZero.exp (r v) := by
    intro v
    obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v.1 (WithZero.exp (r v))
    have hc0 : c ≠ 0 := fun h => by
      rw [h, map_zero] at hc
      exact WithZero.exp_ne_zero hc.symm
    obtain ⟨_, ⟨s, rfl⟩, hz⟩ := Dense.inter_nhds_nonempty
      (show Dense (Set.range (algebraMap K (v.1.adicCompletion K))) from
        HeightOneSpectrum.denseRange_algebraMap K v.1) (ball_mem_nhds (𝓞 K) K v.1 (t v) c hc0)
    refine ⟨s, ?_⟩
    rw [Valuation.map_sub_swap, ← hc]
    exact hz
  choose s hs using hs
  obtain ⟨x, hx⟩ := exists_forall_valuation_sub_lt S s r
  refine ⟨x, fun v => ?_⟩
  have hsplit : t v - algebraMap K (v.1.adicCompletion K) x =
      (t v - algebraMap K (v.1.adicCompletion K) (s v)) + algebraMap K (v.1.adicCompletion K) (s v - x) := by
    rw [map_sub]; abel
  rw [hsplit]
  refine Valuation.map_add_lt _ (hs v) ?_
  rw [show algebraMap K (v.1.adicCompletion K) (s v - x) = ((s v - x : K) : v.1.adicCompletion K) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hx v

end WeakApproximation

section Components

open scoped WithZero

private theorem componentMatrix_mul (v : HeightOneSpectrum (𝓞 K)) (a b : AdelicGL2 (𝓞 K) K) :
    componentMatrix v (a * b) = componentMatrix v a * componentMatrix v b := by
  simp only [componentMatrix, map_mul, Units.val_mul]

private theorem componentMatrix_one (v : HeightOneSpectrum (𝓞 K)) : componentMatrix v (1 : AdelicGL2 (𝓞 K) K) = 1 := by
  simp only [componentMatrix, map_one, Units.val_one]

private theorem v_mul_apply_le (v : HeightOneSpectrum (𝓞 K)) (A B : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (α β : ℤᵐ⁰) (hA : ∀ i j, Valued.v (A i j) ≤ α) (hB : ∀ i j, Valued.v (B i j) ≤ β) (i j : Fin 2) :
    Valued.v ((A * B) i j) ≤ α * β := by
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine Valuation.map_add_le _ ?_ ?_ <;> rw [map_mul] <;> exact mul_le_mul' (hA _ _) (hB _ _)

end Components

open scoped WithZero in

theorem kZeroSet_meets (S : Finset (HeightOneSpectrum (𝓞 K))) (m : ↥S → ℕ)
    (g : AdelicGL2 (𝓞 K) K) :
    ∃ γ : GL (Fin 2) K, globalPoints (𝓞 K) K γ * g ∈ kZeroSet S m := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hS
  · exact ⟨1, fun v => absurd v.2 (by simp [hS])⟩

  set G : ∀ v : ↥S, Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K) := fun v => componentMatrix v.1 g with hG
  set Gi : ∀ v : ↥S, Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K) := fun v => componentMatrix v.1 g⁻¹ with hGi
  have hGiG : ∀ v : ↥S, Gi v * G v = 1 := fun v => by
    rw [hGi, hG, ← componentMatrix_mul, inv_mul_cancel, componentMatrix_one]
  let μ : ↥S → ℤ := fun v => ∑ i : Fin 2, ∑ j : Fin 2, |WithZero.log (Valued.v (G v i j))|
  have hμ : ∀ (v : ↥S) (i j : Fin 2), Valued.v (G v i j) ≤ WithZero.exp (μ v) := by
    intro v i j
    by_cases h0 : Valued.v (G v i j) = 0
    · rw [h0]; exact zero_le'
    rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    refine (le_abs_self _).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun i' => ∑ j' : Fin 2, |WithZero.log (Valued.v (G v i' j'))|)
      (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j' => |WithZero.log (Valued.v (G v i j'))|) (fun j' _ => abs_nonneg _)
      (Finset.mem_univ j)

  have hx : ∀ i j : Fin 2, ∃ x : K, ∀ v : ↥S,
      Valued.v (Gi v i j - algebraMap K (v.1.adicCompletion K) x) < WithZero.exp (-((m v : ℤ) + 1) - μ v) :=
    fun i j => exists_forall_valued_sub_lt S (fun v => Gi v i j) fun v => -((m v : ℤ) + 1) - μ v
  choose x hx using hx
  let X : Matrix (Fin 2) (Fin 2) K := Matrix.of fun i j => x i j
  let Xv : ∀ v : ↥S, Matrix (Fin 2) (Fin 2) (v.1.adicCompletion K) := fun v =>
    (algebraMap K (v.1.adicCompletion K)).mapMatrix X

  have hE : ∀ (v : ↥S) (i j : Fin 2), Valued.v (((Xv v - Gi v) * G v) i j) ≤ WithZero.exp (-((m v : ℤ) + 1)) := by
    intro v i j
    have h := v_mul_apply_le v.1 (Xv v - Gi v) (G v) (WithZero.exp (-((m v : ℤ) + 1) - μ v)) (WithZero.exp (μ v))
      (fun k l => ?_) (hμ v) i j
    · rwa [← WithZero.exp_add, show -((m v : ℤ) + 1) - μ v + μ v = -((m v : ℤ) + 1) by ring] at h
    rw [Matrix.sub_apply, Valuation.map_sub_swap]
    exact (hx k l v).le
  have hXG : ∀ v : ↥S, Xv v * G v = 1 + (Xv v - Gi v) * G v := fun v => by
    rw [sub_mul, hGiG]; abel
  have hlt1 : ∀ v : ↥S, WithZero.exp (-((m v : ℤ) + 1)) < 1 := fun v => by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hdiag : ∀ (v : ↥S) (i : Fin 2), Valued.v ((Xv v * G v) i i) = 1 := fun v i => by
    rw [hXG, Matrix.add_apply, Matrix.one_apply_eq, Valuation.map_add_eq_of_lt_left]
    · exact map_one _
    · rw [map_one]; exact lt_of_le_of_lt (hE v i i) (hlt1 v)
  have hoff : ∀ (v : ↥S) (i j : Fin 2), i ≠ j →
      Valued.v ((Xv v * G v) i j) ≤ WithZero.exp (-((m v : ℤ) + 1)) := fun v i j hij => by
    rw [hXG, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add]
    exact hE v i j

  have hdet : X.det ≠ 0 := by
    obtain ⟨v₀, hv₀⟩ := hS
    intro h0
    have h1 : (Xv ⟨v₀, hv₀⟩ * G ⟨v₀, hv₀⟩).det = 0 := by
      rw [Matrix.det_mul, show (Xv ⟨v₀, hv₀⟩).det = 0 from ?_, zero_mul]
      change ((algebraMap K (v₀.adicCompletion K)).mapMatrix X).det = 0
      rw [← RingHom.map_det, h0, map_zero]
    have h2 : Valued.v ((Xv ⟨v₀, hv₀⟩ * G ⟨v₀, hv₀⟩).det) = 1 := by
      rw [Matrix.det_fin_two, sub_eq_add_neg, Valuation.map_add_eq_of_lt_left]
      · rw [map_mul, hdiag, hdiag, mul_one]
      · rw [Valuation.map_neg, map_mul, map_mul, hdiag, hdiag, mul_one]
        calc Valued.v ((Xv ⟨v₀, hv₀⟩ * G ⟨v₀, hv₀⟩) 0 1) * Valued.v ((Xv ⟨v₀, hv₀⟩ * G ⟨v₀, hv₀⟩) 1 0)
            ≤ WithZero.exp (-((m ⟨v₀, hv₀⟩ : ℤ) + 1)) * WithZero.exp (-((m ⟨v₀, hv₀⟩ : ℤ) + 1)) :=
              mul_le_mul' (hoff _ 0 1 (by decide)) (hoff _ 1 0 (by decide))
          _ < 1 := by rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    rw [h1, map_zero] at h2
    exact zero_ne_one h2
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero X hdet, fun v => ?_⟩

  have hcomp : componentMatrix v.1 (globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.mkOfDetNeZero X hdet) * g) =
      Xv v * G v := by
    rw [componentMatrix_mul]
    congr 1
  show MemZK0At v.1 (m v) _
  rw [MemZK0At, hcomp, hdiag v 1, hdiag v 0]
  refine ⟨one_ne_zero, rfl, (hoff v 0 1 (by decide)).trans (hlt1 v).le, ?_⟩
  rw [one_mul]
  refine (hoff v 1 0 (by decide)).trans ?_
  rw [WithZero.exp_le_exp]
  omega

open scoped Classical in

noncomputable def archNormFactor (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∏ w : InfinitePlace K,
    if hw : w.IsReal then ((Real.sqrt |(realComponent w hw g).det| : ℝ) : ℂ)⁻¹
    else ((‖(complexComponent w (InfinitePlace.not_isReal_iff_isComplex.mp hw) g).det‖ : ℝ) : ℂ)⁻¹

noncomputable def archW'
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  archW archR archC dR dC g * archNormFactor g

noncomputable def jlSeries' {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) : AdelicGL2 (𝓞 K) K → ℂ :=
  whittakerSeries d.a d.epsChar (archW' archR archC dR dC) dF.Wf

noncomputable def theForm {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) : AdelicGL2 (𝓞 K) K → ℂ :=
  extendByRationalPoints (kZeroSet S d.m) (kZeroSet_meets S d.m) (jlSeries' d archR archC dR dC dF)

noncomputable abbrev pinsOf (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    CarrierPins K :=
  productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
    (adelicBox K)

theorem theForm_eq
    {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) :
    theForm d archR archC dR dC dF =
      extendByRationalPoints (kZeroSet S d.m) (kZeroSet_meets S d.m) (jlSeries' d archR archC dR dC dF) :=
  rfl

noncomputable def translateSum
    {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}
    {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ}
    {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi)
    {n : ℕ} (ks : Fin n → AdelicGL2 (𝓞 K) K) (cs : Fin n → ℂ) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∑ i, cs i * theForm d archR archC dR dC dF (g * ks i)

end LanglandsTunnell.Converse.CuspSynthesis

end


