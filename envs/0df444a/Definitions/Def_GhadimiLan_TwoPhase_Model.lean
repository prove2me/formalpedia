-- Prove2me | Definitions.Def_GhadimiLan_TwoPhase_Model
-- name    : GhadimiLan_TwoPhase_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:03:53.003838+00:00
-- url     : https://prove2.me/theorems/55bf84d0-e517-47ba-ba1b-7f3981970a14
-- title:
--   §§1–2: RSG runs, stochastic oracle, and two-phase selection
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be differentiable and bounded below, with $L$-Lipschitz gradient $g=\nabla f$. Its optimal value $f^*$ is the infimum of $f$. A stochastic first-order oracle returns $G(x,\xi)$. At every RSG step, its conditional mean at the current iterate is $g(x)$ and the mean squared error is at most $\sigma^2$; the noise variables may depend on earlier ones.
--
--   Starting from $x_1$, a run follows $x_{k+1}=x_k-\gamma_kG(x_k,\xi_k)$ and outputs $x_R$, where $R\in\{1,\ldots,N\}$ has the mass function of (2.3) and is independent of the run's noise. The constant step is $\gamma_k=\min\{1/L,\widetilde D/(\sigma\sqrt N)\}$. The model defines $D_f=\sqrt{2(f(x_1)-f^*)/L}$ and $\mathcal B_N=LD_f^2/N+(\widetilde D+D_f^2/\widetilde D)\sigma/\sqrt N$.
--
--   A two-phase system draws $S$ independent RSG outputs $\bar x_s$. For each candidate, it averages $T$ further oracle calls into $\widehat g_s=T^{-1}\sum_{k=1}^T G(\bar x_s,\eta_{s,k})$ and chooses any candidate with minimum $\|\widehat g_s\|$. The same post-optimization samples may be recycled across candidates. The resulting point is $\bar x^*$.
--
--   These definitions provide the common model for the one-run rate, probability amplification, and final two-phase guarantee.
--
--   **Formalization Note** The noise space is any measurable space; the paper uses Borel subsets of Euclidean space. The algorithm is indexed from one, while the candidates use `Fin S`. The conditional oracle assumptions include explicit integrability, and the oracle is jointly measurable. The selected minimizer may use any tie rule and is not assumed measurable. Positive $L$, $\sigma$, and $\widetilde D$ rule out zero denominators and empty estimates.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, Assumption A1 and Eqs. (1.1)–(1.3), p. 2; RSG method and Eq. (2.3), pp. 5–6; Eqs. (2.13)–(2.14), p. 8; 2-RSG method and Eq. (2.21), p. 11

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory

namespace GhadimiLan.TwoPhase

/-- Assumption A1 along a possibly dependent-noise run. The conditional mean is taken
with respect to the past, and each Bochner integral is protected by integrability. -/
def AssumptionA1 {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : MeasureTheory.Measure Ω) (ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›)
    (g : GhadimiLan.RSG.E n → GhadimiLan.RSG.E n) (G : GhadimiLan.RSG.E n → Ξ → GhadimiLan.RSG.E n)
    (ξ : ℕ → Ω → Ξ) (x : ℕ → Ω → GhadimiLan.RSG.E n) (σ : ℝ) : Prop :=
  0 ≤ σ ∧ ∀ k, 1 ≤ k →
    Measurable[ℱ k] (ξ k) ∧
    Integrable (fun ω => G (x k ω) (ξ k ω)) μ ∧
    (MeasureTheory.condExp (ℱ (k - 1)) μ
      (fun ω => G (x k ω) (ξ k ω)) =ᵐ[μ]
      fun ω => g (x k ω)) ∧
    Integrable (fun ω => ‖G (x k ω) (ξ k ω) - g (x k ω)‖ ^ 2) μ ∧
    (∫ ω, ‖G (x k ω) (ξ k ω) - g (x k ω)‖ ^ 2 ∂μ) ≤ σ ^ 2

/-- The constant step (2.13). The conditions `L, σ, D̃ > 0` and `N ≥ 1` are
recorded by the problem and by the theorems that use it. -/
noncomputable def rsgStep (L Dt σ : ℝ) (N : ℕ) : ℝ :=
  min (1 / L) (Dt / (σ * Real.sqrt N))

/-- The bound 𝓑_N of (2.14). -/
noncomputable def BN (L Df Dt σ : ℝ) (N : ℕ) : ℝ :=
  L * Df ^ 2 / N + (Dt + Df ^ 2 / Dt) * σ / Real.sqrt N

/-- The problem (1.1), its true infimum, the Borel oracle, and the positive
parameters used in (2.13). The noise carrier generalizes the paper's Borel subset
of a Euclidean space to a measurable space. -/
structure Problem (n : ℕ) (Ξ : Type*) [MeasurableSpace Ξ] where
  f : GhadimiLan.RSG.E n → ℝ
  g : GhadimiLan.RSG.E n → GhadimiLan.RSG.E n
  G : GhadimiLan.RSG.E n → Ξ → GhadimiLan.RSG.E n
  L : ℝ
  σ : ℝ
  Dt : ℝ
  fstar : ℝ
  x₁ : GhadimiLan.RSG.E n
  smooth : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L
  L_pos : 0 < L
  σ_pos : 0 < σ
  Dt_pos : 0 < Dt
  infimum : IsGLB (Set.range f) fstar
  oracle_measurable : Measurable (Function.uncurry G)

/-- The constant D_f from (2.5). -/
noncomputable def Df {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (P : Problem n Ξ) : ℝ :=
  Real.sqrt (2 * (P.f P.x₁ - P.fstar) / P.L)

/-- One independent draw of the RSG output. Its trajectory comes from the
oracle recursion, not from a performance bound assumed in advance. -/
structure Run {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Problem n Ξ) (N : ℕ) (μ : MeasureTheory.Measure Ω) where
  ℱ : MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›
  ξ : ℕ → Ω → Ξ
  x : ℕ → Ω → GhadimiLan.RSG.E n
  R : Ω → ℕ
  recursion : GhadimiLan.RSG.IsRSGRun P.G (fun _ => rsgStep P.L P.Dt P.σ N) P.x₁ ξ x
  a1 : AssumptionA1 μ ℱ P.g P.G ξ x P.σ
  index : GhadimiLan.RSG.IsRandomOutputIndex μ R P.L (fun _ => rsgStep P.L P.Dt P.σ N) N
  index_indep : ProbabilityTheory.IndepFun R (fun ω k => ξ k ω) μ

/-- The output x_R of one RSG run. -/
def output {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Problem n Ξ} {N : ℕ} {μ : MeasureTheory.Measure Ω}
    (A : Run P N μ) (ω : Ω) : GhadimiLan.RSG.E n := A.x (A.R ω) ω

/-- The sample average (2.21), with one sequence of post-optimization samples
per candidate. The same sequence may be reused for several candidates. -/
noncomputable def estimate {n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Problem n Ξ} {N : ℕ} {μ : MeasureTheory.Measure Ω}
    {S : ℕ} (runs : Fin S → Run P N μ)
    (η : Fin S → ℕ → Ω → Ξ) (T : ℕ) (s : Fin S) (ω : Ω) : GhadimiLan.RSG.E n :=
  (1 / (T : ℝ)) • ∑ k ∈ Finset.Icc 1 T, P.G (output (runs s) ω) (η s k ω)

/-- Assumption A1 during post-optimization, conditioned on the known candidate.
The filtration at time zero contains the candidate, so recycled samples are allowed. -/
def PostA1 {n S N : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Problem n Ξ) (μ : MeasureTheory.Measure Ω)
    (runs : Fin S → Run P N μ)
    (𝒢 : Fin S → MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›)
    (η : Fin S → ℕ → Ω → Ξ) : Prop :=
  (∀ s, Measurable[𝒢 s 0] (output (runs s))) ∧
    ∀ s k, 1 ≤ k →
      Measurable[𝒢 s k] (η s k) ∧
      Integrable (fun ω => P.G (output (runs s) ω) (η s k ω)) μ ∧
      (MeasureTheory.condExp (𝒢 s (k - 1)) μ
        (fun ω => P.G (output (runs s) ω) (η s k ω)) =ᵐ[μ]
        fun ω => P.g (output (runs s) ω)) ∧
      Integrable (fun ω => ‖P.G (output (runs s) ω) (η s k ω) -
        P.g (output (runs s) ω)‖ ^ 2) μ ∧
      (∫ ω, ‖P.G (output (runs s) ω) (η s k ω) -
        P.g (output (runs s) ω)‖ ^ 2 ∂μ) ≤ P.σ ^ 2

/-- The S candidate runs, their independence, the post-optimization sample
phase, and an arbitrary minimizer of the observed gradient norms (any tie rule;
no measurability of the selection is assumed). -/
structure System {n S N T : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Problem n Ξ) (μ : MeasureTheory.Measure Ω) where
  runs : Fin S → Run P N μ
  outputs_indep : ProbabilityTheory.iIndepFun (fun s ω => output (runs s) ω) μ
  𝒢 : Fin S → MeasureTheory.Filtration ℕ ‹MeasurableSpace Ω›
  η : Fin S → ℕ → Ω → Ξ
  post_a1 : PostA1 P μ runs 𝒢 η
  sStar : Ω → Fin S
  selected_min : ∀ ω s, ‖estimate runs η T (sStar ω) ω‖ ≤ ‖estimate runs η T s ω‖

/-- The point selected in the post-optimization phase. -/
def chosen {n S N T : ℕ} {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Problem n Ξ} {μ : MeasureTheory.Measure Ω}
    (A : System (S := S) (N := N) (T := T) P μ) (ω : Ω) : GhadimiLan.RSG.E n :=
  output (A.runs (A.sStar ω)) ω

end GhadimiLan.TwoPhase


