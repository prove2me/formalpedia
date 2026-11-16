-- Prove2me | Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Privacy
-- name    : PrivateContinualCounting_Kraft_Supplement_Privacy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:24:56.835657+00:00
-- url     : https://prove2.me/theorems/3704cbb6-2657-4987-a236-6494852c03a6
-- title:
--   Additive processes, finite transcripts and Gaussian testing privacy
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space. An additive data-independent counter is one measurable real process $(N_t)_{t\ge0}$, with $N_0=0$ almost surely and finite second moments, released as $Y_t=S_t+N_t$ for every input stream. No centering, stationarity, Gaussianity or independent-increment condition is imposed. Its interval variance and zero-based increment are
--   $$V_N(a,w)=\operatorname{Var}_P(N_{a+w}-N_a),\qquad D_i=N_{i+1}-N_i.$$
--   The uniform envelope means $V_N(a,w)\le B(w)$ for every $a\ge0,w\ge1$. Source input $i+1$ is coordinate $i$ in the reused stream representation.
--
--   Finite-transcript $(\varepsilon,\delta)$-privacy uses the published finite-database approximate-DP predicate on each prefix input, padded by zeros. All laws here depend only on that prefix, so this is equivalent to the source's quantification over infinite streams. The referenced predicate uses exactly-one-coordinate adjacency; identical databases satisfy the inequality automatically for the nonnegative parameters in the statements.
--
--   For probability measures $P,Q$ and $0\le\alpha\le1$, randomized testing privacy uses
--   $$T(P,Q)(\alpha)=\inf_{\substack{\phi\text{ measurable},\ 0\le\phi\le1\\\int\phi\,dP\le\alpha}}\left(1-\int\phi\,dQ\right).$$
--   Every ordered adjacent transcript pair must have tradeoff at least that of $\mathcal N(0,1)$ versus $\mathcal N(\mu,1)$. Set
--   $$\delta_\mu(\varepsilon)=\Phi(-\varepsilon/\mu+\mu/2)-e^\varepsilon\Phi(-\varepsilon/\mu-\mu/2),\quad c_{\varepsilon,\delta}=\frac{1-\delta}{4(1+e^\varepsilon)}.$$
--   An admissible scale is any $\mu>0$ with $\delta_\mu(\varepsilon)\le\delta$. The scalar LTI noise and its transcript law are computed directly from the published factors and one independent standard Gaussian seed, with scale $\Delta/\mu$. This supplies privacy and interval vocabulary; it assumes no calibration or accuracy theorem.
--
--   **Formalization Note** Tests are bounded, so their expectations under the probability laws used here are integrable. The feasible set of the testing infimum contains the zero test and lies in $[0,1]$. The predicate is used only for probability measures and $\alpha\in[0,1]$.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), p. 6, PDF p. 8, Section 2.1 and Definition 2.3; p. 9, PDF p. 11, Section 4

import Definitions.Def_PrivateContinualCounting_Kraft_GaussianCounter
import Definitions.Def_PrivateContinualCounting_Kraft_LTIFactors
import Definitions.Def_PrivRobustStat_Privacy

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

/-- A finite input padded by zero, using the published stream type. -/
def extendStream {n : ℕ} (x : Fin n → Set.Icc (0 : ℝ) 1) : Stream :=
  fun j => if h : j < n then x ⟨j,h⟩ else ⟨0, by constructor <;> norm_num⟩

/-- Privacy of every positive finite transcript. The reused finite-database definition has
exact-change adjacency; unchanged databases obey the inequality for ε,δ≥0 automatically. -/
def TranscriptDP (law : (x : Stream) → (n : ℕ) → Measure (Fin n → ℝ)) (ε δ : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → PrivRobustStat.IsApproxDP (n := n) (fun x => law (extendStream x) n) ε δ

/-- The Neyman–Pearson tradeoff, over measurable randomized tests. For α∈[0,1] its
feasible set is nonempty (the zero test), and objective values lie in [0,1]. -/
noncomputable def testingTradeoff {X : Type} [MeasurableSpace X]
    (P Q : Measure X) (α : ℝ) : ℝ :=
  sInf {β : ℝ | ∃ φ : X → ℝ, Measurable φ ∧
    (∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) ∧
    (∫ x, φ x ∂P) ≤ α ∧ β = 1 - ∫ x, φ x ∂Q}

def TranscriptGDP (law : (x : Stream) → (n : ℕ) → Measure (Fin n → ℝ)) (μ : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ x y : Stream, Adjacent x y →
    ∀ α ∈ Set.Icc (0 : ℝ) 1,
      testingTradeoff (gaussianReal 0 1) (gaussianReal μ 1) α ≤
        testingTradeoff (law x n) (law y n) α

noncomputable def gaussianDelta (ε μ : ℝ) : ℝ :=
  (gaussianReal 0 1).real (Set.Iic (-ε / μ + μ / 2)) -
  Real.exp ε * (gaussianReal 0 1).real (Set.Iic (-ε / μ - μ / 2))

def AdmissibleGDP (ε δ μ : ℝ) : Prop := 0 < μ ∧ gaussianDelta ε μ ≤ δ

/-- An arbitrary stream-independent process. No Gaussianity, centering or stationarity. -/
structure AdditiveNoise (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) where
  noise : ℕ → Ω → ℝ
  measurable : ∀ t, Measurable (noise t)
  secondMoment : ∀ t, MemLp (noise t) 2 P
  zero : ∀ᵐ ω ∂P, noise 0 ω = 0

noncomputable def AdditiveNoise.law {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (N : AdditiveNoise Ω P) (x : Stream) (n : ℕ) : Measure (Fin n → ℝ) :=
  P.map (fun ω k => prefixSum x (k.val + 1) + N.noise (k.val + 1) ω)

noncomputable def AdditiveNoise.intervalVariance {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (N : AdditiveNoise Ω P) (a w : ℕ) : ℝ :=
  variance (fun ω => N.noise (a+w) ω - N.noise a ω) P

/-- Zero-based increment i is the source's D_{i+1}. -/
def AdditiveNoise.increment {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (N : AdditiveNoise Ω P) (i : ℕ) (ω : Ω) : ℝ := N.noise (i+1) ω - N.noise i ω

def UniformEnvelope {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (N : AdditiveNoise Ω P) (B : ℕ → ℝ) : Prop :=
  ∀ a w : ℕ, 0 < w → N.intervalVariance a w ≤ B w

noncomputable def privacyConstant (ε δ : ℝ) : ℝ :=
  (1-δ)/(4*(1+Real.exp ε))

/-- Directly defined actual LTI noise and laws; admissibility is a theorem obligation
when the raw factors are constructed, and is assumed only when already given LTI factors. -/
noncomputable def scalarNoise (d : LTIData ℝ 1) (μ : ℝ) (t : ℕ)
    (ω : ℕ × Fin 1 → ℝ) : ℝ :=
  Real.sqrt d.deltaSq / μ *
    ∑ i ∈ Finset.range t, d.l (t-1-i) 0 * ω (i,0)

noncomputable def scalarLaw (d : LTIData ℝ 1) (μ : ℝ) (x : Stream) (n : ℕ) :
    Measure (Fin n → ℝ) :=
  (gaussianSeed (ℕ × Fin 1)).map
    (fun ω k => prefixSum x (k.val+1) + scalarNoise d μ (k.val+1) ω)

noncomputable def scalarIntervalVariance (d : LTIData ℝ 1) (μ : ℝ) (a w : ℕ) : ℝ :=
  variance (fun ω => scalarNoise d μ (a+w) ω - scalarNoise d μ a ω)
    (gaussianSeed (ℕ × Fin 1))

end PrivateContinualCounting.Kraft.Supplement


