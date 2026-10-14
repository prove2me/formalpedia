-- Prove2me | Definitions.Def_ReflectedRWLDP_SamplePath_Model
-- name    : ReflectedRWLDP_SamplePath_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:34:34.682977+00:00
-- url     : https://prove2.me/theorems/900cdc4a-49a6-4886-8717-47117dc3f0f4
-- title:
--   §2.1–2.2, pp. 4–7 — the reflected random walk, Assumptions 2.1–2.3, regeneration times, busy-period areas $W_j$, $V_n$, $\lambda$ and the processes $\bar Y_n$, $\bar Z_n$, $\bar S_n$
-- statement:
--   **The chain.** Let $U_1,U_2,\dots$ be i.i.d. copies of a real random variable $U$ with $\mu=\mathbf E(U)<0$. The reflected random walk is the Lindley recursion
--   $$X_{n+1}=[X_n+U_{n+1}]^+,\qquad n\ge 0,\qquad X_0=0 ;$$
--   $\mathbf P_{xy}$ denotes the law of the chain started at $X_0=xy$.
--
--   **Assumptions.** Let $\theta_+$ and $\theta_-$ be the supremum and infimum of $\{\theta:\mathbf E(e^{\theta U})<\infty\}$.
--   1. (Assumption 2.1) $-\infty\le\theta_-<0<\theta_+\le\infty$.
--   2. (Assumption 2.2) $\displaystyle\lim_{n\to\infty}\frac{\log\mathbf P(U\ge n)}{n}=-\theta_+$ and $\displaystyle\lim_{n\to\infty}\frac{\log\mathbf P(-U\ge n)}{n}=\theta_-$.
--   3. (Assumption 2.3) $\mathbf P(U>0)>0$.
--
--   A constant $p>0$ is fixed and $\alpha=1/(1+p)$.
--
--   **Regeneration.** $T_0=0$ and $T_i=\inf\{k>T_{i-1}:X_k=0\}$; $N(t)=\max\{k\ge0:T_k\le t\}$; the area of the $j$-th busy period is
--   $$W_j=\sum_{i=T_{j-1}+1}^{T_j}X_i^p ,$$
--   the area of the last busy period is $V_n=\sum_{i=T_{N(n)}+1}^{n}X_i^p$, and
--   $$\lambda=\frac{\mathbf E\big(\sum_{i=1}^{T_1}X_i^p\big)}{\mathbf E(T_1)} .$$
--
--   **Processes in $\mathbb D[0,1]$.**
--   $$\bar Y_n(t)=\frac1n\sum_{i=1}^{\lfloor nt\rfloor}X_i^p,\qquad \bar Z_n(t)=\frac1n\sum_{j=1}^{N(nt)}W_j,\qquad \bar S_n(t)=\frac1nV_n\mathbb 1_{\{1\}}(t),\qquad t\in[0,1].$$
--   The file also defines the block vector $\big(\frac1n\sum_{j=N(nt_{i-1})+1}^{N(nt_i)}W_j\big)_{i=1}^k$ in $\mathbb R^k_+$ of Lemmas 3.2–3.3.
--
--   $\bar Y_n$ is the process of the main theorem; $\bar Z_n$ and $\bar S_n$ split it into completed busy periods and the busy period in progress.
--
--   **Formalization Note** The increments are a sequence `U : ℕ → Ω → ℝ` with `U i` the paper's $U_{i+1}$, so the generic $U$ is `U 0`. They are measurable, independent (`iIndepFun`) and identically distributed. Integrability of $U$ is stated explicitly; Assumption 2.1 implies it. $\mathbf E(e^{\theta U})$ is a lower Lebesgue integral in $[0,\infty]$ and $\theta_\pm\in[-\infty,\infty]$. Assumption 2.2 runs over $n\in\mathbb N$ in the extended reals with $\log 0=-\infty$. The chain is defined from an arbitrary start $x_0$, and $x_0=0$ is the paper's $X$. $T_i\in\mathbb N\cup\{\infty\}$ (an empty infimum is $\infty$). $W_j\in[0,\infty]$ is a sum over $T_{j-1}<i\le T_j$, which is infinite when $T_j=\infty$. $N(t)=N(\lfloor t\rfloor)$ is a supremum of natural numbers. $\lambda$ is the real part of the ratio of the two expectations in $[0,\infty]$; both are finite under the assumptions. Every $W_j$ with $j\le N(nt)$ is finite, so $\bar Z_n$ uses its real value. The three processes are step paths $t\mapsto h(\lfloor nt\rfloor)$. For $\bar S_n$, $h(k)=V_n/n$ if $k=n$ and $0$ otherwise; on $[0,1]$ with $n\ge1$, $\lfloor nt\rfloor=n$ exactly when $t=1$. $\mathbb R^k_+$ carries the sup distance, which gives the Euclidean topology.
-- source:
--   Bazhba, Blanchet, Rhee & Zwart, Sample-Path Large Deviations for Unbounded Additive Functionals of the Reflected Random Walk, arXiv:2003.14381v3, pp. 4–7, §2.1 (Lindley recursion, Assumptions 2.1–2.3, Ȳ_n, α), §2.2 (T_i, λ, N(t), τ_j, W_j, Z̄_n, V_n, S̄_n); pp. 10–12, Lemmas 3.2–3.3

import Mathlib
import Definitions.Def_ReflectedRWLDP_SamplePath_PathSpace
import Definitions.Def_ReflectedRWLDP_SamplePath_LDP

namespace ReflectedRWLDP.SamplePath

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-!
Bazhba, Blanchet, Rhee & Zwart, arXiv:2003.14381v3, §2.1–2.2 (pp. 4–7) and §3 (pp. 9–12): the
reflected random walk `X_{n+1} = [X_n + U_{n+1}]⁺`, Assumptions 2.1–2.3, the speed exponent
`α = 1/(1+p)`, the regeneration times `T_i`, the renewal counting process `N(t)`, the busy-period
areas `W_j`, the area `V_n` of the last busy period, the regenerative mean `λ`, and the processes
`Ȳ_n`, `Z̄_n`, `S̄_n` as random elements of `𝔻[0,1]`.

Indexing: the increments are `U : ℕ → Ω → ℝ` with `U i` the paper's `U_{i+1}`, so the paper's generic
increment `U` (whose law enters every rate function) is `U 0`.
-/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `E(e^{θV})` as a lower Lebesgue integral in `[0, ∞]` (never a junk value off the domain of the
moment generating function). -/
noncomputable def expMoment (P : Measure Ω) (V : Ω → ℝ) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * V ω)) ∂P

/-- `θ₊ = sup {θ : E(e^{θV}) < ∞}` (Assumption 2.1), in `EReal` (it may be `+∞`). -/
noncomputable def thetaPlus (P : Measure Ω) (V : Ω → ℝ) : EReal :=
  ⨆ (θ : ℝ) (_ : expMoment P V θ < ⊤), (θ : EReal)

/-- `θ₋ = inf {θ : E(e^{θV}) < ∞}` (Assumption 2.1), in `EReal` (it may be `−∞`). -/
noncomputable def thetaMinus (P : Measure Ω) (V : Ω → ℝ) : EReal :=
  ⨅ (θ : ℝ) (_ : expMoment P V θ < ⊤), (θ : EReal)

/-- The standing assumptions of the paper (§2.1, pp. 4–5) on the increments `U` and the exponent
`p`:
* `U_1, U_2, …` (here `U 0, U 1, …`) are i.i.d. copies of a random variable `U` with
  `µ = E(U) < 0` (integrability is implied by Assumption 2.1 and is stated for definiteness);
* Assumption 2.1: `−∞ ≤ θ₋ < 0 < θ₊ ≤ ∞`;
* Assumption 2.2: `lim_n log P(U ≥ n)/n = −θ₊` and `lim_n log P(−U ≥ n)/n = θ₋` (`n ∈ ℕ`, in `EReal`,
  `log 0 = −∞`);
* Assumption 2.3: `P(U > 0) > 0`;
* `p > 0`. -/
structure Standing (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ) : Prop where
  isProbability : IsProbabilityMeasure P
  measurable : ∀ i, Measurable (U i)
  indep : iIndepFun U P
  identDistrib : ∀ i, IdentDistrib (U i) (U 0) P P
  integrable : Integrable (U 0) P
  mean_neg : ∫ ω, U 0 ω ∂P < 0
  assumption_2_1 : thetaMinus P (U 0) < 0 ∧ 0 < thetaPlus P (U 0)
  assumption_2_2_upper :
    Tendsto (fun n : ℕ => speedLog (n : ℝ) (P {ω | (n : ℝ) ≤ U 0 ω})) atTop
      (𝓝 (-thetaPlus P (U 0)))
  assumption_2_2_lower :
    Tendsto (fun n : ℕ => speedLog (n : ℝ) (P {ω | (n : ℝ) ≤ -U 0 ω})) atTop
      (𝓝 (thetaMinus P (U 0)))
  assumption_2_3 : 0 < P {ω | 0 < U 0 ω}
  p_pos : 0 < p

/-- `α = 1/(1+p)` (p. 5). -/
noncomputable def alpha (p : ℝ) : ℝ := 1 / (1 + p)

/-- The reflected random walk (Lindley recursion, p. 4) started at `x₀`:
`X_0 = x₀`, `X_{n+1} = [X_n + U_{n+1}]⁺` (here `U n` is the paper's `U_{n+1}`). The paper's chain is
`x₀ = 0`; `P_{xy}` of §4 is the law of the chain with `x₀ = xy`. -/
noncomputable def lindley (x₀ : ℝ) (U : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => x₀
  | n + 1 => fun ω => max (lindley x₀ U n ω + U n ω) 0

/-- The regeneration (return-to-zero) times of a path `x` (p. 6): `T_0 = 0` and
`T_i = inf {k > T_{i−1} : x_k = 0}` in `ℕ∞` (`= ∞` when there is no such `k`). -/
noncomputable def retTime (x : ℕ → ℝ) : ℕ → ℕ∞
  | 0 => 0
  | i + 1 => ⨅ (k : ℕ) (_ : retTime x i < (k : ℕ∞)) (_ : x k = 0), (k : ℕ∞)

/-- `N(m) = max {k ≥ 0 : T_k ≤ m}` for an integer time `m`. (The set contains `0` and is finite, since
`T_k ≥ k`.) -/
noncomputable def NcountNat (x : ℕ → ℝ) (m : ℕ) : ℕ :=
  sSup {k : ℕ | retTime x k ≤ (m : ℕ∞)}

/-- The renewal counting process `N(t) = max {k ≥ 0 : T_k ≤ t}`, `t ≥ 0` (p. 6). Since the `T_k` are
integers (or `∞`), `T_k ≤ t` iff `T_k ≤ ⌊t⌋`. -/
noncomputable def Ncount (x : ℕ → ℝ) (t : ℝ) : ℕ := NcountNat x ⌊t⌋₊

/-- The area `W_j = ∑_{i=T_{j−1}+1}^{T_j} x_i^p` under `x^p` during the `j`-th busy period (p. 7),
`j ≥ 1`, in `[0, ∞]`; when `T_j = ∞` the sum runs over all `i > T_{j−1}`. -/
noncomputable def W (x : ℕ → ℝ) (p : ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑' i : ℕ, Set.indicator {i : ℕ | retTime x (j - 1) < (i : ℕ∞) ∧ (i : ℕ∞) ≤ retTime x j}
    (fun i : ℕ => ENNReal.ofReal (x i ^ p)) i

open Classical in
/-- `V_n = ∑_{i=T_{N(n)}+1}^{n} x_i^p`, the area under `x^p` during the last (incomplete)
regeneration cycle up to time `n` (p. 7). -/
noncomputable def V (x : ℕ → ℝ) (p : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ (Finset.Icc 1 n).filter (fun i : ℕ => retTime x (NcountNat x n) < (i : ℕ∞)), x i ^ p

/-- The path `k ↦ X_k(ω)` of the reflected random walk started at `0`. -/
noncomputable def chain (U : ℕ → Ω → ℝ) (ω : Ω) : ℕ → ℝ := fun k => lindley 0 U k ω

/-- `λ = E(∑_{i=1}^{T₁} X_i^p) / E(T₁)` (p. 6), for the chain started at `0`: the ratio of the two
expectations in `[0, ∞]`, converted to a real number. (Under the standing assumptions both
expectations are finite and `E(T₁) ≥ 1`.) -/
noncomputable def lam (P : Measure Ω) (U : ℕ → Ω → ℝ) (p : ℝ) : ℝ :=
  ((∫⁻ ω, W (chain U ω) p 1 ∂P) / (∫⁻ ω, ENat.toENNReal (retTime (chain U ω) 1) ∂P)).toReal

/-- `Ȳ_n(t) = (1/n) ∑_{i=1}^{⌊nt⌋} X_i^p`, `t ∈ [0,1]` (p. 5), as a random element of `𝔻[0,1]`. -/
noncomputable def Ybar (U : ℕ → Ω → ℝ) (p : ℝ) (n : ℕ) (ω : Ω) : DPath 1 :=
  stepPath n (fun k => (n : ℝ)⁻¹ * ∑ i ∈ Finset.Icc 1 k, chain U ω i ^ p)

/-- `Z̄_n(t) = (1/n) ∑_{j=1}^{N(nt)} W_j`, `t ∈ [0,1]` (p. 7), as a random element of `𝔻[0,1]`
(`N(nt) = N(⌊nt⌋)`; every `W_j` with `j ≤ N(nt)` is finite). -/
noncomputable def Zbar (U : ℕ → Ω → ℝ) (p : ℝ) (n : ℕ) (ω : Ω) : DPath 1 :=
  stepPath n (fun k =>
    (n : ℝ)⁻¹ * (∑ j ∈ Finset.Icc 1 (NcountNat (chain U ω) k), W (chain U ω) p j).toReal)

/-- `S̄_n(t) = (1/n) V_n 𝟙_{{1}}(t)`, `t ∈ [0,1]` (p. 7), as a random element of `𝔻[0,1]` (for
`n ≥ 1` and `t ∈ [0,1]`, `⌊nt⌋ = n` iff `t = 1`; for `n = 0` both sides are `0`). -/
noncomputable def Sbar (U : ℕ → Ω → ℝ) (p : ℝ) (n : ℕ) (ω : Ω) : DPath 1 :=
  stepPath n (fun k => if k = n then (n : ℝ)⁻¹ * V (chain U ω) p n else 0)

/-- The nonnegative orthant `ℝ^k_+`, with the sup distance (the same topology and compact sets as
the Euclidean one). -/
def NonnegVec (k : ℕ) : Type := {x : Fin k → ℝ // ∀ i, 0 ≤ x i}

instance (k : ℕ) : PseudoEMetricSpace (NonnegVec k) :=
  inferInstanceAs (PseudoEMetricSpace {x : Fin k → ℝ // ∀ i, 0 ≤ x i})

/-- The vector `((1/n)∑_{j=N(nt₀)+1}^{N(nt₁)} W_j, …, (1/n)∑_{j=N(nt_{k−1})+1}^{N(nt_k)} W_j)` of
Lemmas 3.2–3.3 (pp. 10–12), for times `t : Fin (k+1) → ℝ` with `t 0 = 0` (so the first block starts at
`N(0) + 1 = 1`). -/
noncomputable def blockVec {k : ℕ} (U : ℕ → Ω → ℝ) (p : ℝ) (t : Fin (k + 1) → ℝ) (n : ℕ)
    (ω : Ω) : NonnegVec k :=
  ⟨fun i => (n : ℝ)⁻¹ *
      (∑ j ∈ Finset.Ioc (Ncount (chain U ω) (n * t i.castSucc))
        (Ncount (chain U ω) (n * t i.succ)), W (chain U ω) p j).toReal,
    fun _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) ENNReal.toReal_nonneg⟩

end ReflectedRWLDP.SamplePath


