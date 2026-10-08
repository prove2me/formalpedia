-- Prove2me | Definitions.Def_JacodTodorov10_LLN_Noise
-- name    : JacodTodorov10_LLN_Noise
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:12.578989+00:00
-- url     : https://prove2.me/theorems/b1defb98-3301-4cfd-958c-e7032c16025e
-- title:
--   §2–§3 — the driving noise: (𝓕ₜ)-Brownian motions, the Poisson random measure, jump integrals, and J1 convergence in probability
-- statement:
--   This file fixes the driving noise of the model of Jacod and Todorov, on a filtered probability space $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},\mathbb P)$ with time $t\in\mathbb R_+=[0,\infty)$ and an auxiliary measurable space $(E,\mathcal E)$ carrying a $\sigma$-finite measure $\lambda$.
--
--   1. **Jumps of a path.** For a process $Y$, $\Delta Y_s = Y_s - Y_{s-}$ is its jump at time $s$, with the convention $Y_{0-}=Y_0$, so $\Delta Y_0 = 0$.
--   2. **Convergence in probability for the Skorokhod topology.** Processes $Y^n$ converge to $Y$ in this sense if every subsequence has a further subsequence along which, almost surely, the paths converge in the Skorokhod ($J_1$) topology on $D[0,\infty)$: all paths are càdlàg, and there are time changes $\lambda_k$ (continuous, strictly increasing, onto) with $Y^{n_k}\circ\lambda_k\to Y$ and $\lambda_k\to\mathrm{id}$ uniformly on bounded intervals.
--   3. **$(\mathcal F_t)$-Brownian motion.** A standard Brownian motion $W$, adapted, whose increments $W_t-W_s$ ($s\le t$) are independent of $\mathcal F_s$. A pair $(W,W')$ consists of two such Brownian motions with jointly independent increments $(W_t-W_s,W'_t-W'_s)$ of $\mathcal F_s$ and independent paths.
--   4. **$(\mathcal F_t)$-Poisson random measure.** $\mu$ is given by its atoms $N(\omega)\subseteq\mathbb R_+\times E$, $\mu(\omega,B)=\#(N(\omega)\cap B)$. It has at most one atom at each time; $\mu(B)$ is a random variable; $\mu([0,t]\times A)$ is $\mathcal F_t$-measurable; $\mathbb E\,\mu(B) = (ds\otimes\lambda)(B)$; and $\mu(B)$ is independent of $\mathcal F_s$ whenever $B\subseteq(s,\infty)\times E$ has finite $ds\otimes\lambda$-measure. So $\mu$ has compensator $\nu(ds,dz)=ds\otimes\lambda(dz)$.
--   5. **Jump integrals.** For a random field $H(\omega,s,z)$, the big-jump sum is
--   $$\int_0^t\!\!\int_E H(s,z)\,1_{\{|H(s,z)|>1\}}\,\mu(ds,dz)=\sum_{(s,z)\in N,\ s\le t,\ |H(s,z)|>1} H(s,z),$$
--   and $J$ is the compensated integral $J_t=\int_0^t\int_E H(s,z)(\mu-\nu)(ds,dz)$ if, for every $t$, the compensated truncated sums
--   $$\sum_{(s,z)\in N,\ s\le t,\ |H(s,z)|>\varepsilon_k} H(s,z)\;-\;\int_0^t\!\!\int_E H(s,z)\,1_{\{|H(s,z)|>\varepsilon_k\}}\,\lambda(dz)\,ds,\qquad \varepsilon_k=\tfrac1{k+1},$$
--   are almost surely finite sums and converge in probability to $J_t$ as $k\to\infty$.
--
--   These objects are the substrate of the representation (2.1) of $X$ and (8.1) of $Z$, of the statistics $U(F)$ and $U(F,k_n)$, and of the mode of convergence of Theorem 3.1.
--
--   **Formalization Note** Paths, càdlàg and Skorokhod convergence are the published `KurtzProtter91.Integrals` definitions. Convergence in probability in the Polish space $D[0,\infty)$ is encoded by the equivalent subsequence criterion, which avoids the $J_1$ metric. No stochastic integral against $\mu-\nu$ exists in Mathlib or on the platform; the Lévy–Itô limit above identifies it, up to null sets for each $t$, for predictable integrands with $\int_0^t\int_E (H^2\wedge|H|)\,d\lambda\,ds<\infty$. Lebesgue measure on $\mathbb R_+$ is the restriction of Lebesgue measure on $\mathbb R$.
-- source:
--   Jacod, Todorov, Do price and volatility jump together?, arXiv:1010.4990v1 (Ann. Appl. Probab. 20 (2010)), §2, p. 3 ((2.1): W, μ, ν = ds ⊗ λ(dz)); §3, p. 4 (ΔY); Theorem 3.1, p. 5 (convergence in probability for the Skorokhod topology); §8.1, p. 24 (W′ in (8.1))

import Mathlib
import Definitions.Def_KurtzProtter91_Integrals_Skorohod

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace JacodTodorov10.LLN

/-- Lebesgue measure on the time axis `ℝ₊ = [0, ∞)`, the pull-back of Lebesgue measure on `ℝ`
(Jacod–Todorov, *Do price and volatility jump together?*, arXiv:1010.4990v1, §2, p. 3: the factor
`ds` of the compensator `ν(ds, dz) = ds ⊗ λ(dz)`). -/
noncomputable def lebPos : Measure ℝ≥0 :=
  (volume : Measure ℝ).comap ((↑) : ℝ≥0 → ℝ)

/-- The jump `ΔY_s(ω) = Y_s(ω) − Y_{s−}(ω)` of a real process at time `s` (arXiv:1010.4990v1, §3,
p. 4: "ΔY_t = Y_t − Y_{t−} is the jump size at time t of any càdlàg process Y"). It is the path-wise
jump of the published `KurtzProtter91.Integrals.jump`; by the convention `Y_{0−} = Y_0` it is `0`
at `s = 0`. -/
noncomputable def pjump {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  KurtzProtter91.Integrals.jump (fun t => Y t ω) s

/-- **Convergence in probability for the Skorokhod (J1) topology** of processes `Y n` to `Yinf`
(arXiv:1010.4990v1, Theorem 3.1, p. 5; (8.27), p. 33), in its subsequence form: every subsequence
has a further subsequence along which the paths converge almost surely in the J1 topology on
`D[0, ∞)` (`KurtzProtter91.Integrals.SkorohodTendsto`: all paths càdlàg, time changes `λ_k` with
`Y ∘ λ_k → Yinf` and `λ_k → id` uniformly on bounded intervals).

Formalization Note: the Skorokhod space is Polish, so for random elements of it convergence in
probability is equivalent to this subsequence criterion; the encoding avoids the J1 metric and the
measurability of path-valued maps. -/
def TendstoInProbJ1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : ℕ → ℝ≥0 → Ω → ℝ)
    (Yinf : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
    ∀ᵐ ω ∂P, KurtzProtter91.Integrals.SkorohodTendsto
      (fun k t => Y (φ (ψ k)) t ω) (fun t => Yinf t ω)

/-- An **`(𝓕_t)`-Brownian motion** (arXiv:1010.4990v1, §2, p. 3, "W is a standard Brownian
motion" on the filtered space): a standard Brownian motion (Mathlib's `IsBrownianReal`), adapted to
`𝓕`, whose increments `W_t − W_s`, `s ≤ t`, are independent of `𝓕_s`. -/
def IsFBrownian {Ω : Type*} [MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ) : Prop :=
  IsBrownianReal W P ∧ Adapted 𝓕 W ∧
    ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance) (𝓕 s) P

/-- The pair `(W, W')` of (8.1) (arXiv:1010.4990v1, §8.1, p. 24: "W′ is another standard Brownian
motion, independent of W"): both are `(𝓕_t)`-Brownian motions, the pair of increments
`(W_t − W_s, W'_t − W'_s)` is independent of `𝓕_s`, and the two paths are independent. -/
def IsFBrownianPair {Ω : Type*} [MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) (W W' : ℝ≥0 → Ω → ℝ) : Prop :=
  IsFBrownian 𝓕 P W ∧ IsFBrownian 𝓕 P W' ∧
    (∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => (W t ω - W s ω, W' t ω - W' s ω)) inferInstance)
        (𝓕 s) P) ∧
    IndepFun (fun ω t => W t ω) (fun ω t => W' t ω) P

/-- The integer-valued random measure `μ(ω, B) = #(N(ω) ∩ B)` with atoms `N(ω) ⊆ ℝ₊ × E`. -/
noncomputable def cnt {Ω E : Type*} (N : Ω → Set (ℝ≥0 × E)) (ω : Ω) (B : Set (ℝ≥0 × E)) :
    ℝ≥0∞ :=
  ((N ω ∩ B).encard : ℝ≥0∞)

/-- An **`(𝓕_t)`-Poisson random measure** `μ` on `[0, ∞) × E` with compensator
`ν(ds, dz) = ds ⊗ λ(dz)` (arXiv:1010.4990v1, §2, p. 3), given by its atoms `N(ω)`
(`μ(ω, B) = #(N(ω) ∩ B)`, see `cnt`). The clauses are (Jacod–Shiryaev II.1.20):
1. at most one atom at each time;
2. `μ(·, B)` is a random variable for every measurable `B`;
3. `μ([0, t] × A)` is `𝓕_t`-measurable (optionality);
4. the intensity is `E μ(B) = (ds ⊗ λ)(B)`;
5. for `B ⊆ (s, ∞) × E` with `(ds ⊗ λ)(B) < ∞`, `μ(B)` is independent of `𝓕_s`.

Together they imply the Poisson law of the counts and the independence over disjoint sets. -/
def IsFPoisson {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω) (lam : Measure E)
    (N : Ω → Set (ℝ≥0 × E)) : Prop :=
  (∀ ω t, {z | (t, z) ∈ N ω}.Subsingleton) ∧
    (∀ B : Set (ℝ≥0 × E), MeasurableSet B → Measurable (fun ω => cnt N ω B)) ∧
    (∀ (t : ℝ≥0) (A : Set E), MeasurableSet A →
      Measurable[𝓕 t] (fun ω => cnt N ω (Set.Icc 0 t ×ˢ A))) ∧
    (∀ B : Set (ℝ≥0 × E), MeasurableSet B → ∫⁻ ω, cnt N ω B ∂P = (lebPos.prod lam) B) ∧
    (∀ (s : ℝ≥0) (B : Set (ℝ≥0 × E)), MeasurableSet B → B ⊆ Set.Ioi s ×ˢ Set.univ →
      (lebPos.prod lam) B < ⊤ →
      Indep (MeasurableSpace.comap (fun ω => cnt N ω B) inferInstance) (𝓕 s) P)

/-- The sum of the big jumps, `∫_0^t ∫_E H(s, z) 1_{|H(s,z)| > 1} μ(ds, dz)` (the last line of
(2.1), arXiv:1010.4990v1, p. 3), as a sum over the atoms `(s, z) ∈ N(ω)` with `s ≤ t` and
`|H(ω, s, z)| > 1`. It is a genuine finite sum when that set is finite (which every
representation asserts almost surely); otherwise `finsum` returns `0`. -/
noncomputable def bigSum {Ω E : Type*} (N : Ω → Set (ℝ≥0 × E)) (H : Ω → ℝ≥0 → E → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ᶠ p ∈ {p : ℝ≥0 × E | p ∈ N ω ∧ p.1 ≤ t ∧ 1 < |H ω p.1 p.2|}, H ω p.1 p.2

/-- The compensated jump sum at level `ε`:
`∑_{(s,z) ∈ N(ω), s ≤ t, |H(s,z)| > ε} H(s, z) − ∫_0^t ∫_E H(s, z) 1_{|H(s,z)| > ε} λ(dz) ds`. -/
noncomputable def compSum {Ω E : Type*} [MeasurableSpace E] (lam : Measure E)
    (N : Ω → Set (ℝ≥0 × E)) (H : Ω → ℝ≥0 → E → ℝ) (ε : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (∑ᶠ p ∈ {p : ℝ≥0 × E | p ∈ N ω ∧ p.1 ≤ t ∧ ε < |H ω p.1 p.2|}, H ω p.1 p.2) -
    ∫ s in (0 : ℝ)..(t : ℝ), ∫ z, (if ε < |H ω s.toNNReal z| then H ω s.toNNReal z else 0) ∂lam

/-- `J` is the **compensated stochastic integral** `J_t = ∫_0^t ∫_E H(s, z)(μ − ν)(ds, dz)`
(the third line of (2.1), arXiv:1010.4990v1, p. 3), in the Lévy–Itô form: for every `t`, the
jumps of size `> ε_k = 1/(k+1)` up to time `t` are a.s. finitely many, and the compensated sums
`compSum lam N H ε_k t` converge in probability to `J_t` as `k → ∞`.

Formalization Note: there is no stochastic integral against `μ − ν` in Mathlib or on the platform.
For a predictable `H` with `∫_0^t ∫_E (H² ∧ |H|) λ(dz) ds < ∞` a.s. this limit exists and is the
stochastic integral, so the relation identifies `J_t` up to null sets, for each `t`. -/
def HasCompInt {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] (P : Measure Ω)
    (lam : Measure E) (N : Ω → Set (ℝ≥0 × E)) (H : Ω → ℝ≥0 → E → ℝ) (J : ℝ≥0 → Ω → ℝ) :
    Prop :=
  ∀ t : ℝ≥0,
    (∀ k : ℕ, ∀ᵐ ω ∂P,
      {p : ℝ≥0 × E | p ∈ N ω ∧ p.1 ≤ t ∧ 1 / ((k : ℝ) + 1) < |H ω p.1 p.2|}.Finite) ∧
    TendstoInMeasure P (fun k ω => compSum lam N H (1 / ((k : ℝ) + 1)) t ω) atTop (J t)

end JacodTodorov10.LLN


