-- Prove2me | Definitions.Def_StationaryBwK_Model
-- name    : StationaryBwK_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:07.790862+00:00
-- url     : https://prove2.me/theorems/381ae32b-7d58-4e8d-8897-7a04ad3e51fa
-- title:
--   Adaptive BwK model: environment, player, $r_t(a)$, $c_{t,i}(a)$, $(\sigma_r,\sigma_c)$-stationarity, random $\mathrm{OPT}_{FD}$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $(\mathcal H_t)_{t\ge0}$ a filtration: $\mathcal H_t$ is the information after round $t$. This definition fixes the Bandits with Knapsacks model against an adaptive adversary.
--
--   1. **Environment.** In every round $t\in[T]$ the adversary's rewards $R_t(a)$ and consumptions $C_{t,i}(a)$ lie in $[0,1]$ and are $\mathcal H_t$-measurable, and a null action $a_0$ has reward $0$ and consumption $0$ of every resource. Their law may depend arbitrarily on the past.
--   2. **Conditional means.** $r_t(a)=\mathbb E[R_t(a)\mid\mathcal H_{t-1}]$ and $c_{t,i}(a)=\mathbb E[C_{t,i}(a)\mid\mathcal H_{t-1}]$.
--   3. **Player.** The played action $A_t\in[K]$ and the choice $I_t\in[d]\cup\{0\}$ of the minimizing subroutine are $\mathcal H_t$-measurable, and they are made without knowledge of round $t$: for every $a$ and $i$,
--   $$\mathbb E[R_t(a)\mid\mathcal H_{t-1}\vee\sigma(A_t,I_t)]=\mathbb E[R_t(a)\mid\mathcal H_{t-1}],\qquad \mathbb E[C_{t,i}(a)\mid\mathcal H_{t-1}\vee\sigma(A_t,I_t)]=\mathbb E[C_{t,i}(a)\mid\mathcal H_{t-1}]$$
--   almost surely.
--   4. **Stationarity (Definition 3.1).** The adversary is $(\sigma_r,\sigma_c)$-stationary if almost surely, for every action $a$ and resource $i$, $\min_t r_t(a)\ge\sigma_r\max_t r_t(a)$ and $\min_t c_{t,i}(a)\ge\sigma_c\max_t c_{t,i}(a)$, with $t$ ranging over $[T]$.
--   5. **Random benchmark.** $\mathrm{OPT}_{FD}(\omega)$ is the benchmark (1) evaluated with $r_t(a)(\omega)$ and $c_{t,i}(a)(\omega)$.
--
--   These are the standing objects of every probabilistic statement of the mission, including the goal, Theorem 5.2.
--
--   **Formalization Note** $\Omega$ is arbitrary (not assumed finite or countable). The paper's history $H_t$ lists the actions and the realized rewards and consumptions; here any filtration to which $R,C,A,I$ are adapted is allowed, which includes the history enlarged by $I_t$. "Without any knowledge of the reward or consumptions of that round or their distribution" is encoded as the conditional mean independence in item 3. Conditional expectations are Mathlib's versions.
-- source:
--   G. Fikioris and É. Tardos, Approximately Stationary Bandits with Knapsacks, arXiv:2302.14686v2 [cs.LG] (preprint, 8 Jul 2023), https://arxiv.org/abs/2302.14686v2, §2, pp.5–6 (model, history, r_t(a), c_t,i(a)); §3, Definition 3.1, p.6; §4, p.7 (OPT_FD depends on the realization), p.8 (choices made without knowledge of round t)

import Mathlib
import Definitions.Def_StationaryBwK_Benchmark
import Definitions.Def_StationaryBwK_StationarySeq

open MeasureTheory

namespace StationaryBwK

/-! # The probabilistic model of Bandits with Knapsacks against an adaptive adversary

Fikioris & Tardos, *Approximately Stationary Bandits with Knapsacks*, arXiv:2302.14686v2,
§2, pp.5–6 (the model, the history, `r_t(a)`, `c_{t,i}(a)`), §3, Definition 3.1, p.6
(`(σr, σc)`-stationarity), §4, display (1), p.7 (`OPT_FD` as a random variable), and §4, p.8
(the player's choices `A_t, I_t` of Algorithm 1).

**Formalization Note.**
* `Ω` is an arbitrary measurable space with a probability measure `μ`; nothing is assumed about it
  (not finite, countable or standard Borel). `ℋ : Filtration ℕ _` is the history: `ℋ t` is the
  information after round `t`, and `ℋ 0` the information before round 1.
* Rounds are `t = 1, …, T`; `R t ω a = R_t(a)`, `C t ω i a = C_{t,i}(a)`, the played action
  `A t ω : Fin K` and `Alg_min`'s choice `I t ω : Option (Fin d)` (`none` is the paper's `i = 0`).
* The paper's history `H_t` contains the actions and the realized rewards and consumptions up to
  round `t`. Here `ℋ` is any filtration to which `R, C, A, I` are adapted; this includes `I`, which
  the martingale of p.16 needs.
* "Without any knowledge of the reward or consumptions of that round or their distribution"
  (pp.6, 8) is encoded as conditional mean independence: given `ℋ (t−1)` and the round-`t`
  choices `(A_t, I_t)`, the conditional expectation of `R_t(a)` and `C_{t,i}(a)` is the one
  given `ℋ (t−1)` alone.
* `r_t(a) = E[R_t(a) | H_{t−1}]` and `c_{t,i}(a) = E[C_{t,i}(a) | H_{t−1}]` are Mathlib conditional
  expectations, i.e. fixed versions; statements about them hold almost surely. -/

variable {Ω : Type*} [m0 : MeasurableSpace Ω]

/-- The conditional expected reward `r_t(a) = E[R_t(a) | H_{t−1}]` (p.6), as a function of the
outcome. -/
noncomputable def rCond {K : ℕ} (μ : Measure Ω) (ℋ : Filtration ℕ m0)
    (R : ℕ → Ω → Fin K → ℝ) (t : ℕ) (a : Fin K) : Ω → ℝ :=
  μ[fun ω => R t ω a | ℋ (t - 1)]

/-- The conditional expected consumption `c_{t,i}(a) = E[C_{t,i}(a) | H_{t−1}]` (p.6). -/
noncomputable def cCond {d K : ℕ} (μ : Measure Ω) (ℋ : Filtration ℕ m0)
    (C : ℕ → Ω → Fin d → Fin K → ℝ) (t : ℕ) (i : Fin d) (a : Fin K) : Ω → ℝ :=
  μ[fun ω => C t ω i a | ℋ (t - 1)]

/-- The environment chosen by an (adaptive) adversary (§2, pp.5–6): in every round `t ∈ [T]` the
rewards `R_t(a)` and consumptions `C_{t,i}(a)` lie in `[0, 1]`, the null action `a₀` has reward `0`
and consumption `0` of every resource, and `R_t, C_t` are known after round `t`
(`ℋ t`-measurable). Nothing restricts how their law depends on the past: the adversary is
adaptive. -/
def IsBwKEnvironment {d K : ℕ} (ℋ : Filtration ℕ m0) (T : ℕ) (a₀ : Fin K)
    (R : ℕ → Ω → Fin K → ℝ) (C : ℕ → Ω → Fin d → Fin K → ℝ) : Prop :=
  (∀ t ∈ Finset.Icc 1 T, ∀ ω a, R t ω a ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ ω i a, C t ω i a ∈ Set.Icc (0 : ℝ) 1) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ ω, R t ω a₀ = 0) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ ω i, C t ω i a₀ = 0) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ a, Measurable[ℋ t] (fun ω => R t ω a)) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ i a, Measurable[ℋ t] (fun ω => C t ω i a))

/-- The σ-algebra generated by the round-`t` choices `(A_t, I_t)`. -/
@[instance_reducible]
def choiceSigma {d K : ℕ} (A : ℕ → Ω → Fin K) (I : ℕ → Ω → Option (Fin d)) (t : ℕ) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap (A t) ⊤ ⊔ MeasurableSpace.comap (I t) ⊤

/-- The player's choices in Algorithm 1 (p.8): in every round `t ∈ [T]` the action `A_t` and
`Alg_min`'s choice `I_t` are known after round `t` (`ℋ t`-measurable, possibly randomized), and
they are made "without any knowledge of the reward or consumptions of that round or their
distribution" (pp.6, 8): conditioning additionally on `(A_t, I_t)` does not change the
conditional expectation of `R_t(a)` or `C_{t,i}(a)` given `ℋ (t−1)`. -/
def IsBwKPlayer {d K : ℕ} (μ : Measure Ω) (ℋ : Filtration ℕ m0) (T : ℕ)
    (R : ℕ → Ω → Fin K → ℝ) (C : ℕ → Ω → Fin d → Fin K → ℝ)
    (A : ℕ → Ω → Fin K) (I : ℕ → Ω → Option (Fin d)) : Prop :=
  (∀ t ∈ Finset.Icc 1 T, choiceSigma A I t ≤ ℋ t) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ a,
    μ[fun ω => R t ω a | ℋ (t - 1) ⊔ choiceSigma A I t] =ᵐ[μ] μ[fun ω => R t ω a | ℋ (t - 1)]) ∧
  (∀ t ∈ Finset.Icc 1 T, ∀ i a,
    μ[fun ω => C t ω i a | ℋ (t - 1) ⊔ choiceSigma A I t] =ᵐ[μ] μ[fun ω => C t ω i a | ℋ (t - 1)])

/-- Definition 3.1, p.6: the adversary is `(σr, σc)`-stationary if for every action `a`, resource
`i` and history `H_T`, `min_t r_t(a) ≥ σr max_t r_t(a)` and `min_t c_{t,i}(a) ≥ σc max_t c_{t,i}(a)`,
with `t` ranging over `[T]`.

**Formalization Note.** "For any history `H_T`" is "for almost every outcome", since `r` and `c`
are conditional expectations. -/
def IsStationaryAdversary {d K : ℕ} (μ : Measure Ω) (ℋ : Filtration ℕ m0) (T : ℕ)
    (σr σc : ℝ) (R : ℕ → Ω → Fin K → ℝ) (C : ℕ → Ω → Fin d → Fin K → ℝ) : Prop :=
  ∀ᵐ ω ∂μ, ∀ a : Fin K,
    IsStationarySeq σr T (fun t => rCond μ ℋ R t a ω) ∧
    ∀ i : Fin d, IsStationarySeq σc T (fun t => cCond μ ℋ C t i a ω)

/-- `OPT_FD` as a random variable (p.7): display (1) evaluated with the conditional expectations
`r_t(a)`, `c_{t,i}(a)` of the realized history. -/
noncomputable def optFDRand {d K : ℕ} (μ : Measure Ω) (ℋ : Filtration ℕ m0) (T : ℕ) (B : ℝ)
    (R : ℕ → Ω → Fin K → ℝ) (C : ℕ → Ω → Fin d → Fin K → ℝ) (ω : Ω) : ℝ :=
  optFD T B (fun t a => rCond μ ℋ R t a ω) (fun t i a => cCond μ ℋ C t i a ω)

end StationaryBwK


