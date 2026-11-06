-- Prove2me | Definitions.Def_FTPLLinBandit_FTPLRun
-- name    : FTPLLinBandit_FTPLRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:03:46.065571+00:00
-- url     : https://prove2.me/theorems/128ca45b-c3bc-4031-9a50-a4b721297e69
-- title:
--   A run of Algorithm 1 against an adaptive adversary: randomness, adversary, elliptical factor
-- statement:
--   Fix an action set $A$, an exploration distribution $\nu$, an argmax selection $x$, a perturbation scheme, an exploration rate $\gamma$, a resampling step size $\beta$, a truncation $N\in\mathbb N$, a scale $\lambda$ and a probability space $(\Omega,P)$. A **run of Algorithm 1** consists of
--
--   1. a filtration $(\mathcal F_t)_{t\ge0}$, $\mathcal F_t$ being the information before round $t$;
--   2. the adversary's reward vectors $\theta_t$ and intercepts $b_t$, each $\mathcal F_t$-measurable, with $|\langle a,\theta_t\rangle+b_t|\le1$ for all $a\in A$ — the adversary "may depend on the past, but chooses $\theta_t$ and $b_t$ before the learner's random draws at round $t$";
--   3. for every round $t$ and each of the $2N+2$ calls of SampleAction in that round (slot $0$ is $a_t$, slot $1$ is $\bar a_t$, slots $2i+2$, $2i+3$ are the pair $u_{i+1},v_{i+1}$ of GeometricResampling), fresh draws: a coin $U$ uniform on $[0,1]$ (the call explores iff $U<\gamma$), an exploration action $X\sim\nu$, a standard perturbation $W\sim P_I$, and (random weighting) weights $\xi_{t,\tau}\sim\varphi$, $\tau<t$. Within a slot these are independent; the $2N+2$ slots of a round are independent; the round's draws are independent of $\mathcal F_t$ and $\mathcal F_{t+1}$-measurable;
--   4. a measurable map $\Sigma\mapsto B(\Sigma)$ with $B(\Sigma)B(\Sigma)^\top=\Sigma$ for positive definite $\Sigma$, through which the elliptical scheme draws $Z=B(\Sigma_t)W\sim P_{\Sigma_t}$.
--
--   The actions, estimates and regret of the run are the definitions `FTPLRun.slotAction`, `FTPLRun.estimate`, `FTPLRun.thetaHat` and `FTPLRun.regret`.
--
--   **Formalization Note** Rounds are indexed from $0$. $\mathrm{Bernoulli}(\gamma)$ is encoded as $U<\gamma$: the same law for $\gamma\in[0,1]$, and "always explore" for $\gamma\ge1$, so the run is defined for every value of the parameters (20). Any measurable factor $B$ (e.g. $\Sigma^{1/2}$, as on p.9, or a Cholesky factor) gives $BW\sim P_\Sigma$. The adversary may be randomized (any filtration to which it is adapted).
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, §2, p.4; Algorithm 1 and Figure 2, p.8; §4, p.9

import Mathlib
import Definitions.Def_FTPLLinBandit_baseLaw
import Definitions.Def_FTPLLinBandit_weightLaw

open MeasureTheory ProbabilityTheory Matrix
open scoped InnerProductSpace

namespace FTPLLinBandit

/-- **A run of Algorithm 1 against an adaptive adversary: the randomness and the adversary.** Wei,
arXiv:2610.17818, §2, p.4 (setting) and Algorithm 1 with Figure 2, p.8.

Parameters: an action set `A ⊆ ℝ^d`, the exploration distribution `ν`, the oracle's argmax
selection `x`, the perturbation scheme `s` (Figure 2), the exploration rate `γ`, the resampling
step size `β`, the truncation `N`, the scale `λ`, and a probability space `(Ω, P)`. A run consists
of

* a filtration `𝓕` (`𝓕 t` is the information before round `t`);
* the adversary's reward vectors `θ_t` and intercepts `b_t`, each `𝓕 t`-measurable, with
  `|⟨a, θ_t⟩ + b_t| ≤ 1` for every `a ∈ A` ("The adversary may depend on the past, but chooses θ_t
  and b_t before the learner's random draws at round t", p.4);
* for every round `t` and every one of the `2N + 2` calls `j` of `SampleAction` in that round
  (slot `0` is `a_t`, slot `1` is `ā_t`, slots `2i + 2`, `2i + 3` are `u_{i+1}`, `v_{i+1}` of
  `GeometricResampling`), fresh draws: a coin `U` uniform on `[0, 1]` (the call explores iff
  `U < γ`), an exploration action `X ∼ ν`, a standard perturbation `W ∼ P_I` (`baseLaw`), and for
  random weighting the weights `ξ_τ ∼ φ`, `τ < t` (`weightLaw`; "it is crucial that Z′_t and
  {ξ_{t,τ}}_{τ<t} are fresh samples in every round", p.9). The `2N + 2` slot draws of round `t` are
  independent, each has the product law above, they are jointly independent of `𝓕 t`, and they
  are `𝓕 (t + 1)`-measurable;
* a measurable map `sq` with `sq Σ · sq Σᵀ = Σ` for positive definite `Σ`, the factor through
  which the elliptical scheme draws `Z = sq(Σ_t) W ∼ P_{Σ_t}` (§4, p.9: "let Z_t = Σ_t^{1/2} S U").

The learner's actions and estimates are computed from these by `FTPLRun.slotAction`,
`FTPLRun.estimate` and `FTPLRun.thetaHat`.

**Formalization Note.** Rounds are indexed from `0` (round `t` here is the paper's round `t + 1`).
`Bernoulli(γ)` is encoded as `U < γ` with `U` uniform on `[0,1]`: the same law for `γ ∈ [0, 1]`,
and "always explore" for `γ ≥ 1`, so the run is defined for every parameter value of (20). The
adaptive adversary is any `𝓕`-predictable pair `(θ_t, b_t)` (it may also be randomized).
Algorithm 1's `Z ∼ ρ_t` is realised from the standard draw `W`: `Z = √λ W + ∑_{τ<t} ξ_τ θ̂_τ` for
random weighting (`√λ W ∼ P_{λI} = ρ₁`) and `Z = sq(Σ_t) W` for the elliptical scheme (any
measurable factor `sq`, e.g. `Σ^{1/2}` or Cholesky, gives the law `P_{Σ_t}`). The elliptical
scheme's weights have the point-mass law `weightLaw (elliptical f) = δ₀` and are unused. -/
structure FTPLRun {d : ℕ} (A : Set (EuclideanSpace ℝ (Fin d)))
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (s : Scheme) (γ β : ℝ) (N : ℕ)
    (lam : ℝ) (Ω : Type*) [mΩ : MeasurableSpace Ω] (P : Measure Ω) where
  /-- the information before round `t` -/
  𝓕 : Filtration ℕ mΩ
  /-- reward vector `θ_t` of round `t` -/
  θ : ℕ → Ω → EuclideanSpace ℝ (Fin d)
  /-- intercept `b_t` of round `t` -/
  b : ℕ → Ω → ℝ
  θ_meas : ∀ t, Measurable[𝓕 t] (θ t)
  b_meas : ∀ t, Measurable[𝓕 t] (b t)
  reward_bdd : ∀ t ω, ∀ a ∈ A, |⟪a, θ t ω⟫_ℝ + b t ω| ≤ 1
  /-- exploration coin of slot `j` in round `t` -/
  U : ℕ → Fin (2 * N + 2) → Ω → ℝ
  /-- exploration action of slot `j` in round `t` -/
  X : ℕ → Fin (2 * N + 2) → Ω → EuclideanSpace ℝ (Fin d)
  /-- standard perturbation draw of slot `j` in round `t` -/
  W : ℕ → Fin (2 * N + 2) → Ω → EuclideanSpace ℝ (Fin d)
  /-- random weights `ξ_{t,τ}`, `τ < t`, of slot `j` in round `t` -/
  ξ : (t : ℕ) → Fin (2 * N + 2) → Ω → Fin t → ℝ
  draw_meas : ∀ t j, Measurable[𝓕 (t + 1)] (fun ω => (U t j ω, X t j ω, W t j ω, ξ t j ω))
  draw_law : ∀ t j, P.map (fun ω => (U t j ω, X t j ω, W t j ω, ξ t j ω)) =
    (volume.restrict (Set.Icc (0 : ℝ) 1)).prod
      (ν.prod ((baseLaw d s).prod (Measure.pi fun _ : Fin t => weightLaw s)))
  draw_iIndep : ∀ t, iIndepFun (fun j ω => (U t j ω, X t j ω, W t j ω, ξ t j ω)) P
  draw_indep_past : ∀ t, Indep (𝓕 t)
    (⨆ j, MeasurableSpace.comap (fun ω => (U t j ω, X t j ω, W t j ω, ξ t j ω)) inferInstance) P
  /-- the factor `B` with `B Bᵀ = Σ` used by the elliptical scheme -/
  sq : Matrix (Fin d) (Fin d) ℝ → Matrix (Fin d) (Fin d) ℝ
  sq_meas : Measurable fun S : Fin d → Fin d → ℝ => Matrix.of.symm (sq (Matrix.of S))
  sq_spec : ∀ S : Matrix (Fin d) (Fin d) ℝ, S.PosDef → sq S * (sq S)ᵀ = S

end FTPLLinBandit


