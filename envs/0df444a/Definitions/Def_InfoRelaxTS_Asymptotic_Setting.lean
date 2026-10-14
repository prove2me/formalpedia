-- Prove2me | Definitions.Def_InfoRelaxTS_Asymptotic_Setting
-- name    : InfoRelaxTS_Asymptotic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:38.768982+00:00
-- url     : https://prove2.me/theorems/e462c456-003d-421a-88fd-73d76278bf6d
-- title:
--   §2.1, §2.4, §3.2–§3.3, pp. 4–20 — Bayesian bandit, outcome law ℐ(y) (4), μ, μ̄, μ̂ (9)–(10), 𝒩_T (37), action laws of TS, IRS.FH, IRS.V-Zero
-- statement:
--   This file fixes the Bayesian multi-armed bandit model of Min, Maglaras and Moallemi (§2.1) and the action laws of three randomized policies: Thompson sampling, IRS.FH and IRS.V-Zero.
--
--   **The model.** There are $K$ arms $a \in \mathcal A = \{1,\dots,K\}$. Arm $a$ has an unknown parameter $\theta_a \in \Theta$. Given $\theta_a$, its rewards $R_{a,1}, R_{a,2}, \dots$ are i.i.d. with law $\mathcal R_a(\theta_a)$, a probability measure on $\mathbb R$ (display (1)). Beliefs $y_a \in \mathcal Y$ index a family of prior laws $\mathcal P_a(y_a)$ on $\Theta$ (display (2)). A Bayesian update $\mathcal U_a : \mathcal Y \times \mathbb R \to \mathcal Y$ maps a belief and an observed reward to the new belief.
--
--   1. **Conjugacy.** If $\theta_a \sim \mathcal P_a(y_a)$ and $R_{a,1} \sim \mathcal R_a(\theta_a)$, then $\theta_a \mid R_{a,1} \sim \mathcal P_a(\mathcal U_a(y_a, R_{a,1}))$. Written as Bayes' rule, for every belief $y_a$ and all measurable $A \subseteq \mathbb R$, $B \subseteq \Theta$:
--   $$\int_B \mathcal R_a(\theta)(A)\, \mathcal P_a(y_a)(d\theta) = \int_A \mathcal P_a\big(\mathcal U_a(y_a, r)\big)(B)\; m_{a,y_a}(dr),$$
--   where $m_{a,y_a}$ is the marginal law of $R_{a,1}$, i.e. $\mathcal R_a$ averaged over $\mathcal P_a(y_a)$.
--   2. **Standing integrability (3).** $\mathbb E_{y_a}|R_{a,1}| < \infty$ for every belief $y_a$ and arm $a$.
--
--   **Means.** The conditional mean reward is $\mu_a(\theta_a) = \mathbb E[R_{a,n} \mid \theta_a] = \int r\, \mathcal R_a(\theta_a)(dr)$, and the predictive mean is $\bar\mu_a(y_a) = \mathbb E_{y_a}[\mu_a(\theta_a)]$ (display (9)). The **outcome** is $\omega = (\theta, (R_{a,n})_{a,n})$. Its law $\mathcal I(y)$ (display (4)) makes the arms independent, draws $\theta_a \sim \mathcal P_a(y_a)$, and then draws the rewards of arm $a$ i.i.d. from $\mathcal R_a(\theta_a)$. The belief of arm $a$ after its first $n$ rewards is $y_{a,0} = y_a$, $y_{a,n+1} = \mathcal U_a(y_{a,n}, R_{a,n+1})$ (display (8)). The posterior predictive mean after $n$ rewards is
--   $$\hat\mu_{a,n}(\omega; y_a) = \bar\mu_a(y_{a,n}).$$
--
--   **Allocations.** For a horizon $T$, the feasible allocations are $\mathcal N_T = \{(n_1,\dots,n_K) \in \mathbb N_0^K : \sum_a n_a = T\}$. For a payoff table $m_{a,i}$, the allocation $n$ earns $\sum_{a=1}^K \sum_{i=1}^{n_a} m_{a,i-1}$; this is the inner problem (37) of IRS.V-Zero with $m_{a,i} = \hat\mu_{a,i}$.
--
--   **Tie-breaking rules.** An *argmax selector* maps each vector $f \in \mathbb R^K$ to an arm maximizing $f$. An *optimal-allocation selector* maps each horizon $T$ and payoff table to an allocation in $\mathcal N_T$ of maximal payoff.
--
--   **Action laws.** Each policy samples its own outcome and returns one arm. The law of that arm is a probability measure on $\mathcal A$.
--   1. **Thompson sampling** (Algorithm 2): sample $\tilde\theta \sim \mathcal P(y) = \bigotimes_a \mathcal P_a(y_a)$ and play $\operatorname{argmax}_a \mu_a(\tilde\theta_a)$. The law of the arm is $\mathbb P[A^{TS}(y) = \cdot\,]$.
--   2. **IRS.FH** (Algorithm 4): sample $\tilde\omega \sim \mathcal I(y)$ and play $\operatorname{argmax}_a \hat\mu_{a,T-1}(\tilde\omega)$. The law of the arm is $\mathbb P[A^{IRS.FH}(T, y) = \cdot\,]$.
--   3. **IRS.V-Zero** (§3.3 and footnote 8): sample $\tilde\omega \sim \mathcal I(y)$, compute an optimal allocation $\tilde n^*$ of (37) for $\tilde\omega$, and play $\operatorname{argmax}_a \tilde n^*_a$. The law of the arm is $\mathbb P[A^{IRS.V\text{-}Zero}(T, y) = \cdot\,]$.
--
--   Every argmax is taken by a given selector.
--
--   These objects are what Proposition 1 of the paper compares: the action laws of IRS.FH and IRS.V-Zero, as the horizon grows, against that of Thompson sampling.
--
--   **Formalization Note.** Arms are `Fin K`, 0-based (the paper's arm $a$ is index $a-1$), and the reward sequence of an arm is `ℕ → ℝ`, 0-based (the paper's $R_{a,n}$ is index $n-1$). One parameter type $\Theta$ and one belief type $\mathcal Y$ serve all arms; they stand for the disjoint unions of the paper's $\Theta_a$ and $\mathcal Y_a$. The paper defines $\hat\mu_{a,n}$ in (10) as the conditional expectation $\mathbb E_{y_a}[\mu_a(\theta_a) \mid R_{a,1},\dots,R_{a,n}]$. Here it is the pathwise conjugate-prior version $\bar\mu_a(y_{a,n})$, which is a version of that conditional expectation under conjugacy and is defined at every outcome, so it can sit inside an argmax. Conjugacy and (3) are recorded as the predicates `IsConjugate` and `RewardsIntegrable`; the theorems take them as hypotheses. Selectors are functions of the vector (or of the payoff table) they maximize. At $T = 0$ the IRS.FH law uses $\hat\mu_{\cdot,0}$ ($T - 1$ is truncated subtraction in `ℕ`); this does not affect any limit in $T$. The objects $\mu_a$, $\bar\mu_a$ are taken from the shared module `InfoRelaxTS.Monotone.Setting` (`Monotone.mu`, `Monotone.muBar`), and the argmax selector, the allocation set $\mathcal N_T$, the payoff of (37) and the optimal-allocation selector from `InfoRelaxTS.Gap.Setting` (`Gap.IsArgmaxSel`, `Gap.allocSet`, `Gap.allocPayoff`, `Gap.IsOptAllocSel`); their definitions are the ones described above.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, pp. 4–6 (1)–(10); p. 9, Algorithm 2; pp. 17–18, (31), Algorithm 4; p. 20, (37) and the selection rule of IRS.V-Zero; p. 25, footnote 8

import Mathlib
import Definitions.Def_InfoRelaxTS_Gap_Setting
import Definitions.Def_InfoRelaxTS_Monotone_Setting

namespace InfoRelaxTS.Asymptotic

open MeasureTheory ProbabilityTheory

/-! Min–Maglaras–Moallemi, *Thompson Sampling with Information Relaxation Penalties*,
arXiv:1902.04251v2, §2.1 (pp. 4–6), §2.4 (pp. 8–9), §3.2–§3.3 (pp. 17–20).

Arms are `Fin K` (the paper's arm `a` is index `a - 1`). One parameter type `Θ` serves every arm
(the disjoint union of the paper's `Θ_a`), one belief type `Y` (the union of the `𝒴_a`).
`R a : Kernel Θ ℝ` is the reward law `𝓡_a(θ_a)` of (1), `P a : Kernel Y Θ` the conjugate prior
family `𝒫_a(y_a)` of (2), `U a : Y → ℝ → Y` the Bayesian update `𝒰_a`. The reward sequence of an
arm is `ℕ → ℝ`, 0-based: the paper's `R_{a,n}` is index `n - 1`. -/

variable {K : ℕ} {Θ Y : Type*} [MeasurableSpace Θ] [MeasurableSpace Y]

/-- An outcome `ω = (θ, (R_{a,n}))` of (4): for each arm its parameter and its reward sequence. -/
abbrev Outcome (K : ℕ) (Θ : Type*) := Fin K → Θ × (ℕ → ℝ)

/-- Conjugacy of `(P, U)` for the reward kernels `R` (p. 5): if `θ_a ∼ 𝒫_a(y_a)` and
`R_{a,1} ∼ 𝓡_a(θ_a)`, then `θ_a ∣ R_{a,1} ∼ 𝒫_a(𝒰_a(y_a, R_{a,1}))`. Stated as Bayes' rule on
rectangles: `ℙ[θ_a ∈ B, R_{a,1} ∈ A] = ∫_A 𝒫_a(𝒰_a(y_a, r))(B) dm(r)`, where `m` is the marginal
law of `R_{a,1}`; this holds for every belief `y_a`. -/
def IsConjugate (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ) (U : Fin K → Y → ℝ → Y) :
    Prop :=
  ∀ (a : Fin K) (ya : Y) (A : Set ℝ) (B : Set Θ), MeasurableSet A → MeasurableSet B →
    ∫⁻ θ in B, R a θ A ∂(P a ya) = ∫⁻ r in A, P a (U a ya r) B ∂((R a) ∘ₘ (P a ya))

/-- Standing assumption (3): `𝔼_{y_a}|R_{a,1}| < ∞` for every belief `y_a` and arm `a`. -/
def RewardsIntegrable (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ) : Prop :=
  ∀ (a : Fin K) (ya : Y), Integrable (fun r : ℝ => r) ((R a) ∘ₘ (P a ya))

/-- The belief of arm `a` after its first `n` rewards (8): `yseq … a ω 0 = y_a` and
`yseq … a ω (n+1) = 𝒰_a(yseq … a ω n, R_{a,n+1})`. -/
def yseq (U : Fin K → Y → ℝ → Y) (y : Fin K → Y) (a : Fin K) (ω : Outcome K Θ) : ℕ → Y
  | 0 => y a
  | n + 1 => U a (yseq U y a ω n) ((ω a).2 n)

/-- The posterior predictive mean `μ̂_{a,n}(ω; y_a)` of (10), in its conjugate-prior (pathwise)
form: the predictive mean of the belief after the first `n` rewards of arm `a`. -/
noncomputable def muHat (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ) (U : Fin K → Y → ℝ → Y)
    (y : Fin K → Y) (a : Fin K) (n : ℕ) (ω : Outcome K Θ) : ℝ :=
  InfoRelaxTS.Monotone.muBar R P a (yseq U y a ω n)

/-- The prior law `𝒫(y) = ⊗_a 𝒫_a(y_a)` of the parameter vector `θ` (2). -/
noncomputable def priorLaw (P : Fin K → Kernel Y Θ) (y : Fin K → Y) : Measure (Fin K → Θ) :=
  Measure.pi fun a => P a (y a)

/-- The outcome law `ℐ(y)` of (4): arms independent, `θ_a ∼ 𝒫_a(y_a)`, and given `θ_a` the
rewards `R_{a,1}, R_{a,2}, …` i.i.d. with law `𝓡_a(θ_a)`. -/
noncomputable def I (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ) (y : Fin K → Y) :
    Measure (Outcome K Θ) :=
  Measure.pi fun a =>
    (P a (y a)).bind fun θ => (Measure.dirac θ).prod (Measure.infinitePi fun _ : ℕ => R a θ)

/-- Law of the action `A^TS(y)` of Thompson sampling (Algorithm 2): sample `θ̃ ∼ 𝒫(y)` and play
`argmax_a μ_a(θ̃_a)`, ties broken by `sel`. -/
noncomputable def tsLaw (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ)
    (sel : (Fin K → ℝ) → Fin K) (y : Fin K → Y) : Measure (Fin K) :=
  (priorLaw P y).map fun θ => sel fun a => InfoRelaxTS.Monotone.mu R a (θ a)

/-- Law of the action `A^{IRS.FH}(T, y)` (Algorithm 4): sample `ω̃ ∼ ℐ(y)` and play
`argmax_a μ̂_{a,T-1}(ω̃)`, ties broken by `sel`. (At `T = 0`, `T - 1 = 0` in `ℕ`.) -/
noncomputable def fhLaw (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ)
    (U : Fin K → Y → ℝ → Y) (sel : (Fin K → ℝ) → Fin K) (T : ℕ) (y : Fin K → Y) :
    Measure (Fin K) :=
  (I R P y).map fun ω => sel fun a => muHat R P U y a (T - 1) ω

/-- Law of the action `A^{IRS.V-Zero}(T, y)` (§3.3, footnote 8 on p. 25): sample `ω̃ ∼ ℐ(y)`,
take the optimal allocation `ñ* = asel T (μ̂(ω̃))` of (37), and play `argmax_a ñ*_a`, ties broken
by `sel`. -/
noncomputable def vzLaw (R : Fin K → Kernel Θ ℝ) (P : Fin K → Kernel Y Θ)
    (U : Fin K → Y → ℝ → Y) (asel : ℕ → (Fin K → ℕ → ℝ) → (Fin K → ℕ))
    (sel : (Fin K → ℝ) → Fin K) (T : ℕ) (y : Fin K → Y) : Measure (Fin K) :=
  (I R P y).map fun ω => sel fun a => ((asel T (fun b i => muHat R P U y b i ω) a : ℕ) : ℝ)

end InfoRelaxTS.Asymptotic


