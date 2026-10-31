-- Prove2me | Definitions.Def_FairExplore_KArmed
-- name    : FairExplore_KArmed
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:38.674418+00:00
-- url     : https://prove2.me/theorems/42dc4ee7-96f9-4ab9-9bfb-9db2e54dd918
-- title:
--   Grouped $K$-armed bandit: gaps, $J^g(a)$, $\mathcal A_{\mathrm{sub}}$, consistency, the KL-UCB index and the single-group instance $\mathcal I_g$
-- statement:
--   The objects of the **grouped $K$-armed bandit** (§2.4.1) for a parameter $\theta$ and action sets $(\mathcal A^g)_{g\in G}$.
--
--   1. **Parameter class.** $\theta\in(0,1)^K$ with $\theta(a)\neq\theta(a')$ for $a\ne a'$; rewards $Y_1(a)\sim\mathrm{Normal}(\theta(a),1)$.
--   2. **Gaps and constants.** $\mathrm{OPT}(g)=\max_{a\in\mathcal A^g}\theta(a)$, $\Delta^g(a)=\mathrm{OPT}(g)-\theta(a)$, $\mathrm{KL}(\alpha,\beta)=(\alpha-\beta)^2/2$, $J^g(a)=1/\mathrm{KL}(\theta(a),\mathrm{OPT}(g))$.
--   3. **Sets.** $\mathcal A^g_{\mathrm{sub}}=\{a\in\mathcal A^g:\theta(a)<\mathrm{OPT}(g)\}$, $G_a=\{g: a\in\mathcal A^g\}$, $\mathcal A_{\mathrm{sub}}=\{a: a\in\mathcal A^g_{\mathrm{sub}}\ \forall g\in G_a\}$, $J(a)=\max_{g\in G_a}J^g(a)$, and $\mathrm{OPT}(\Gamma(a))=\min_{g\in G_a}\mathrm{OPT}(g)$.
--   4. **Consistency.** A policy is *consistent* ($\pi\in\Psi$) if $R_T(\pi,\mathcal I)=o(T^b)$ for every instance and every $b>0$; it is *log-consistent* (Definition 2) if $\mathbb E\big[\sum_{a\in\mathcal A^g_{\mathrm{sub}}}N^g_T(a)\big]=O(\log T)$ for every instance and every group.
--   5. **KL-UCB index** (6) = (16): with $f(t)=\log t+3\log\log t$,
--   $$\mathrm{UCB}_t(a)=\max\{q:\ N_t(a)\,\mathrm{KL}(\hat\theta_t(a),q)\le f(t)\}.$$
--   6. **Single-group instance $\mathcal I_g$** (§2.3): the arms are $\mathcal A\cup\{a_0\}$ with a null action $a_0$ of mean $0$ that pays no reward; group $g$ keeps $\mathcal A^g$, every other group can only pull $a_0$; consistency for instances of this type is defined as in 4.
--
--   These are the quantities in which program (13), PF-UCB and every milestone are written.
--
--   **Formalization Note** The instances of a class share the known structure $(G,p,\mathcal A^g)$ and differ in $\theta$ (p.6: all quantities except $\theta$ are known to the policy). $O(\log T)$ is $\exists C,T_0,\ \forall T\ge T_0$. $J^g(a)$ at an optimal arm is the paper's $1/0$ and Lean's $0$; it is always multiplied by $\Delta^g(a)=0$ or not used. $\mathrm{OPT}(g)$, $J(a)$ and $\mathrm{OPT}(\Gamma(a))$ are $0$ on an empty index set, which the theorems exclude. The level is $f(t)$ for $t\ge3$ and $f(1)=f(2)=f(3)$ (the convention of the published `CappeKLUCB_ExpFam_Setting`); the UCB of an unpulled arm is $+\infty$ (every $q$ satisfies the constraint). The null action's reward law is the point mass at $0$. The printed "$\mathcal A\cap\{a_0\}$" is read as $\mathcal A\cup\{a_0\}$.
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, §2.3, p.8; §2.4.1, p.9 ((5), (6)); p.7 (Ψ); proof of Theorem 1, p.11 (sets); App. B, (16), p.31; Definition 2, p.32

import Mathlib
import Definitions.Def_FairExplore_GroupedBandit

open MeasureTheory ProbabilityTheory Filter Topology

namespace FairExplore

variable {γ α : Type*}

/-- The parameter class of the grouped K-armed bandit (§2.4.1, p.9): "Assume θ ∈ (0,1)^K … We
assume that θ(a) ≠ θ(a′) for all a ≠ a′." -/
def InKClass (θ : α → ℝ) : Prop :=
  (∀ a, θ a ∈ Set.Ioo (0 : ℝ) 1) ∧ Function.Injective θ

/-- The reward laws of the grouped K-armed bandit: `Y_1(a) ∼ Normal(θ(a), 1)` (p.9). -/
noncomputable def gaussLaw (θ : α → ℝ) : α → Measure ℝ :=
  fun a => gaussianReal (θ a) 1

instance (θ : α → ℝ) (a : α) : IsProbabilityMeasure (gaussLaw θ a) := by
  unfold gaussLaw; infer_instance

/-- `KL(α, β) = (α − β)²/2`, the Kullback–Leibler divergence between two unit-variance normal laws
(p.9). -/
noncomputable def klGauss (x y : ℝ) : ℝ := (x - y) ^ 2 / 2

/-- `∆^g(a) = OPT(g) − θ(a)` (p.9). -/
noncomputable def gap (A : γ → Finset α) (θ : α → ℝ) (g : γ) (a : α) : ℝ :=
  opt A θ g - θ a

/-- `J^g(a) = 1/KL(θ(a), OPT(g))` (p.9).

**Formalization Note** For an arm optimal for `g` the paper's value is `1/0`; Lean's `1/0 = 0`.
Every use multiplies it by `∆^g(a) = 0` or restricts to suboptimal arms. -/
noncomputable def Jg (A : γ → Finset α) (θ : α → ℝ) (g : γ) (a : α) : ℝ :=
  1 / klGauss (θ a) (opt A θ g)

/-- `A^g_sub = {a ∈ A^g : θ(a) < OPT(g)}`, the suboptimal arms of group `g` (p.11). -/
noncomputable def subG (A : γ → Finset α) (θ : α → ℝ) (g : γ) : Finset α :=
  (A g).filter fun a => θ a < opt A θ g

/-- `G_a ⊆ G`: the groups connected to arm `a` (p.9). -/
def groupsOf [Fintype γ] [DecidableEq α] (A : γ → Finset α) (a : α) : Finset γ :=
  Finset.univ.filter fun g => a ∈ A g

/-- `A_sub = {a ∈ A : a ∈ A^g_sub ∀ g ∈ G_a}`, the arms optimal for no group (p.11). -/
noncomputable def subAll [Fintype γ] [Fintype α] [DecidableEq α] (A : γ → Finset α)
    (θ : α → ℝ) : Finset α :=
  Finset.univ.filter fun a => ∀ g ∈ groupsOf A a, a ∈ subG A θ g

/-- `J(a) = max_{g ∈ G_a} J^g(a)` (p.11); `0` if `G_a = ∅` (a case the theorems exclude). -/
noncomputable def Jmax [Fintype γ] [DecidableEq α] (A : γ → Finset α) (θ : α → ℝ) (a : α) : ℝ :=
  if h : (groupsOf A a).Nonempty then (groupsOf A a).sup' h (fun g => Jg A θ g a) else 0

/-- `OPT(Γ(a)) = min_{g ∈ G_a} OPT(g)`, where `Γ(a) = argmin_{g ∈ G_a} OPT(g)` (p.11, p.34); `0`
if `G_a = ∅` (a case the theorems exclude). -/
noncomputable def optGamma [Fintype γ] [DecidableEq α] (A : γ → Finset α) (θ : α → ℝ)
    (a : α) : ℝ :=
  if h : (groupsOf A a).Nonempty then (groupsOf A a).inf' h (opt A θ) else 0

variable [Fintype γ] [MeasurableSpace γ] [DecidableEq γ] [DecidableEq α]

/-- The group regret `R^g_T(π, I)` in the grouped K-armed bandit with parameter `θ` (p.6, p.9). -/
noncomputable def groupRegretK (S : GroupedStructure γ α) (θ : α → ℝ) (π : Policy γ α) (T : ℕ)
    (g : γ) : ℝ :=
  groupRegret S (gaussLaw θ) θ π T g

/-- The total regret `R_T(π, I)` in the grouped K-armed bandit with parameter `θ` (p.6, (5)). -/
noncomputable def regretK (S : GroupedStructure γ α) (θ : α → ℝ) (π : Policy γ α) (T : ℕ) : ℝ :=
  regret S (gaussLaw θ) θ π T

/-- `E[N_T(a)]`: the expected number of pulls of arm `a` in paper times `1, …, T` in the grouped
K-armed bandit with parameter `θ` (as a `∫⁻` of a count, finite since it is at most `T`). -/
noncomputable def expPulls (S : GroupedStructure γ α) (θ : α → ℝ) (π : Policy γ α) (T : ℕ)
    (a : α) : ℝ :=
  (∫⁻ ω, (N π ω T a : ENNReal) ∂(law S (gaussLaw θ))).toReal

/-- Consistent policies `Ψ` for the grouped K-armed bandits with known structure `S` (p.7):
`R_T(π, I) = o(T^b)` for every instance `I` of the class and every `b > 0`.

**Formalization Note** The class `𝓘` is every parameter `θ ∈ (0,1)^K` with distinct entries, the
known structure `S` being fixed (p.6: all quantities except `θ` are known to the policy). -/
def IsConsistent (S : GroupedStructure γ α) (π : Policy γ α) : Prop :=
  ∀ θ : α → ℝ, InKClass θ → ∀ b : ℝ, 0 < b →
    Tendsto (fun T : ℕ => regretK S θ π T / (T : ℝ) ^ b) atTop (𝓝 0)

/-- Log-consistent policies (Definition 2, p.32): for every instance and every group `g`,
`E[∑_{a ∈ A_sub(g)} N^g_T(a)] = O(log T)`, where `A_sub(g) = A^g_sub`.

**Formalization Note** `O(log T)` is `∃ C T₀, ∀ T ≥ T₀, … ≤ C log T` (App. B.1, p.31: the constant
may depend on the instance). The instances range over the parameters `θ` of the K-armed class for
the known structure `S` (the reading used for `Ψ` as well). -/
def IsLogConsistent [Fintype α] (S : GroupedStructure γ α) (π : Policy γ α) : Prop :=
  ∀ θ : α → ℝ, InKClass θ → ∀ g : γ, ∃ C T₀ : ℝ, ∀ T : ℕ, T₀ ≤ T →
    (∫⁻ ω, ∑ a ∈ subG S.A θ g, (gN π ω T g a : ENNReal) ∂(law S (gaussLaw θ))).toReal
      ≤ C * Real.log T

/-- The exploration level `f(t) = log t + 3 log log t` of the UCB (6) = (16) (p.9, p.31), for paper
time `t ≥ 3`, and `f(1) = f(2) = f(3)`.

**Formalization Note** `log log t` is undefined at `t = 1` and negative at `t = 2`; the small-`t`
convention is that of the published `CappeKLUCB_ExpFam_Setting`. The value at `t = 0` is never
used. -/
noncomputable def fexp (t : ℕ) : ℝ :=
  if t ≤ 3 then Real.log 3 + 3 * Real.log (Real.log 3)
  else Real.log t + 3 * Real.log (Real.log t)

/-- The KL-UCB index (6) = (16) (p.9, p.31) for an empirical mean `m`, a pull count `n` and a level
`f`: `max {q : n · KL(m, q) ≤ f}`, and `⊤` when `n = 0` (then every `q` qualifies). -/
noncomputable def ucbIdx (m : ℝ) (n : ℕ) (f : ℝ) : EReal :=
  if n = 0 then ⊤ else ((sSup {q : ℝ | (n : ℝ) * klGauss m q ≤ f} : ℝ) : EReal)

/-- `UCB_t(a)` (16) computed from the history of the first `t` steps, i.e. at paper time `t + 1`:
`max {q : N_{t+1}(a) KL(θ̂_{t+1}(a), q) ≤ log(t+1) + 3 log log(t+1)}`. -/
noncomputable def History.ucb {t : ℕ} (h : History γ α t) (a : α) : EReal :=
  ucbIdx (h.mean a) (h.count a) (fexp (t + 1))

/-! ### The single-group instance `I_g` of §2.3 -/

/-- The single-group structure `I_g` (§2.3, p.8): the arm set is `A ∪ {a₀}` (printed `A ∩ {a₀}`,
a typo), with `none` the null action `a₀`; group `g` keeps its arms `A^g`, every other group has
only `{a₀}` available; same groups and arrival probabilities. -/
def single (S : GroupedStructure γ α) (g : γ) : GroupedStructure γ (Option α) where
  A h := if h = g then (S.A g).map Function.Embedding.some else {none}
  p := S.p
  p_nonneg := S.p_nonneg
  p_sum := S.p_sum

/-- The means of `I_g`: `µ(a₀) = 0` and `θ(a)` for the real arms (p.8). -/
def extendNull (θ : α → ℝ) : Option α → ℝ :=
  fun o => o.elim 0 θ

/-- The reward laws of `I_g`: the null action pays no reward ("we receive no reward under any
action", p.8), the real arms are `Normal(θ(a), 1)`. -/
noncomputable def nullLaw (θ : α → ℝ) : Option α → Measure ℝ :=
  fun o => o.elim (Measure.dirac 0) (fun a => gaussianReal (θ a) 1)

instance (θ : α → ℝ) (o : Option α) : IsProbabilityMeasure (nullLaw θ o) := by
  cases o <;> (unfold nullLaw; simp only [Option.elim]; infer_instance)

/-- `R_T(π′, I_g)`: the total regret of a policy for instances of type `I_g` on `I_g(θ)`. -/
noncomputable def regretNull (S : GroupedStructure γ α) (θ : α → ℝ) (g : γ)
    (π : Policy γ (Option α)) (T : ℕ) : ℝ :=
  regret (single S g) (nullLaw θ) (extendNull θ) π T

/-- Consistent policies for instances of type `I_g` (p.8, (2)): `R_T(π′, I_g) = o(T^b)` for every
`b > 0` and every instance `I_g(θ)` with `θ` in the K-armed class. -/
def IsConsistentNull (S : GroupedStructure γ α) (g : γ) (π : Policy γ (Option α)) : Prop :=
  ∀ θ : α → ℝ, InKClass θ → ∀ b : ℝ, 0 < b →
    Tendsto (fun T : ℕ => regretNull S θ g π T / (T : ℝ) ^ b) atTop (𝓝 0)

end FairExplore


