-- Prove2me | Definitions.Def_RelPerfMFG_TwoLayer
-- name    : RelPerfMFG_TwoLayer
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:28:24.041444+00:00
-- url     : https://prove2.me/theorems/8f3cd2f1-729f-47c8-90f7-6023ebe46c55
-- title:
--   Assumption 4.1, team payoff $\mathbb V$ (4.1), member payoff $\mathfrak V$, Definitions 4.1–4.3 and $\beta^*$ (4.6)
-- statement:
--   Fix $\theta\in(0,1)$ and rewards $R,G:\mathbb R_+\times(\mathbb R^e)^N\to\mathbb R_+$.
--
--   1. **Assumption 4.1** (pp.17–18): (i) $x\mapsto R(x,y)$ and $x\mapsto R(x,y)G(x,y)$ are concave and continuously differentiable; (ii) $R'(x,y)>0$ and $G'(x,y)>0$; (iii) for $x>0$, $\mathbb E[R'G+RG']<\infty$ and $\mathbb E[R']<\infty$; (iv) for any $K>0$ there are $\alpha\in(0,1)$ and $A\ge0$ with $\mathbb E[A]<\infty$ such that $K\max\{R(x,Y),R(x,Y)G(x,Y)\}\le(1-\alpha)C_t(x)+A$ for all $x\ge0$ and $t$; (v) there are $L\ge0$ and $B\ge0$ with $\mathbb E[B]<\infty$ such that $G(\sum_tx_t,Y)\le L\sum_tC_t(x_t)+B$.
--   2. **Team payoff** (4.1), p.18: for $a,a^*\in\mathcal A$,
--   $$\mathbb V(a,a^*)=\mathbb E\Big[R\Big(\sum_ta_t\Big)\Big((1-\theta)+\theta\frac{G(\sum_ta_t)}{\mathbb E[G(\sum_ta^*_t)]}\Big)-\sum_tC_t(a_t)\Big].$$
--   3. **Definition 4.1**: $a^*\in\mathcal A$ is a team-wise equilibrium if $a^*\in\arg\max_{a\in\mathcal A}\mathbb V(a,a^*)$.
--   4. **Member payoff** (p.19): with $\bar a'_t=\mathbb E[a'_t\mid\mathcal F^Y_t]$ (4.2), $\bar a''_t=\mathbb E[a''_t\mid\mathcal F^Y_t]$ (4.3),
--   $$\mathfrak V(a;a',\beta,a'')=\mathbb E\Big[\Big((1-\beta)+\beta\frac{\sum_t\phi_t(a_t,X_{t+1})}{\sum_t\bar a'_t}\Big)R\Big(\sum_t\bar a'_t\Big)\Big((1-\theta)+\theta\frac{G(\sum_t\bar a'_t)}{\mathbb E[G(\sum_t\bar a''_t)]}\Big)-\sum_tC_t(a_t)\Big].$$
--   5. **Definition 4.2**: $\hat a'\in\tilde{\mathcal A}$ is an equilibrium control w.r.t. $\beta\in\mathcal F^Y_N$ and $a''$ if $\hat a'\in\arg\max_{a\in\tilde{\mathcal A}}\mathfrak V(a;\hat a',\beta,a'')$ (4.4); $\beta$ is an intra-team optimal RPC w.r.t. $a''$ if some such $\hat a'$ has $\mathfrak V(\hat a';\hat a',\beta,a'')=\sup_{a'\in\tilde{\mathcal A}}\mathbb V(\bar a',\bar a'')$ (4.5), and then $\hat a'$ is an optimal equilibrium control.
--   6. **Definition 4.3**: $(\beta^*,a^*)$ is an equilibrium for the two-layer game if $\beta^*$ is an intra-team optimal RPC w.r.t. $a^*$ and $a^*$ is an optimal equilibrium control w.r.t. $\beta^*$ and $a^*$.
--   7. **The weight (4.6)**, p.20: with $S^*=\sum_ta^*_t$,
--   $$\beta^*=\frac{R'(S^*)S^*}{R(S^*)}+\frac{\theta G'(S^*)S^*}{\theta G(S^*)+(1-\theta)\mathbb E[G(S^*)]}.$$
--
--   **Formalization Note** (i)–(ii) hold for every $y$ with derivatives at $x>0$ (footnote 2). Team payoffs are Bochner expectations; a team-wise equilibrium has an integrable payoff and beats every $a\in\mathcal A$ in the extended sense. Member payoffs and their equilibrium value are expectations in the extended sense (`ExpLE`, `ExpEq`), and the supremum in (4.5) is an extended supremum (`IsTeamSup`), so no junk value of a real $\sup$ or of a non-integrable integral enters. Aggregates are conditional expectations of nonnegative variables (`aggregate`). Representative-player and representative-team form; Lean's $x/0=0$. The printed "$C(a_t)$" in $\mathfrak V$ is $C_t(a_t)$, and "$\beta$ is" in Definition 4.3 is $\beta^*$.
-- source:
--   Zhou, Optimal relative performance criteria in mean field contribution games, SSRN 3742584 (Nov. 13, 2022), Assumption 4.1, pp.17–18; (4.1) and Definition 4.1, pp.18–19; Section 4.2, p.19 ((4.2), (4.3), member payoff, Definition 4.2, (4.4), (4.5)); Definition 4.3 and (4.6), p.20

import Mathlib
import Definitions.Def_RelPerfMFG_Setup
import Definitions.Def_RelPerfMFG_Centralized

open MeasureTheory ProbabilityTheory

namespace RelPerfMFG

variable {Ω : Type*} [MeasurableSpace Ω] {N d e : ℕ}

/-- **Assumption 4.1(i)**, Zhou, *Optimal relative performance criteria in mean field
contribution games*, SSRN 3742584 (Nov. 13, 2022), p.17: for every `y`, the maps `x ↦ R(x, y)`
and `x ↦ R(x, y)G(x, y)` are concave and continuously differentiable.

**Formalization Note.** Concavity on `ℝ₊`; "continuously differentiable" in the sense of
footnote 2 (p.5): continuous on `ℝ₊`, `C¹` on `(0, ∞)`. -/
def Ass41i (R G : ℝ → NoisePath N e → ℝ) : Prop :=
  ∀ y, ConcaveOn ℝ (Set.Ici 0) (fun x => R x y) ∧ IsC1Fn2 (fun x => R x y) ∧
    ConcaveOn ℝ (Set.Ici 0) (fun x => R x y * G x y) ∧ IsC1Fn2 (fun x => R x y * G x y)

/-- **Assumption 4.1(ii)**, SSRN 3742584 (Nov. 13, 2022), p.17:
`R′(x, y) := ∂R/∂x (x, y) > 0` and `G′(x, y) := ∂G/∂x (x, y) > 0` for any `y`.

**Formalization Note.** At every `x > 0` (footnote 2: `R′(0)` may be `+∞`); a positive
`rderiv` forces differentiability, since Lean's derivative of a non-differentiable function is
`0`. -/
def Ass41ii (R G : ℝ → NoisePath N e → ℝ) : Prop :=
  ∀ y, ∀ x : ℝ, 0 < x → 0 < rderiv (fun x => R x y) x ∧ 0 < rderiv (fun x => G x y) x

/-- **Assumption 4.1(iii)**, SSRN 3742584 (Nov. 13, 2022), p.17: for any `x > 0`,
`E[R′(x, Y)G(x, Y) + R(x, Y)G′(x, Y)] < ∞` and `E[R′(x, Y)] < ∞`.

**Formalization Note.** Both integrands are nonnegative (by (ii) and `R, G ≥ 0`); finiteness of
the expectation is integrability. -/
def Ass41iii (μ : Measure Ω) (Y : Ω → NoisePath N e) (R G : ℝ → NoisePath N e → ℝ) : Prop :=
  ∀ x : ℝ, 0 < x →
    Integrable (fun ω => rderiv (fun x => R x (Y ω)) x * G x (Y ω) +
      R x (Y ω) * rderiv (fun x => G x (Y ω)) x) μ ∧
    Integrable (fun ω => rderiv (fun x => R x (Y ω)) x) μ

/-- **Assumption 4.1(iv)**, SSRN 3742584 (Nov. 13, 2022), p.17: for any constant `K > 0` there
are a constant `α ∈ (0, 1)` and a random variable `A ≥ 0` with `E[A] < ∞` such that
`K max{R(x, Y), R(x, Y)G(x, Y)} ≤ (1 − α)C_t(x) + A` for all `x ≥ 0`, `t = 0, …, N − 1`.

**Formalization Note.** `α` and `A` depend on `K`; the inequality holds a.s., simultaneously
for all `x ≥ 0` and `t`. -/
def Ass41iv (μ : Measure Ω) (Y : Ω → NoisePath N e) (C : Fin N → ℝ → ℝ)
    (R G : ℝ → NoisePath N e → ℝ) : Prop :=
  ∀ K : ℝ, 0 < K → ∃ α ∈ Set.Ioo (0 : ℝ) 1, ∃ A : Ω → ℝ, IsAdmissibleBound μ A ∧
    ∀ᵐ ω ∂μ, ∀ x : ℝ, 0 ≤ x → ∀ t : Fin N,
      K * max (R x (Y ω)) (R x (Y ω) * G x (Y ω)) ≤ (1 - α) * C t x + A ω

/-- **Assumption 4.1(v)**, SSRN 3742584 (Nov. 13, 2022), p.18: there are a constant `L ≥ 0` and a
random variable `B ≥ 0` with `E[B] < ∞` such that
`G(Σ_{t=0}^{N−1} x_t, Y) ≤ L Σ_{t=0}^{N−1} C_t(x_t) + B` for all `(x₀, …, x_{N−1}) ∈ ℝ₊ᴺ`.

**Formalization Note.** Almost surely, simultaneously for all nonnegative vectors. -/
def Ass41v (μ : Measure Ω) (Y : Ω → NoisePath N e) (C : Fin N → ℝ → ℝ)
    (G : ℝ → NoisePath N e → ℝ) : Prop :=
  ∃ L : ℝ, 0 ≤ L ∧ ∃ B : Ω → ℝ, IsAdmissibleBound μ B ∧
    ∀ᵐ ω ∂μ, ∀ x : Fin N → ℝ, (∀ t, 0 ≤ x t) →
      G (∑ t, x t) (Y ω) ≤ L * ∑ t, C t (x t) + B ω

/-- **Assumption 4.1 (i)–(v)**, SSRN 3742584 (Nov. 13, 2022), pp.17–18. -/
def Assumption41 (μ : Measure Ω) (Y : Ω → NoisePath N e) (C : Fin N → ℝ → ℝ)
    (R G : ℝ → NoisePath N e → ℝ) : Prop :=
  Ass41i R G ∧ Ass41ii R G ∧ Ass41iii μ Y R G ∧ Ass41iv μ Y C R G ∧ Ass41v μ Y C G

/-- The integrand of the team payoff `𝕍(a, a*)` (4.1), SSRN 3742584 (Nov. 13, 2022), p.18:
`R(Σ_t a_t)((1 − θ) + θ · G(Σ_t a_t)/E[G(Σ_t a*_t)]) − Σ_t C_t(a_t)`, with `R(·) = R(·, Y)`,
`G(·) = G(·, Y)`.

**Formalization Note.** `E[G(Σ a*_t)]` is a Bochner integral; Lean's `x / 0 = 0` agrees with the
paper's value `G/∞ = 0` when `G(Σ a*_t)` is not integrable. -/
noncomputable def teamIntegrand (μ : Measure Ω) (Y : Ω → NoisePath N e) (C : Fin N → ℝ → ℝ)
    (R G : ℝ → NoisePath N e → ℝ) (θ : ℝ) (a aS : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  R (∑ t, a t ω) (Y ω) *
      ((1 - θ) + θ * G (∑ t, a t ω) (Y ω) / ∫ ω', G (∑ t, aS t ω') (Y ω') ∂μ) -
    ∑ t, C t (a t ω)

/-- **The team payoff `𝕍(a, a*)`** (4.1), SSRN 3742584 (Nov. 13, 2022), §4.1, p.18:
`𝕍(a, a*) := E[R(Σ_t a_t)((1 − θ) + θ G(Σ_t a_t)/E[G(Σ_t a*_t)]) − Σ_t C_t(a_t)]`. -/
noncomputable def teamValue (μ : Measure Ω) (Y : Ω → NoisePath N e) (C : Fin N → ℝ → ℝ)
    (R G : ℝ → NoisePath N e → ℝ) (θ : ℝ) (a aS : Fin N → Ω → ℝ) : ℝ :=
  ∫ ω, teamIntegrand μ Y C R G θ a aS ω ∂μ

/-- **Team-wise equilibrium**, SSRN 3742584 (Nov. 13, 2022), Definition 4.1, p.19:
`a* ∈ 𝒜` with `a* ∈ argmax_{a ∈ 𝒜} 𝕍(a, a*)`.

**Formalization Note.** `𝕍(a*, a*)` is finite (integrable integrand), and every `a ∈ 𝒜` has
`𝕍(a, a*) ≤ 𝕍(a*, a*)` in the extended sense (`ExpLE`). -/
def IsTeamwiseEq (μ : Measure Ω) (Y : Ω → NoisePath N e) (C : Fin N → ℝ → ℝ)
    (R G : ℝ → NoisePath N e → ℝ) (θ : ℝ) (aS : Fin N → Ω → ℝ) : Prop :=
  IsCtrlA Y aS ∧ Integrable (teamIntegrand μ Y C R G θ aS aS) μ ∧
    ∀ a : Fin N → Ω → ℝ, IsCtrlA Y a →
      ExpLE μ (teamIntegrand μ Y C R G θ a aS) (teamValue μ Y C R G θ aS aS)

/-- The integrand of the member payoff `𝔙(a; a′, β, a″)`, SSRN 3742584 (Nov. 13, 2022), §4.2,
p.19:
`((1 − β) + β Σ_t φ_t(a_t, X_{t+1}) / Σ_t ā′_t) R(Σ_t ā′_t) ((1 − θ) + θ G(Σ_t ā′_t)/E[G(Σ_t ā″_t)])
 − Σ_t C_t(a_t)`, with `ā′_t = E[a′_t | F^Y_t]` (4.2) and `ā″_t = E[a″_t | F^Y_t]` (4.3);
`𝔙(a; a′, β, a″)` is its expectation.

**Formalization Note.** The printed `C(a_t)` is `C_t(a_t)`. Representative form: the member's
own noise is `X`; 0-based periods (`φ t (a t ω) (X ω t)` is paper `φ_t(a_t, X_{t+1})`). The
aggregates are `aggregate` (conditional expectations of nonnegative variables). Lean's
`x / 0 = 0`. -/
noncomputable def memberIntegrand (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → NoisePath N d)
    (Y : Ω → NoisePath N e) (φ : Fin N → ℝ → (Fin d → ℝ) → ℝ) (C : Fin N → ℝ → ℝ)
    (R G : ℝ → NoisePath N e → ℝ) (θ : ℝ) (a a' : Fin N → Ω → ℝ) (β : Ω → ℝ)
    (a'' : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  ((1 - β ω) + β ω * (∑ t, φ t (a t ω) (X ω t)) / ∑ t, aggregate μ Y a' t ω) *
      R (∑ t, aggregate μ Y a' t ω) (Y ω) *
      ((1 - θ) + θ * G (∑ t, aggregate μ Y a' t ω) (Y ω) /
        ∫ ω', G (∑ t, aggregate μ Y a'' t ω') (Y ω') ∂μ) -
    ∑ t, C t (a t ω)

/-- **Equilibrium control w.r.t. `β` and `a″`, with payoff `v`**, SSRN 3742584 (Nov. 13, 2022),
Definition 4.2, (4.4), p.19: `â′ ∈ 𝒜̃`, `𝔙(â′; â′, β, a″) = v`, and
`â′ ∈ argmax_{a ∈ 𝒜̃} 𝔙(a; â′, β, a″)`, i.e. `𝔙(a; â′, β, a″) ≤ v` for every `a ∈ 𝒜̃`.

**Formalization Note.** The deviations `a ∈ 𝒜̃` may depend on the member's own noise `X`. The
value and the comparisons are expectations in the extended sense (`ExpEq`, `ExpLE`): no deviation
is discarded, and no claim is made about an expectation that is undefined (`E[f⁺] = E[f⁻] = ∞`). -/
def IsEquilibriumControlVal (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → NoisePath N d)
    (Y : Ω → NoisePath N e) (φ : Fin N → ℝ → (Fin d → ℝ) → ℝ) (C : Fin N → ℝ → ℝ)
    (R G : ℝ → NoisePath N e → ℝ) (θ : ℝ) (β : Ω → ℝ) (a'' â : Fin N → Ω → ℝ) (v : ℝ) :
    Prop :=
  IsCtrlTilde X Y â ∧ ExpEq μ (memberIntegrand μ X Y φ C R G θ â â β a'') v ∧
    ∀ a : Fin N → Ω → ℝ, IsCtrlTilde X Y a →
      ExpLE μ (memberIntegrand μ X Y φ C R G θ a â β a'') v

/-- **The optimality condition (4.5)**, SSRN 3742584 (Nov. 13, 2022), Definition 4.2, p.19:
`v = sup_{a′ ∈ 𝒜̃} 𝕍(ā′, ā″)`, with `ā′`, `ā″` from (4.2)–(4.3).

**Formalization Note.** The supremum is taken in the extended sense: every `a′ ∈ 𝒜̃` has
`𝕍(ā′, ā″) ≤ v` (`ExpLE`), and for every `ε > 0` some `a′ ∈ 𝒜̃` with a finite (integrable) team
payoff has `𝕍(ā′, ā″) > v − ε`. No junk value of a real `⨆` is involved. -/
def IsTeamSup (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → NoisePath N d)
    (Y : Ω → NoisePath N e) (C : Fin N → ℝ → ℝ) (R G : ℝ → NoisePath N e → ℝ) (θ : ℝ)
    (a'' : Fin N → Ω → ℝ) (v : ℝ) : Prop :=
  (∀ a' : Fin N → Ω → ℝ, IsCtrlTilde X Y a' →
      ExpLE μ (teamIntegrand μ Y C R G θ (aggregate μ Y a') (aggregate μ Y a'')) v) ∧
    ∀ ε > (0 : ℝ), ∃ a' : Fin N → Ω → ℝ, IsCtrlTilde X Y a' ∧
      Integrable (teamIntegrand μ Y C R G θ (aggregate μ Y a') (aggregate μ Y a'')) μ ∧
      v - ε < teamValue μ Y C R G θ (aggregate μ Y a') (aggregate μ Y a'')

/-- **Optimal equilibrium control w.r.t. `β` and `a″`**, SSRN 3742584 (Nov. 13, 2022),
Definition 4.2, p.19: `â′` is an equilibrium control w.r.t. `β` and `a″` (4.4) whose payoff
satisfies `𝔙(â′; â′, β, a″) = sup_{a′ ∈ 𝒜̃} 𝕍(ā′, ā″)` (4.5). -/
def IsOptimalEquilibriumControl (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → NoisePath N d)
    (Y : Ω → NoisePath N e) (φ : Fin N → ℝ → (Fin d → ℝ) → ℝ) (C : Fin N → ℝ → ℝ)
    (R G : ℝ → NoisePath N e → ℝ) (θ : ℝ) (β : Ω → ℝ) (a'' â : Fin N → Ω → ℝ) : Prop :=
  ∃ v : ℝ, IsEquilibriumControlVal μ X Y φ C R G θ β a'' â v ∧ IsTeamSup μ X Y C R G θ a'' v

/-- **Intra-team optimal RPC w.r.t. `a″`**, SSRN 3742584 (Nov. 13, 2022), Definition 4.2, p.19:
`β ∈ F^Y_N` and there is an equilibrium control `â′ ∈ 𝒜̃` w.r.t. `β` and `a″` with
`𝔙(â′; â′, β, a″) = sup_{a′ ∈ 𝒜̃} 𝕍(ā′, ā″)` (4.5).

**Formalization Note.** `β ∈ F^Y_N` is a real random variable measurable for `σ(Y) = mY Y N`. -/
def IsIntraTeamOptimalRPC (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → NoisePath N d)
    (Y : Ω → NoisePath N e) (φ : Fin N → ℝ → (Fin d → ℝ) → ℝ) (C : Fin N → ℝ → ℝ)
    (R G : ℝ → NoisePath N e → ℝ) (θ : ℝ) (β : Ω → ℝ) (a'' : Fin N → Ω → ℝ) : Prop :=
  Measurable[mY Y N] β ∧
    ∃ â : Fin N → Ω → ℝ, IsOptimalEquilibriumControl μ X Y φ C R G θ β a'' â

/-- **Equilibrium for the two-layer mean-field contribution game**, SSRN 3742584
(Nov. 13, 2022), Definition 4.3, p.20: `(β*, a*)` is an equilibrium if `β*` is an intra-team
optimal RPC w.r.t. `a*`, and `a*` is an optimal equilibrium control w.r.t. `β*` and `a*`.

**Formalization Note.** The printed "`β` is an intra-team optimal RPC" is `β*`. -/
def IsTwoLayerEquilibrium (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → NoisePath N d)
    (Y : Ω → NoisePath N e) (φ : Fin N → ℝ → (Fin d → ℝ) → ℝ) (C : Fin N → ℝ → ℝ)
    (R G : ℝ → NoisePath N e → ℝ) (θ : ℝ) (β : Ω → ℝ) (aS : Fin N → Ω → ℝ) : Prop :=
  IsIntraTeamOptimalRPC μ X Y φ C R G θ β aS ∧
    IsOptimalEquilibriumControl μ X Y φ C R G θ β aS aS

/-- **The intra-team optimal RPC weight `β*`** (4.6), SSRN 3742584 (Nov. 13, 2022), Theorem 4.2,
p.20: with `S* = Σ_{t=0}^{N−1} a*_t`,
`β* := R′(S*) S* / R(S*) + θ G′(S*) S* / (θ G(S*) + (1 − θ) E[G(S*)])`, a random variable.

**Formalization Note.** `R′ = rderiv (R · Y)`, `G′ = rderiv (G · Y)`; Lean's `x / 0 = 0`. -/
noncomputable def betaStar (μ : Measure Ω) (Y : Ω → NoisePath N e) (R G : ℝ → NoisePath N e → ℝ)
    (θ : ℝ) (aS : Fin N → Ω → ℝ) (ω : Ω) : ℝ :=
  rderiv (fun x => R x (Y ω)) (∑ t, aS t ω) * (∑ t, aS t ω) / R (∑ t, aS t ω) (Y ω) +
    θ * rderiv (fun x => G x (Y ω)) (∑ t, aS t ω) * (∑ t, aS t ω) /
      (θ * G (∑ t, aS t ω) (Y ω) + (1 - θ) * ∫ ω', G (∑ t, aS t ω') (Y ω') ∂μ)

end RelPerfMFG


