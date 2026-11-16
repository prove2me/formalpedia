-- Prove2me | Definitions.Def_LearnVsOpt_Supplement_Weak
-- name    : LearnVsOpt_Supplement_Weak
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:21:21.135599+00:00
-- url     : https://prove2.me/theorems/f50f63df-75c6-47c0-84b2-d988540f1fb4
-- title:
--   Weak BSE (28), the vertex gap $\Delta(x)$ (29), learners, stationary optimizers and generic learner entries
-- statement:
--   Objects of §7.3–7.4 and Appendix H.
--
--   For $x\in\Delta_{n_O}$:
--
--   1. the **budget-feasible polytope** is $\mathcal F(x)=\{y\in\Delta_{n_L}: x^\top C_L y\le\rho_L\}$;
--   2. the learner's **optimal utility** is $V_L(x)=\max_{y\in\mathcal F(x)}x^\top U_L y$;
--   3. the **suboptimal vertices** are $\mathcal V^{\mathrm{sub}}(x)=\mathcal V(x)\setminus\mathrm{BR}_L(x)$, where $\mathcal V(x)$ is the vertex set of $\mathcal F(x)$;
--   4. the **vertex suboptimality gap** (29) is $\Delta(x)=\min_{v\in\mathcal V^{\mathrm{sub}}(x)}(V_L(x)-x^\top U_L v)$, or $1$ when $\mathcal V^{\mathrm{sub}}(x)=\emptyset$.
--
--   The **Weak Budgeted Stackelberg Equilibrium value** (28) is
--   $$\mathrm{WBSE}=\sup_{x_1,x_2\in\Delta_{n_O},\,q\in[0,1]} q\min_{y_1\in \mathrm{BR}_L(x_1)}x_1^\top U_O y_1+(1-q)\min_{y_2\in \mathrm{BR}_L(x_2)}x_2^\top U_O y_2$$
--   subject to
--   $$q\max_{y_1\in \mathrm{BR}_L(x_1)}x_1^\top C_O y_1+(1-q)\max_{y_2\in \mathrm{BR}_L(x_2)}x_2^\top C_O y_2\le\rho_O.$$
--   Ties in the learner's best response are broken against the optimizer.
--
--   The section also defines:
--
--   - A **learning algorithm** is any kernel from the past $(i_r,j_r)_{r<t}$ to the law of $j_t$, with no budget constraint.
--   - A learner has **regret and overspending at most $r$ at horizon $T$** when both are at most $r$ on every phase of every optimizer that is stationary on at most three contiguous intervals partitioning $[T]$.
--   - An **oblivious optimizer** draws $i_t\sim\xi(t)$ independently in each round. The law of their play is built round by round.
--   - On an interval $\mathcal I$ where $i_t\sim x$, the learner's **expected stochastic regret** is $|\mathcal I|V_L(x)-\mathbb E[\sum_{t\in\mathcal I}U_L[i_t,j_t]]$ and its **expected overspending** is $\mathbb E[\sum_{t\in\mathcal I}C_L[i_t,j_t]]-\rho_L|\mathcal I|$.
--   - The **two-phase optimizer** plays $x_1$ in rounds $t\le T_1$ and $x_2$ afterwards. An optimizer is **three-phase** when it is stationary on each of the intervals $\{1,\dots,a\}$, $\{a+1,\dots,b\}$ and $\{b+1,\dots,T\}$.
--   - The **game with generic learner entries** fixes $U_O$ and $C_O$. Its learner matrices have free entries on $[n_O]\times([n_L]\setminus\{j_0\})$ and a zero column $j_0$ (Appendix H).
--
--   **Formalization Note** Maxima and minima are written as $\sup$ and $\inf$ of value sets; under the null actions these sets are nonempty compact polytopes' images, so they are attained. Mixed strategies of oblivious optimizers are laws on $[n_O]$.
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, (28)–(29) and Lemma 7.3 p.24; Theorem 7.4 p.25; Appendix H p.40

import Mathlib
import Definitions.Def_LearnVsOpt_BSE
import Definitions.Def_LearnVsOpt_Play

set_option autoImplicit false

open scoped Matrix

namespace LearnVsOpt.Supplement

variable {nO nL : ℕ}

/-- **The learner's budget-feasible polytope** `𝓕(x) = {y ∈ Δ_{n_L} : x⊤C_L y ≤ ρ_L}` (Fikioris, Sivan &
Tardos, arXiv:2611.05580, §7.3, p.24). -/
def feasSet (G : Game nO nL) (ρL : ℝ) (x : Fin nO → ℝ) : Set (Fin nL → ℝ) :=
  {y | y ∈ stdSimplex ℝ (Fin nL) ∧ x ⬝ᵥ (G.CL *ᵥ y) ≤ ρL}

/-- The learner's optimal utility `V_L(x) = max_{y ∈ 𝓕(x)} x⊤U_L y` (p.24).

**Formalization Note.** Written as `sSup`; under the learner's null action `𝓕(x)` is a nonempty
compact polytope, so the supremum is a maximum. -/
noncomputable def VL (G : Game nO nL) (ρL : ℝ) (x : Fin nO → ℝ) : ℝ :=
  sSup ((fun y => x ⬝ᵥ (G.UL *ᵥ y)) '' feasSet G ρL x)

/-- The suboptimal vertices `𝒱^sub(x) = 𝒱(x) \ BR_L(x)` of `𝓕(x)` (p.24), with `𝒱(x)` the extreme points
of `𝓕(x)`. -/
def Vsub (G : Game nO nL) (ρL : ℝ) (x : Fin nO → ℝ) : Set (Fin nL → ℝ) :=
  Set.extremePoints ℝ (feasSet G ρL x) \ G.BRx ρL x

open Classical in
/-- **The vertex suboptimality gap** (29), p.24: `Δ(x) = min_{v ∈ 𝒱^sub(x)} (V_L(x) − x⊤U_L v)` if
`𝒱^sub(x) ≠ ∅`, and `Δ(x) = 1` otherwise.

**Formalization Note.** Written as `sInf`; `𝒱^sub(x)` is finite, so the infimum is a minimum. -/
noncomputable def gap (G : Game nO nL) (ρL : ℝ) (x : Fin nO → ℝ) : ℝ :=
  if (Vsub G ρL x).Nonempty then sInf ((fun v => VL G ρL x - x ⬝ᵥ (G.UL *ᵥ v)) '' Vsub G ρL x)
  else 1

/-- The optimizer's pessimistic utility `min_{y ∈ BR_L(x)} x⊤U_O y` ((28), p.24).

**Formalization Note.** Written as `sInf`; `BR_L(x)` is a nonempty compact polytope under the learner's
null action. -/
noncomputable def minUO (G : Game nO nL) (ρL : ℝ) (x : Fin nO → ℝ) : ℝ :=
  sInf ((fun y => x ⬝ᵥ (G.UO *ᵥ y)) '' G.BRx ρL x)

/-- The optimizer's pessimistic cost `max_{y ∈ BR_L(x)} x⊤C_O y` ((28), p.24), written as `sSup`. -/
noncomputable def maxCO (G : Game nO nL) (ρL : ℝ) (x : Fin nO → ℝ) : ℝ :=
  sSup ((fun y => x ⬝ᵥ (G.CO *ᵥ y)) '' G.BRx ρL x)

/-- `(x₁, x₂, q)` is a **feasible solution to (28)**, p.24: `x₁, x₂ ∈ Δ_{n_O}`, `q ∈ [0, 1]`, and
`q · max_{y₁ ∈ BR_L(x₁)} x₁⊤C_O y₁ + (1 − q) · max_{y₂ ∈ BR_L(x₂)} x₂⊤C_O y₂ ≤ ρ_O`. -/
def IsWBSEFeasible (G : Game nO nL) (ρL ρO : ℝ) (x₁ x₂ : Fin nO → ℝ) (q : ℝ) : Prop :=
  x₁ ∈ stdSimplex ℝ (Fin nO) ∧ x₂ ∈ stdSimplex ℝ (Fin nO) ∧ q ∈ Set.Icc (0 : ℝ) 1 ∧
    q * maxCO G ρL x₁ + (1 - q) * maxCO G ρL x₂ ≤ ρO

/-- **The Weak Budgeted Stackelberg Equilibrium value** (28), p.24:
`WBSE = sup q · min_{y₁ ∈ BR_L(x₁)} x₁⊤U_O y₁ + (1 − q) · min_{y₂ ∈ BR_L(x₂)} x₂⊤U_O y₂` over the
feasible solutions `(x₁, x₂, q)`. Ties in the learner's best response are broken against the optimizer
in both the objective and the constraint, unlike the optimistic `LearnVsOpt.Game.BSE₂` (26).

**Formalization Note.** Written as `sSup` of the set of values; with the optimizer's zero-cost action
the set is nonempty, and it lies in `[0, 1]`. -/
noncomputable def WBSE (G : Game nO nL) (ρL ρO : ℝ) : ℝ :=
  sSup {v | ∃ x₁ x₂ : Fin nO → ℝ, ∃ q : ℝ, IsWBSEFeasible G ρL ρO x₁ x₂ q ∧
    v = q * minUO G ρL x₁ + (1 - q) * minUO G ρL x₂}

/-- **Any learning algorithm** (Lemma 7.3, p.24; Theorem 7.4, p.25): a kernel from the past
`(i_r, j_r)_{r < t}` to the law of `j_t`. No budget constraint is imposed.

**Formalization Note.** Against an optimizer that does not react to the learner, the joint law of play
of any learner, however it randomizes internally, is that of such a kernel, so this class is fully
general. -/
abbrev Learner (nO nL : ℕ) : Type := List (Fin nO × Fin nL) → PMF (Fin nL)

/-- An optimizer that draws `i_t ∼ ξ(t)` independently in each round `t`, whatever the past. -/
abbrev OblOpt (nO : ℕ) : Type := ℕ → PMF (Fin nO)

/-- The law of the first `t` rounds of play between the optimizer `ξ` and the learner `A`: in round
`t + 1`, `i ∼ ξ(t + 1)` and, independently given the past, `j ∼ A(past)`. -/
noncomputable def oblLaw (ξ : OblOpt nO) (A : Learner nO nL) :
    ℕ → PMF (List (Fin nO × Fin nL))
  | 0 => PMF.pure []
  | t + 1 => (oblLaw ξ A t).bind fun ω =>
      (ξ (t + 1)).bind fun i => (A ω).bind fun j => PMF.pure (ω ++ [(i, j)])

/-- The entry `M[i_t, j_t]` of round `t ≥ 1` of a play (`0` past its end). -/
def pathEntry (ω : List (Fin nO × Fin nL)) (M : Matrix (Fin nO) (Fin nL) ℝ) (t : ℕ) : ℝ :=
  ((ω[t - 1]?).map fun p => M p.1 p.2).getD 0

/-- The mixed strategy `x ∈ Δ_{n_O}` of a law on `[n_O]`. -/
noncomputable def toVec (p : PMF (Fin nO)) : Fin nO → ℝ := fun i => (p i).toReal

/-- The learner's **expected stochastic regret** on the interval `I` where `i_t ∼ x`:
`|I| V_L(x) − E[Σ_{t ∈ I} U_L[i_t, j_t]]` (Lemma 7.3, p.24). -/
noncomputable def regretOn (G : Game nO nL) (ρL : ℝ) (μ : PMF (List (Fin nO × Fin nL)))
    (I : Finset ℕ) (x : Fin nO → ℝ) : ℝ :=
  (I.card : ℝ) * VL G ρL x - expect μ (fun ω => ∑ t ∈ I, pathEntry ω G.UL t)

/-- The learner's **expected overspending** on `I`: `E[Σ_{t ∈ I} C_L[i_t, j_t]] − ρ_L |I|`
(Lemma 7.3, p.24). -/
noncomputable def overOn (G : Game nO nL) (ρL : ℝ) (μ : PMF (List (Fin nO × Fin nL)))
    (I : Finset ℕ) : ℝ :=
  expect μ (fun ω => ∑ t ∈ I, pathEntry ω G.CL t) - ρL * I.card

/-- The two-phase optimizer of Theorem 7.4, p.25: `i_t ∼ x₁` for `t ≤ T₁`, `i_t ∼ x₂` afterwards. -/
def twoPhase (T₁ : ℕ) (x₁ x₂ : PMF (Fin nO)) : OblOpt nO := fun t => if t ≤ T₁ then x₁ else x₂

/-- `ξ` is stationary on each of three contiguous intervals `{1, …, a}`, `{a + 1, …, b}`,
`{b + 1, …, T}` partitioning `[T]` (any of them may be empty), with laws `x₁, x₂, x₃`. -/
def IsThreePhase (ξ : OblOpt nO) (T a b : ℕ) (x₁ x₂ x₃ : PMF (Fin nO)) : Prop :=
  a ≤ b ∧ b ≤ T ∧ (∀ t ∈ Finset.Ioc 0 a, ξ t = x₁) ∧ (∀ t ∈ Finset.Ioc a b, ξ t = x₂) ∧
    (∀ t ∈ Finset.Ioc b T, ξ t = x₃)

/-- The learner `A` has expected stochastic regret and expected overspending at most `r` on every phase
of every optimizer that is stationary on at most three contiguous intervals partitioning `[T]`
(Theorem 7.4, p.25: "Reg, Over = o(T)", read with `r = r(T)`). -/
def IsLowRegret (G : Game nO nL) (ρL : ℝ) (T : ℕ) (A : Learner nO nL) (r : ℝ) : Prop :=
  ∀ (ξ : OblOpt nO) (a b : ℕ) (x₁ x₂ x₃ : PMF (Fin nO)), IsThreePhase ξ T a b x₁ x₂ x₃ →
    regretOn G ρL (oblLaw ξ A T) (Finset.Ioc 0 a) (toVec x₁) ≤ r ∧
    overOn G ρL (oblLaw ξ A T) (Finset.Ioc 0 a) ≤ r ∧
    regretOn G ρL (oblLaw ξ A T) (Finset.Ioc a b) (toVec x₂) ≤ r ∧
    overOn G ρL (oblLaw ξ A T) (Finset.Ioc a b) ≤ r ∧
    regretOn G ρL (oblLaw ξ A T) (Finset.Ioc b T) (toVec x₃) ≤ r ∧
    overOn G ρL (oblLaw ξ A T) (Finset.Ioc b T) ≤ r

/-- A learner matrix with a zero null column: entry `M'[i, j]` off the column `j₀`, and `0` on it
(Appendix H, p.40). -/
def withNull (j₀ : Fin nL) (M' : Fin nO → {j : Fin nL // j ≠ j₀} → ℝ) :
    Matrix (Fin nO) (Fin nL) ℝ :=
  fun i j => if h : j = j₀ then 0 else M' i ⟨j, h⟩

theorem withNull_mem (j₀ : Fin nL) (M' : Fin nO → {j : Fin nL // j ≠ j₀} → ℝ)
    (hM : ∀ i j, M' i j ∈ Set.Icc (0 : ℝ) 1) (i : Fin nO) (j : Fin nL) :
    withNull j₀ M' i j ∈ Set.Icc (0 : ℝ) 1 := by
  unfold withNull
  split_ifs with h
  · exact ⟨le_rfl, zero_le_one⟩
  · exact hM i _

/-- **The game with generic learner entries** (Appendix H, p.40): the optimizer's `U_O`, `C_O` are fixed,
and the learner's `U_L`, `C_L` have the free entries `U'`, `C'` on `[n_O] × ([n_L] \ {j₀})` and
`U_L[·, j₀] = C_L[·, j₀] = 0`. -/
def learnerGame (UO CO : Matrix (Fin nO) (Fin nL) ℝ) (hUO : ∀ i j, UO i j ∈ Set.Icc (0 : ℝ) 1)
    (hCO : ∀ i j, CO i j ∈ Set.Icc (0 : ℝ) 1) (j₀ : Fin nL)
    (U' C' : Fin nO → {j : Fin nL // j ≠ j₀} → ℝ) (hU : ∀ i j, U' i j ∈ Set.Icc (0 : ℝ) 1)
    (hC : ∀ i j, C' i j ∈ Set.Icc (0 : ℝ) 1) : Game nO nL where
  UO := UO
  UL := withNull j₀ U'
  CO := CO
  CL := withNull j₀ C'
  UO_mem := hUO
  UL_mem := withNull_mem j₀ U' hU
  CO_mem := hCO
  CL_mem := withNull_mem j₀ C' hC

end LearnVsOpt.Supplement


