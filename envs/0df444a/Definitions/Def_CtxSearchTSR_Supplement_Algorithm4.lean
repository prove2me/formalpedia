-- Prove2me | Definitions.Def_CtxSearchTSR_Supplement_Algorithm4
-- name    : CtxSearchTSR_Supplement_Algorithm4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:22:18.507073+00:00
-- url     : https://prove2.me/theorems/16a96699-d547-453d-a18a-d8e6101c6538
-- title:
--   Algorithm 4 (Adversarial Contextual Bilateral Trade): states, plans, finite lotteries, (21), run and expected loss
-- statement:
--   A **state** is a center $m=(m_S,m_B)\in\mathbb R^{2d}$ and a block-diagonal matrix $R=\operatorname{diag}(R_S,R_B)\succ 0$. Its potential at a pair $w=(s,b)$ is (20):
--
--   $$\Phi(m,R,w)=\Phi(m_S,R_S,s)+\Phi(m_B,R_B,b),\qquad \Phi(m,R,z)=\operatorname{Tr}R+(z-m)^\top R^{-1}(z-m).$$
--
--   A **plan** $a$ is a common price $p_a$ and two successor states $(m_a^{(y)},R_a^{(y)})$, $y\in\{0,1\}$. At context $x$, $Y_a(w)=\mathbf 1\{x^\top s\le p_a\le x^\top b\}$, $\ell_a(w)=(x^\top(b-s))_+(1-Y_a(w))$ and $\Phi_a^+(w)=\Phi(m_a^{(Y_a(w))},R_a^{(Y_a(w))},w)$. A **finite lottery** $Q$ is a probability distribution on finitely many plans. It satisfies **(21)** at state $(m,R)$, context $x$ and slack $\gamma$ if, for every $w\in K=B_2^d\times B_2^d$,
--
--   $$\mathbb E_{a\sim Q}\big[\ell_a(w)+2^{10}\Phi_a^+(w)\big]\le 2^{10}\Phi(m,R,w)+\gamma.\qquad(21)$$
--
--   A **lottery rule** is **valid** (the property Lemma 3.3 provides) if for every state with $R\succ 0$, every $\|x\|_2\le1$ and every $\gamma\in(0,1]$ it returns a finite lottery whose successor matrices are block-diagonal positive definite and which satisfies (21).
--
--   **Algorithm 4** with a lottery rule starts at $m_1=0$, $R_1=I_{2d}/\sqrt d$. In round $t$ it receives $x_t$, sets $\gamma_t=\frac1{t(t+1)}$, draws a plan from the rule's lottery at $(m_t,R_t)$, $x_t$, $\gamma_t$, posts its price, observes $Y_t$ and keeps that plan's successor for $Y_t$. Contexts are chosen by an adaptive strategy from the observed history (contexts, drawn plans, trade bits). The expected total loss against a fixed $w$ is the exact expectation over the $T$ successive draws.
--
--   **Formalization Note** A block-diagonal state is stored as its four blocks; $R\succ0$ iff both blocks are positive definite; $R_1$ is $(\sqrt d)^{-1}I_d$ on each block. A finite lottery is a list of plans with nonnegative weights summing to $1$. Algorithm 4 is specified in the paper through Lemma 3.3 ("choose a lottery of plans as in Lemma 3.3"), so it is parametrized by a valid lottery rule; that one exists is Lemma 3.3. Rounds are 0-based, so round index $t$ has slack $\frac1{(t+1)(t+2)}$. $\Phi$ is the published `CtxSearchTSR.Phi`.
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), §3.2 (20) p.14, Lemma 3.3 (21) p.15, Algorithm 4 p.16, App. D.2 p.28

import Mathlib
import Definitions.Def_CtxSearchTSR_Protocol
import Definitions.Def_CtxSearchTSR_Potentials
import Definitions.Def_CtxSearchTSR_Supplement_BilateralTrade

open Matrix

namespace CtxSearchTSR.Supplement

/-!
# Algorithm 4 (Adversarial Contextual Bilateral Trade): states, plans, lotteries, (21), the run

Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, *Contextual Search and Bilateral Trade with a
Trace-Square-Root Potential*, STOC 2027 submission (manuscript sha256 70eeb0d1…),
§3.2 (p.14, (20)), Lemma 3.3 (p.15, (21)), Algorithm 4 (p.16), proof of Lemma 3.3 (App. D.2, p.28).

* A state is a center m = (m_S, m_B) ∈ ℝ^{2d} and a block-diagonal R = diag(R_S, R_B) ≻ 0, with
  potential Φ(m, R, w) = Φ(m_S, R_S, s) + Φ(m_B, R_B, b) (20), Φ the search potential (12).
* A plan a is a common price p_a and two successor states (m_a^(y), R_a^(y)), y ∈ {0, 1}, each
  R_a^(y) block-diagonal positive definite. Y_a(w) = 1{xᵀs ≤ p_a ≤ xᵀb},
  ℓ_a(w) = (xᵀ(b − s))₊(1 − Y_a(w)), Φ_a⁺(w) = Φ(m_a^(Y_a(w)), R_a^(Y_a(w)), w).
* (21): E_{a∼Q}[ℓ_a(w) + 2¹⁰Φ_a⁺(w)] ≤ 2¹⁰Φ(m, R, w) + γ for every w ∈ K = B₂^d × B₂^d.
* Algorithm 4: m₁ = 0, R₁ = I_{2d}/√d; round t: γₜ = 1/(t(t+1)); choose a lottery as in Lemma 3.3
  for (mₜ, Rₜ), xₜ, γₜ; draw a plan, post its price, observe Yₜ, keep that plan's successor for Yₜ.

**Formalization Note.**
* A block-diagonal state is stored as its blocks (m_S, m_B, R_S, R_B); R ≻ 0 iff R_S ≻ 0 and
  R_B ≻ 0. R₁ = I_{2d}/√d is `(√d)⁻¹ • 1` on each block.
* A finite lottery is a finite list of plans with nonnegative weights summing to 1.
* Algorithm 4 is parametrized by a lottery rule `𝓛` mapping (state, context, slack) to a finite
  lottery ("the lottery can be chosen as a function of the state and context", Lemma 3.3).
  `ValidLotteryRule 𝓛` is exactly what Lemma 3.3 provides: for every admissible state, every
  ‖x‖₂ ≤ 1 and every γ ∈ (0, 1], the lottery's successor matrices are block-diagonal positive
  definite and (21) holds.
* With w fixed the only randomness is the learner's draws. The context strategy maps the observed
  history (contexts, drawn plans, trade bits, oldest first) to the next context and may depend on
  the fixed w; it never sees the current draw. The expected total loss is the exact finite
  expectation over the T successive draws, computed by backward recursion.
* Rounds are 0-based: index t is the paper's round t + 1, so its slack is 1/((t+1)(t+2)).
-/

/-- A block-diagonal state (m_S, m_B, diag(R_S, R_B)). -/
structure BState (d : ℕ) where
  /-- The seller block of the center. -/
  mS : Fin d → ℝ
  /-- The buyer block of the center. -/
  mB : Fin d → ℝ
  /-- The seller block of R. -/
  RS : Matrix (Fin d) (Fin d) ℝ
  /-- The buyer block of R. -/
  RB : Matrix (Fin d) (Fin d) ℝ

/-- R = diag(R_S, R_B) ≻ 0. -/
def BState.Admissible {d : ℕ} (σ : BState d) : Prop := σ.RS.PosDef ∧ σ.RB.PosDef

/-- The initial state of Algorithm 4: m₁ = 0, R₁ = I_{2d}/√d. -/
noncomputable def BState.init (d : ℕ) : BState d :=
  ⟨0, 0, (Real.sqrt (d : ℝ))⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ),
    (Real.sqrt (d : ℝ))⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)⟩

/-- The potential (20): Φ(m, R, w) = Φ(m_S, R_S, s) + Φ(m_B, R_B, b). -/
noncomputable def phiPair {d : ℕ} (σ : BState d) (s b : Fin d → ℝ) : ℝ :=
  Phi σ.mS σ.RS s + Phi σ.mB σ.RB b

/-- A plan: a common price and a successor state for each trade bit (`false` = 0, `true` = 1). -/
structure Plan (d : ℕ) where
  /-- The posted price p_a. -/
  p : ℝ
  /-- The successor state (m_a^(y), R_a^(y)). -/
  succ : Bool → BState d

/-- A finite lottery of plans: plans `plan i` with weights `wt i ≥ 0`, Σ wt = 1. -/
structure Lottery (d : ℕ) where
  /-- The number of atoms. -/
  n : ℕ
  /-- The weights. -/
  wt : Fin n → ℝ
  /-- The plans. -/
  plan : Fin n → Plan d
  wt_nonneg : ∀ i, 0 ≤ wt i
  wt_sum : ∑ i, wt i = 1

/-- Y_a(w) = 1{xᵀs ≤ p_a ≤ xᵀb}. -/
noncomputable def planBit {d : ℕ} (a : Plan d) (x s b : Fin d → ℝ) : Bool :=
  tradeBit (x ⬝ᵥ s) (x ⬝ᵥ b) a.p

/-- ℓ_a(w) = (xᵀ(b − s))₊(1 − Y_a(w)). -/
noncomputable def planLoss {d : ℕ} (a : Plan d) (x s b : Fin d → ℝ) : ℝ :=
  tradeLoss (x ⬝ᵥ s) (x ⬝ᵥ b) a.p

/-- Φ_a⁺(w) = Φ(m_a^(Y_a(w)), R_a^(Y_a(w)), w). -/
noncomputable def planSuccPotential {d : ℕ} (a : Plan d) (x s b : Fin d → ℝ) : ℝ :=
  phiPair (a.succ (planBit a x s b)) s b

/-- Inequality (21) for the lottery `Q` at state `σ`, context `x`, slack `γ`, for every w ∈ K. -/
def Lottery.Satisfies21 {d : ℕ} (Q : Lottery d) (σ : BState d) (x : Fin d → ℝ) (γ : ℝ) : Prop :=
  ∀ s b : Fin d → ℝ, eucNorm s ≤ 1 → eucNorm b ≤ 1 →
    ∑ i, Q.wt i * (planLoss (Q.plan i) x s b + 2 ^ 10 * planSuccPotential (Q.plan i) x s b)
      ≤ 2 ^ 10 * phiPair σ s b + γ

/-- A lottery rule as in Lemma 3.3: at every admissible state, context with ‖x‖₂ ≤ 1 and slack
γ ∈ (0, 1], it returns a finite lottery of admissible plans satisfying (21). -/
def ValidLotteryRule {d : ℕ} (𝓛 : BState d → (Fin d → ℝ) → ℝ → Lottery d) : Prop :=
  ∀ (σ : BState d) (x : Fin d → ℝ) (γ : ℝ), σ.Admissible → eucNorm x ≤ 1 → 0 < γ → γ ≤ 1 →
    (∀ i y, (((𝓛 σ x γ).plan i).succ y).Admissible) ∧ (𝓛 σ x γ).Satisfies21 σ x γ

/-- One round's observed record: context, drawn plan (the learner's randomization), trade bit. -/
structure AdvTradeRecord (d : ℕ) where
  /-- The context xₜ. -/
  x : Fin d → ℝ
  /-- The drawn plan. -/
  a : Plan d
  /-- The trade bit Yₜ. -/
  Y : Bool

/-- An adaptive context strategy: the next context as a function of the observed history. -/
abbrev AdvTradeStrategy (d : ℕ) : Type := List (AdvTradeRecord d) → (Fin d → ℝ)

/-- The slack γ of round index `t` (0-based): 1/((t+1)(t+2)), the paper's 1/(t(t+1)) for round t. -/
noncomputable def slack (t : ℕ) : ℝ := 1 / (((t : ℝ) + 1) * ((t : ℝ) + 2))

/-- The expected loss of the remaining `k` rounds of Algorithm 4 from round index `t`, state `σ`
and history `h`, against the fixed pair (s, b). -/
noncomputable def alg4Value {d : ℕ} (𝓛 : BState d → (Fin d → ℝ) → ℝ → Lottery d)
    (X : AdvTradeStrategy d) (s b : Fin d → ℝ) :
    ℕ → ℕ → BState d → List (AdvTradeRecord d) → ℝ
  | _, 0, _, _ => 0
  | t, k + 1, σ, h =>
    ∑ i, (𝓛 σ (X h) (slack t)).wt i *
      (planLoss ((𝓛 σ (X h) (slack t)).plan i) (X h) s b +
        alg4Value 𝓛 X s b (t + 1) k
          (((𝓛 σ (X h) (slack t)).plan i).succ (planBit ((𝓛 σ (X h) (slack t)).plan i) (X h) s b))
          (h ++ [⟨X h, (𝓛 σ (X h) (slack t)).plan i,
            planBit ((𝓛 σ (X h) (slack t)).plan i) (X h) s b⟩]))

/-- The expected total loss Σ_{t=1}^T 𝔼[ℓₜ] of Algorithm 4 against the fixed pair (s, b). -/
noncomputable def alg4ExpectedTotalLoss {d : ℕ} (𝓛 : BState d → (Fin d → ℝ) → ℝ → Lottery d)
    (X : AdvTradeStrategy d) (s b : Fin d → ℝ) (T : ℕ) : ℝ :=
  alg4Value 𝓛 X s b 0 T (BState.init d) []

end CtxSearchTSR.Supplement


