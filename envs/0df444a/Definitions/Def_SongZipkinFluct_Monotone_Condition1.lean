-- Prove2me | Definitions.Def_SongZipkinFluct_Monotone_Condition1
-- name    : SongZipkinFluct_Monotone_Condition1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:36:34.585154+00:00
-- url     : https://prove2.me/theorems/9eae161e-0e72-440b-989c-4242dcb421f4
-- title:
--   §4.1, (14) and Condition 1 — stochastic partial-monotonicity of the world chain, and the order ≤_st
-- statement:
--   Let $\preceq$ be a partial order on the world states $\mathbf I$. A real function $f$ on $\mathbf I$ is *nondecreasing* if $i \preceq j$ implies $f(i) \le f(j)$.
--
--   **The world process.** The transition function of $A$ is
--   $$P(t)(i,k) = \sum_{n\ge 0} e^{-\mu t}\frac{(\mu t)^n}{n!}\,(P_\mu)^n(i,k), \qquad P_\mu = I + Q/\mu .$$
--   A family $X = (X(t))_{t\ge0}$ of $\mathbf I$-valued random variables on a probability space $(\Omega,\mathbb P)$ is *a version of $A$ started at $i$* if for all times $0 \le t_0 \le \dots \le t_n$ and states $k_0,\dots,k_n$
--   $$\mathbb P\big(X(t_0)=k_0,\dots,X(t_n)=k_n\big) = P(t_0)(i,k_0)\prod_{r=0}^{n-1} P(t_{r+1}-t_r)(k_r,k_{r+1}).$$
--
--   **Stochastic partial-monotonicity (14).** $A$ is *stochastically partial-monotone* if for any $i \preceq j$ "there is a way to construct the process so that"
--   $$[A(t)\mid A(0)=i] \preceq [A(t)\mid A(0)=j] \quad \text{for all } t \ge 0 \text{ w.p.1},$$
--   that is, there are a probability space and versions $X$, $X'$ of $A$ started at $i$ and at $j$ with $X(t) \preceq X'(t)$ for all $t \ge 0$, almost surely.
--
--   **Condition 1.** (a) $A$ is stochastically partial-monotone; (b) $\lambda_i$ is nondecreasing in $i$ for $\preceq$.
--
--   **Stochastic order.** For laws $a$, $b$ on $\{0,1,2,\dots\}$, $a \le_{st} b$ means $\sum_{e \ge d} a(e) \le \sum_{e\ge d} b(e)$ for every $d$.
--
--   Condition 1 is the hypothesis of every result in §4 of the paper. It says that a world started higher stays higher and has a higher demand rate.
--
--   **Formalization Note.** Condition 1(a) is the coupling (14) itself, not its consequence (15) ($E[f(A(t))\mid A(0)=i]$ nondecreasing in $i$ for nondecreasing $f$), which is strictly weaker for a partial order. The probability space may depend on the pair $(i,j)$. The transition function is written by uniformization at the model's rate $\mu \ge q^*$; for a bounded generator it does not depend on that rate.
-- source:
--   Song and Zipkin, Inventory Control in a Fluctuating Demand Environment, Oper. Res. 41(2):351–370 (1993), DOI 10.1287/opre.41.2.351, p. 359, §4.1, display (14) and Condition 1; p. 355 (≤_st)

import Mathlib
import Definitions.Def_SongZipkinFluct_Monotone_Model

open MeasureTheory

namespace SongZipkinFluct.Monotone

namespace Model

variable {I : Type} (M : Model I) [DecidableEq I]

/-- One step of the world chain uniformized at rate `μ`: `P_μ = I + Q/μ`, i.e. probability
`q_ik/μ` for `k ≠ i` and `1 + q_ii/μ` for `k = i` (§2, p. 354; cf. §4.1, p. 359). -/
noncomputable def worldStep (i k : I) : ℝ := (if i = k then 1 else 0) + M.Q i k / M.μ

/-- `(P_μ)^n (i, k)`, the `n`-step transition probabilities of the uniformized world chain. -/
noncomputable def worldPow : ℕ → I → I → ℝ
  | 0, i, k => if i = k then 1 else 0
  | n + 1, i, k => ∑' m : I, M.worldStep i m * worldPow n m k

/-- The transition function of the world chain `A` (§1, p. 353),
`P(t)(i, k) = P(A(t) = k | A(0) = i) = Σ_n e^{−μt} (μt)^n / n! · (P_μ)^n (i, k)`.

**Formalization Note.** The paper never constructs `A`. For a conservative generator with
`q* < ∞` this uniformization formula is the (unique) transition function, and it does not depend on
the rate as long as the rate is at least `q*`; the model's `μ ≥ q* + λ*` is used. -/
noncomputable def worldTrans (t : ℝ) (i k : I) : ℝ :=
  ∑' n : ℕ, Real.exp (-M.μ * t) * (M.μ * t) ^ n / (n.factorial : ℝ) * M.worldPow n i k

/-- `X` is (a version of) **the world process `A` started at `i`** on the probability space
`(Ω, ℙ)`: every `X t` is a measurable map to the discrete space `I`, and the finite-dimensional
distributions are those of a Markov chain with transition function `P(t)` started at `i`: for times
`0 ≤ t₀ ≤ t₁ ≤ ⋯ ≤ t_n` and states `k₀, …, k_n`,
`ℙ(X(t₀) = k₀, …, X(t_n) = k_n) = P(t₀)(i, k₀) ∏_r P(t_{r+1} − t_r)(k_r, k_{r+1})`. -/
def IsWorldProcess {Ω : Type} [MeasurableSpace Ω] (ℙ : Measure Ω) (X : ℝ → Ω → I) (i : I) :
    Prop :=
  (∀ (t : ℝ) (k : I), MeasurableSet {ω | X t ω = k}) ∧
  ∀ (n : ℕ) (t : Fin (n + 1) → ℝ) (k : Fin (n + 1) → I), 0 ≤ t 0 → Monotone t →
    ℙ {ω | ∀ r, X (t r) ω = k r} =
      ENNReal.ofReal (M.worldTrans (t 0) i (k 0) *
        ∏ r : Fin n, M.worldTrans (t r.succ - t r.castSucc) (k r.castSucc) (k r.succ))

/-- **Stochastic partial-monotonicity**, display (14) (§4.1, p. 359): "`A` is stochastically
partial-monotone if, for any `i` and `j` with `i ⪯ j`, there is a way to construct the process so that
`[A(t) | A(0) = i] ⪯ [A(t) | A(0) = j]` for all `t ≥ 0` w.p.1."

For every pair `i ⪯ j` there is a probability space carrying two versions `X`, `X'` of the world
process, started at `i` and at `j`, with `X(t) ⪯ X'(t)` for all `t ≥ 0`, almost surely.

**Formalization Note.** The coupling is the paper's definition (14), not its consequence (15)
(`E f(A(t))` nondecreasing in the initial state for nondecreasing `f`), which is strictly weaker for a
partial order (Massey 1987). The probability space may depend on the pair `(i, j)`. -/
def StochPartialMonotone [PartialOrder I] : Prop :=
  ∀ i j : I, i ≤ j →
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (ℙ : Measure Ω) (X X' : ℝ → Ω → I),
      IsProbabilityMeasure ℙ ∧ M.IsWorldProcess ℙ X i ∧ M.IsWorldProcess ℙ X' j ∧
      ∀ᵐ ω ∂ℙ, ∀ t : ℝ, 0 ≤ t → X t ω ≤ X' t ω

/-- **Condition 1** (§4.1, p. 359): (a) `A` is stochastically partial-monotone; (b) `λ_i` is
nondecreasing in `i` for the partial order `⪯` (`i ⪯ j ⇒ λ_i ≤ λ_j`). -/
def Condition1 [PartialOrder I] : Prop :=
  M.StochPartialMonotone ∧ Monotone M.lam

end Model

/-- The **usual stochastic order** `≤_st` (p. 355) between two laws on `ℕ` given by their mass
functions `a`, `b`: `X ≤_st Y` iff `P(X ≥ d) ≤ P(Y ≥ d)` for every `d`. -/
def StLe (a b : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, ∑' e : {e : ℕ // d ≤ e}, a e ≤ ∑' e : {e : ℕ // d ≤ e}, b e

end SongZipkinFluct.Monotone


