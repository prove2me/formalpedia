-- Prove2me | Definitions.Def_BilateralProfit_Algorithm1
-- name    : BilateralProfit_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:52.659004+00:00
-- url     : https://prove2.me/theorems/90428844-c000-4262-80c0-55d5148ce6e4
-- title:
--   Algorithm 1 (adversarial bilateral trade): run, randomness, expected profit, cost, and the resolution $K(T)$
-- statement:
--   **Algorithm 1** with horizon $T$ and resolution $K$: set $w_1(a')=1/|\mathcal A|$ for every $a'\in\mathcal A$; for $t=1,\dots,T$: $(a_t,Q_0,Q_1)\leftarrow\mathrm{OneRound}(w_t)$ with fresh randomness; post $a_t$ and observe $Z_t=z_{a_t}(v_t)$; set $w_{t+1}=Q_{Z_t}$.
--
--   The valuation sequence $v_1,\dots,v_T\in[0,1]^2$ is fixed in advance (an oblivious adversary); the algorithm uses $v_t$ only through the trade bit $Z_t$. Its only randomness is the draw $j^\star$ of each OneRound call, uniform on $\{1,\dots,J\}$ and independent across rounds. The expectation $\mathbb E[\cdot]$ over the algorithm is the average over the $J^T$ equally likely draw sequences, $\mathbb E[\mathrm{Profit}_t(p_t,q_t)]$ is the expected profit of round $t$, and the **cost** of a run is the number of unit-cost operations it performs.
--
--   The resolution used for horizon $T$ is
--   $$K(T)=\max\Big(2,\ \Big\lceil (T/\log^7T)^{1/3}\Big\rceil\Big),$$
--   an explicit choice of the paper's $K=\Theta((T/\log^7T)^{1/3})$.
--
--   **Formalization Note** Rounds are indexed $0,\dots,T-1$; the weight list holds $w_1,\dots,w_{T+1}$ at indices $0,\dots,T$. A draw sequence is a function from rounds to $\{0,\dots,J-1\}$.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Algorithm 1, p.17 (PDF 19); regret definition, §2, p.4 (PDF 6); choice of K, p.23 (PDF 25)

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_BilateralProfit_OneRound

namespace BilateralProfit

open CapacitatedAssort.General (Work charge)

/-! # Algorithm 1 (adversarial bilateral trade), its randomness, its regret and its cost

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), Algorithm 1, p.17
(PDF 19); the regret `R_T(𝒜, 𝒮)`, §2, p.4 (PDF 6); the choice `K = Θ((T/log⁷ T)^{1/3})`,
p.23 (PDF 25).

**Formalization Note.** Rounds are `t : Fin T` (round `t + 1` of the paper). The valuation
sequence `S : Fin T → ℝ × ℝ` is fixed in advance (oblivious adversary); the algorithm reads
`S t` only through the trade test of round `t`, after posting `a_t`. Its only randomness is
one draw `j⋆` per round, uniform on `{1, …, J}` and independent across rounds: the sample space
is `Fin T → Fin J` with the uniform law, and `E[·]` is the average over it. The run records the
posted actions `a_t` and the weights `w_t` (`w_1` uniform, `w_{t+1} = Q_{Z_t}`); the weight list
has `w_1, …, w_{T+1}` at indices `0, …, T`. The cost is the final counter of the run in the
model of `OneRound`. -/

/-- Algorithm 1 at resolution `K` on the valuations `S`, with the draws `ω t` (`j⋆ = ω t + 1`)
of OneRound in round `t`. Returns the posted actions and the weight vectors
`w_1, …, w_{T+1}`. -/
noncomputable def alg1 (K T : ℕ) (S : Fin T → ℝ × ℝ) (ω : Fin T → Fin (Jpar K)) :
    Work (Array (Act K) × Array (Act K → ℝ)) := do
  let w₁ ← tab (actList K) fun _ => do
    charge 2 -- cardinality, division
    pure (1 / nA K)
  let mut w := w₁
  let mut acts : Array (Act K) := #[]
  let mut ws : Array (Act K → ℝ) := #[w₁]
  for t in List.finRange T do
    charge 2 -- loop dispatch, read of the draw `ω t`
    let P ← oneRound K w (ω t)
    charge 6 -- post `a_t`, read `v_t`, two comparisons, conjunction, branch
    let wNext := if Trades (S t) (pt K P.1.1) then P.2.2 else P.2.1
    charge (actList K).length -- copy `w_{t+1}(a′) ← Q_{Z_t}(a′)` for every `a′ ∈ 𝒜`
    w := wNext
    acts := acts.push P.1
    ws := ws.push wNext
  return (acts, ws)

/-- The action `a_t` posted in round `t`. -/
noncomputable def alg1Act (K T : ℕ) (S : Fin T → ℝ × ℝ) (ω : Fin T → Fin (Jpar K))
    (t : Fin T) : Act K :=
  (runW (alg1 K T S ω)).1.1.getD t default

/-- The weight vector `w_{t+1}` (index `t ∈ {0, …, T}`). -/
noncomputable def alg1W (K T : ℕ) (S : Fin T → ℝ × ℝ) (ω : Fin T → Fin (Jpar K))
    (t : ℕ) : Act K → ℝ :=
  (runW (alg1 K T S ω)).1.2.getD t fun _ => 0

/-- The number of unit-cost operations of the run. -/
noncomputable def alg1Cost (K T : ℕ) (S : Fin T → ℝ × ℝ) (ω : Fin T → Fin (Jpar K)) : ℕ :=
  (runW (alg1 K T S ω)).2

/-- Expectation over the algorithm's randomness: the uniform average over
`ω ∈ Fin T → Fin J`. -/
noncomputable def expectAlg (K T : ℕ) (f : (Fin T → Fin (Jpar K)) → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card (Fin T → Fin (Jpar K))

/-- `E[Profit_t(p_t, q_t)]`, the expected profit of Algorithm 1 in round `t`. -/
noncomputable def expProfit (K T : ℕ) (S : Fin T → ℝ × ℝ) (t : Fin T) : ℝ :=
  expectAlg K T fun ω => profit (S t) (pt K (alg1Act K T S ω t).1)

/-- The resolution used for horizon `T`: `K(T) = max(2, ⌈(T / log⁷ T)^{1/3}⌉)`, an explicit
choice of the paper's `K = Θ((T/log⁷ T)^{1/3})` (p.23), natural logarithm. -/
noncomputable def Kpin (T : ℕ) : ℕ :=
  max 2 ⌈((T : ℝ) / Real.log T ^ 7) ^ ((1 : ℝ) / 3)⌉₊

end BilateralProfit


