-- Prove2me | Definitions.Def_FakeUserRanking_FORC_Supplement_EventE
-- name    : FakeUserRanking_FORC_Supplement_EventE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:31:54.962078+00:00
-- url     : https://prove2.me/theorems/4977ff33-52e0-4134-8898-8b361c0e702e
-- title:
--   (8)–(9), pp. 20–21 — FAR's confidence windows w_{i,t} and the event E
-- statement:
--   The concentration event used in the analysis of FAR.
--
--   For a product $i\in[n]$ and a round $t\in[T]$, let $\eta_{i,t}$ and $r_{i,t}$ be FAR's feedback count and average reward of product $i$ at the end of round $t$, and let $\delta=1/(nT)$. The window of product $i$ in round $t$ is
--
--   $$w_{i,t}=\begin{cases}\sqrt{\dfrac{\log(2nT/\delta)}{\eta_{i,t}}}+\dfrac{F}{\eta_{i,t}}, & \eta_{i,t}>0,\\[2mm] \max\Bigl(1,\sqrt{\log(2nT/\delta)}+F\Bigr), & \eta_{i,t}=0,\end{cases}\qquad(9)$$
--
--   and the event $\mathcal E_{i,t}$ is
--
--   $$\mathcal E_{i,t}=\{\,r_{i,t}-w_{i,t}\le\mu_i\le r_{i,t}+w_{i,t}\,\}.\qquad(8)$$
--
--   The event $\mathcal E=\bigcap_{i\in[n],\,t\in[T]}\mathcal E_{i,t}$ says that, at the end of every round, every click probability lies in its window around FAR's empirical estimate. Lemma 2 shows that it is likely; Lemmas 3 and 4 describe FAR's graph and rankings on it.
--
--   **Formalization Note** The state at the end of round $t$ is FAR's state after processing the first $t$ rounds of a trajectory; $\mathcal E$ is a property of a trajectory, quantified over $t=1,\dots,T$ and all products. Products are `Fin n`, indexed from $0$. Logarithms are natural.
--
--   Differences from the source:
--   - encoding: Products, positions and rounds use 1-based indices → Fin indices are 0-based; the state after t rounds uses the first t observations; reason: Relabelling preserves every source instance and round.
--   - encoding: E is an event of FAR’s run, with counts and means after rounds 1 through T → eventE is a predicate on trajectories using farStateAt after the first t observations; reason: Taking its probability under the published trajectory law gives the same event; the zero-feedback branch is retained.
-- source:
--   Golrezaei, Manshadi, Schneider, Sekar, Learning Product Rankings Robust to Fake Users, arXiv:2009.05138v1, pp. 20–21, (8), (9) and the definition of E

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_Supplement_FAR

namespace FakeUserRanking.FORC.Supplement

variable {n : ℕ}

/-- FAR's state at the end of round `t` of trajectory `τ` (after Steps 6–7 of the first `t`
rounds): its counts are `η_{i,t}`, its averages `r_{i,t}`, its graph the graph after round `t`.
`t = 0` is the initial state. -/
noncomputable def farStateAt (n T F : ℕ) (tb : List (Fin 1 × Obs n) → Finset (Fin n) → Fin n)
    (fb : List (Fin 1 × Obs n) → Equiv.Perm (Fin n)) (τ : Fin T → Step n 1) (t : ℕ) :
    FarState n :=
  farState n T F tb fb (algHist τ t)

/-- The window (9), p. 21:
`w_{i,t} = √(log(2nT/δ)/η_{i,t}) + F/η_{i,t}` if `η_{i,t} > 0`, and
`w_{i,t} = max(1, √(log(2nT/δ)) + F)` if `η_{i,t} = 0`, with `δ = 1/(nT)`. -/
noncomputable def farWindow (n T F : ℕ) (st : FarState n) (i : Fin n) : ℝ :=
  if st.cnt i = 0 then max 1 (Real.sqrt (Real.log (2 * n * T / farDelta n T)) + F)
  else farRadius n T F st i

/-- The event `E = ∩_{i ∈ [n], t ∈ [T]} E_{i,t}` of (8), p. 20–21: at the end of every round
`t ∈ {1, …, T}` and for every product `i`, `r_{i,t} − w_{i,t} ≤ μ_i ≤ r_{i,t} + w_{i,t}`. -/
def eventE (inst : Instance n) (T F : ℕ) (tb : List (Fin 1 × Obs n) → Finset (Fin n) → Fin n)
    (fb : List (Fin 1 × Obs n) → Equiv.Perm (Fin n)) (τ : Fin T → Step n 1) : Prop :=
  ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ i : Fin n,
    (farStateAt n T F tb fb τ t).avg i - farWindow n T F (farStateAt n T F tb fb τ t) i ≤ inst.μ i ∧
      inst.μ i ≤ (farStateAt n T F tb fb τ t).avg i + farWindow n T F (farStateAt n T F tb fb τ t) i

end FakeUserRanking.FORC.Supplement


