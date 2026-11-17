-- Prove2me | Definitions.Def_MCPoise_Supplement_Delivers
-- name    : MCPoise_Supplement_Delivers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:13:48.862889+00:00
-- url     : https://prove2.me/theorems/428a0bc5-b588-4417-84a5-1e0ed4a44aea
-- title:
--   Delivery and completion times of a multicommodity multicast schedule
-- statement:
--   Let $G$ be a graph with demand pairs $(s_1, t_1), \dots, (s_k, t_k)$ and let $S = (M_1, \dots, M_T)$ be a list of rounds.
--
--   1. Demand $i$ is **delivered by round $r$** when $t_i$ holds at time $r$ the message that $s_i$ held at time $0$ (telephone-model propagation).
--   2. $S$ is a **multicommodity multicast schedule** when every demand is delivered by round $T$.
--   3. The **completion time** $C_i(S)$ of demand $i$ is the first round $r$ by which demand $i$ is delivered.
--
--   The total completion time $\sum_i C_i(S)$ is the objective of Average Multicommodity Multicast.
--
--   **Formalization Note** Demands are counted by index, so repeated demands count separately; a demand with $s_i = t_i$ completes at time $0$. The completion time is an infimum of natural numbers, which is $0$ on the empty set; it is only used for schedules that deliver every demand, where the set contains $T$.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §1, p.2 (definition of MCMC); §1.2, p.3 (Average Multicommodity Multicast objective)

import Mathlib
import Definitions.Def_MCPoise_Inst
import Definitions.Def_MCPoise_Supplement_TempReach

namespace MCPoise.Supplement

/-- The rounds of a finite schedule `S = [M₁, …, M_T]`: round `r` is `M_r` for `1 ≤ r ≤ T`, and empty otherwise. -/
def finRounds (S : List (List (ℕ × ℕ))) : ℕ → List (ℕ × ℕ) :=
  fun r => if r = 0 then [] else S.getD (r - 1) []

/-- Demand `i` is delivered by round `r`: the sink `t_i` holds at time `r` the message `s_i` held at time `0`. -/
def DeliveredBy (I : Inst) (S : List (List (ℕ × ℕ))) (i : Fin I.k) (r : ℕ) : Prop :=
  TempReach (finRounds S) (I.s i).val 0 (I.t i).val r

/-- **A multicommodity multicast schedule.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §1, p.2: "find a schedule that transfers the message from every source `s_i` to its corresponding destination
`t_i`".

`Delivers I S`: every demand `i` is delivered by the end of `S`, that is, by round `S.length`.

**Formalization Note.** Demands are counted by index (footnote 2, p.9); `s_i = t_i` is delivered at time `0`. -/
def Delivers (I : Inst) (S : List (List (ℕ × ℕ))) : Prop :=
  ∀ i : Fin I.k, DeliveredBy I S i S.length

/-- **Completion time of demand `i`**: the first round at which `t_i` holds the message of `s_i`.
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §1.2, p.3: "the times at which each sink `t_i` first receives the message from its source `s_i`".

**Formalization Note.** `sInf` on `ℕ` is `0` on the empty set; every statement using `complTime` assumes
`Delivers I S`, under which the set contains `S.length` and `complTime` is the true least round. It is `0` when
`s_i = t_i`. -/
noncomputable def complTime (I : Inst) (S : List (List (ℕ × ℕ))) (i : Fin I.k) : ℕ :=
  sInf {r : ℕ | DeliveredBy I S i r}

end MCPoise.Supplement


