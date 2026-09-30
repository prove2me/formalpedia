-- Prove2me | Definitions.Def_AlgMechDesign_Randomized_BiasedMinWork
-- name    : AlgMechDesign_Randomized_BiasedMinWork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T20:19:04.120517+00:00
-- url     : https://prove2.me/theorems/0784bc78-166b-49fe-958a-373d75c6d6ab
-- title:
--   The biased min work mechanism and the randomly biased min work mechanism for two agents
-- statement:
--   This file defines the mechanisms of Fig. 1 and Definition 17 of Nisan and Ronen for task scheduling with two agents $1, 2$; for an agent $i$, $i' = 3 - i$ denotes the other agent.
--
--   The **biased min work mechanism** has parameters $\beta \ge 1$ and a bit vector $s \in \{1,2\}^k$. On the declared types $t = (t^1, t^2)$ it treats each task $j$ separately: let $i = s_j$ (the favoured agent) and $i' = 3 - i$.
--
--   1. If $t^i_j \le \beta \cdot t^{i'}_j$, task $j$ goes to agent $i$, who is paid $\beta \cdot t^{i'}_j$ for it.
--   2. Otherwise task $j$ goes to agent $i'$, who is paid $\beta^{-1} \cdot t^i_j$ for it.
--
--   An agent's payment is the sum of its payments over the tasks it receives.
--
--   The **randomly biased min work mechanism** is the distribution over biased min work mechanisms with $\beta = 4/3$ and $s$ uniform on $\{1,2\}^k$. Its objective value on a type vector $t$ is the expected make-span
--   $$
--   \mathbb{E}_s\big[g(x_s(t), t)\big] = \frac{1}{2^k} \sum_{s \in \{1,2\}^k} g\big(x_s(t), t\big),
--   $$
--   where $x_s$ is the allocation of the biased min work mechanism with parameters $4/3$ and $s$.
--
--   **Formalization Note** The agents $1, 2$ are `Fin 2 = {0, 1}` and the other agent is `other i = 1 - i`. The tie rule of Fig. 1 is kept: at $t^i_j = \beta \cdot t^{i'}_j$ the task goes to the favoured agent. Since the distribution on $s$ is uniform on a finite set, the expectation of Definition 15 is the finite average above; no measure theory is involved.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 182, Fig. 1 and Definition 17; p. 181, Definition 15

import Mathlib
import Definitions.Def_AlgMechDesign_Randomized_Model

namespace AlgMechDesign.Randomized

open Finset

/-- The other agent of a two-agent instance: the paper's `i' = 3 − i` on agents `{1, 2}`, which on
`Fin 2 = {0, 1}` is `1 - i` (so `other 0 = 1`, `other 1 = 0`). -/
def other (i : Fin 2) : Fin 2 := 1 - i

/-- The allocation of the biased min work mechanism (Fig. 1, p. 182) with parameters `β` and
`s ∈ {1, 2}ᵏ` on declarations `t`: task `j` goes to the favoured agent `i = s j` if
`tⁱ_j ≤ β · t^{i'}_j`, and to the other agent `i'` otherwise. -/
noncomputable def bmwAlloc {k : ℕ} (β : ℝ) (s : Fin k → Fin 2) (t : Fin 2 → Fin k → ℝ) :
    Fin k → Fin 2 :=
  fun j => if t (s j) j ≤ β * t (other (s j)) j then s j else other (s j)

/-- The payments of the biased min work mechanism (Fig. 1): for each task `j` with favoured agent
`i = s j`, if `i` gets `j` it is paid `β · t^{i'}_j`; otherwise the other agent `i'` gets `j` and
is paid `β⁻¹ · tⁱ_j`. The payment to an agent is the sum over the tasks it receives. -/
noncomputable def bmwPay {k : ℕ} (β : ℝ) (s : Fin k → Fin 2) (t : Fin 2 → Fin k → ℝ)
    (i : Fin 2) : ℝ :=
  ∑ j, if bmwAlloc β s t j = i then
      (if i = s j then β * t (other (s j)) j else β⁻¹ * t (s j) j)
    else 0

/-- The biased min work allocations with `β = 4/3` (Def. 17), indexed by `s ∈ {1, 2}ᵏ`. -/
noncomputable def rbmwAlloc {k : ℕ} (s : Fin k → Fin 2) (t : Fin 2 → Fin k → ℝ) :
    Fin k → Fin 2 :=
  bmwAlloc (4 / 3) s t

/-- The biased min work payments with `β = 4/3` (Def. 17), indexed by `s ∈ {1, 2}ᵏ`. -/
noncomputable def rbmwPay {k : ℕ} (s : Fin k → Fin 2) (t : Fin 2 → Fin k → ℝ) (i : Fin 2) : ℝ :=
  bmwPay (4 / 3) s t i

/-- The objective of the randomly biased min work mechanism (Defs. 15, 17): the expected make-span
when `s` is uniform on `{1, 2}ᵏ`, i.e. the average of the make-spans over all `2ᵏ` vectors `s`. -/
noncomputable def expMakespan {k : ℕ} (t : Fin 2 → Fin k → ℝ) : ℝ :=
  (1 / 2 ^ k) * ∑ s : Fin k → Fin 2, makespan t (rbmwAlloc s t)

end AlgMechDesign.Randomized


