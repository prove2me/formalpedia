-- Prove2me | Definitions.Def_SendSplit_DPEquations_Equations
-- name    : SendSplit_DPEquations_Equations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:25:20.39046+00:00
-- url     : https://prove2.me/theorems/a54eb20e-8f90-43ab-b902-ba1de6845746
-- title:
--   Eqs. (1)–(3) — A_I, sending costs c_ij(r_I), the splitting term B_iI, and +∞-or-real solutions of (1) and (2)
-- statement:
--   This file states the send-and-split dynamic-programming equations (1)–(3) of Section 3 for an arbitrary array $C' = (C'_{jI})$ of extended reals.
--
--   **Sending arcs.** For a set $I$ with $r_I \neq 0$, let $A_I = A$ if $r_I > 0$ and $A_I = \{ (i,j) : (j,i) \in A \}$ if $r_I < 0$. Sending $r_I < 0$ units from $i$ to $j$ means sending $-r_I > 0$ units along the reverse arc from $j$ to $i$, so for $(i,j) \in A_I$ the **sending cost** is
--
--   $$c_{ij}(r_I) \;=\; \begin{cases} c_{ij}(r_I) & \text{if } r_I > 0, \\ c_{ji}(-r_I) & \text{if } r_I < 0. \end{cases}$$
--
--   **Splitting term (3).** For $|I| > 1$,
--   $$B'_{iI} \;=\; \min_{\emptyset \subset J \subset I} \bigl[ C'_{iJ} + C'_{i, I \setminus J} \bigr],$$
--   the minimum over nonempty proper subsets $J$ of $I$; for $|I| = 1$, $B'_{iI} = 0$ if $I = \{i\}$ and $B'_{iI} = +\infty$ otherwise.
--
--   **Solutions of (1) and (2).** An array $C' = (C'_{jI})$, $j \in N$, $\emptyset \subset I \subseteq D$, is a **$+\infty$ or real-valued solution of (1) and (2)** if every entry is $+\infty$ or real and, for every $i \in N$ and every $\emptyset \subset I \subseteq D$:
--
--   1. if $r_I = 0$, then $C'_{iI} = C'_{j I_j}$ for all $j \in I$, where $I_j = I \setminus \{j\}$; (1)
--   2. if $r_I \neq 0$, then
--   $$C'_{iI} \;=\; \min_{(i,j)\in A_I} \bigl[ c_{ij}(r_I) + C'_{jI} \bigr] \;\wedge\; B'_{iI}, \qquad (2)$$
--   where $B'$ is computed from $C'$ by (3) and $\wedge$ is the minimum.
--
--   Theorem 2 states that the subproblem minimum costs $C_{iI}$ form the greatest such solution, and the only one when every simple circulation has positive cost.
--
--   **Formalization Note** Values are `EReal`. The sending cost `sendCost` is $+\infty$ for pairs $(i,j) \notin A_I$, so the minimum over $A_I$ is written as a `Finset.inf` over all nodes $j$; a node with no arc in $A_I$ gets the empty minimum $+\infty$, as on the page (the right side of (2) is then $B'_{iI}$). `IsSendArc` is the predicate $(i,j) \in A_I$. `splitCost` treats $|I| = 1$ by the printed special case, not by the empty minimum. `IsSolution` requires $C'_{jI} \neq -\infty$ on every admissible $I$ ("$+\infty$ or real-valued"); the values of $C'$ at other sets are irrelevant. Equation (1) is required only when $r_I = 0$ and (2) only when $r_I \neq 0$.
-- source:
--   Erickson, Monma, Veinott, Send-and-Split Method for Minimum-Concave-Cost Network Flows, Math. Oper. Res. 12 (1987), pp. 640–641, Eqs. (1), (2), (3)

import Mathlib
import Definitions.Def_SendSplit_DPEquations_Network
import Definitions.Def_SendSplit_DPEquations_Subproblem

namespace SendSplit.DPEquations

/-- `(i, j) ∈ A_I` (p. 640): `A_I = A` if `r_I > 0`, and `A_I = {(i, j) : (j, i) ∈ A}` if
`r_I < 0`. (`A_I` is only used when `r_I ≠ 0`.) -/
def IsSendArc {n : ℕ} (A : Finset (Fin n × Fin n)) (r : Fin n → ℝ) (I : Finset (Fin n))
    (i j : Fin n) : Prop :=
  (0 < demandSum r I ∧ (i, j) ∈ A) ∨ (demandSum r I < 0 ∧ (j, i) ∈ A)

/-- The cost `c_ij(r_I)` of sending `r_I` units from `i` to `j` along an arc of `A_I`
(p. 640): `c_ij(r_I)` if `r_I > 0` and `(i, j) ∈ A`; `c_ji(-r_I)` if `r_I < 0` and
`(j, i) ∈ A`; and `+∞` when `(i, j) ∉ A_I`, so that a minimum over `A_I` is a minimum over
all nodes `j`. -/
noncomputable def sendCost {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ)
    (r : Fin n → ℝ) (I : Finset (Fin n)) (i j : Fin n) : EReal :=
  if 0 < demandSum r I ∧ (i, j) ∈ A then ((c i j (demandSum r I) : ℝ) : EReal)
  else if demandSum r I < 0 ∧ (j, i) ∈ A then ((c j i (-demandSum r I) : ℝ) : EReal)
  else ⊤

/-- `B_iI` computed from an array `C'` by (3) (p. 641): for `|I| > 1`,
`B_iI = min_{∅ ⊂ J ⊂ I} [C'_iJ + C'_{i, I \ J}]` over nonempty proper subsets `J`; for
`|I| = 1`, `B_iI = 0` if `I = {i}` and `+∞` otherwise. -/
noncomputable def splitCost {n : ℕ} (C' : Fin n → Finset (Fin n) → EReal) (i : Fin n)
    (I : Finset (Fin n)) : EReal :=
  if I.card = 1 then (if I = {i} then 0 else ⊤)
  else (I.powerset.filter (fun J => J.Nonempty ∧ J ≠ I)).inf
    (fun J => C' i J + C' i (I \ J))

/-- A `+∞`-or-real-valued solution of (1) and (2), with `B` defined by (3) (pp. 640–641):
an array `C'_jI` (`j ∈ N`, `∅ ⊂ I ⊆ D`; values at other `I` are irrelevant) such that every
entry is `+∞` or real, and for every node `i` and every `∅ ⊂ I ⊆ D`:
(1) if `r_I = 0` then `C'_iI = C'_{j, I \ {j}}` for all `j ∈ I`;
(2) if `r_I ≠ 0` then `C'_iI = min_{(i,j) ∈ A_I} [c_ij(r_I) + C'_jI] ∧ B'_iI`. -/
def IsSolution {n : ℕ} (A : Finset (Fin n × Fin n)) (c : Fin n → Fin n → ℝ → ℝ)
    (r : Fin n → ℝ) (C' : Fin n → Finset (Fin n) → EReal) : Prop :=
  (∀ j I, IsAdmissible r I → C' j I ≠ ⊥) ∧
  ∀ i I, IsAdmissible r I →
    (demandSum r I = 0 → ∀ j ∈ I, C' i I = C' j (I.erase j)) ∧
    (demandSum r I ≠ 0 →
      C' i I = (Finset.univ.inf fun j => sendCost A c r I i j + C' j I) ⊓ splitCost C' i I)

end SendSplit.DPEquations


