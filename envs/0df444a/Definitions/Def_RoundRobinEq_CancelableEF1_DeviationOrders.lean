-- Prove2me | Definitions.Def_RoundRobinEq_CancelableEF1_DeviationOrders
-- name    : RoundRobinEq_CancelableEF1_DeviationOrders
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:18:15.539986+00:00
-- url     : https://prove2.me/theorems/f2ce97b0-c509-496f-963c-d769d704bb35
-- title:
--   pp. 11, 20 — round order of A′_i, allocation-time order of A_j, the parity split Y_1, Y_2, and Algorithm 3 orders
-- statement:
--   Fix a profile $\succ$, an agent $i$ and a deviation $\succ'_i$, and let $(A'_1, \dots, A'_n)$ be the output of Round-Robin$(\succ'_i, \succ_{-i})$ while $(A_1, \dots, A_n)$ is that of Round-Robin$(\succ)$. With $m = kn$, the proofs of Theorems 4.4 and 4.5 use the following orderings.
--
--   1. $A'_i = \{x_1, \dots, x_k\}$, where $x_r$ is the good agent $i$ receives in round $r$ of Round-Robin$(\succ'_i, \succ_{-i})$; $X^{r} = \{x_1, \dots, x_r\}$ denotes a prefix (with $X^0 = \emptyset$).
--   2. For another agent $j$, $A_j = \{y_1, \dots, y_k\}$, indexed in the order in which these goods are allocated in Round-Robin$(\succ'_i, \succ_{-i})$.
--   3. $A_j \setminus \{y_1\}$ is split into $Y_1 = \{y_3, y_5, \dots\}$ (odd indices) and $Y_2 = \{y_2, y_4, \dots\}$ (even indices), so that $|Y_1| = \lfloor (k-1)/2 \rfloor$ and $|Y_2| = \lceil (k-1)/2 \rceil$.
--   4. (Algorithm 3) Given $x_1, x_2, \dots$, a set $Y$ and a valuation $v$, Algorithm 3 fills positions $j = |Y|, \dots, 1$ in turn, putting in position $j$ a good $y'_j$ of minimum marginal value $v(\,\cdot \mid \{x_1, \dots, x_{j-1}\})$ among the goods of $Y$ not yet placed. An ordering $(y'_1, \dots, y'_{|Y|})$ of $Y$ is an **Algorithm 3 order** if it arises this way for some tie-breaking, that is, if for every $j$ and every $t \le j$,
--   $$v(y'_j \mid \{x_1, \dots, x_{j-1}\}) \le v(y'_t \mid \{x_1, \dots, x_{j-1}\}).$$
--
--   These orderings are how the proof of Theorem 4.5 compares the goods agent $j$ keeps in equilibrium with the goods agent $i$ obtains by deviating.
--
--   **Formalization Note** Sequences are functions `ℕ → M` read on $0, \dots, k-1$, so the paper's $x_r$ is `x (r-1)`, and `xPrefix x r` is $\{x_1, \dots, x_r\}$ (the image of indices $< r$). `IsRoundEnum σ' i k x` says that the good picked at agent $i$'s step $r n + i$ (0-based) is `x r` for each $r < k$. `IsTimeEnum σ' A k y` says that `y` is injective on $\{0, \dots, k-1\}$ with image $A$ and that a smaller index is never allocated later in the run of `σ'`. In 0-based indices $Y_1$ is the image of the even indices $a \ge 2$ and $Y_2$ that of the odd indices. `IsAlg3Order v x Y z` characterises the outputs of Algorithm 3 for every tie-breaking; the paper breaks ties lexicographically, so statements quantified over all Algorithm 3 orders cover the paper's.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 11, Algorithm 3; p. 20, proof of Theorem 4.4 (x_r, y_r, Y_1, Y_2); p. 21, proof of Theorem 4.5

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableEF1_Setting

namespace RoundRobinEq.CancelableEF1

/-! The orderings used in the proofs of Theorems 4.4 and 4.5, §4.2, pp. 20–21, and Algorithm 3,
p. 11, of Amanatidis et al., arXiv:2301.13652v1. Sequences are maps `ℕ → M` read on `0, …, k − 1`:
the paper's `x_r` (1-based) is `x (r − 1)`. -/

variable {M : Type*} [DecidableEq M]

/-- `{x_1, …, x_r}` in the paper's 1-based notation: the image of `x` on the indices `0, …, r − 1`
(so `xPrefix x 0 = ∅` and `xPrefix x (r − 1)` is the paper's `{x_1, …, x_{r−1}}`). -/
def xPrefix (x : ℕ → M) (r : ℕ) : Finset M :=
  (Finset.range r).image x

variable [Fintype M] {n : ℕ} [NeZero n]

/-- `x_1, …, x_k` are the goods agent `i` receives in Round-Robin(σ'), indexed by round: for every
0-based round `r < k`, the good picked at agent `i`'s step `r·n + i` is `x r` (p. 20: "`x_r` was
allocated in round `r`"). -/
def IsRoundEnum (σ' : Fin n → List M) (i : Fin n) (k : ℕ) (x : ℕ → M) : Prop :=
  ∀ r < k, pick σ' (r * n + i.val) = some (x r)

/-- `y_1, …, y_k` enumerates the set `A` (of `k` goods) in the order in which its goods are
allocated in Round-Robin(σ') (p. 20): `y` is injective on `0, …, k − 1` with image `A`, and a good
with a smaller index is allocated no later than one with a larger index. -/
def IsTimeEnum (σ' : Fin n → List M) (A : Finset M) (k : ℕ) (y : ℕ → M) : Prop :=
  Set.InjOn y (Finset.range k : Set ℕ) ∧ (Finset.range k).image y = A ∧
    ∀ a b : ℕ, a < b → b < k → ∀ t : ℕ, y b ∈ allocBefore σ' t → y a ∈ allocBefore σ' t

/-- `Y_1` (p. 20): the goods of `A_j \ {y_1}` with odd (1-based) index, i.e.
`{y_3, y_5, …}`; 0-based, the indices `a < k` with `a ≥ 2` even. -/
def Y1 (y : ℕ → M) (k : ℕ) : Finset M :=
  ((Finset.range k).filter (fun a => 2 ≤ a ∧ a % 2 = 0)).image y

/-- `Y_2` (p. 20): the goods of `A_j \ {y_1}` with even (1-based) index, i.e.
`{y_2, y_4, …}`; 0-based, the odd indices `a < k`. -/
def Y2 (y : ℕ → M) (k : ℕ) : Finset M :=
  ((Finset.range k).filter (fun a => a % 2 = 1)).image y

/-- `(z_1, …, z_{|Y|})` is an output of Algorithm 3 (p. 11) on input `X = (x_1, x_2, …)`, `Y` and
`v`, for some tie-breaking: `z` lists `Y` without repetition, and for every (0-based) position
`r < |Y|` the good `z r` minimizes the marginal value `v(· | {x_1, …, x_r})` (1-based: position
`j = r + 1` and prefix `{x_1, …, x_{j−1}}`) over the goods `z 0, …, z r` not yet placed when
Algorithm 3, running `j = |Y|, …, 1`, fills position `j`. -/
def IsAlg3Order (v : Finset M → ℝ) (x : ℕ → M) (Y : Finset M) (z : ℕ → M) : Prop :=
  Set.InjOn z (Finset.range Y.card : Set ℕ) ∧ (Finset.range Y.card).image z = Y ∧
    ∀ r < Y.card, ∀ t ≤ r, RoundRobinEq.CancelableBluff.marginal v {z r} (xPrefix x r) ≤ RoundRobinEq.CancelableBluff.marginal v {z t} (xPrefix x r)

end RoundRobinEq.CancelableEF1


