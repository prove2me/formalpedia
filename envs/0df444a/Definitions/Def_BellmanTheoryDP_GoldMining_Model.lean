-- Prove2me | Definitions.Def_BellmanTheoryDP_GoldMining_Model
-- name    : BellmanTheoryDP_GoldMining_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:30:56.637087+00:00
-- url     : https://prove2.me/theorems/3bd28cbe-b267-4388-bff6-427ac2d21e0c
-- title:
--   Bellman's two-mine gold-mining problem: choice sequences, expected return and the optimal return $f(x,y)$
-- statement:
--   This definition sets up Problem 2 of Bellman's *The theory of dynamic programming* (1954), the stochastic gold-mining problem.
--
--   There are two gold mines, Anaconda ($A$) and Bonanza ($B$), holding initial amounts $x$ and $y$ of gold, and one machine. A use of the machine in Anaconda succeeds with probability $p$, mines a fraction $r$ of the gold currently there, and leaves the machine undamaged; with probability $1-p$ it mines nothing and the machine is destroyed. In Bonanza the corresponding numbers are $q$ and $s$. As long as the machine is undamaged, the operator chooses which mine to use next.
--
--   Since the only thing an operator ever observes is that the machine is still working, a policy is a **choice sequence** $\sigma = (\sigma_0, \sigma_1, \dots)$ with $\sigma_n \in \{A, B\}$, the mine used at use number $n$ (counting from $0$) if the machine has survived until then. Write $a_n(\sigma)$ and $b_n(\sigma)$ for the numbers of uses of $A$ and of $B$ among uses $0, \dots, n-1$, and $\pi_A = p$, $\pi_B = q$. Use $n$ collects
--   $$g_n(\sigma; x, y) = \begin{cases} r\,x\,(1-r)^{a_n(\sigma)} & \sigma_n = A,\\ s\,y\,(1-s)^{b_n(\sigma)} & \sigma_n = B,\end{cases}$$
--   and it does so exactly when uses $0, \dots, n$ all succeed, which has probability $\prod_{k=0}^{n} \pi_{\sigma_k}$. The **expected return** of $\sigma$ is
--   $$J(\sigma; x, y) = \sum_{n=0}^{\infty} \Big(\prod_{k=0}^{n} \pi_{\sigma_k}\Big)\, g_n(\sigma; x, y),$$
--   and the **optimal return**, Bellman's (8.1), is
--   $$f(x, y) = \sup_{\sigma} J(\sigma; x, y),$$
--   the supremum over all choice sequences.
--
--   These are the objects in terms of which the functional equation (8.2) and the decision rule (8.3) are stated.
--
--   **Formalization Note** The mines are the two-element type `Mine`, a choice sequence is a function `ℕ → Mine`, and all quantities are real numbers. The series is a real `tsum` and the supremum a real `iSup`; for parameters $p, q, r, s \in (0,1)$ and $x, y \ge 0$ the terms are nonnegative and every partial sum is at most $x + y$, so the series converges and the family of returns is bounded above (stated as the separate theorem `expectedReturn_le_add`), and neither Lean junk value ($0$ for a divergent series or an unbounded supremum) occurs. The definitions themselves carry no hypotheses on the parameters; the theorems do.
-- source:
--   Bellman, The theory of dynamic programming, Bull. Amer. Math. Soc. 60 (1954), p. 508, Section 8, Problem 2 and Eq. (8.1)

import Mathlib

namespace BellmanTheoryDP.GoldMining

/-- The two gold mines of Bellman's Problem 2: Anaconda (`A`) and Bonanza (`B`). -/
inductive Mine
  | A
  | B
  deriving DecidableEq

/-- A (pure) policy for Problem 2: the mine chosen at use number `n = 0, 1, 2, …`, applied as
long as the machine is undamaged. The only information a policy ever receives is that the
machine is still undamaged, so every history-dependent pure policy is such a sequence. -/
abbrev ChoiceSeq := ℕ → Mine

/-- Number of uses of Anaconda among the first `n` uses (uses `0, …, n-1`). -/
def usesA (σ : ChoiceSeq) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun k => σ k = Mine.A)).card

/-- Number of uses of Bonanza among the first `n` uses (uses `0, …, n-1`). -/
def usesB (σ : ChoiceSeq) (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun k => σ k = Mine.B)).card

/-- Probability that one use of the machine in the given mine succeeds (leaves it undamaged):
`p` in Anaconda, `q` in Bonanza. -/
def successProb (p q : ℝ) : Mine → ℝ
  | Mine.A => p
  | Mine.B => q

/-- Probability that uses `0, 1, …, n` all succeed, i.e. that the gold of use `n` is collected:
`∏_{k ≤ n} (p if σ k = A, q if σ k = B)`. -/
def survival (p q : ℝ) (σ : ChoiceSeq) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (n + 1), successProb p q (σ k)

/-- Gold mined by use number `n` if it succeeds, starting from `x` in Anaconda and `y` in
Bonanza: a fraction `r` of what is left in Anaconda, `r * x * (1 - r) ^ (usesA σ n)`, or a
fraction `s` of what is left in Bonanza, `s * y * (1 - s) ^ (usesB σ n)`. -/
def gain (r s : ℝ) (σ : ChoiceSeq) (x y : ℝ) (n : ℕ) : ℝ :=
  match σ n with
  | Mine.A => r * x * (1 - r) ^ usesA σ n
  | Mine.B => s * y * (1 - s) ^ usesB σ n

/-- Expected amount of gold mined before the machine is damaged, using the choice sequence `σ`
from initial amounts `x` (Anaconda) and `y` (Bonanza):
`J σ x y = ∑_{n ≥ 0} survival n * gain n`. -/
noncomputable def expectedReturn (p q r s : ℝ) (σ : ChoiceSeq) (x y : ℝ) : ℝ :=
  ∑' n : ℕ, survival p q σ n * gain r s σ x y n

/-- Bellman's (8.1): `f(x, y)`, the expected amount of gold mined before the machine is damaged
using an optimal policy, i.e. the supremum of `expectedReturn` over all choice sequences. -/
noncomputable def optimalReturn (p q r s x y : ℝ) : ℝ :=
  ⨆ σ : ChoiceSeq, expectedReturn p q r s σ x y

end BellmanTheoryDP.GoldMining


