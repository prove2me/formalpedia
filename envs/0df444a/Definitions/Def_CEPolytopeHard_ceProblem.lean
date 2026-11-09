-- Prove2me | Definitions.Def_CEPolytopeHard_ceProblem
-- name    : CEPolytopeHard_ceProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:46.395876+00:00
-- url     : https://prove2.me/theorems/4b62a9d3-999d-4273-9283-32a30971a20f
-- title:
--   Search problem: $\varepsilon(N)$-correlated equilibrium with at most $N^C$ support profiles
-- statement:
--   For a number of players $n_0$, a real $C \ge 1$ and an accuracy function $\varepsilon : \mathbb N \to \mathbb R$, the search problem $\mathrm{CE}(n_0, C, \varepsilon)$ is:
--
--   1. **Instance.** The encoding $s$ of a valid multilinear polytope game $G$ with exactly $n_0$ players; $N = |s|$ is its encoding length.
--   2. **Answer.** The encoding of a list $L$ of pairs (rational weight $w \ge 0$, rational profile of the shape of $G$) with $\sum w = 1$, whose listed distribution $\mu_L$ is an $\varepsilon(N)$-correlated equilibrium of $G$ and has at most $N^C$ support profiles:
--   $$
--   |\operatorname{supp} \mu_L| \le N^C .
--   $$
--
--   This is the problem of Theorem 4: "computing an $\epsilon$-correlated equilibrium supported on at most $N^C$ profiles in a multilinear game on explicit rational polytopes".
--
--   **Formalization Note** The support counts distinct profiles of positive weight. The accuracy is fixed with the problem as a function of $N$. No bound is placed on the length of an answer.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Theorem 4, p.6 (restated p.19); Sections 2.1, 2.3, pp.10–11

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CEPolytopeHard_MLGame
import Definitions.Def_CEPolytopeHard_MLGame_Valid
import Definitions.Def_CEPolytopeHard_MLGame_encode
import Definitions.Def_CEPolytopeHard_IsApproxCE
import Definitions.Def_CEPolytopeHard_encodeDist

set_option autoImplicit false

namespace CEPolytopeHard

/-- The **search problem of computing an ε-correlated equilibrium with support at most `N^C`** in
an `n₀`-player multilinear polytope game (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang,
*The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version
of November 2, 2026, sha256 6aec500a…7820, Theorem 4, p.6: "Let N be the binary encoding length of
the game’s description. For every fixed C ≥ 1, computing an ϵ-correlated equilibrium supported on
at most N^C profiles in a multilinear game on explicit rational polytopes").

* An instance is the encoding `s` of a valid multilinear polytope game `G` with exactly `n₀`
  players; `N = |s|`.
* An answer is the encoding of a list `L` of pairs `(w, p)` of a rational weight and a rational
  profile of the shape of `G`, with every `w ≥ 0` and `∑ w = 1`, such that the listed
  distribution (equal profiles merged) is an `ε(N)`-correlated equilibrium of `G` whose support
  (distinct profiles of positive weight) has at most `N^C` elements.

**Formalization Note** The accuracy `ε` is a function of `N`, fixed with the problem. `C` is real
and `N^C` is the real power. There is no bound on the length of an answer. -/
def ceProblem (n₀ : ℕ) (C : ℝ) (ε : ℕ → ℝ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ G : MLGame, G.encode = s ∧ G.Valid ∧ G.n = n₀
  answer s t := ∃ G : MLGame, G.encode = s ∧ G.Valid ∧ G.n = n₀ ∧
    ∃ L : List (ℚ × List (List ℚ)), encodeDist L = t ∧ (∀ e ∈ L, G.Shaped e.2) ∧
      (∀ e ∈ L, 0 ≤ e.1) ∧ (L.map Prod.fst).sum = 1 ∧
      IsApproxCE G.strategySet G.utility (ε s.length) (G.distOf L) ∧
      ((G.distOf L).support.card : ℝ) ≤ (s.length : ℝ) ^ C

end CEPolytopeHard


