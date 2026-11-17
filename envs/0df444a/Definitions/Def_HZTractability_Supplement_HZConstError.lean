-- Prove2me | Definitions.Def_HZTractability_Supplement_HZConstError
-- name    : HZTractability_Supplement_HZConstError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:28:27.500948+00:00
-- url     : https://prove2.me/theorems/500973f0-ec11-4270-b2b4-ed7191e5c1e5
-- title:
--   Search problem: a normalized additive $\varepsilon$-equilibrium of an HZ market with utilities in $\{0,a,1\}$
-- statement:
--   For a rational middle value $a$ and a rational accuracy $\varepsilon$, an **instance** is an $N\times N$ rational utility matrix $u$ with $N\ge1$ and every entry $u_{ij}\in\{0,a,1\}$ (row $i$ is buyer $i$, column $j$ is good $j$); the same $a$ is used for all buyers. An **answer** is a rational allocation $x$ and rational prices $p$ that form a normalized additive $\varepsilon$-equilibrium of $u$ (Definition 2.2): $x\ge0$ feasible (all row and column sums equal to one), $p\ge0$ with $\min_j p_j=0$, and for every buyer $i$
--   $$p\cdot x_i\le1+\varepsilon,\qquad U_i(x_i)\ge V_i(p)-\varepsilon,$$
--   with $V_i(p)$ the budget-one optimum of (OptBundle).
--
--   This is the problem shown PPAD-hard in Theorem 1.2; unlike the problem of Theorem 1.1, its accuracy does not shrink with $N$.
--
--   **Formalization Note** It coincides with the published `HZTractability.HZThreeValue a ε` except that the accuracy is $\varepsilon$ instead of $\varepsilon/N$. Instances and answers are the published self-delimiting codes `CardinalMatching.encRatMatrix` / `encRatVec`; answers are rational.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Theorem 1.2, p.2 (PDF p.4); Definition 2.2, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_HZTractability_IsNormAddEq

set_option autoImplicit false

namespace HZTractability.Supplement

/-- **The constant-error search problem of Theorem 1.2** (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, Theorem 1.2, p.2 (PDF 4): "computing a normalized
additive ε0-equilibrium of an HZ market with utilities in {0, a, 1}").

For a rational middle value `a` and a rational accuracy `ε`: an instance is the code
`encRatMatrix N u` of an `N × N` rational utility matrix with `N ≥ 1` and every entry in `{0, a, 1}`
(row `i` = buyer `i`, column `j` = good `j`). An answer on it is the code
`encRatMatrix N x ++ encRatVec N p` of a rational allocation `x` and rational prices `p` forming a
normalized additive `ε`-equilibrium of `u` (Definition 2.2, the published `IsNormAddEq`).

**Formalization Note** Identical to the published `HZTractability.HZThreeValue a ε` except that the
accuracy is `ε` itself, not `ε/N`. Search problems are the published `TetrisHard.Rows.SearchProblem`;
codes are the published self-delimiting `CardinalMatching.encRatMatrix` / `encRatVec`. Answers are
rational (Lemma 4.11 supplies rational answers of polynomial length, p.19). The middle value `a` is
one value common to all buyers. -/
def HZConstError (a ε : ℚ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (N : ℕ) (u : Fin N → Fin N → ℚ), 1 ≤ N ∧
    (∀ i j, u i j = 0 ∨ u i j = a ∨ u i j = 1) ∧ s = CardinalMatching.encRatMatrix N u
  answer s t := ∃ (N : ℕ) (u : Fin N → Fin N → ℚ), 1 ≤ N ∧
    (∀ i j, u i j = 0 ∨ u i j = a ∨ u i j = 1) ∧ s = CardinalMatching.encRatMatrix N u ∧
    ∃ (x : Fin N → Fin N → ℚ) (p : Fin N → ℚ),
      t = CardinalMatching.encRatMatrix N x ++ CardinalMatching.encRatVec N p ∧
      IsNormAddEq (fun i j => (u i j : ℝ)) (ε : ℝ) (fun i j => (x i j : ℝ)) (fun j => (p j : ℝ))

end HZTractability.Supplement


