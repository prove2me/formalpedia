-- Prove2me | Definitions.Def_HZTractability_HZThreeValue
-- name    : HZTractability_HZThreeValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:08:34.316373+00:00
-- url     : https://prove2.me/theorems/66e4d367-439f-46a6-9bcc-6fc2eb9e2f26
-- title:
--   The search problem of Theorem 1.1: normalized additive $\varepsilon/N$-equilibria with utilities in $\{0,a,1\}$
-- statement:
--   Fix a rational middle value $a$ and a rational accuracy parameter $\varepsilon$. An **instance** is an $N\times N$ utility matrix $u$ with $N\ge 1$ and every entry in $\{0,a,1\}$ (row $i$ is buyer $i$, column $j$ is good $j$), written in binary. An **answer** on it is a rational allocation $x$ and rational prices $p$ forming a normalized additive $(\varepsilon/N)$-equilibrium of $u$ (Definition 2.2), where $N$ is the instance's number of buyers.
--
--   With $\varepsilon=\varepsilon^*(a)$ this is the problem that Theorem 1.1 proves PPAD-complete. The same middle value $a$ is used by all buyers.
--
--   **Formalization Note** Search problems are the public `TetrisHard.Rows.SearchProblem`; instances are `encRatMatrix N u` and answers `encRatMatrix N x ++ encRatVec N p` (public self-delimiting encodings). Answers are rational; Lemma 4.11 supplies rational answers of polynomial bit length.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Theorem 1.1, p.1 (PDF p.3); Definition 2.2, p.7

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_HZTractability_IsNormAddEq

namespace HZTractability

/-- **The search problem of Theorem 1.1** (Panageas–Shein–Taherijam–Vazirani, *Exploring the
Tractability Frontier of Hylland–Zeckhauser Models*, arXiv:2610.35848, held version, sha256
74b7bf9f…, Theorem 1.1, p.1 (PDF 3): "computing a normalized additive ε∗(a)/N-equilibrium of an
N-buyer HZ market … when all utilities belong to {0, a, 1}").

For a rational middle value `a` and a rational accuracy parameter `ε`: an instance is the code
`encRatMatrix N u` of an `N × N` rational utility matrix with `N ≥ 1` and every entry in
`{0, a, 1}` (row `i` = buyer `i`, column `j` = good `j`). An answer on it is the code
`encRatMatrix N x ++ encRatVec N p` of a rational allocation `x` and rational prices `p` that form a
normalized additive `(ε/N)`-equilibrium of `u` (Definition 2.2, `IsNormAddEq`), where `N` is the
instance's number of buyers.

**Formalization Note** Search problems are the public `TetrisHard.Rows.SearchProblem`; instances
and answers use the public self-delimiting `CardinalMatching.encRatMatrix` / `encRatVec`. The paper
does not fix an encoding; answers are taken rational (Lemma 4.11 supplies rational answers of
polynomial bit length). The middle value `a` is one value common to all buyers (p.1–2). -/
def HZThreeValue (a ε : ℚ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (N : ℕ) (u : Fin N → Fin N → ℚ), 1 ≤ N ∧
    (∀ i j, u i j = 0 ∨ u i j = a ∨ u i j = 1) ∧ s = CardinalMatching.encRatMatrix N u
  answer s t := ∃ (N : ℕ) (u : Fin N → Fin N → ℚ), 1 ≤ N ∧
    (∀ i j, u i j = 0 ∨ u i j = a ∨ u i j = 1) ∧ s = CardinalMatching.encRatMatrix N u ∧
    ∃ (x : Fin N → Fin N → ℚ) (p : Fin N → ℚ),
      t = CardinalMatching.encRatMatrix N x ++ CardinalMatching.encRatVec N p ∧
      IsNormAddEq (fun i j => (u i j : ℝ)) ((ε : ℝ) / N) (fun i j => (x i j : ℝ))
        (fun j => (p j : ℝ))

end HZTractability


