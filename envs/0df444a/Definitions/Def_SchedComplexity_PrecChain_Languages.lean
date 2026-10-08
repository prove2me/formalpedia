-- Prove2me | Definitions.Def_SchedComplexity_PrecChain_Languages
-- name    : SchedComplexity_PrecChain_Languages
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:03:00.168741+00:00
-- url     : https://prove2.me/theorems/1d639ad6-5fdc-4962-b489-f7ef09f58171
-- title:
--   Binary languages of n|m|I,prec,1≤p_j1≤p_*|C_max and n|m|I,prec,1≤p_j1≤p_*,w_j=1|Σw_jC_j
-- statement:
--   The recognition problems of Theorem 1(l) as languages over the four-letter alphabet $\{0, 1, -, \#\}$ of the published encoding `ProjSchedTW.Complexity.Encoding`.
--
--   1. The **code** of an instance $I$ with threshold $y$ lists, each in binary (least significant bit first) followed by a separator, the numbers $n$, $m$, then $p_1,\dots,p_n$, then the precedence matrix row by row ($1$ if $J_j < J_k$, else $0$), then $y$. The code determines $(I, y)$.
--   2. For a constant $p_*$, the language $L_{C_{\max}}(p_*)$ consists of the codes of pairs $(I, y)$ such that $I$ belongs to the class $n|m|I,\mathit{prec},1\le p_{j1}\le p_*$ and some feasible schedule of $I$ has $C_{\max} \le y$.
--   3. The language $L_{\Sigma C}(p_*)$ consists of the codes of pairs $(I, y)$ such that $I$ belongs to the same class and some feasible schedule of $I$ has $\sum_j C_j \le y$.
--
--   Following Section 2 of the paper, an optimization problem is replaced by the question whether a solution with value $\le y$ exists. These are the two sides of Theorem 1(l).
--
--   **Formalization Note** $p_*$ is a constant of the problem class (Section 3: "constant lower and upper bounds for the processing times"), so it is a parameter of the language and is not written in the code. All weights equal $1$ in the target problem, so they carry no data and are not written. Codes of instances outside the class are not in either language.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 4 (Section 2, recognition problems), pp. 6–7 (Section 3), p. 9, Theorem 1(l)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_SchedComplexity_PrecChain_Model

namespace SchedComplexity.PrecChain

open ProjSchedTW.Complexity (BSym encNats)

/-- The code of an instance `I` with threshold `y`: the numbers `n`, `m`, then `p_j` for
`j < n`, then the precedence matrix row by row (`1` if `J_j < J_k`, else `0`), then `y`, each in
binary (`encNats`). The code determines `(I, y)`: the separators delimit the numbers, `n` says
how many processing times and matrix entries follow. -/
def code (I : Instance) (y : ℕ) : List BSym :=
  encNats ([I.n, I.m] ++ List.ofFn I.p ++
    (List.ofFn fun j : Fin I.n => List.ofFn fun k : Fin I.n =>
      if I.prec j k then 1 else 0).flatten ++ [y])

/-- The recognition version of `n|m|I,prec,1≤p_j1≤p_*|C_max` for the constant `p_*`
(Section 2, p. 4; Section 3, pp. 6–7): codes of pairs `(I, y)` with `I` in the class and some
feasible schedule of `I` with `C_max ≤ y`. -/
def cmaxLang (pstar : ℕ) : CookPvsNP.Lang BSym :=
  { c | ∃ (I : Instance) (y : ℕ), I.InClass pstar ∧ CmaxYes I y ∧ c = code I y }

/-- The recognition version of `n|m|I,prec,1≤p_j1≤p_*,w_j=1|Σw_jC_j` for the constant `p_*`:
codes of pairs `(I, y)` with `I` in the class and some feasible schedule of `I` with
`Σ_j C_j ≤ y`. All weights equal `1`, so they carry no data and are not written. -/
def sumCLang (pstar : ℕ) : CookPvsNP.Lang BSym :=
  { c | ∃ (I : Instance) (y : ℕ), I.InClass pstar ∧ SumCYes I y ∧ c = code I y }

end SchedComplexity.PrecChain


