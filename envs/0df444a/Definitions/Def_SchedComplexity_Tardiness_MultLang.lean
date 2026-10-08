-- Prove2me | Definitions.Def_SchedComplexity_Tardiness_MultLang
-- name    : SchedComplexity_Tardiness_MultLang
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:52:58.817984+00:00
-- url     : https://prove2.me/theorems/a7280d08-2d74-4937-9b96-6394dca4fbd8
-- title:
--   The language of $n|1||\sum w_jT_j$ in the multiplicity encoding of the Remark (p. 23)
-- statement:
--   The Remark on p. 23 of the paper settles the polynomiality of the reductions 4(d) and 4(a), whose number of jobs is polynomial in $A$ and $a_*$ rather than in the length of the KNAPSACK input, "by characterizing a subset of jobs with identical data $(p_{jr},w_j,r_j,d_j)$ by its cardinality and a single copy of the data".
--
--   Accordingly an instance of $n|1||\sum w_jT_j$ is given here as a list of **job types** $(m_i,p_i,w_i,d_i)$, $i=1,\dots,k$: $m_i$ jobs with processing time $p_i$, weight $w_i$ and due date $d_i$ (release dates $0$). The **expanded instance** has the jobs $(i,\ell)$ with $\ell<m_i$, each carrying the data of its type. The code of an instance with threshold $y$ is
--
--   $$\mathrm{enc}\big(k,\;m_1,p_1,w_1,d_1,\;\dots,\;m_k,p_k,w_k,d_k,\;y\big),$$
--
--   all numbers in binary; it determines the list and $y$. The language consists of the codes whose expanded instance has a feasible schedule with $\sum_j w_jT_j\le y$.
--
--   **Formalization Note** Under the one-copy-per-job encoding the paper does not claim that its reduction is polynomial (the Remark), so the goal theorem targets this language. Every list of types is a valid instance (types with $m_i=0$ contribute no jobs).
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 23, Remark

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_SchedComplexity_Tardiness_Model

namespace SchedComplexity.Tardiness

open CookPvsNP ProjSchedTW.Complexity

/-- A job type of the multiplicity encoding (Remark, p. 23): `count` jobs with identical data
processing time `p`, weight `w` and due date `d` (release date `0`). -/
structure JobType where
  count : ℕ
  p : ℕ
  w : ℕ
  d : ℕ

/-- The jobs of the expanded instance of a list `L` of job types: the pairs `(i, k)` with `i` a type
and `k < count_i` a copy of it. -/
abbrev ExpandedJob (L : List JobType) : Type := Σ i : Fin L.length, Fin (L.get i).count

/-- Processing time of an expanded job: that of its type. -/
def expandP (L : List JobType) : ExpandedJob L → ℕ := fun x => (L.get x.1).p

/-- Weight of an expanded job: that of its type. -/
def expandW (L : List JobType) : ExpandedJob L → ℕ := fun x => (L.get x.1).w

/-- Due date of an expanded job: that of its type. -/
def expandD (L : List JobType) : ExpandedJob L → ℕ := fun x => (L.get x.1).d

/-- The code of an instance of `n|1||Σw_jT_j` in the multiplicity encoding together with the
threshold `y`: the number `k` of job types, then `count, p, w, d` of each type in turn, then `y`,
each in binary (`encNats`). The code determines `L` and `y`. -/
def multCode (L : List JobType) (y : ℕ) : List BSym :=
  encNats (L.length :: (L.flatMap fun c => [c.count, c.p, c.w, c.d]) ++ [y])

/-- The language of `n|1||Σw_jT_j` in the multiplicity encoding of the Remark on p. 23: codes of
pairs `(L, y)` such that the expanded instance (each type repeated `count` times) has a feasible
schedule with `Σ_j w_j T_j ≤ y`. -/
def wtLangMult : Lang BSym :=
  { x | ∃ (L : List JobType) (y : ℕ), x = multCode L y ∧
      HasScheduleLE (expandP L) (expandW L) (expandD L) y }

end SchedComplexity.Tardiness


