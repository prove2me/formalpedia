-- Prove2me | Definitions.Def_SchedComplexity_Shops_Problems
-- name    : SchedComplexity_Shops_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:10:02.971144+00:00
-- url     : https://prove2.me/theorems/f3b46da4-81dc-4201-bbe1-8e87aac0565d
-- title:
--   The languages of n|2|F,r_n≥0|C_max, n|2|F,tree|C_max, n|2|G,m_j≤3|C_max and n|3|G,m_j≤2|C_max
-- statement:
--   This definition specifies the four target problems of Theorem 4(g)–(j) as languages of binary strings.
--
--   The problem classes are cut out of the general shop model by the parameters of the report's notation $n|m|\ell,\lambda|k$:
--
--   1. $\ell=F$ (**flow shop**): every job has $m_j=m$ operations with machine order $(M_1,\dots,M_m)$;
--   2. $\ell=G$, $m_j\le m_*$ (**job shop**): every job has between $1$ and $m_*$ operations, with an arbitrary machine order;
--   3. $r_n\ge 0$: every job except the last one, $J_n$, has release date $0$;
--   4. without a release-date parameter all release dates are $0$;
--   5. *tree*: the precedence graph is a branching; without *prec* or *tree* there are no precedence arcs.
--
--   For $m$ machines and a class $\mathcal C$ of instances, the language consists of the binary codes of the pairs (instance $I$, threshold $y\in\mathbb N$) such that $I\in\mathcal C$ and $I$ has a feasible schedule with $C_{\max}\le y$. The four languages are
--
--   $$n|2|F,r_n{\ge}0|C_{\max},\qquad n|2|F,\mathit{tree}|C_{\max},\qquad n|2|G,m_j{\le}3|C_{\max},\qquad n|3|G,m_j{\le}2|C_{\max}.$$
--
--   Instances outside the class are not in the language. These are the recognition versions (Section 2: "the existence of a solution with value $\le y$") of the problems to which Theorem 4 reduces KNAPSACK.
--
--   **Formalization Note** The code of an instance is the binary code (`encNats`, from `ProjSchedTW.Complexity.Encoding`) of the number list `ShopInstance.code`. The flow-shop condition constrains only the machine lists; processing times may be zero.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 4 (Section 2), pp. 6–7 (Section 3: F, G, r_n≥0, tree, m_j≤m_*), p. 16 (Theorem 4(g)–(j))

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_SchedComplexity_Shops_Model

namespace SchedComplexity.Shops

open CookPvsNP ProjSchedTW.Complexity

namespace ShopInstance

variable {n m : ℕ} (I : ShopInstance n m)

/-- `ℓ = F` (flow shop, p. 6): every job has `m_j = m` operations with machine order
`μ_j = (M_1, …, M_m)`. Only the machine list is constrained; processing times may be zero. -/
def IsFlowShop : Prop := ∀ j : Fin n, (I.ops j).map Prod.fst = List.finRange m

/-- `ℓ = G, m_j ≤ m_*` (general job shop with at most `m_*` operations per job, pp. 6–7): every
job has between `1` and `m_*` operations, with an arbitrary machine order (repetitions
allowed). -/
def IsJobShopOpsLE (mstar : ℕ) : Prop :=
  ∀ j : Fin n, 1 ≤ (I.ops j).length ∧ (I.ops j).length ≤ mstar

/-- `r_n ≥ 0` (p. 7): every job except the last one, `J_n`, has release date `0`. -/
def OnlyLastReleased : Prop := ∀ j : Fin n, j.val + 1 < n → I.release j = 0

/-- No `r_j` in `λ` (p. 6, "unless stated otherwise … `r_j = 0` for each `J_j`"). -/
def AllReleasedAtZero : Prop := ∀ j : Fin n, I.release j = 0

/-- No precedence constraints (neither `prec` nor `tree` in `λ`). -/
def NoPrec : Prop := I.prec = ∅

end ShopInstance

/-- The language of a scheduling problem with `m` machines whose instances form the class `C`
(Section 2, p. 4): the binary codes (`encNats` of `ShopInstance.code`) of the pairs
(instance `I`, threshold `y ∈ ℕ`) such that `I` belongs to the class and has a feasible
schedule with `C_max ≤ y`. Instances outside the class are not in the language. -/
def shopLang (m : ℕ) (C : ∀ {n : ℕ}, ShopInstance n m → Prop) : Lang BSym :=
  { x | ∃ (n : ℕ) (I : ShopInstance n m) (y : ℕ), C I ∧ I.HasScheduleLE y ∧
      x = encNats (I.code y) }

/-- `n|2|F,r_n≥0|C_max` (Theorem 4(g)): two-machine flow shop, release date `0` for every job but
the last, no precedence constraints. -/
def langFlowRn : Lang BSym :=
  shopLang 2 (fun I => I.IsFlowShop ∧ I.OnlyLastReleased ∧ I.NoPrec)

/-- `n|2|F,tree|C_max` (Theorem 4(h)): two-machine flow shop, all release dates `0`, precedence
constraints forming a branching. -/
def langFlowTree : Lang BSym :=
  shopLang 2 (fun I => I.IsFlowShop ∧ I.AllReleasedAtZero ∧ I.IsBranching)

/-- `n|2|G,m_j≤3|C_max` (Theorem 4(i)): two-machine job shop, at most three operations per job,
all release dates `0`, no precedence constraints. -/
def langJob2Ops3 : Lang BSym :=
  shopLang 2 (fun I => I.IsJobShopOpsLE 3 ∧ I.AllReleasedAtZero ∧ I.NoPrec)

/-- `n|3|G,m_j≤2|C_max` (Theorem 4(j)): three-machine job shop, at most two operations per job,
all release dates `0`, no precedence constraints. -/
def langJob3Ops2 : Lang BSym :=
  shopLang 3 (fun I => I.IsJobShopOpsLE 2 ∧ I.AllReleasedAtZero ∧ I.NoPrec)

end SchedComplexity.Shops


