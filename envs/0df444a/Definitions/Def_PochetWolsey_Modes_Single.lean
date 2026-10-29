-- Prove2me | Definitions.Def_PochetWolsey_Modes_Single
-- name    : PochetWolsey_Modes_Single
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:59.326099+00:00
-- url     : https://prove2.me/theorems/100fa834-82ff-464b-afaa-2587827d5bad
-- title:
--   One-setup binary models and flow formulations
-- statement:
--   Let $I=\{0,\ldots,m\}$ include an idle item and let the periods be $0,\ldots,n$. Write $y_i(t)$ for setup, $\chi_{ij}(t)$ for the change from $i$ in period $t$ to $j$ in period $t+1$, and $z_i(t)$ for startup of $i$ in period $t+1$. All discrete coordinates are real-valued binary indicators. The original changeover set has one setup per period and
--   $$\chi_{ij}(t)\ge y_i(t)+y_j(t+1)-1,\qquad \chi_{ij}(t)\le y_i(t),y_j(t+1).$$
--   The original startup set has one setup per period and
--   $$z_i(t)\ge y_i(t+1)-y_i(t),\qquad z_i(t)\le y_i(t+1),\quad z_i(t)\le1-y_i(t).$$
--   The flow polyhedron uses unit boxes, $\sum_i y_i(0)=1$, $y_i(t)=\sum_j\chi_{ij}(t)$ and $\sum_i\chi_{ij}(t)=y_j(t+1)$. The startup polyhedron uses unit boxes, one setup per period, the first two startup inequalities, and
--   $$z_i(t)+\sum_{j\ne i}(y_j(t+1)-z_j(t))\le1-y_i(t).$$
--   These are separate binary sets and continuous constraint systems; no hull equality is built into their definitions.
--
--   **Formalization Note** The graph has $n+1$ periods $0,\ldots,n$ and $n$ internal transitions. A transition index $t$ connects periods $t$ and $t+1$ and stores the book’s changeover or startup at the latter period. No transition into the first period is recorded, consistently with (12.2)–(12.3), which apply only from the second period onward. There are $m+1$ labels including idle label $0$.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 377 (PDF 388), Section 12.2.2, pp. 376–378, Eqs. (12.1)–(12.4)

import Mathlib

namespace PochetWolsey.Modes

abbrev Item (m : ℕ) := Fin (m + 1)
abbrev Grid (m n : ℕ) := Item m → Fin (n + 1) → ℝ
abbrev EdgeGrid (m n : ℕ) := Item m → Fin n → ℝ
abbrev ChangeGrid (m n : ℕ) := Item m → Item m → Fin n → ℝ

def Binary {α : Type*} (x : α → ℝ) : Prop := ∀ a, x a = 0 ∨ x a = 1

def UnitBox {α : Type*} (x : α → ℝ) : Prop := ∀ a, 0 ≤ x a ∧ x a ≤ 1

/-- Original one-setup changeover constraints, with only internal transitions recorded. -/
def singleChangeSet (m n : ℕ) : Set (Grid m n × ChangeGrid m n) :=
  {p | (∀ i, Binary (p.1 i)) ∧ (∀ i j, Binary (p.2 i j)) ∧
    (∀ t, ∑ i, p.1 i t = 1) ∧
    (∀ i j t, p.2 i j t ≥ p.1 i t.castSucc + p.1 j t.succ - 1 ∧
      p.2 i j t ≤ p.1 i t.castSucc ∧ p.2 i j t ≤ p.1 j t.succ)}

/-- Equations (12.1)--(12.4), after relabeling the first period as 0. -/
def singleFlowPolyhedron (m n : ℕ) : Set (Grid m n × ChangeGrid m n) :=
  {p | (∀ i, UnitBox (p.1 i)) ∧ (∀ i j, UnitBox (p.2 i j)) ∧
    (∑ i, p.1 i 0 = 1) ∧
    (∀ i t, p.1 i t.castSucc = ∑ j, p.2 i j t) ∧
    (∀ j t, ∑ i, p.2 i j t = p.1 j t.succ)}

/-- Original binary startup model; starts are recorded on internal transitions. -/
def singleStartupSet (m n : ℕ) : Set (Grid m n × EdgeGrid m n) :=
  {p | (∀ i, Binary (p.1 i)) ∧ (∀ i, Binary (p.2 i)) ∧
    (∀ t, ∑ i, p.1 i t = 1) ∧
    (∀ i t, p.2 i t ≥ p.1 i t.succ - p.1 i t.castSucc ∧
      p.2 i t ≤ p.1 i t.succ ∧ p.2 i t ≤ 1 - p.1 i t.castSucc)}

/-- Proposition 12.4, on the same internal transitions as (12.2)--(12.3). -/
def singleStartupPolyhedron (m n : ℕ) : Set (Grid m n × EdgeGrid m n) :=
  {p | (∀ i, UnitBox (p.1 i)) ∧ (∀ i, UnitBox (p.2 i)) ∧
    (∀ t, ∑ i, p.1 i t = 1) ∧
    (∀ i t, p.2 i t ≥ p.1 i t.succ - p.1 i t.castSucc ∧
      p.2 i t ≤ p.1 i t.succ ∧
      p.2 i t + ∑ j ∈ Finset.univ.erase i, (p.1 j t.succ - p.2 j t)
        ≤ 1 - p.1 i t.castSucc)}

end PochetWolsey.Modes


