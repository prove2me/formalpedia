-- Prove2me | Definitions.Def_PochetWolsey_Variants_SalesModel
-- name    : PochetWolsey_Variants_SalesModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:31.954804+00:00
-- url     : https://prove2.me/theorems/e22a7de3-93d2-4060-9c0f-d9e71b43a472
-- title:
--   Nonnegative-demand lot-sizing with bounded sales
-- statement:
--   Let $n\ge1$ be a finite horizon. Period $t$ has fixed demand $d_t\ge0$ and potential sales $u_t\ge0$. A positive constant $M$ is at least $\sum_t(d_t+u_t)$. A point consists of production $x$, sales $v$, and setups $y$. The feasible set is defined by
--   $$x_t\ge0,\quad 0\le v_t\le u_t,\quad y_t\in\{0,1\},\quad x_t\le My_t,$$
--   $$\sum_{j\le t}x_j\ge\sum_{j\le t}(d_j+v_j),\qquad \sum_jx_j=\sum_j(d_j+v_j).$$
--   The cumulative inequalities express nonnegative inventory, and total balance fixes both endpoint stocks at zero. A regeneration pattern consists of period sets $I\subseteq J$ and $H$: setups are the indicator of $J$, sales equal $u_t$ on $H$ and zero elsewhere, and each $t\in I$ produces the entire demand plus sales from $t$ up to the next member of $I$, or the horizon end if none exists. Production is zero outside $I$.
--
--   These definitions support the extreme-point characterization without defining the feasible set by the claimed characterization.
--
--   **Formalization Note** The three real arrays are stored as $(x,v,y)$. Period $t$ in the book corresponds to index $t-1$ in $\mathrm{Fin}(n)$. The standing predicate imposes nonnegative demands only for this subsection, not for Section 11.1.1.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 338 (PDF 351), Section 11.1.2 and constraints (11.1)–(11.4); DOI 10.1007/0-387-33477-7

import Mathlib

open scoped BigOperators

namespace PochetWolsey.Variants

abbrev SalesPoint (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ)

structure SalesModel (n : ℕ) where
  d : Fin n → ℝ
  u : Fin n → ℝ
  M : ℝ

def SalesModel.Standing {n : ℕ} (D : SalesModel n) : Prop :=
  0 < n ∧ (∀ t, 0 ≤ D.d t ∧ 0 ≤ D.u t) ∧
  0 < D.M ∧ (∑ t, (D.d t + D.u t)) ≤ D.M

def SalesModel.feasible {n : ℕ} (D : SalesModel n) : Set (SalesPoint n) :=
  {w | (∀ t, 0 ≤ w.1 t ∧ 0 ≤ w.2.1 t ∧ w.2.1 t ≤ D.u t ∧
        (w.2.2 t = 0 ∨ w.2.2 t = 1) ∧ w.1 t ≤ D.M * w.2.2 t) ∧
    (∀ t, (∑ j ∈ Finset.univ.filter (fun j => j ≤ t), (w.2.1 j + D.d j)) ≤
      ∑ j ∈ Finset.univ.filter (fun j => j ≤ t), w.1 j) ∧
    (∑ j, w.1 j) = ∑ j, (w.2.1 j + D.d j)}

noncomputable def SalesModel.regenerationPattern {n : ℕ} (D : SalesModel n)
    (w : SalesPoint n) : Prop :=
  ∃ I J H : Finset (Fin n), I ⊆ J ∧
    (∀ t, w.2.2 t = if t ∈ J then 1 else 0) ∧
    (∀ t, w.2.1 t = if t ∈ H then D.u t else 0) ∧
    (∀ t, w.1 t = if t ∈ I then
      ∑ r ∈ Finset.univ.filter (fun r => t ≤ r ∧ ∀ j ∈ I, t < j → r < j),
        (w.2.1 r + D.d r) else 0)

end PochetWolsey.Variants


