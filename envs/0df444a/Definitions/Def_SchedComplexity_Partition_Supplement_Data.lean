-- Prove2me | Definitions.Def_SchedComplexity_Partition_Supplement_Data
-- name    : SchedComplexity_Partition_Supplement_Data
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:23:14.420092+00:00
-- url     : https://prove2.me/theorems/746d35fa-ac49-4461-8322-790793d0af89
-- title:
--   Section 3 — weights, due dates and derived job quantities
-- statement:
--   A scheduling instance has jobs $J_1,\ldots,J_n$ and machines $M_1,\ldots,M_m$. Its operation lists, processing times, release dates and precedence arcs are the published general-shop data. This module adds a nonnegative integer weight $w_j$ and due date $d_j$ to every job. For natural-number start times, $B_j$ is the start of its first operation and $C_j$ the completion of its last operation. The derived quantities are
--
--   $$L_j=C_j-d_j,\qquad T_j=\max\{0,L_j\},\qquad U_j=\begin{cases}0&C_j\le d_j,\\1&C_j>d_j.\end{cases}$$
--
--   Lateness and tardiness are evaluated in the integers. The module also supplies the data changes specified in Theorem 1(i),(j),(k): all due dates can be set to zero; alternatively a first machine is added, its operation on job $j$ has duration $r_j$, old machine indices increase by one, and all release dates become zero. Weights and due dates are preserved by the latter construction.
--
--   These data extend the shared shop model without redefining operations or precedence. **Formalization Note** Jobs and machines are 0-based. Start times are natural numbers because the paper computes them from processing orders on nonnegative integer data (p. 6). Empty operation lists have $B_j=C_j=0$, extending the published completion convention; no positive-operation-count premise is added. Zero processing times are retained, as required by p. 12.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), Sections 2–3, pp. 4, 6–7; proof of Theorem 1(i)–(k), p. 9

import Mathlib
import Definitions.Def_SchedComplexity_Shops_Model

namespace SchedComplexity.Partition.Supplement

/-- Section 3, p. 6: the published shop data, extended only by weights and due dates.
All numeric data, including processing times and release dates, are nonnegative integers.
Jobs and machines are 0-based. The underlying operation lists may repeat machines.
Start times are natural numbers, as computed from processing orders on integer data in the
source. Zero operations are retained; their start and completion are defined as zero. -/
structure Instance (n m : ℕ) where
  shop : SchedComplexity.Shops.ShopInstance n m
  weight : Fin n → ℕ
  due : Fin n → ℕ

/-- First operation start B_j; zero for an empty operation list. -/
def beginning {n m : ℕ} (Q : SchedComplexity.Shops.ShopInstance n m)
    (S : Q.Op → ℕ) (j : Fin n) : ℕ :=
  if h : 0 < (Q.ops j).length then S ⟨j, ⟨0, h⟩⟩ else 0

/-- Signed lateness (p. 6); subtraction is in ℤ, never truncated. -/
def lateness {n m : ℕ} (I : Instance n m)
    (Q : SchedComplexity.Shops.ShopInstance n m) (S : Q.Op → ℕ) (j : Fin n) : ℤ :=
  (Q.completion S j : ℤ) - (I.due j : ℤ)

/-- Tardiness max(0,C_j-d_j), evaluated in ℤ. -/
def tardiness {n m : ℕ} (I : Instance n m)
    (Q : SchedComplexity.Shops.ShopInstance n m) (S : Q.Op → ℕ) (j : Fin n) : ℤ :=
  max 0 (lateness I Q S j)

/-- Indicator U_j of completing after the due date. -/
def lateIndicator {n m : ℕ} (I : Instance n m)
    (Q : SchedComplexity.Shops.ShopInstance n m) (S : Q.Op → ℕ) (j : Fin n) : ℕ :=
  if Q.completion S j ≤ I.due j then 0 else 1

/-- Theorem 1(i),(j), p. 9: set all due dates to zero. -/
def zeroDueDates {n m : ℕ} (I : Instance n m) : Instance n m :=
  { I with due := fun _ => 0 }

/-- Theorem 1(k), p. 9: add a first machine, shift the old machines by one, prepend
an operation of duration r_j to job j, and set all releases to zero. On the source class
only the last job can have nonzero r_j. Weight and due date are unchanged. -/
def absorbRelease {n m : ℕ} (I : Instance n m) : Instance n (m + 1) :=
  { shop :=
      { ops := fun j => (⟨0, Nat.zero_lt_succ m⟩, I.shop.release j) ::
          (I.shop.ops j).map (fun e => (e.1.succ, e.2))
        release := fun _ => 0
        prec := I.shop.prec }
    weight := I.weight
    due := I.due }

end SchedComplexity.Partition.Supplement


