-- Prove2me | Definitions.Def_FedergruenTzur_MinPred_RankedList
-- name    : FedergruenTzur_MinPred_RankedList
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:52:57.005559+00:00
-- url     : https://prove2.me/theorems/1cfb25a5-b2b4-4764-bdcc-4bfb6ed9de2f
-- title:
--   Ranked candidate lists of Theorem 1, their g-values g(1) = D(j), g(l) = G(i_l, i_{l−1}), and condition (6)
-- statement:
--   Fix $j \ge 1$. A set $S = \{i_1, \dots, i_r\} \subseteq \{1, \dots, j\}$ is **ranked** as in Theorem 1 of Federgruen and Tzur if its elements are numbered in nonascending order of their $\tilde C$-values,
--   $$
--   \tilde C(i_1) \ge \tilde C(i_2) \ge \dots \ge \tilde C(i_r),
--   $$
--   with periods of equal $\tilde C$-value ranked in ascending order of their indices: if $\tilde C(i_k) = \tilde C(i_{k+1})$ then $i_k < i_{k+1}$. The **critical values** of the ranked list are
--   $$
--   g(1) = D(j), \qquad g(l) = G(i_l, i_{l-1}) \quad (l = 2, \dots, r),
--   $$
--   with $G$ the symmetrically extended root (5), and **condition (6)** is
--   $$
--   g(1) < g(2) < \dots < g(r) < \infty. \tag{6}
--   $$
--
--   Condition (6) is the test of the paper's main theorem: a ranked superset of $\Omega(j)$ equals $\Omega(j)$ exactly when (6) holds.
--
--   **Formalization Note.** A ranked set is a duplicate-free list `L = [i_1, …, i_r]` of periods in $\{1,\dots,j\}$ in which every earlier entry $a$ and later entry $b$ satisfy $\tilde C(b) < \tilde C(a)$, or $\tilde C(a) = \tilde C(b)$ and $a < b$. Lean lists are 0-based: `gval j L m` is the paper's $g(m+1)$ and `L.getD m 0` is $i_{m+1}$. The values are extended reals (`EReal`), so $g(l) = \pm\infty$ is kept, and the final conjunct "$< \infty$" of (6) is part of the condition. For the empty list (6) reduces to $D(j) < \infty$.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, p. 915, THEOREM 1 (ranking of S, definition of g(1), …, g(r), condition (6))

import Mathlib
import Definitions.Def_FedergruenTzur_MinPred_Breakpoint

/-!
# Federgruen–Tzur (1991), Theorem 1: ranked candidate lists, their `g`-values and condition (6)

A. Federgruen and M. Tzur, Management Science 37(8), 1991, §2, p. 915, Theorem 1.

A set `S = {i_1, …, i_r} ⊆ {1, …, j}` ranked as in Theorem 1 is a list `L = [i_1, …, i_r]`:
* `IsRanked j L`: the entries are distinct periods in `{1, …, j}` ordered by nonascending `C̃`-value,
  with equal `C̃`-values ranked in ascending order of period index, i.e. for every earlier entry `a`
  and later entry `b`: `C̃(b) < C̃(a)`, or `C̃(a) = C̃(b)` and `a < b`.
* `gval j L m` is the paper's `g(m + 1)` (Lean lists are 0-based, the paper is 1-based):
  `g(1) = D(j)` and `g(l) = G(i_l, i_{l-1})` for `l = 2, …, r`.
* `Cond6 j L` is condition (6): `g(1) < g(2) < ⋯ < g(r) < ∞`.

**Formalization Note.** `L.getD m 0` is the paper's `i_{m+1}`; out-of-range indices are never used
in `gval` for `m < L.length`. For the empty list `Cond6` reduces to `D(j) < ∞`, which is true.
-/

namespace FedergruenTzur.MinPred

namespace LotSizing

variable (P : LotSizing)

/-- `L` lists distinct periods of `{1, …, j}` in nonascending order of `C̃`, ties broken by
ascending period index. -/
def IsRanked (j : ℕ) (L : List ℕ) : Prop :=
  L.Nodup ∧ (∀ i ∈ L, 1 ≤ i ∧ i ≤ j) ∧
    L.Pairwise (fun a b => P.Ctil b < P.Ctil a ∨ (P.Ctil a = P.Ctil b ∧ a < b))

/-- The `g`-values of Theorem 1, 0-based: `gval j L 0 = D(j)` (the paper's `g(1)`) and, for
`m ≥ 1`, `gval j L m = G(i_{m+1}, i_m)` (the paper's `g(m + 1)`), with `i_{m+1} = L.getD m 0`. -/
noncomputable def gval (j : ℕ) (L : List ℕ) (m : ℕ) : EReal :=
  if m = 0 then ((P.D j : ℝ) : EReal) else P.G (L.getD m 0) (L.getD (m - 1) 0)

/-- Condition (6): `g(1) < g(2) < ⋯ < g(r) < ∞`. -/
def Cond6 (j : ℕ) (L : List ℕ) : Prop :=
  (∀ m, m + 1 < L.length → P.gval j L m < P.gval j L (m + 1)) ∧
    P.gval j L (L.length - 1) < ⊤

end LotSizing

end FedergruenTzur.MinPred


