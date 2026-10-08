-- Prove2me | Definitions.Def_FedergruenTzur_MinPred_Model
-- name    : FedergruenTzur_MinPred_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:14:58.750517+00:00
-- url     : https://prove2.me/theorems/72947c9e-2def-4870-8ac2-912aa9221778
-- title:
--   The dynamic lot size model of §1 and the zero-inventory recursion (2): D, H, c_ij, C̃, S, F(t) and F(l, t)
-- statement:
--   The **dynamic lot size model** of Federgruen and Tzur (§1) is specified, for periods $i = 1, 2, \dots$, by
--
--   1. the demand $d_i$,
--   2. the setup cost $K_i$,
--   3. the variable per unit order cost $c_i$,
--   4. the cost $h_i$ of carrying a unit of inventory at the end of period $i$.
--
--   Starting inventory in period 1 and ending inventory at the horizon are zero. The auxiliary notation is: the cumulative demand $D(i) = \sum_{k=1}^{i} d_k$ and cumulative holding cost $H(i) = \sum_{k=1}^{i} h_k$ (so $D(0) = H(0) = 0$); for $i < j$, $h_{ij} = h_i + h_{i+1} + \dots + h_{j-1}$ and $c_{ij} = c_i + h_{ij}$, the cost of ordering a unit in period $i$ and carrying it till period $j$; $\tilde C(i) = c_i - H(i-1)$; and the carrying cost under zero-inventory ordering of an order placed in period $i$ that covers the demands of periods $i, \dots, j$,
--   $$
--   S(i, j) = \sum_{r=i}^{j-1} h_r \bigl(D(j) - D(r)\bigr).
--   $$
--
--   The costs are given by the zero-inventory recursion (2): $F(0) = 0$, and for $1 \le l \le t$
--   $$
--   F(l, t) = F(l-1) + K_l + S(l, t) + c_l\,[D(t) - D(l-1)], \qquad F(t) = \min_{1 \le l \le t} F(l, t).
--   $$
--   Here $F(l, t)$ is the cost of the first $t$ periods when the last setup is in period $l$, and $F(t)$ the minimum cost of the first $t$ periods.
--
--   These objects underlie every statement of the mission: the comparison of two candidate last setup periods, the breakpoints $G(k,l)$, and the Minimal Optimal Predecessors lists $\Omega(j)$.
--
--   **Formalization Note.** The data are four functions $\mathbb N \to \mathbb R$ bundled in a structure `LotSizing`; their values at index $0$ are never used. No sign assumptions are made. $F$ is *defined* by the recursion (2) (with $F(0) = 0$ as in Step 0 of the paper's Algorithm). The paper justifies (2) as the minimum cost over all feasible policies by Lemma 1 (Wagner–Whitin: an optimal zero-inventory ordering policy exists), which is not part of this mission. The horizon $n$ is not a parameter, since every statement only involves periods up to a given $t$. The file also contains the structural unfolding lemma $F(t+1) = \min_{1 \le l \le t+1} F(l, t+1)$.
-- source:
--   Federgruen and Tzur, A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models with n Periods in O(n log n) or O(n) Time, Management Science 37(8), 1991, pp. 912–913, §1 (notation) and eq. (2); F(0) = 0 from the Algorithm, Step 0, p. 918

import Mathlib

/-!
# Federgruen–Tzur (1991), §1: the dynamic lot size model and the recursion (2)

A. Federgruen and M. Tzur, *A Simple Forward Algorithm to Solve General Dynamic Lot Sizing Models
with n Periods in O(n log n) or O(n) Time*, Management Science 37(8), 1991, §1, pp. 912–913.

The data of the model are the demands `d i`, setup costs `K i`, variable per unit order costs `c i`
and unit holding costs `h i` of the periods `i = 1, 2, …` (the values at index `0` are never used).
The auxiliary notation of p. 912 is
* `D i = ∑_{k=1}^{i} d k` (cumulative demand; `D 0 = 0`),
* `H i = ∑_{k=1}^{i} h k` (cumulative holding cost; `H 0 = 0`),
* `cij i j = c i + h i + ⋯ + h (j-1)` (the paper's `c_{ij} = c_i + h_{ij}`),
* `Ctil i = c i - H (i - 1)` (the paper's `C̃(i)`),
* `S i j = ∑_{r=i}^{j-1} h r * (D j - D r)` (zero-inventory carrying cost of an order in `i` covering
  the demands of `i, …, j`).

The costs are those of the zero-inventory recursion (2), p. 913, with `F(0) = 0` (Step 0 of the
Algorithm, p. 918):
* `Flast l t = Fopt (l - 1) + K l + S l t + c l * (D t - D (l - 1))` is `F(l, t)` of (2);
* `Fopt t = min_{1 ≤ l ≤ t} F(l, t)` for `t ≥ 1` and `Fopt 0 = 0`.

**Formalization Note.** `Fopt` is *defined* by the recursion (2). Its identification with the
minimum cost over all feasible policies is Lemma 1 of the paper (Wagner–Whitin), which is not
formalized here. The horizon `n` is not a parameter: every statement only uses periods `≤ t`.
No sign assumptions are imposed on the data.
-/

namespace FedergruenTzur.MinPred

/-- The data of the dynamic lot size model of §1 (p. 912): demand `d i`, setup cost `K i`,
variable per unit order cost `c i` and unit holding cost `h i` (end of period `i`), for periods
`i = 1, 2, …`. -/
structure LotSizing where
  d : ℕ → ℝ
  K : ℕ → ℝ
  c : ℕ → ℝ
  h : ℕ → ℝ

namespace LotSizing

variable (P : LotSizing)

/-- Cumulative demand `D(i) = ∑_{k=1}^{i} d_k`. -/
def D (i : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 i, P.d k

/-- Cumulative holding cost `H(i) = ∑_{k=1}^{i} h_k`. -/
def H (i : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 i, P.h k

/-- `c_{ij} = c_i + h_i + h_{i+1} + ⋯ + h_{j-1}`: cost of ordering a unit in `i` and carrying it
till `j`. -/
def cij (i j : ℕ) : ℝ := P.c i + ∑ r ∈ Finset.Ico i j, P.h r

/-- `C̃(i) = c_i - H(i - 1)`. -/
def Ctil (i : ℕ) : ℝ := P.c i - P.H (i - 1)

/-- `S(i, j) = ∑_{r=i}^{j-1} h_r (D(j) - D(r))`. -/
def S (i j : ℕ) : ℝ := ∑ r ∈ Finset.Ico i j, P.h r * (P.D j - P.D r)

/-- `F(t)`: `F(0) = 0` and, for `t ≥ 1`, `F(t) = min_{1 ≤ l ≤ t} F(l, t)` with `F(l, t)` given by
the recursion (2). -/
noncomputable def Fopt : ℕ → ℝ
  | 0 => 0
  | t + 1 => (Finset.Icc 1 (t + 1)).attach.inf' (by simp)
      (fun l => Fopt (l.1 - 1) + P.K l.1 + P.S l.1 (t + 1) + P.c l.1 * (P.D (t + 1) - P.D (l.1 - 1)))
decreasing_by
  have := (Finset.mem_Icc.mp l.2).2
  omega

/-- `F(l, t) = F(l - 1) + K_l + S(l, t) + c_l [D(t) - D(l - 1)]`, the recursion (2). -/
noncomputable def Flast (l t : ℕ) : ℝ :=
  P.Fopt (l - 1) + P.K l + P.S l t + P.c l * (P.D t - P.D (l - 1))

theorem Fopt_zero : P.Fopt 0 = 0 := by
  rw [Fopt]

theorem Fopt_succ (t : ℕ) :
    P.Fopt (t + 1) = (Finset.Icc 1 (t + 1)).inf' (by simp) (fun l => P.Flast l (t + 1)) := by
  rw [Fopt]
  apply le_antisymm
  · exact Finset.le_inf' _ _ fun l hl =>
      Finset.inf'_le (fun l : Finset.Icc 1 (t + 1) => P.Flast l.1 (t + 1)) (Finset.mem_attach _ ⟨l, hl⟩)
  · exact Finset.le_inf' _ _ fun l _ => Finset.inf'_le (fun l => P.Flast l (t + 1)) l.2

end LotSizing

end FedergruenTzur.MinPred


