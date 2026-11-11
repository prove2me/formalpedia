-- Prove2me | Definitions.Def_IIDMultiItem_TwoPoint_Model
-- name    : IIDMultiItem_TwoPoint_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:55:53.359866+00:00
-- url     : https://prove2.me/theorems/19a64b93-7cf9-415a-9332-5cdbf8bda83d
-- title:
--   Finite multi-item auctions: type spaces, randomized mechanisms, supply, DSIC and ex-post IR, expected revenue (§2.1)
-- statement:
--   A seller has $m$ indivisible items and faces $n$ additive buyers. A **type space** consists of a finite set $T$ of types, a value vector $t=(t_1,\dots,t_m)$ for every type ($t_j$ is the value for item $j$) and a probability mass function $f$ on $T$; it is a **prior** when $f(t)>0$ for every $t$ and $\sum_t f(t)=1$. In the paper a value distribution $F$ has finite support $\mathrm{supp}(F)=\{a_1<\dots<a_K\}$ with $a_1>0$ and mass function $f$, and the type space is $T=\mathrm{supp}(F)^m$ with $f(t)=\prod_j f(t_j)$.
--
--   A profile of reports is $v=(v_1,\dots,v_n)\in T^n$, and $v_{-i}$ are the reports of the buyers other than $i$. A (direct, possibly randomized) **mechanism** $M=(x,s)$ assigns to every profile allocation probabilities $x_{ij}(v)$ and expected payments $s_i(v)\in\mathbb R$. It is **feasible** if $x_{ij}(v)\in[0,1]$ and the supply constraint holds:
--   $$\sum_{i=1}^n x_{ij}(v)\le 1\qquad(j\in[m],\ v\in T^n).\tag{2.1}$$
--   It is **deterministic** if every $x_{ij}(v)\in\{0,1\}$. With $u_i(t;v_{-i})=t\cdot x_i(t,v_{-i})-s_i(t,v_{-i})$, the mechanism is **DSIC and ex-post IR** if for all $i$, $v_{-i}$ and $t,t'\in T$
--   $$u_i(t';v_{-i})\ \ge\ t'\cdot x_i(t,v_{-i})-s_i(t,v_{-i}),\qquad u_i(t;v_{-i})\ge 0.\tag{2.2}$$
--   The **expected revenue** is $\mathrm{Rev}(M)=\mathbb E_v\sum_i s_i(v)=\sum_{v\in T^n}\big(\prod_i f(v_i)\big)\sum_i s_i(v)$, and $\mathrm{OPT}(F;n,m)$ is the largest expected revenue of a mechanism satisfying (2.1) and (2.2): it is stated as the greatest element of the set of these revenues. Finally $\max\{0,g_1,\dots,g_n\}$ is written `posMax g`.
--
--   **Formalization Note.** `TypeSpace T m` holds `val : T → Fin m → ℝ` and `pmf : T → ℝ`; `TypeSpace.IsPrior` says `pmf` is positive and sums to one; `FinPrior` is a finite distribution (positive support points, positive masses summing to one) and `FinPrior.typeSpace F m` is $\mathrm{supp}(F)^m$ with the product mass function. A `Mechanism T n m` is a pair of functions on profiles `Fin n → T`; buyer indices are `Fin n` and items `Fin m`. The others' reports $v_{-i}$ are the coordinates $\ell\ne i$ of a profile `v`, and `Function.update v i t` is the profile in which $i$ reports $t$. `payoff Ts i v w t` is $w\cdot x_i(t,v_{-i})-s_i(t,v_{-i})$ and `util Ts i v t` is $u_i(t;v_{-i})$. `admissibleRevenues Ts n` is the set of $\mathrm{Rev}(M)$ over all feasible, DSIC, ex-post IR mechanisms.
-- source:
--   Liu, Liu, Wang, Optimal Multi-Item Auctions with I.I.D. Values, arXiv:2610.11051 (held version, PDF of 2026-11-03, sha256 983080a4…), pp. 9–10 (PDF 11–12), §2.1, (2.1)–(2.2)

import Mathlib

open scoped BigOperators

/-!
# Finite multi-item auctions: types, randomized mechanisms, DSIC, ex-post IR, expected revenue

Liu, Liu, Wang, *Optimal Multi-Item Auctions with I.I.D. Values*, arXiv:2610.11051 (held version,
PDF of 2026-11-03, sha256 983080a4…), §2.1, pp. 9–10.

A seller has `m` items and faces `n` additive buyers. A buyer's type ranges over a finite type
space `T`; type `t` has value vector `val t : Fin m → ℝ` and probability `pmf t`. In the paper
`T = supp(F)^m` with the product mass function (`FinPrior.typeSpace`); Section 3 identifies a type
with the set of items valued high (the two-point type space is defined with the counts).

A (direct, possibly randomized) mechanism assigns to every profile `v : Fin n → T` allocation
probabilities `x v i j` and expected payments `s v i`. Buyer `i`'s report is coordinate `i` of the
profile; the reports `v_{-i}` of the others are the other coordinates, and `Function.update v i t`
is the profile in which buyer `i` reports `t` and the others report `v_{-i}`.
-/

namespace IIDMultiItem.TwoPoint

/-- A finite type space for `m` items: value vectors and a probability mass function on the
finite type `T`. Whether `pmf` is a positive probability mass function is the separate predicate
`TypeSpace.IsPrior`. -/
structure TypeSpace (T : Type) (m : ℕ) where
  /-- `val t j` is the value of type `t` for item `j`. -/
  val : T → Fin m → ℝ
  /-- `pmf t` is the probability of type `t`. -/
  pmf : T → ℝ

/-- Every type has positive probability and the probabilities sum to one. -/
def TypeSpace.IsPrior {T : Type} [Fintype T] {m : ℕ} (Ts : TypeSpace T m) : Prop :=
  (∀ t, 0 < Ts.pmf t) ∧ ∑ t, Ts.pmf t = 1

/-- A finite value distribution `F` (§2.1): finite support `supp` of positive points, with
positive probabilities `pmf` summing to one over the support. -/
structure FinPrior where
  /-- The support `supp(F) = {a_1 < ⋯ < a_K}`. -/
  supp : Finset ℝ
  /-- The probability mass function `f`. -/
  pmf : ℝ → ℝ
  supp_pos : ∀ x ∈ supp, 0 < x
  pmf_pos : ∀ x ∈ supp, 0 < pmf x
  pmf_sum : ∑ x ∈ supp, pmf x = 1

/-- The type space `T = supp(F)^m` with `f(t) = ∏_j f(t_j)` (§2.1). -/
def FinPrior.typeSpace (F : FinPrior) (m : ℕ) : TypeSpace (Fin m → F.supp) m where
  val t j := (t j : ℝ)
  pmf t := ∏ j, F.pmf (t j)

/-- A direct mechanism `M = (x, s)` for `n` buyers and `m` items on the type space `T`:
allocation probabilities `x v i j` and expected payments `s v i ∈ ℝ` (no sign restriction) at
every profile `v ∈ T^n`. -/
structure Mechanism (T : Type) (n m : ℕ) where
  x : (Fin n → T) → Fin n → Fin m → ℝ
  s : (Fin n → T) → Fin n → ℝ

namespace Mechanism

variable {T : Type} {n m : ℕ}

/-- Feasibility: `x_ij(v) ∈ [0, 1]` and the supply constraint (2.1) `∑_i x_ij(v) ≤ 1`. -/
def Feasible (M : Mechanism T n m) : Prop :=
  (∀ v i j, 0 ≤ M.x v i j ∧ M.x v i j ≤ 1) ∧ ∀ v j, ∑ i, M.x v i j ≤ 1

/-- The mechanism is deterministic: every `x_ij(v)` lies in `{0, 1}`. -/
def Deterministic (M : Mechanism T n m) : Prop :=
  ∀ v i j, M.x v i j = 0 ∨ M.x v i j = 1

/-- Utility of buyer `i` with true value vector `w` who reports `t` while the others report
`v_{-i}` (the other coordinates of `v`): `w · x_i(t, v_{-i}) − s_i(t, v_{-i})`. -/
def payoff (M : Mechanism T n m) (Ts : TypeSpace T m) (i : Fin n) (v : Fin n → T)
    (w t : T) : ℝ :=
  (∑ j, Ts.val w j * M.x (Function.update v i t) i j) - M.s (Function.update v i t) i

/-- `u_i(t; v_{-i}) = t · x_i(t, v_{-i}) − s_i(t, v_{-i})`. -/
def util (M : Mechanism T n m) (Ts : TypeSpace T m) (i : Fin n) (v : Fin n → T) (t : T) : ℝ :=
  M.payoff Ts i v t t

/-- DSIC and ex-post IR (2.2): for all `i`, `v_{-i}` and `t, t' ∈ T`,
`u_i(t'; v_{-i}) ≥ t' · x_i(t, v_{-i}) − s_i(t, v_{-i})` and `u_i(t; v_{-i}) ≥ 0`. -/
def DSIC_IR (M : Mechanism T n m) (Ts : TypeSpace T m) : Prop :=
  (∀ i v t t', M.payoff Ts i v t' t ≤ M.util Ts i v t') ∧ ∀ i v t, 0 ≤ M.util Ts i v t

/-- Expected revenue `Rev_F(M) = E_v ∑_i s_i(v)`, the reports independent with mass function
`pmf`. -/
def Rev [Fintype T] (M : Mechanism T n m) (Ts : TypeSpace T m) : ℝ :=
  ∑ v : Fin n → T, (∏ i, Ts.pmf (v i)) * ∑ i, M.s v i

/-- The values `Rev(M)` of all mechanisms satisfying (2.1) and (2.2): `OPT(F; n, m)` is the
greatest element of this set (`IsGreatest`). -/
def admissibleRevenues [Fintype T] (Ts : TypeSpace T m) (n : ℕ) : Set ℝ :=
  {r | ∃ M : Mechanism T n m, M.Feasible ∧ M.DSIC_IR Ts ∧ M.Rev Ts = r}

end Mechanism

/-- `max{0, g_1, …, g_n}` (equal to `0` when `n = 0`). -/
noncomputable def posMax {n : ℕ} (g : Fin n → ℝ) : ℝ :=
  (insert (0 : ℝ) (Finset.univ.image g)).max' (Finset.insert_nonempty _ _)

end IIDMultiItem.TwoPoint


