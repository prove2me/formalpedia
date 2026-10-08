-- Prove2me | Definitions.Def_OptInapprox_Bal2Sat_Setting
-- name    : OptInapprox_Bal2Sat_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:21:22.546478+00:00
-- url     : https://prove2.me/theorems/78a87e1b-d1d5-4842-b2d6-66a11131ae34
-- title:
--   Definitions 10, 12, §7.2, Theorem 3 — weighted MAX-2SAT (TRUE = −1), balancedness, OPT, the vector relaxation SDP, β, hyperplane rounding
-- statement:
--   This file fixes the objects of the Balanced-MAX-2SAT algorithm of Khot, Kindler, Mossel and O'Donnell (proof of Theorem 4).
--
--   **Bits.** Following §7.2, the bit TRUE is the real number $-1$ and FALSE is $1$. An assignment of the variables $x_0,\dots,x_{n-1}$ is a point $x \in \{-1,1\}^n$.
--
--   **Instances (Definition 10).** A *literal* is a variable $x_i$ or its negation $\neg x_i$; arithmetically it is $y = r_i x_i$ with a sign $r_i \in \{-1,1\}$ ($r_i = -1$ for the negated variable). A literal is true exactly when $y = -1$. A weighted MAX-2SAT instance on $n$ variables is a finite list of clauses $C_1,\dots,C_m$, each a disjunction $(y \vee z)$ of exactly two literals (possibly on the same variable), together with nonnegative weights $w_{C} \ge 0$. The *satisfied weight* of an assignment $x$ is
--   $$
--   \mathrm{sat}(x) = \sum_{C} w_C\,[\,C \text{ is satisfied by } x\,],
--   $$
--   and the optimum is $\mathrm{OPT} = \max_{x \in \{-1,1\}^n} \mathrm{sat}(x)$.
--
--   **Balancedness (Definition 12).** The instance is *balanced* if for every variable $i$ the expected satisfied weight when $x_i$ is set to $1$ and the other variables are uniformly random equals the expected satisfied weight when $x_i$ is set to $-1$ and the others are uniformly random:
--   $$
--   \sum_{x:\,x_i = 1} \mathrm{sat}(x) = \sum_{x:\,x_i=-1} \mathrm{sat}(x)
--   $$
--   (both sides range over $2^{n-1}$ assignments, so the common factor $2^{-(n-1)}$ is dropped).
--
--   **The semidefinite relaxation.** For unit vectors $v_0,\dots,v_{n-1} \in \mathbb R^d$ ($v_i\cdot v_i = 1$), the relaxed objective is
--   $$
--   \mathrm{SDPobj}(v) = \sum_{C=(r_ix_i \vee r_jx_j)} w_C\Bigl(\tfrac34 - \tfrac14\,(r_iv_i)\cdot(r_jv_j)\Bigr),
--   $$
--   and $\mathrm{SDP}$ is the supremum of $\mathrm{SDPobj}(v)$ over all unit-vector families in every dimension $d$.
--
--   **The constant (Theorem 3).**
--   $$
--   \beta = \min_{\pi/2 \le \theta \le \pi} \frac{2 + (2/\pi)\theta}{3 - \cos\theta} \approx 0.943 .
--   $$
--
--   **Rounding.** Given unit vectors $v_i \in \mathbb R^d$ and a point $r \in \mathbb R^d$, the rounded assignment is $x_i = \operatorname{sgn}(r\cdot v_i)$, with $x_i = -1$ (TRUE) when $r\cdot v_i < 0$ and $x_i = 1$ (FALSE) otherwise.
--
--   These are the objects in which the paper's approximation guarantee for Balanced-MAX-2SAT is stated.
--
--   **Formalization Note** An assignment is `Fin n → Bool`, read through `pm true = -1`, `pm false = 1`; a literal is a pair `(i, r) : Fin n × Bool` with `r = true` for the negated variable. Weights are real with nonnegativity a field of the structure. Vectors of $\mathbb R^d$ are `Fin d → ℝ`, with the coordinate inner product `dot`. `OPT` is a `Finset.sup'` over the $2^n$ assignments. `sdpValue` is a real `sSup` of a set that is nonempty (take $d = 1$, all $v_i = 1$) and bounded above by $\sum_C w_C$, so the supremum is genuine. `beta` is the `sInf` of the image of the compact interval $[\pi/2, \pi]$ under a continuous function, hence the attained minimum. At $r\cdot v_i = 0$ the rounding outputs FALSE ($\operatorname{sgn} 0 = 1$); this tie has probability $0$ under a Gaussian $r$ and does not affect any expectation.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 12, Theorem 3 (β); p. 16, Definition 10 and §7.2 (TRUE = −1); p. 21, Definition 12 and the proof of Theorem 4 (OBJ, OPT, SDP, rounding)

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_Cube

namespace OptInapprox.Bal2Sat

noncomputable section

open Finset

/-- A literal `(i, r)` of MAX-2SAT (Definition 10, p. 16): the variable `xᵢ` if `r = false`,
its negation `¬xᵢ` if `r = true`. Arithmetically (proof of Theorem 4, p. 21) it is
`y = rᵢ xᵢ` with the sign `rᵢ = OptInapprox.MaxCut.pm r`. -/
abbrev Literal (n : ℕ) := Fin n × Bool

/-- Whether the literal `l = (i, r)` is true under the Boolean assignment `x`:
`xᵢ` is true iff `x i = true`, and `¬xᵢ` is true iff `x i = false`. -/
def litTrue {n : ℕ} (l : Literal n) (x : Fin n → Bool) : Bool :=
  if l.2 then !(x l.1) else x l.1

/-- The ±1 value `y = rᵢ xᵢ` of the literal `l = (i, r)` under `x` (TRUE ↦ −1). -/
def litVal {n : ℕ} (l : Literal n) (x : Fin n → Bool) : ℝ := OptInapprox.MaxCut.pm l.2 * OptInapprox.MaxCut.pm (x l.1)

/-- A 2-clause `(y ∨ z)` is satisfied iff one of its two literals is true. -/
def clauseSat {n : ℕ} (C : Literal n × Literal n) (x : Fin n → Bool) : Bool :=
  litTrue C.1 x || litTrue C.2 x

/-- A weighted MAX-2SAT instance on the variables `x₀, …, x_{n−1}` (Definition 10, p. 16):
`m` disjunctions of exactly two literals each, with a nonnegative weight function. The two
literals of a clause may involve the same variable. -/
structure Instance (n : ℕ) where
  /-- number of clauses -/
  m : ℕ
  /-- the `c`-th clause `(y ∨ z)`, as its pair of literals -/
  clause : Fin m → Literal n × Literal n
  /-- the weight of each clause -/
  w : Fin m → ℝ
  /-- weights are nonnegative -/
  w_nonneg : ∀ c, 0 ≤ w c

/-- The weighted MAX-2SAT objective of Definition 10: the total weight of the clauses satisfied
by the assignment `x`. -/
def satWeight {n : ℕ} (I : Instance n) (x : Fin n → Bool) : ℝ :=
  ∑ c, I.w c * (if clauseSat (I.clause c) x then 1 else 0)

/-- `OPT`, the optimum of the instance: the maximum of `satWeight I` over all `2ⁿ`
assignments (a finite nonempty set). -/
def OPT {n : ℕ} (I : Instance n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (satWeight I)

/-- Balancedness, Definition 12 (p. 21), for weighted MAX-2SAT: for each variable `i`, the
expected satisfied weight when `xᵢ` is set to `1` (FALSE) and the other variables are uniform
equals the expected satisfied weight when `xᵢ` is set to `−1` (TRUE) and the other variables
are uniform. Both conditional expectations are averages over `2ⁿ⁻¹` assignments, so the common
normalisation is dropped and the two sums are compared. -/
def IsBalanced {n : ℕ} (I : Instance n) : Prop :=
  ∀ i : Fin n,
    ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = false), satWeight I x =
      ∑ x ∈ Finset.univ.filter (fun x : Fin n → Bool => x i = true), satWeight I x

/-- The inner product `u · v = Σₖ uₖ vₖ` of two vectors of `ℝᵈ`, written in coordinates. -/
def dot {d : ℕ} (u v : Fin d → ℝ) : ℝ := ∑ k, u k * v k

/-- A family `v₀, …, v_{n−1}` of unit vectors of `ℝᵈ` (`vᵢ · vᵢ = 1`): a feasible point of the
vector (semidefinite) relaxation. -/
def IsUnitFamily {n d : ℕ} (v : Fin n → Fin d → ℝ) : Prop :=
  ∀ i, ∑ k, v i k ^ 2 = 1

/-- The objective of the semidefinite relaxation of the balanced objective
`OBJ = Σ_{C=(y∨z)} 3/4 − (1/4) y·z` (proof of Theorem 4, p. 21), with `xᵢ` replaced by the
vector `vᵢ`: a clause `(rᵢxᵢ ∨ rⱼxⱼ)` contributes `3/4 − (1/4)(rᵢvᵢ · rⱼvⱼ)`. -/
def sdpObj {n d : ℕ} (I : Instance n) (v : Fin n → Fin d → ℝ) : ℝ :=
  ∑ c, I.w c * (3 / 4 - 1 / 4 *
    (OptInapprox.MaxCut.pm (I.clause c).1.2 * OptInapprox.MaxCut.pm (I.clause c).2.2 *
      dot (v (I.clause c).1.1) (v (I.clause c).2.1)))

/-- `SDP`, the optimal value of the semidefinite program: the supremum of `sdpObj I v` over all
unit-vector families `v` in every dimension `d`. The set is nonempty (`d = 1`, all `vᵢ = 1`)
and bounded above by the total weight, so this real supremum is a genuine one. -/
def sdpValue {n : ℕ} (I : Instance n) : ℝ :=
  sSup {s : ℝ | ∃ (d : ℕ) (v : Fin n → Fin d → ℝ), IsUnitFamily v ∧ s = sdpObj I v}

/-- Theorem 3's constant (p. 12):
`β = min_{π/2 ≤ θ ≤ π} (2 + (2/π)θ) / (3 − cos θ)` (≈ 0.943). The function is continuous on the
compact interval, so the infimum is attained. -/
def beta : ℝ :=
  sInf ((fun θ : ℝ => (2 + 2 / Real.pi * θ) / (3 - Real.cos θ)) ''
    Set.Icc (Real.pi / 2) Real.pi)

/-- Random-hyperplane rounding (proof of Theorem 4, p. 21): given the unit vectors `vᵢ ∈ ℝᵈ` and
a realisation `r ∈ ℝᵈ` of the Gaussian vector, set `xᵢ = sgn(r · vᵢ)`, i.e. `xᵢ = −1` (TRUE) if
`r · vᵢ < 0` and `xᵢ = 1` (FALSE) otherwise (the tie `r · vᵢ = 0` has probability `0`). -/
def round {n d : ℕ} (v : Fin n → Fin d → ℝ) (r : Fin d → ℝ) : Fin n → Bool :=
  fun i => decide (dot r (v i) < 0)

end

end OptInapprox.Bal2Sat


