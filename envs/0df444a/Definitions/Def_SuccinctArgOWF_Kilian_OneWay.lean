-- Prove2me | Definitions.Def_SuccinctArgOWF_Kilian_OneWay
-- name    : SuccinctArgOWF_Kilian_OneWay
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:09:38.759248+00:00
-- url     : https://prove2.me/theorems/a0902461-2842-4088-948a-7dbf5527c431
-- title:
--   Definitions 3.2–3.3 — injective and exponentially hard one-way functions
-- statement:
--   A function $f:\{0,1\}^n\to\{0,1\}^{d}$, $d=d(n)$, denotes a family $\{f_n\}$ given by one map on $\{0,1\}^*$ (§3.2).
--
--   1. $f$ is *computable in polynomial time* if one machine computes $f(x)$ within $p(|x|)$ steps for a polynomial $p$.
--   2. $f$ is *injective* on $\{0,1\}^n$ if $f(x_0)\neq f(x_1)$ for all distinct $x_0,x_1\in\{0,1\}^n$ (Definition 3.3).
--   3. For $t,n\in\mathbb N$ and $\epsilon\in[0,1]$, $f$ is $(t,\epsilon)$*-one-way* on $\{0,1\}^n$ (Definition 3.2) if every adversary $A$ of running time at most $t$ (worst case over all inputs of the output length of $f$ on $\{0,1\}^n$ and over its random tape) satisfies
--
--   $$\Pr_{x\leftarrow\{0,1\}^n}\bigl[f(A(f(x)))=f(x)\bigr]\le\epsilon ,$$
--
--   where the probability is also over the coins of $A$ and the output of $A$ must lie in $\{0,1\}^n$.
--   4. $f$ is *exponentially hard with constants* $\delta,\zeta$ if $f$ is $(2^{\delta n},2^{-\zeta n})$-one-way for all sufficiently large $n$.
--
--   These are the hardness assumptions of Theorem 4.1, Corollary 6.3 and Corollary 6.5.
--
--   **Formalization Note** The real budget $2^{\delta n}$ enters through its floor; running times are natural numbers, so this changes no adversary.
-- source:
--   Jesko Dujmovic, Daniel Wichs, STOC 2027 submission #650 (October 2026), §3.2, Definitions 3.2 and 3.3, pp. 7–8 (PDF pp. 9–10)

import Mathlib
import Definitions.Def_SuccinctArgOWF_Kilian_Machines

set_option autoImplicit false

namespace SuccinctArgOWF.Kilian

/-! # One-way functions (§3.2, Definitions 3.2–3.3)

A function `f : {0,1}^n → {0,1}^d` is a family `{f_n}` given by one map `f : {0,1}^* → {0,1}^*`
restricted to each input length. -/

open MetaSearch.Heyting

/-- `f` is computable in polynomial time (§3.2): one machine computes `f(x)` within `p(|x|)` steps
for a polynomial `p`. -/
def PolyTime (f : Str → Str) : Prop :=
  ∃ (M : Machine) (p : Polynomial ℕ), ∀ x : Str, M.evalWithin x (p.eval x.length) = some (f x)

/-- `f` is injective on `{0,1}^n` (Definition 3.3). -/
def InjectiveAt (f : Str → Str) (n : ℕ) : Prop :=
  ∀ x₀ x₁ : Str, x₀.length = n → x₁.length = n → x₀ ≠ x₁ → f x₀ ≠ f x₁

/-- The inputs an inverter for `f` on `{0,1}^n` may receive: one invocation (phase `0`) on any
string of the output length of `f` on `{0,1}^n`. -/
def invSched (f : Str → Str) (n : ℕ) : Set (List (ℕ × Str)) :=
  {sch | ∃ x y : Str, x.length = n ∧ y.length = (f x).length ∧ sch = [(0, y)]}

/-- The success probability `Pr_{x ← {0,1}^n}[f(A(f(x))) = f(x)]` of an adversary `A` with random tape
of length `t` (output: component `1` of its single invocation, which must lie in `{0,1}^n`); the
probability is over `x` and the coins of `A`. -/
noncomputable def invProb (f : Str → Str) (n t : ℕ) (A : Adv) : ℝ :=
  prob fun xω : (Fin n → Bool) × (Fin t → Bool) =>
    let x := List.ofFn xω.1
    let a := outC (A.outs (List.ofFn xω.2) [] [(0, f x)]) 0 1
    a.length = n ∧ f a = f x

/-- Definition 3.2: `f` is `(t, ε)`-one-way on `{0,1}^n` if every adversary of running time at most
`t` inverts `f(x)`, `x ← {0,1}^n`, with probability at most `ε`. -/
def OneWayAt (f : Str → Str) (n t : ℕ) (ε : ℝ) : Prop :=
  ∀ A : Adv, A.RunsWithin t [] (invSched f n) → invProb f n t A ≤ ε

/-- `f` is `(2^{δn}, 2^{-ζn})`-one-way for all sufficiently large `n` (exponential hardness with the
constants `δ, ζ`, Definition 3.2). The real budget `2^{δn}` is used through its floor, since running
times are natural numbers. -/
def ExpHard (f : Str → Str) (δ ζ : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ n ≥ n₀, OneWayAt f n ⌊(2 : ℝ) ^ (δ * n)⌋₊ ((2 : ℝ) ^ (-(ζ * n)))

end SuccinctArgOWF.Kilian


