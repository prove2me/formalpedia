-- Prove2me | Definitions.Def_STOC2027BoolCSP_Approximation_Instance
-- name    : STOC2027BoolCSP_Approximation_Instance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:19.125635+00:00
-- url     : https://prove2.me/theorems/1072f32b-a2a1-4094-a8b6-57c4e5ba8475
-- title:
--   Boolean Max-$k$-CSP instances with rational weights, $\mathrm{val}_I$, $\mathrm{OPT}(I)$ and $\alpha_k$
-- statement:
--   An instance $I$ of Boolean Max-CSP consists of an explicit list of $n$ variables, each taking a value in $\{-1,1\}$, and a finite list of constraints. A constraint $C$ reads $r$ input positions; position $j$ reads the variable $\mathrm{scope}_C(j)$, and several positions may read the same variable. It carries an explicit truth table $P_C:\{-1,1\}^r\to\{0,1\}$ and a rational weight $w_C$.
--
--   The instance is a **Boolean Max-$k$-CSP instance with nonnegative rational weights** when every weight is nonnegative and every constraint is evaluated on at most $k$ distinct variables. Repeated positions are evaluated at the same variable, so a constraint listing a variable several times is the induced predicate on its distinct variables, and its arity is the number of distinct variables. Constant predicates, zero weights, empty constraint lists and $n=0$ are all allowed.
--
--   For an assignment $x\in\{-1,1\}^n$ the value and the optimum are
--   $$\mathrm{val}_I(x)=\sum_{C} w_C\,\mathbf 1\big[P_C(x_{\mathrm{scope}_C(1)},\dots,x_{\mathrm{scope}_C(r)})=1\big],\qquad \mathrm{OPT}(I)=\max_{x\in\{-1,1\}^n}\mathrm{val}_I(x),$$
--   the maximum being over all $2^n$ assignments (for $n=0$, the unique empty assignment). Finally $\alpha_k=(k+1)/2^k$ is the ratio of equation (1).
--
--   These are the objects of Theorem 1.1: the algorithm is measured against the true optimum of the original, unnormalized instance.
--
--   **Formalization Note** A sign $\pm1$ is a Boolean (`true` is $+1$, `sgnOf`). The truth table is a function on $\{-1,1\}^r$; its explicit $2^r$-bit table is the input encoding of `Def_..._Encoding`. `OPT` is `Finset.sup'` over the finite set of assignments.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 1, 5 (PDF 4, 8), equation (1) and Section 2 (instances, arity, value)

import Mathlib

namespace STOC2027BoolCSP.Approximation

/-- A Boolean value read as a sign in `{-1, 1}`: `true ↦ 1`, `false ↦ -1`. -/
def sgnOf (b : Bool) : ℝ := if b then 1 else -1

/-- A constraint of a Boolean CSP on the variables `Fin n` (Section 2, printed p. 5). It reads
`arity` input positions; position `j` reads the variable `scope j`, and positions may repeat a
variable. `pred` is its explicit truth table on the positions and `weight` its rational weight. -/
structure Constraint (n : ℕ) where
  arity : ℕ
  scope : Fin arity → Fin n
  pred : (Fin arity → Bool) → Bool
  weight : ℚ

/-- An instance of Boolean Max-CSP: an explicit list of `n` variables and a finite list of
constraints on them. -/
structure Instance where
  n : ℕ
  cons : List (Constraint n)

namespace Instance

/-- The instance is a Boolean Max-`k`-CSP instance with nonnegative rational weights: every
constraint is evaluated on at most `k` distinct variables (repeated positions count once), and
every weight is nonnegative. -/
def IsMaxkCSP (k : ℕ) (I : Instance) : Prop :=
  ∀ c ∈ I.cons, (Finset.univ.image c.scope).card ≤ k ∧ 0 ≤ c.weight

/-- The value `val_I(x) = Σ_C w_C · 1[P_C(x along the scope of C) = 1]` of an assignment. -/
noncomputable def val (I : Instance) (x : Fin I.n → Bool) : ℝ :=
  (I.cons.map (fun c => if c.pred (fun j => x (c.scope j)) then (c.weight : ℝ) else 0)).sum

/-- The optimum `OPT(I)`: the maximum of `val_I` over all `2^n` assignments (for `n = 0` the
unique empty assignment). -/
noncomputable def opt (I : Instance) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty I.val

end Instance

/-- The approximation ratio `α_k = (k+1)/2^k` of equation (1). -/
noncomputable def alpha (k : ℕ) : ℝ := ((k : ℝ) + 1) / 2 ^ k

end STOC2027BoolCSP.Approximation


