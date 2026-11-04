-- Prove2me | Definitions.Def_ReverseLogisticsNEBS_fPlus
-- name    : ReverseLogisticsNEBS_fPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:06.355178+00:00
-- url     : https://prove2.me/theorems/a1dc9935-4e7f-4563-b8b9-0dce7a8b5f05
-- title:
--   Increasing and decreasing parts $f^\pm$ of a convex function, minimizers, and the Karush recursion
-- statement:
--   For a function $f:\mathbb R\to\mathbb R$ the module defines
--
--   $$
--   f^+(x) := \inf_{\theta \ge x} f(\theta), \qquad f^-(y) := \inf_{\theta \le y} f(\theta) - \inf_{\theta} f(\theta).
--   $$
--
--   For a convex $f$ with a finite minimizer $S$ these are exactly the paper's
--   $f^+(x) = f(S)$ if $x \le S$ and $f(x)$ otherwise, and $f^-(y) = f(y) - f(S)$ if $y \le S$ and $0$ otherwise: the increasing and the decreasing parts of $f$.
--
--   It also defines:
--
--   1. `HasMin f`: $f$ has a finite minimizer;
--   2. the set $\arg\min f$, and its infimum and supremum in the extended reals ($\pm\infty$ when the argmin is a ray);
--   3. the recursion of Lemma 1: from $v_1, \dots, v_N$, $w_1 := v_1$ and $w_j := v_j + w^-_{j-1}$.
--
--   These are the building blocks of the component cost functions of Theorem 3 and of the basestock levels of Theorem 4.
--
--   **Formalization Note** The infimum formulas are used so that $f^\pm$ does not depend on a choice of minimizer. Every statement that uses $f^\pm$ assumes that $f$ has a finite minimizer, so the junk value of `sInf` on a set unbounded below never enters a statement.
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), p.14 (the f^± notation), p.39 (Lemma 1, w_j := v_j + w^−_{j−1}), p.15 (inf/sup arg min in Theorem 4)

import Mathlib

namespace ReverseLogisticsNEBS

/-- **The increasing part `f^+`** of a function `f : ℝ → ℝ` (p.14): `f^+(x) = inf_{θ ≥ x} f(θ)`.

For a convex `f` with a finite minimizer `S` this is the paper's
`f^+(x) := f(S)` if `x ≤ S`, `f(x)` otherwise.

The module also defines the decreasing part `f^−`, the predicate "`f` has a finite minimizer",
the recursion `w_j := v_j + w^−_{j−1}` of Lemma 1 (p.39), and the extended-real levels
`inf arg min` and `sup arg min` used in Theorem 4 (p.15).

**Formalization Note.** The paper defines `f^±` only "for any convex function `f : ℝ → ℝ` with a
finite minimizer `S`"; there the infimum formulas above agree with it and do not depend on the
choice of `S`. Every statement using `f^±` assumes that `f` has a minimizer, so the junk value of
`sInf` on sets unbounded below never occurs in a statement. -/
noncomputable def fPlus (f : ℝ → ℝ) (x : ℝ) : ℝ := sInf (f '' Set.Ici x)

/-- **The decreasing part `f^−`** (p.14): `f^−(y) = inf_{θ ≤ y} f(θ) − inf_θ f(θ)`; for a convex
`f` with a finite minimizer `S` this is the paper's `f^−(y) := f(y) − f(S)` if `y ≤ S`, `0`
otherwise. -/
noncomputable def fMinus (f : ℝ → ℝ) (y : ℝ) : ℝ := sInf (f '' Set.Iic y) - sInf (Set.range f)

/-- `f` has a finite minimizer: some `S ∈ ℝ` with `f S ≤ f x` for all `x`. -/
def HasMin (f : ℝ → ℝ) : Prop := ∃ S, ∀ x, f S ≤ f x

/-- The set `arg min f` of minimizers of `f : ℝ → ℝ`. -/
def argminSet (f : ℝ → ℝ) : Set ℝ := {S | ∀ x, f S ≤ f x}

/-- `inf arg min_Y f(Y)` in the extended reals (`−∞` if the minimizers are unbounded below, `+∞`
if there is none). Used for `S^E_jt`, Theorem 4(a), p.15. -/
noncomputable def infArgmin (f : ℝ → ℝ) : EReal := sInf ((fun x : ℝ => (x : EReal)) '' argminSet f)

/-- `sup arg min_Y f(Y)` in the extended reals (`+∞` if the minimizers are unbounded above, `−∞`
if there is none). Used for `S^R_jt` and `S_jt`, Theorem 4(b)–(c), p.15. -/
noncomputable def supArgmin (f : ℝ → ℝ) : EReal := sSup ((fun x : ℝ => (x : EReal)) '' argminSet f)

/-- The recursion of **Lemma 1** (p.39): from functions `v_1, …, v_N` (indices `0, …, N − 1`),
`w_1 := v_1` and `w_j := v_j + w^−_{j−1}`. Indexed by `ℕ`; only indices `< N` are used. -/
noncomputable def karushW {N : ℕ} (v : Fin N → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun Y => if h : 0 < N then v ⟨0, h⟩ Y else 0
  | n + 1 => fun Y =>
      (if h : n + 1 < N then v ⟨n + 1, h⟩ Y else 0) + fMinus (karushW v n) Y

end ReverseLogisticsNEBS


