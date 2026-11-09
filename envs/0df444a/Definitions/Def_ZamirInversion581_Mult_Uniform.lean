-- Prove2me | Definitions.Def_ZamirInversion581_Mult_Uniform
-- name    : ZamirInversion581_Mult_Uniform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:57.698398+00:00
-- url     : https://prove2.me/theorems/1cc73885-0a8c-4b94-b2c5-1cc5641a105e
-- title:
--   Uniform mean, variance and probability on a finite type
-- statement:
--   For a finite type $\alpha$ and $g:\alpha\to\mathbb R$, this file defines the three quantities that every probability in Section 2 of the paper reduces to:
--
--   $$
--   \mathbb E_x[g(x)]=\frac1{|\alpha|}\sum_{x\in\alpha}g(x),\qquad \mathrm{Var}_x(g)=\mathbb E_x\bigl[(g(x)-\mathbb E[g])^2\bigr],\qquad \Pr_x[p(x)]=\frac{|\{x:p(x)\}|}{|\alpha|}.
--   $$
--
--   All three are plain finite averages, so a statement using them involves no measure theory.
--
--   **Formalization Note** All index types used in this mission (matrices, vectors, $\mathrm{GL}_m(F)$, and their products) are nonempty, so the denominator is nonzero wherever these are used.
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.6–10, §2, uniform distributions over matrices, vectors and invertible matrices; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib

set_option autoImplicit false

namespace ZamirInversion581.Mult

/-!
# Uniform expectation, variance and probability on a finite type

Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256
175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, §2, pp.6–10: every probability in
§2 is over uniform matrices, vectors or invertible matrices. All index types used in this mission
are nonempty, so the denominators below are nonzero there; on an empty type Lean's `x / 0 = 0`
would apply, and no item uses that case.
-/

/-- `E_{x ∼ α}[g x]` for `x` uniform on the finite type `α`. -/
noncomputable def unifMean {α : Type*} [Fintype α] (g : α → ℝ) : ℝ :=
  (∑ x, g x) / (Fintype.card α : ℝ)

/-- `Var_{x ∼ α}(g x) = E[(g x − E[g])²]` for `x` uniform on the finite type `α`. -/
noncomputable def unifVar {α : Type*} [Fintype α] (g : α → ℝ) : ℝ :=
  unifMean fun x => (g x - unifMean g) ^ 2

open Classical in
/-- `Pr_{x ∼ α}[p x]` for `x` uniform on the finite type `α`. -/
noncomputable def unifProb {α : Type*} [Fintype α] (p : α → Prop) : ℝ :=
  ((Finset.univ.filter p).card : ℝ) / (Fintype.card α : ℝ)

end ZamirInversion581.Mult


