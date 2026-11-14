-- Prove2me | Definitions.Def_NarrowDNF_BourgainDuality
-- name    : NarrowDNF_BourgainDuality
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:58:55.720203+00:00
-- url     : https://prove2.me/theorems/c4dda740-c134-4b97-a616-f82409600fe4
-- title:
--   Weighted four-thirds moments and their signed cube-root dual witnesses
-- statement:
--   Let $A$ be a finite set and let $w,f:A\to\mathbb R$. Define the unnormalized weighted four-thirds moment by
--   $$M_{4/3}(w,f)=\sum_{a\in A}w(a)|f(a)|^{4/3}.$$
--   No normalization of $w$ is implicit. When $w$ is nonnegative this is the usual weighted $L^{4/3}$ moment; positivity and any total-mass assumptions are hypotheses of later inequalities rather than conditions hidden in the definition.
--
--   For a real number $t$, define the signed cube-root witness
--   $$d(t)=\begin{cases}|t|^{1/3},&t\ge0,\\-|t|^{1/3},&t<0.\end{cases}$$
--   The choice makes the dual pairing and fourth moment naturally involve the same power $|t|^{4/3}$. This explicit scalar witness is used in finite weighted Holder duality and in transporting fourth-moment contraction through self-adjoint operators. The bundle supplies the moment and witness formulas; the contraction and duality estimates are separate theorem nodes.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainDuality.lean#L76-L77
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainDuality.lean#L17-L19

import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace NarrowDNF.BourgainDuality
end NarrowDNF.BourgainDuality


/-!
# Finite fourth-moment duality

Weighted Hölder and finite self-adjoint operator duality used by the Bourgain
square-function proof. Every weight is explicit; zero weights are allowed.
-/
noncomputable section
open scoped BigOperators
namespace NarrowDNF.BourgainDuality

variable {α : Type*} [Fintype α]

/-- Weighted L(4/3) moment; using a moment instead of a norm keeps the final
contraction statement free of extraneous outer fractional powers. -/
def moment43 (w f : α → ℝ) : ℝ := ∑ x, w x * |f x| ^ (4/3 : ℝ)







/-- The pointwise extremizer for L(4/3)-L4 duality. -/
def dual43 (t : ℝ) : ℝ := if 0 ≤ t then |t| ^ (1/3 : ℝ) else -|t| ^ (1/3 : ℝ)









end NarrowDNF.BourgainDuality


