-- Prove2me | Definitions.Def_ProcessingNetworks_PathCompact_ConvergesUOC
-- name    : ProcessingNetworks_PathCompact_ConvergesUOC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:29:31.016905+00:00
-- url     : https://prove2.me/theorems/202ef27a-1a8d-427d-9bae-4317bd7353e1
-- title:
--   Definition A.6 — uniform convergence on compact sets (u.o.c.) of paths in $D^d$
-- statement:
--   Let $D^d$ denote the set of paths $x:\mathbb R_+\to\mathbb R^d$ that are right continuous on $\mathbb R_+$ and have left limits on $(0,\infty)$, and for $t>0$ let $\|x\|_t=\sup_{0\le s\le t}|x(s)|$, where $|\cdot|$ is the $\ell^1$ norm on $\mathbb R^d$.
--
--   A sequence $\{x_n\}\subset D^d$ **converges uniformly on compact sets** to $x^*$, written $x_n\to x^*$ u.o.c., if $x^*\in D^d$ and
--
--   $$\lim_{n\to\infty}\|x_n-x^*\|_t=0\qquad\text{for every }t>0.$$
--
--   This is the mode of convergence of fluid limits throughout the book; when the limit is continuous it coincides with convergence in the Skorohod $J_1$ topology.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$ and paths take values in an arbitrary uniform space $E$; the book's spaces $D$ and $D^d$ are the cases $E=\mathbb R$ and $E=\mathbb R^d$ (`Fin d → ℝ`). Membership in $D^d$ is the public predicate `RBMSensitivity.IsRCLL`, required of every $x_n$ and of the limit. The convergence on $[0,t]$ is stated as uniform convergence (`TendstoUniformlyOn`), which for `Fin d → ℝ` uses the sup norm; it is equivalent to the $\ell^1$ norm, so the notion is the same, and no real supremum (whose value $0$ on an unbounded set would be junk) appears.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Appendix A, §A.3, Definition A.6, p.258 (PDF 274); space D^d, p.258; norm |·|, Guide p.xv

import Mathlib
import Definitions.Def_RBMSensitivity_IsRCLL

open Filter Topology
open scoped NNReal

namespace ProcessingNetworks.PathCompact

/-- **Uniform convergence on compact sets (u.o.c.)**, Dai & Harrison, *Processing Networks*
(pre-publication draft 2020-4-2, spnbook.org), Appendix A, §A.3, Definition A.6, p.258 (PDF 274):
a sequence `{xₙ} ⊂ D^d` converges u.o.c. to `x*`, written `xₙ → x*` u.o.c., if `x* ∈ D^d` and,
for every `t > 0`, `‖xₙ − x*‖ₜ = sup_{0 ≤ s ≤ t} |xₙ(s) − x*(s)| → 0` as `n → ∞`.

`ConvergesUOC xs x` asserts: every `xs n` lies in `D` (right continuous on `ℝ₊` with left limits
on `(0, ∞)`, the public predicate `RBMSensitivity.IsRCLL`), the limit `x` lies in `D`, and for
every `t > 0` the sequence converges to `x` uniformly on `[0, t]`.

**Formalization Note.** Time is `ℝ≥0` (the book's `ℝ₊`), the book's index set `{1, 2, …}` is
`ℕ`. The value space `E` is any uniform space; the book's cases are `E = ℝ` (the space `D`) and
`E = Fin d → ℝ` (the space `D^d`). The book measures `|xₙ(s) − x*(s)|` with the `ℓ¹` norm of
`ℝ^d` (Guide, p.xv), Lean's uniform structure on `Fin d → ℝ` is that of the sup norm; the two
norms are equivalent, so uniform convergence on `[0, t]` is the same notion. Stating the
convergence as `TendstoUniformlyOn` avoids a real supremum, whose junk value `0` on an unbounded
set would otherwise matter. -/
def ConvergesUOC {E : Type*} [UniformSpace E] (xs : ℕ → ℝ≥0 → E) (x : ℝ≥0 → E) : Prop :=
  (∀ n, RBMSensitivity.IsRCLL (xs n)) ∧ RBMSensitivity.IsRCLL x ∧
    ∀ t : ℝ≥0, 0 < t → TendstoUniformlyOn xs x atTop (Set.Icc 0 t)

end ProcessingNetworks.PathCompact


