-- Prove2me | Definitions.Def_ZOGlobalLB_lipConst
-- name    : ZOGlobalLB_lipConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:45:17.732233+00:00
-- url     : https://prove2.me/theorems/380a71cb-c72d-46d5-817a-d5ef2a19c342
-- title:
--   Global Lipschitz constant $\mathrm{Lip}(f)$
-- statement:
--   For a map $f$ between metric spaces, the **global Lipschitz constant** is
--   $$\mathrm{Lip}(f)=\sup_{x\neq y}\frac{d(f(x),f(y))}{d(x,y)}\in[0,\infty],$$
--   the smallest $K$ with $d(f(x),f(y))\le K\,d(x,y)$ for all $x,y$.
--
--   It is the constant used in the admissible class (2) for $\mathrm{Lip}(\nabla f)$ and $\mathrm{Lip}(f_\xi)$, and in the noise-moment bounds of the paper.
--
--   **Formalization Note.** The value is in $[0,\infty]$ ($\infty$ exactly for non-Lipschitz maps), so a bound $\mathrm{Lip}(f)\le K$ means that $f$ is $K$-Lipschitz; there is no junk value of a real supremum.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Section 2, p.4 ("Here Lip denotes the global Lipschitz constant")

import Mathlib

open scoped ENNReal

namespace ZOGlobalLB

/-- **Global Lipschitz constant** `Lip(f)`.
Xia, Yuan, *On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization*,
arXiv:2610.19652, Section 2, p.4: "Here Lip denotes the global Lipschitz constant", used in the
class (2) for `Lip(∇f)` and `Lip(f_ξ)`, and throughout the appendices (e.g. (36), Theorem D.1).

`lipConst f = sup_{x ≠ y} d(f x, f y) / d(x, y)`, the smallest `K` with
`d(f x, f y) ≤ K d(x, y)` for all `x, y`.

**Formalization Note.** The value lies in `ℝ≥0∞`: it is `⊤` exactly when `f` is not Lipschitz, so
a bound `lipConst f ≤ ENNReal.ofReal K` says that `f` is `K`-Lipschitz, with no junk value of a
real supremum of an unbounded set. On a one-point (or empty) domain the supremum is empty and the
value is `0`. -/
noncomputable def lipConst {α β : Type*} [EMetricSpace α] [PseudoEMetricSpace β] (f : α → β) :
    ℝ≥0∞ :=
  ⨆ (x : α) (y : α) (_ : x ≠ y), edist (f x) (f y) / edist x y

end ZOGlobalLB


