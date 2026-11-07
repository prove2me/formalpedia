-- Prove2me | Definitions.Def_DynHaussler_center
-- name    : DynHaussler_center
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:35:41.259573+00:00
-- url     : https://prove2.me/theorems/a1d0cb59-f563-43d7-bea9-478f0a592939
-- title:
--   Center $a(V,x)=\tfrac12(\ell(V,x)+u(V,x))$ of Eq. (32)
-- statement:
--   Let $V\subseteq[0,1]^X$ be nonempty of finite rank $r=\mathrm{sfat}_\eta(V)$, and $x\in X$. The two critical thresholds and their **center** are
--   $$
--   \ell(V,x)=\inf\{z\in[0,1]:\mathrm{sfat}_\eta(\{f\in V:f(x)\le z\})=r\},\qquad
--   u(V,x)=\sup\{z\in[0,1]:\mathrm{sfat}_\eta(\{f\in V:f(x)\ge z\})=r\},
--   $$
--   $$
--   a(V,x)=\tfrac12\bigl(\ell(V,x)+u(V,x)\bigr),
--   $$
--   with the convention $\mathrm{sfat}_\eta(\emptyset)=-1$ for the fibers. Both sets are nonempty ($z=1$ and $z=0$), so the center lies in $[0,1]$.
--
--   The center is the provisional prediction of every schedule simulation, and Lemma 12 shows that a sufficiently separated correction from it lowers the rank.
--
--   **Formalization Note** The fiber condition uses the rank wrapper `rank` ($\bot$ for the empty fiber), so an empty fiber never counts as rank $0$. The Lean definition is total; outside nonempty classes of finite rank its value (a number in $[0,1]$) is not used by any statement.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eq. (32), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_DynHaussler_rank

set_option autoImplicit false

namespace DynHaussler

/-- The **center** `a(V, x)` of a class `V` at an instance `x`, Eq. (32): with `r = sfat_η(V)`,
`ℓ(V, x) = inf {z ∈ [0,1] : sfat_η({f ∈ V : f(x) ≤ z}) = r}`,
`u(V, x) = sup {z ∈ [0,1] : sfat_η({f ∈ V : f(x) ≥ z}) = r}`, and `a(V, x) = (ℓ(V, x) + u(V, x))/2`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Eq. (32), p.18 (PDF p.20).

**Formalization Note** The fiber condition uses `rank` (the rank wrapper, `⊥` for the empty
class, as the paper's `sfat_η(∅) = −1`), so that an empty fiber never counts as having rank `0`.
The paper defines the center for nonempty `V` of finite rank, where both sets are nonempty
(`z = 1`, `z = 0`) and bounded; the Lean definition is total (on other inputs it is a value in
`[0,1]` that no statement uses). -/
noncomputable def center {X : Type*} (η : ℝ) (V : Set (X → ℝ)) (x : X) : ℝ :=
  (sInf {z : ℝ | z ∈ Set.Icc (0 : ℝ) 1 ∧
      rank η {f ∈ V | f x ≤ z} = ((NondualOpt.sfat V η : ℕ∞) : WithBot ℕ∞)} +
    sSup {z : ℝ | z ∈ Set.Icc (0 : ℝ) 1 ∧
      rank η {f ∈ V | z ≤ f x} = ((NondualOpt.sfat V η : ℕ∞) : WithBot ℕ∞)}) / 2

end DynHaussler


