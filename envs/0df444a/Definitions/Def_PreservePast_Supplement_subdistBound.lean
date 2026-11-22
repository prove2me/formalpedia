-- Prove2me | Definitions.Def_PreservePast_Supplement_subdistBound
-- name    : PreservePast_Supplement_subdistBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:25:57.950413+00:00
-- url     : https://prove2.me/theorems/8999e670-c4ec-47f7-9c0e-00d4d0af5ad3
-- title:
--   The product subdistribution bound $\mathrm{sub}(f,\epsilon,\mu)$ and the all-coordinate success of a protocol
-- statement:
--   Let $f\subseteq X\times Y\times Z$ be a relation on finite sets and $\mu=\mu_A\otimes\mu_B$ a product law on $X\times Y$.
--
--   The **product subdistribution bound** is
--   $$\mathrm{sub}(f,\epsilon,\mu)=\min_{\lambda}\ \log_2\max_{\lambda(x,y)>0}\frac{\lambda(x,y)}{\mu(x,y)},$$
--   the minimum over product laws $\lambda=\lambda_A\otimes\lambda_B$ under which some fixed output $z$ is valid with probability at least $1-\epsilon$; it is $+\infty$ if no such law has a finite ratio.
--
--   For $k$ independent instances drawn from $\mu^{\otimes k}$, the **all-coordinate success** of a deterministic two-party protocol with inputs in $X^k$, $Y^k$ and outputs in $Z^k$ is the probability that the output is valid in every coordinate.
--
--   These are the objects of the strong direct-product theorem (Theorem 3).
--
--   **Formalization Note** A deterministic protocol is the published protocol tree `PermInvCC.ProtoTree` (at each internal node Alice or Bob sends one bit computed from their own input; leaves carry the output; the depth is the worst-case communication; rounds are unrestricted). Laws are probability mass functions; the bound is an extended real, with density ratios computed in $[0,\infty]$ so that a positive mass over a zero baseline gives $+\infty$.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb55cb5da782f256c3a4d1c95195bee48a2f4d0b2ed1e22bccd96d00fa), §2, p.5 (PDF p.7); Appendix B, pp.14–16 (PDF pp.16–18)

import Mathlib
import Definitions.Def_PermInvCC_ProtoTree

open MeasureTheory
open scoped Classical

namespace PreservePast.Supplement

/-- **The product subdistribution bound** `sub(f, ε, μ)` of a relation `f ⊆ X × Y × Z` under the
product law `μ = μ_A ⊗ μ_B`. P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §2, p.5 (PDF p.7): "Write c = sub(f, ϵ, µ) for the minimum
log₂ max_{λ(x,y)>0} λ(x, y)/µ(x, y) over product laws λ under which some fixed output is valid
with probability at least 1 − ϵ; this is the product subdistribution bound of [JKN07]"; Appendix B,
p.16 (PDF p.18): "if its feasible set is empty its value is +∞".

**Formalization Note.** Laws on the finite sets are `PMF`s. The value is an `EReal`: the density
ratio is computed in `ℝ≥0∞` (so `λ(x,y)/0 = ∞` for `λ(x,y) > 0`), `log₂` is
`ENNReal.log / ln 2`, and an infimum over an empty feasible set is `⊤ = +∞`. Over the finitely
supported feasible laws the infimum is the minimum of the source. -/
noncomputable def subdistBound {X Y Z : Type} [Fintype X] [Fintype Y] (f : X → Y → Z → Prop)
    (ε : ℝ) (μA : PMF X) (μB : PMF Y) : EReal :=
  ⨅ (lA : PMF X) (lB : PMF Y)
    (_ : ∃ z : Z, ENNReal.ofReal (1 - ε) ≤
      ∑ x, ∑ y, lA x * lB y * (if f x y z then 1 else 0)),
    ENNReal.log (⨆ (x : X) (y : Y) (_ : 0 < lA x * lB y), lA x * lB y / (μA x * μB y)) /
      ((Real.log 2 : ℝ) : EReal)

/-- **All-coordinate success of a deterministic protocol** on `k` independent instances drawn
from `μ^{⊗k}`, `μ = μ_A ⊗ μ_B`: the probability that the `k` outputs are valid for all `k`
coordinates (§2, p.5, Theorem 3: "all-coordinate success").

**Formalization Note.** A deterministic protocol is the published protocol tree
`PermInvCC.ProtoTree` (internal nodes: Alice or Bob sends one bit computed from their own input;
leaves carry the output, so the output is determined by the transcript; `depth` is the worst-case
number of communicated bits; no restriction on rounds). -/
noncomputable def allCoordSuccess {X Y Z : Type} [Fintype X] [Fintype Y] (f : X → Y → Z → Prop)
    (μA : PMF X) (μB : PMF Y) (k : ℕ)
    (π : PermInvCC.ProtoTree (Fin k → X) (Fin k → Y) (Fin k → Z)) : ENNReal :=
  ∑ x : Fin k → X, ∑ y : Fin k → Y, (∏ i, μA (x i) * μB (y i)) *
    (if ∀ i, f (x i) (y i) (π.eval x y i) then 1 else 0)

end PreservePast.Supplement


