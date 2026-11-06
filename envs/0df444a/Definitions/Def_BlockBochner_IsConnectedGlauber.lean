-- Prove2me | Definitions.Def_BlockBochner_IsConnectedGlauber
-- name    : BlockBochner_IsConnectedGlauber
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:53.956202+00:00
-- url     : https://prove2.me/theorems/a351ca94-5656-4f16-b18e-960e021c0ab6
-- title:
--   Connectedness: $\ker L_{\mathrm{Glaub}}$ = constants
-- statement:
--   A measure $\nu$ on $\prod_iX_i$ (finitely many sites) is connected when every $f\in L^2(\nu)$ with $L_{\mathrm{Glaub}}f=0$ is $\nu$-a.e. constant, i.e. $\ker L_{\mathrm{Glaub}}$ consists only of constant functions.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Theorem 3, p.4; Sec. 2.2, p.16

import Mathlib
import Definitions.Def_BlockBochner_glauberLap

open MeasureTheory

namespace BlockBochner

/-- **Connectedness: `ker L_Glaub` consists only of constant functions.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 3, p.4
("such that ker(L_Glaub) consists only of constant functions (connectedness)") and Sec. 2.2, p.16
(a link is connected if `ker L_Glaub,ν` consists only of constant functions).

**Formalization Note** Every element of the kernel of `glauberLap ν` on `L²(ν)` is `ν`-a.e. equal to a
constant function. -/
def IsConnectedGlauber {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (ν : Measure (∀ i, X i)) : Prop :=
  ∀ f ∈ LinearMap.ker (glauberLap ν).toLinearMap, ∃ c : ℝ, (f : (∀ i, X i) → ℝ) =ᵐ[ν] fun _ => c

end BlockBochner


