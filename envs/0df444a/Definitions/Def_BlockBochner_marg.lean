-- Prove2me | Definitions.Def_BlockBochner_marg
-- name    : BlockBochner_marg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:30.154487+00:00
-- url     : https://prove2.me/theorems/814cdff0-57f3-4b7f-acae-523c0f1237ca
-- title:
--   Marginal $\mu_U$ of $\mu$ on a set of sites
-- statement:
--   For a measure $\mu$ on $\prod_{v\in V}S_v$ and $U\subseteq V$, $\mu_U$ is the law of $X_U=(X_v)_{v\in U}$: the image of $\mu$ under the restriction $x\mapsto(x_v)_{v\in U}$, a measure on $\prod_{v\in U}S_v$. With $U=T$ this is the joint law of the blocks $(Y_1,\dots,Y_m)$, $Y_a=X_{T_a}$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 1.2, p.3

import Mathlib

open MeasureTheory

namespace BlockBochner

/-- **Marginal `µ_U` of `µ` on the sites of `U`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.2, p.3: "the joint law of
`(Y₁, …, Y_m)` on `S₁ × ⋯ × S_m`, which is the marginal of µ on the sites in `T`."

**Formalization Note** The image of `µ` under the restriction `x ↦ (x_v)_{v ∈ U}`, a measure on
`∏_{v ∈ U} S_v`. Grouping the coordinates of `U` into the blocks `Y_a = X_{T_a}` is a relabelling of
this product and is not made explicit. -/
noncomputable def marg {V : Type*} {S : V → Type*} [∀ v, MeasurableSpace (S v)]
    (μ : Measure (∀ v, S v)) (U : Finset V) : Measure (∀ v : U, S v) :=
  μ.map (fun x (v : U) => x v)

end BlockBochner


