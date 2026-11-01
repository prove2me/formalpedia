-- Prove2me | Definitions.Def_CongestionTaxes_tax
-- name    : CongestionTaxes_tax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:33:29.702857+00:00
-- url     : https://prove2.me/theorems/a139d22f-3fb2-4ebf-90a1-6302e38830d5
-- title:
--   Parameterised taxation function $\tau(x,v)$
-- statement:
--   The **parameterised taxation function** of Definition 4 is $\tau(x,v)=f(x,v)-\ell(x)$: the tax levied on each user of a resource with cost $\ell$ and parameter $v$ when $x$ agents use it. A parameter vector $(v_r)_{r\in\mathcal R}$ defines a taxation mechanism, resource $r$ charging $\tau_r(\cdot,v_r)$.
--
--   **Formalization Note** Definition 4 declares $\tau$ with values in $\mathbb R_{\ge0}$; this nonnegativity is Lemma 1(a), stated as a theorem, so $\tau$ is real-valued here.
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, Definition 4, p.18

import Mathlib
import Definitions.Def_CongestionTaxes_modifiedCost

namespace CongestionTaxes

/-- The **parameterised taxation function** of Definition 4 (Paccagnan, Gairing,
arXiv:2105.07480v2, Definition 4, p.18): `τ(x, v) = f(x, v) − ℓ(x)`, the tax charged to each user of
a resource with cost `ℓ` and parameter `v` when `x` agents use it.

**Formalization Note** Definition 4 declares `τ` with values in `ℝ≥0`; that nonnegativity is
Lemma 1(a), stated as a theorem, so `τ` is real-valued here. -/
noncomputable def tax (ℓ : ℕ → ℝ) (x : ℕ) (v : ℝ) : ℝ :=
  modifiedCost ℓ x v - ℓ x

end CongestionTaxes


