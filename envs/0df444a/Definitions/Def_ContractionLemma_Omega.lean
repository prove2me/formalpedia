-- Prove2me | Definitions.Def_ContractionLemma_Omega
-- name    : ContractionLemma_Omega
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:00:22.291813+00:00
-- url     : https://prove2.me/theorems/8cfeab6a-611d-4939-9bcd-81a49042b291
-- title:
--   The weights $\Omega_{t,j}=E_t(0)\,r_{t,j}(-t/\alpha)$
-- statement:
--   Let $z_0,\dots,z_{D^*}$ be nodes with Lagrange basis polynomials $\ell_j(z)=\prod_{k\ne j}(z-z_k)/(z_j-z_k)$, and let $r_{t,j}$ be the part of degree below $m_t$ of the power series $\ell_j(z)/E_t(t+\alpha z)$. The **weights** of one call of the recursion are
--
--   $$
--   \Omega_{t,j}=E_t(0)\,r_{t,j}(-t/\alpha).
--   $$
--
--   They express $F(0)$ as a linear combination of the values $F(t+\alpha z_j)$ and do not depend on the network.
--
--   **Formalization Note** The weights are computed in $\mathbb Q[U]/(f)$, since they may have denominators that are powers of $2$. $1/(z_j-z_k)$ is `Ring.inverse`; differences of distinct binary nodes are units of $\mathcal O$.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), App. A.6 ("One call"), p.76

import Mathlib
import Definitions.Def_ContractionLemma_zoom
import Definitions.Def_ContractionLemma_Et
import Definitions.Def_ContractionLemma_NodeField

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- The Lagrange basis polynomial `ℓ_j(z) = ∏_{k ≠ j} (z − z_k)/(z_j − z_k)` of the nodes
`z_0, …, z_D` (p.76). `1/(z_j − z_k)` is `Ring.inverse`; for distinct binary nodes the
differences are units of `O` (p.96). -/
noncomputable def lagrangeBasis {K : Type*} [CommRing K] {D : ℕ} (z : Fin (D + 1) → K)
    (j : Fin (D + 1)) : K[X] :=
  ∏ k ∈ Finset.univ.erase j, (C (Ring.inverse (z j - z k)) * (X - C (z k)))

/-- **The weights `Ω_{t,j}`** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), App. A.6 ("One call"), p.76 (PDF p.79): `Ω_{t,j} = E_t(0) r_{t,j}(−t/α)`,
where `r_{t,j}` is the part of degree below `m_t` of the power series `ℓ_j(z)/E_t(t + αz)`;
computed in `ℚ[U]/(f)` (the fractions of the node ring). -/
noncomputable def Omega (f : ℤ[X]) (a : ℕ) (q : ℕ → ℕ) (t : ℤ) {D : ℕ}
    (z : Fin (D + 1) → NodeField f) (j : Fin (D + 1)) : NodeField f :=
  algebraMap ℚ (NodeField f) ((Et a q t).eval 0) *
    (PowerSeries.trunc (orderAt q t)
        (((lagrangeBasis z j : (NodeField f)[X]) : PowerSeries (NodeField f)) *
          PowerSeries.map (algebraMap ℚ (NodeField f)) (invZoomEt a q t))).eval
      (algebraMap ℚ (NodeField f) (-(t : ℚ) / alpha a))

end ContractionLemma


