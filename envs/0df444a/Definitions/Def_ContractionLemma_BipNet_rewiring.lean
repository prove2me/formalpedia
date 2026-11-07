-- Prove2me | Definitions.Def_ContractionLemma_BipNet_rewiring
-- name    : ContractionLemma_BipNet_rewiring
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:59:58.375476+00:00
-- url     : https://prove2.me/theorems/45521077-a4bd-488e-9b9e-89af72a4bce2
-- title:
--   The rewiring polynomial $F(T)=\Phi_G(W(T))$
-- statement:
--   For a bipartite network $G$ with entries in a commutative $\mathbb Q$-algebra and a placement of its edges into packets, the **rewiring polynomial** along the shift curve is
--
--   $$
--   F(T)=\Phi_G\big(W(T)\big).
--   $$
--
--   Since $W(0)=I$, the value $F(0)$ is the contraction of $G$; the proof of the contraction lemma recovers this value from data at the other grid points.
--
--   **Formalization Note** The curve has rational coefficients, mapped into the algebra of the entries.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Definition A.6, p.55 and App. A.4.1, p.58

import Mathlib
import Definitions.Def_ContractionLemma_BipNet
import Definitions.Def_ContractionLemma_BipNet_Phi
import Definitions.Def_ContractionLemma_Placement

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

namespace BipNet

variable {U W E K : Type*}

/-- **The rewiring polynomial along the shift curve** (Definition A.6, p.55, with the curve of
Lemma A.7) — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript, sha256 049caea1…):
`F(T) = Φ_G(W(T))`, for a bipartite network with entries in a commutative `ℚ`-algebra `K` and
a placement of its edges into packets. -/
noncomputable def rewiring [Fintype U] [Fintype W] [Fintype E] [DecidableEq E] [CommRing K]
    [Algebra ℚ K] {a : ℕ} (G : BipNet U W E K) (pl : Placement E a) : K[X] :=
  G.PhiAt (pl.wiring.map (Polynomial.map (algebraMap ℚ K)))

end BipNet

end ContractionLemma


