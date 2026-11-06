-- Prove2me | Definitions.Def_GnpColoring_blockGen
-- name    : GnpColoring_blockGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:29.310963+00:00
-- url     : https://prove2.me/theorems/22bf4ffc-f7ac-4c7b-8ed2-843ffdbf5c4b
-- title:
--   The block-dynamics generator $L$
-- statement:
--   Let $\mu$ be the uniform measure on proper $q$-colourings of $G$ and $S$ a vertex set with blocks $\mathcal B$. The **block dynamics** has generator
--
--   $$L=\sum_{s\in S}L_s+\sum_{B\in\mathcal B}L_B,\qquad L_sf(\sigma)=f(\sigma)-\mathbb E_\mu[f\mid\sigma_{V-s}],$$
--
--   so each singleton and each block is resampled from its conditional law at rate one.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 3.2, p.15

import Mathlib
import Definitions.Def_GnpColoring_blocks
import Definitions.Def_GnpColoring_blockLap
import Definitions.Def_mm_transport

open scoped Classical
open Finset

namespace GnpColoring

/-- **The block-dynamics generator** `L = Σ_{s∈S} L_s + Σ_{B∈𝓑} L_B` for the uniform measure `µ` on
proper `q`-colourings of `G`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 3.2, p.15: "We consider block dynamics with generator L = Σ_{s∈S} L_s + Σ_{B∈𝓑} L_B".

**Formalization Note** `µ` is `MarkovMixing.properColoringDist G q` (uniform on proper colourings,
zero elsewhere); `L_s` is `SpinGirth5.singleLap µ s`. -/
noncomputable def blockGen {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (S : Finset (Fin n))
    (f : (Fin n → Fin q) → ℝ) : (Fin n → Fin q) → ℝ :=
  fun x => ∑ s ∈ S, SpinGirth5.singleLap (MarkovMixing.properColoringDist G q) s f x +
    ∑ B ∈ blocks G S, blockLap (MarkovMixing.properColoringDist G q) B f x

end GnpColoring


