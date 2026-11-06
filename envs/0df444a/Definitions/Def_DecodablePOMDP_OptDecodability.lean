-- Prove2me | Definitions.Def_DecodablePOMDP_OptDecodability
-- name    : DecodablePOMDP_OptDecodability
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:22:58.535288+00:00
-- url     : https://prove2.me/theorems/0d2faf13-41c6-41c3-b021-15cee7115c6c
-- title:
--   The optimal decodability constant $\rho(K)$
-- statement:
--   For a channel $K$ from $\mathcal S$ to $\mathcal O$, let $\mathcal D$ be the set of decoders (column-stochastic matrices from $\mathcal O$ to $\mathcal S$). The **optimal decodability constant** is
--
--   $$\rho(K)=\max_{D\in\mathcal D}\ \min_{s\in\mathcal S}\ \sum_yK(y\mid s)\,D(s\mid y).$$
--
--   $K$ is $\rho$-decodable exactly for $\rho\le\rho(K)$, and $\rho(K)$ is the value of a linear program (App. A.9).
--
--   **Formalization Note** The maximum is a real supremum over the decoders and the minimum a real infimum over $\mathcal S$; attainment is part of the A.9 milestone.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), App. A.9, p.20

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist

namespace DecodablePOMDP

open CalibratedCE.Forecast

/-- **Optimal decodability constant** `ρ(K) := max_{D∈𝒟} min_{s∈S} Σ_y K(y | s) D(s | y)` (A.9,
p.20), `𝒟` the column-stochastic decoders from `O` to `S` (`D y s = D(s | y)`).

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.9, p.20: "Let D be the set of all
column-stochastic matrices in R^{S×O}, representing decoders from O to S. Recall that
ρ(K) := max_{D∈D} min_{s∈S} ds(D) = max_{D∈D} min_{s∈S} Σ_y K(y|s)D(s|y)."

**Formalization Note.** The outer `max` is a real `⨆` over the decoders, the inner `min` a real
`⨅` over `S`; attainment is a claim of milestone A.9, not part of the definition. -/
noncomputable def optDecodability {S O : Type} [Fintype S] [Fintype O] (Kc : S → O → ℝ) : ℝ :=
  ⨆ D : {D : O → S → ℝ // ∀ y, IsDist (D y)}, ⨅ s, ∑ y, Kc s y * D.1 y s

end DecodablePOMDP


