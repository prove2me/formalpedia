-- Prove2me | Definitions.Def_GnpColoring_vertexWeight
-- name    : GnpColoring_vertexWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:22.26635+00:00
-- url     : https://prove2.me/theorems/27fc71ad-c644-431b-9cae-e78e1c3d02c2
-- title:
--   The vertex weight $W(v)$ (3.1)
-- statement:
--   For a graph $G$ and parameters $d,\eta,A,C$, with $\alpha=C\log d$, the weight of a vertex $v$ is
--
--   $$W(v)=\begin{cases}\alpha^{-1}, & \deg_G(v)\le\bar\Delta,\\ \alpha^{A}\deg_G(v)/d, & \deg_G(v)>\bar\Delta.\end{cases}$$
--
--   Low-degree vertices discount a path's weight by $\alpha^{-1}$; hubs inflate it in proportion to their degree. The weights decide which vertices are breakpoints.
--
--   **Formalization Note** $\alpha^A$ is the real power.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 3.1, Eq. (3.1), p.15

import Mathlib
import Definitions.Def_GnpColoring_deltaBar
import Definitions.Def_GnpColoring_alphaW

open scoped Classical
open Finset

namespace GnpColoring

/-- **The vertex weight** (3.1): `W(v) = α⁻¹` if `deg_G(v) ≤ Δ̄`, and `W(v) = α^A deg_G(v)/d`
if `deg_G(v) > Δ̄`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 3.1, Eq. (3.1), p.15 (and Eq. (4.1), p.35).

**Formalization Note** `α^A` is the real power `Real.rpow` (A is a real constant). -/
noncomputable def vertexWeight {n : ℕ} (G : SimpleGraph (Fin n)) (d η A C : ℝ) (v : Fin n) : ℝ :=
  if (G.degree v : ℝ) ≤ deltaBar d η then (alphaW C d)⁻¹
  else alphaW C d ^ A * (G.degree v : ℝ) / d

end GnpColoring


