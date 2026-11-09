-- Prove2me | Definitions.Def_IntADSat_Delta
-- name    : IntADSat_Delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:25.46833+00:00
-- url     : https://prove2.me/theorems/85cb8490-6058-4bcc-b595-727810d50769
-- title:
--   Degree-difference product $\Delta_G$
-- statement:
--   For a simple graph $G$ with set of distinct degrees $\mathcal D_G$,
--
--   $$
--   \Delta_G=\prod_{\substack{d,h\in\mathcal D_G\\ d<h}}(h-d).
--   $$
--
--   An empty product is $1$, so $\Delta_G$ is always a positive integer ($\Delta_G=1$ for a regular graph). Theorem B.1 shows $\Delta_G^3\mathbb Z^n\subseteq\Lambda_G$ with high probability, so every prime divisor of the defect $\mathbb Z^n/\Lambda_G$ divides $\Delta_G$.
--
--   **Formalization Note** Computed in $\mathbb N$; each factor $h-d$ has $d<h$, so the natural-number subtraction is exact.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Appendix B, p.14 (PDF 15)

import Mathlib
import Definitions.Def_IntADSat_degreeSet

set_option autoImplicit false

namespace IntADSat

/-- The degree-difference product `Δ_G = ∏_{d, h ∈ 𝒟_G, d < h} (h − d)`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Appendix B, p.14 (PDF 15)). An empty product is `1`, so `Δ_G` is always a positive integer
(for a regular graph `Δ_G = 1`).

**Formalization Note** Computed in `ℕ`; the subtraction `h − d` is exact because `d < h`. -/
noncomputable def Delta {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  ∏ dh ∈ (degreeSet G ×ˢ degreeSet G).filter (fun dh => dh.1 < dh.2), (dh.2 - dh.1)

end IntADSat


