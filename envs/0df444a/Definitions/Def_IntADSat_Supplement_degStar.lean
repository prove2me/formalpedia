-- Prove2me | Definitions.Def_IntADSat_Supplement_degStar
-- name    : IntADSat_Supplement_degStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:42:31.110347+00:00
-- url     : https://prove2.me/theorems/47f84d15-b53f-4cf8-8b88-932e6848730a
-- title:
--   $\Delta_*=\max(1,\max_v\deg v)$
-- statement:
--   For a graph $G$,
--   $$\Delta_*=\max\Big(1,\ \max_{v}\deg_G(v)\Big),$$
--   the maximum degree floored at $1$. Every entry of a word vector of length $\ell$ has absolute value at most $\Delta_*^\ell$, and $\Delta_*$ enters the index bound and the word-length bound (A.1) of Theorem A.6.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), §A.2, p.12 (PDF 13)

import Mathlib
import Definitions.Def_IntADSat_deg

set_option autoImplicit false

namespace IntADSat.Supplement

/-- `Δ_* = max(1, max_v deg(v))`, the maximum degree floored at `1`
(Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), §A.2, p.12 (PDF 13)).

**Formalization Note** The inner maximum is a `Finset.sup` over the vertices (it is `0` on the empty
vertex set, where `Δ_* = 1`). -/
noncomputable def degStar {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  max 1 (Finset.univ.sup fun v => IntADSat.deg G v)

end IntADSat.Supplement


