-- Prove2me | Definitions.Def_IntADSat_KP__d24af9
-- name    : IntADSat_KP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:20.230722+00:00
-- url     : https://prove2.me/theorems/d24af9c0-c7d1-4b52-9da9-b7795afed183
-- title:
--   Parameter $K=\lceil 10\sqrt n\rceil$ of (B.1)
-- statement:
--   One of the parameters fixed in display (B.1) for the integer construction of Appendix B: for $n\in\mathbb N$,
--
--   $$
--   K=\lceil 10\sqrt n\rceil.
--   $$
--
--   The paper's roles: $k$ bounds the low-degree classes, $K$ all degree classes, $s$ is the size of the second-round column sets, $r$ the number of seed vertices of largest degree, and $g$ their degree separation.
--
--   **Formalization Note** Real powers and square roots of $(n:\mathbb R)$; `Nat.floor`/`Nat.ceil` of a nonnegative real.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), display (B.1), p.16 (PDF 17)

import Mathlib

set_option autoImplicit false

namespace IntADSat

/-- The parameter `K = ⌈10√n⌉` of display (B.1) (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.16 (PDF 17)).

**Formalization Note** Real power of `(n : ℝ)`; `⌊·⌋₊`/`⌈·⌉₊` are `Nat.floor`/`Nat.ceil` of a
nonnegative real. -/
noncomputable def KP (n : ℕ) : ℕ :=
  ⌈10 * Real.sqrt n⌉₊

end IntADSat


