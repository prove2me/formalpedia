-- Prove2me | Definitions.Def_RandLatEnum_Supplement_fglProduct
-- name    : RandLatEnum_Supplement_fglProduct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:58:48.463701+00:00
-- url     : https://prove2.me/theorems/b8e5c341-7381-460e-9279-a0d2dd45d9f9
-- title:
--   Feng–Gao–Liu geometric product $P(B)$
-- statement:
--   For an ordered basis $B=(b_1,\dots,b_n)$ with Gram–Schmidt lengths $a_i=\|b_i^*\|$, the **Feng–Gao–Liu geometric product** is
--   $$P(B)=\prod_{i=1}^{n}\max\{1,a_i^{-1}\}.$$
--
--   For a determinant-one lattice and search radius $\sqrt n$, $\sqrt{P(B)}$ is the dominant geometric factor in the running-time analysis of the Feng–Gao–Liu collision search; Theorems 1.6 and 1.7 bound it.
--
--   **Formalization Note** $a_i$ is the published `KannanLattice.Core.gsLen`; only bases (all $a_i>0$) are evaluated.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08adef70deb2f23a9a830e01c5a5b031ddaf5e0d4f88ce5174d67214b37), (8.4), p.31; p.6

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice

namespace RandLatEnum.Supplement

open KannanLattice.Core

/-- The **Feng–Gao–Liu geometric product** `P(B) = ∏_{i=1}^{n} max{1, a_i^{-1}}`, `a_i = ‖b*_i‖`
(Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), (8.4), p.31; also p.6): the geometric factor of the FGL collision search at
radius `√n` for determinant-one lattices. The theorems bound `√P(B)`.

**Formalization Note.** `a_i` is the published `KannanLattice.Core.gsLen`. For a basis every
`a_i > 0`; on a dependent family Lean's `0⁻¹ = 0` would give the factor `1`, a case that never
occurs (only bases are evaluated). -/
noncomputable def fglProduct {n k : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin k)) : ℝ :=
  ∏ i, max 1 (gsLen b i)⁻¹

end RandLatEnum.Supplement


