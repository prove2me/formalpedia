-- Prove2me | Definitions.Def_MaskingHardness_pairD
-- name    : MaskingHardness_pairD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:49.920195+00:00
-- url     : https://prove2.me/theorems/e752a2a0-53a4-4a71-858d-07aae2515745
-- title:
--   The $\mathcal D$-weighted pairing $\langle a,b\rangle_{\mathcal D}$
-- statement:
--   For a distribution $\mathcal D$ on $\mathcal X\times\mathcal Y$ and functions $a,b:\mathcal X\times\mathcal Y\to\mathbb R^k$,
--
--   $$
--   \langle a,b\rangle_{\mathcal D}=\mathbb E_{(x,y)\sim\mathcal D}\bigl[\langle a(x,y),b(x,y)\rangle\bigr]=\sum_{x,y}\mathcal D(x,y)\,\langle a(x,y),b(x,y)\rangle .
--   $$
--
--   This is the pairing under which the regularizer/constraint functionals $R,S$ of Theorem 3.3 are conjugate.
--
--   **Formalization Note** Functions on $\mathcal X\times\mathcal Y$ are curried, `a : X → Y → (Fin k → ℝ)`.
-- source:
--   Gopalan–Prabhakaran–Tankala, Universal Hardness From Masking Channels, arXiv:2611.05296 (held version, sha256 31134e8d098ff93ca941097a6dd864cef12b6344e5d41c53281f43af7e683e8d), Theorem 3.3 (b), p.21 (PDF p.23); Eq. (8), p.20 (PDF p.22)

import Mathlib

namespace MaskingHardness

/-- **The `D`-weighted pairing** `⟨a, b⟩_D = E_D[⟨a(x, y), b(x, y)⟩]` of functions
`a, b : X × Y → ℝᵏ` (Gopalan–Prabhakaran–Tankala, *Universal Hardness From Masking Channels*,
arXiv:2611.05296, held version sha256 31134e8d…3e8d, Theorem 3.3 (b), printed p.21 = PDF p.23;
also (8), printed p.20 = PDF p.22).

**Formalization Note** Functions on `X × Y` are curried, `a : X → Y → ℝᵏ`. -/
noncomputable def pairD {X Y : Type*} [Fintype X] [Fintype Y] {k : ℕ} (D : X → Y → ℝ)
    (a b : X → Y → Fin k → ℝ) : ℝ :=
  ∑ x, ∑ y, D x y * (a x y ⬝ᵥ b x y)

end MaskingHardness


