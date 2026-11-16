-- Prove2me | Definitions.Def_FasterPrimeEnum_Supplement_rho
-- name    : FasterPrimeEnum_Supplement_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:48:59.077202+00:00
-- url     : https://prove2.me/theorems/bbb2326a-6750-4e33-9216-5d2f5d7e1c3f
-- title:
--   The quantity $\rho(W)$ of (6.32)
-- statement:
--   For a positive integer $W$ and $d\in D=\{-1,-2,2\}$ let
--
--   $$
--   \rho_d(W):=\big|\{w\in\mathbb Z/W\mathbb Z:\ w=-d\alpha^2\text{ for some }\alpha\in\mathbb Z/W\mathbb Z\}\big|,\qquad \rho(W):=\max_{d\in D}\rho_d(W).
--   $$
--
--   It counts the residues modulo $W$ that the square-supported series of §6 can occupy, and enters the second term of the core algorithm's cost (6.5).
--
--   **Formalization Note** The residues $\alpha$ are $0,\dots,W-1$ and $-d\alpha^2$ is reduced to $[0,W)$; $D$ is the published `FasterPrimeEnum.D`.
-- source:
--   Harvey, Faster enumeration of primes, arXiv:2606.22851 (held version, sha256 7fc13f17…), eq. (6.32), p.48

import Mathlib
import Definitions.Def_FasterPrimeEnum_H

set_option autoImplicit false

namespace FasterPrimeEnum

namespace Supplement

/-- `ρ_d(W) := |{w ∈ Z/WZ : w = −dα² for some α ∈ Z/WZ}|` (D. Harvey, *Faster enumeration of primes*,
arXiv:2606.22851, held version, sha256 7fc13f17…, eq. (6.32), p.48). The residues `α ∈ Z/WZ` are
`0, …, W − 1`, and `w = −dα² mod W` is its least nonnegative residue. -/
def rhoD (d : ℤ) (W : ℕ) : ℕ :=
  ((Finset.range W).image fun a : ℕ => (-d * (a : ℤ) ^ 2) % (W : ℤ)).card

/-- **`ρ(W)`** — eq. (6.32), p.48: "ρ(W) := max_{d∈D} ρ_d(W) where
ρ_d(W) := |{w ∈ Z/WZ : w = −dα² for some α ∈ Z/WZ}|", with `D = {−1, −2, 2}` the published
`FasterPrimeEnum.D` (Definition 2.1, p.13). Used for `W ≥ 1`. -/
def rho (W : ℕ) : ℕ := D.sup fun d => rhoD d W

end Supplement

end FasterPrimeEnum


