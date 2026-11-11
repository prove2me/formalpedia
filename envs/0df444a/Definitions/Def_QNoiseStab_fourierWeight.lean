-- Prove2me | Definitions.Def_QNoiseStab_fourierWeight
-- name    : QNoiseStab_fourierWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:44.403551+00:00
-- url     : https://prove2.me/theorems/8a538135-6322-41b9-9b19-8086b1faec63
-- title:
--   Fourier weight $|\mathrm{Supp}'(z)|$ of a frequency vector $z\in\mathbb Z_m^n$
-- statement:
--   For a frequency vector $z\in\mathbb Z_m^{\,n}$, its **Fourier weight** is the number of nonzero coordinates,
--
--   $$
--   |\mathrm{Supp}'(z)|=\#\{\,i\in[n]: z_i\neq0\,\}.
--   $$
--
--   A Fourier basis state $|\hat z\rangle$ has Fourier degree $|\mathrm{Supp}'(z)|$; the subspace $B_t$ is spanned by those with $|\mathrm{Supp}'(z)|\le t$. The restricted count $|\mathrm{Supp}'(z)\cap A|$ for $A\subseteq[n]$ is written out where it is used.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Definition 2.10, p.10; §3, p.11 (Supp′(z))

import Mathlib

namespace QNoiseStab

/-- The Fourier weight `|Supp′(z)|` of a frequency vector `z ∈ Z_mⁿ`: the number of coordinates
with `z_i ≠ 0` (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and
Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…),
Definition 2.10, p.10: "such that at most t of the zi ≠ 0"; and the sums over `|Supp′(z)| ≤ t`,
p.11). The restricted count `|Supp′(z) ∩ A|` is written `(A.filter fun i => z i ≠ 0).card` where
it is used. -/
def fourierWeight {n m : ℕ} (z : Fin n → ZMod m) : ℕ :=
  (Finset.univ.filter fun i => z i ≠ 0).card

end QNoiseStab


