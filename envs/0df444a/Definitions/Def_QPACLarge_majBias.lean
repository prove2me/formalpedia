-- Prove2me | Definitions.Def_QPACLarge_majBias
-- name    : QPACLarge_majBias
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:18.425225+00:00
-- url     : https://prove2.me/theorems/e06b09f0-7fff-47ff-ae20-5879c7881ff2
-- title:
--   Expected majority sign $\mathbb E[\mathrm{Sign}(B_1,\dots,B_m)]$
-- statement:
--   For independent signs $B_1, \dots, B_m$ of mean $1/\sqrt N$ (each $B_i = b$ with probability $(1 + b/\sqrt N)/2$, the only law of a sign with this mean),
--   $$
--   \mathbb E[\mathrm{Sign}(B_1, \dots, B_m)] = \sum_{B \in \{\pm1\}^m} \prod_{i=1}^m \frac{1 + B_i/\sqrt N}{2} \cdot \mathrm{Sign}(B).
--   $$
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 3.5, p.28

import Mathlib
import Definitions.Def_QPACLarge_signMaj
import Definitions.Def_QPACLarge_sgn

namespace QPACLarge

/-- **Expected sign of the majority of independent signs of mean `1/√N`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Lemma 3.5, p.28: "independent signs `B₁, …, B_m ∈ {−1, +1}` of mean `1/√N`",
`E[Sign(B₁, …, B_m)]`.

`majBias N m = Σ_v Πᵢ ((1 + Bᵢ/√N)/2) · Sign(B)` over `v ∈ {0,1}^m`, `Bᵢ = (−1)^{vᵢ}`: each `Bᵢ`
equals `b ∈ {±1}` with probability `(1 + b/√N)/2`, which is the only law of a sign with mean
`1/√N`. -/
noncomputable def majBias (N m : ℕ) : ℝ :=
  ∑ v : Fin m → Bool,
    (∏ i, (1 + sgn (v i) * (Real.sqrt N)⁻¹) / 2) * signMaj (fun i => sgn (v i))

end QPACLarge


