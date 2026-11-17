-- Prove2me | Definitions.Def_SpencerEight_Supplement_IsSelfDualBasis
-- name    : SpencerEight_Supplement_IsSelfDualBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:50:36.240241+00:00
-- url     : https://prove2.me/theorems/271ca144-1c04-49bc-80dd-5ffba575bc50
-- title:
--   Self-dual basis of $\mathrm{GF}(2^k)$ over $\mathbb F_2$
-- statement:
--   Let $\mathrm{Tr}:\mathrm{GF}(2^k)\to\mathbb F_2$, $\mathrm{Tr}[x]=x+x^2+x^4+\dots+x^{2^{k-1}}$, be the absolute trace. A basis $b_1,\dots,b_k$ of $\mathrm{GF}(2^k)$ over $\mathbb F_2$ is **self-dual** if it is orthonormal for the trace form:
--   $$
--   \mathrm{Tr}[b_ib_j]=\mathbf 1\{i=j\}\qquad(1\le i,j\le k).
--   $$
--   Through a self-dual basis, the coordinates of $x$ are $(\mathrm{Tr}[xb_1],\dots,\mathrm{Tr}[xb_k])$ and the dot product of coordinate vectors is $\mathrm{Tr}[xy]$.
--
--   **Formalization Note** $\mathrm{GF}(2^k)$ is `GaloisField 2 k` and the absolute trace is `Algebra.trace (ZMod 2) (GaloisField 2 k)`, which for a finite field equals the sum of the Galois conjugates. This is the field trace, not the matrix trace.
-- source:
--   Song, Zhang, Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), Section 15.3, p.291 (PDF p.291)

import Mathlib

namespace SpencerEight.Supplement

/-- A self-dual basis of `GF(2^k)` over `F₂` (Section 15.3, Song, Zhang, *Matrix Spencer: Eight Standard Deviations Suffice and an Almost-Linear Time Algorithm for Dense Input*, arXiv:2609.15025 (held version, sha256 9ccbcdb8…), p.291 (PDF p.291)):
a basis `b₁, …, b_k` with `Tr[bᵢ bⱼ] = 1{i = j}`, where `Tr` is the absolute trace
`GF(2^k) → F₂`, `x ↦ x + x² + ⋯ + x^{2^{k−1}}`.

**Formalization Note** `GF(2^k)` is Mathlib's `GaloisField 2 k` and `F₂` is `ZMod 2`. The absolute trace is
`Algebra.trace (ZMod 2) (GaloisField 2 k)`, the trace of multiplication; for a finite field it equals the sum
of the Galois conjugates `x + x² + ⋯ + x^{2^{k−1}}`. It is the field trace, not the matrix trace. -/
def IsSelfDualBasis {k : ℕ} (b : Module.Basis (Fin k) (ZMod 2) (GaloisField 2 k)) : Prop :=
  ∀ i j, Algebra.trace (ZMod 2) (GaloisField 2 k) (b i * b j) = if i = j then 1 else 0

end SpencerEight.Supplement


