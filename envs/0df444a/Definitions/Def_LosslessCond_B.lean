-- Prove2me | Definitions.Def_LosslessCond_B
-- name    : LosslessCond_B
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:26.655214+00:00
-- url     : https://prove2.me/theorems/e1851686-ce83-4a31-ba58-48fdf71be6d5
-- title:
--   Coefficients $B(r)=(r+1)\lceil\log(r+1)\rceil+2$ and $a(r,s)=B(r)2^s$
-- statement:
--   For an integer $r$ (used for $r\ge 1$), with logarithms to base two,
--   $$
--   B(r)=(r+1)\,\lceil\log(r+1)\rceil+2,\qquad a(r,s)=B(r)\,2^s .
--   $$
--   $B(r)$ pays, per leaf of a depth-$s$ tree, for the row-sum description of a leaf condition, its output, and one intersection/union choice; $a(r,s)$ is the hitting-set size of Lemma 5.1.
--
--   **Formalization Note** $\lceil\log m\rceil$ is `Nat.clog 2 m`, exact for $m\ge 1$.
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), (4.2), p.12 (PDF p.13); (5.1), p.13 (PDF p.14)

import Mathlib

namespace LosslessCond

/-- The **row-sum coefficient** `B(r) = (r + 1)⌈log(r + 1)⌉ + 2` (Mackenzie, arXiv:2609.28691, held
version sha256 ce75e6d4…, (4.2), p.12; (5.1), p.13).

**Formalization Note** Logarithms are to base two and `⌈log m⌉ = Nat.clog 2 m`, which is exact for
`m ≥ 1`. The paper uses `B(r)` only for `r ≥ 1`; the theorems of the mission carry that
hypothesis. -/
def B (r : ℕ) : ℕ := (r + 1) * Nat.clog 2 (r + 1) + 2

/-- The **hitting-set size** `a(r, s) = B(r)·2^s` (Mackenzie, arXiv:2609.28691, (5.1), p.13). -/
def a (r s : ℕ) : ℕ := B r * 2 ^ s

end LosslessCond


