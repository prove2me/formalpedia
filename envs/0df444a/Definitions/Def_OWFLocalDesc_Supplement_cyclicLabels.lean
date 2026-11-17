-- Prove2me | Definitions.Def_OWFLocalDesc_Supplement_cyclicLabels
-- name    : OWFLocalDesc_Supplement_cyclicLabels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:41:47.158966+00:00
-- url     : https://prove2.me/theorems/52d0fc8e-ca6c-4fa0-a388-fa2f914de932
-- title:
--   The cyclic first-bit labeling (Theorem B.2)
-- statement:
--   Let $X=(X_1,\dots,X_m)$ be a vector of points in $\{0,1\}^n$, $n\ge1$, and write $B_i$ for the first bit of $X_i$. The **cyclic first-bit labeling** gives each point the first bit of the next point, cyclically:
--   $$Y_i=B_{i+1}\quad(1\le i<m),\qquad Y_m=B_1 .$$
--
--   This labeling is computable by a constant-length global program that reads the whole point vector. Theorem B.2 shows that its pointwise quantiles are nevertheless large for most point vectors.
--
--   **Formalization Note** Indices are zero-based (`Fin m`), and `finRotate m` sends $i$ to $i+1 \bmod m$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem B.2, p.38

import Mathlib
set_option autoImplicit false

namespace OWFLocalDesc.Supplement

/-- **The cyclic first-bit labeling (Theorem B.2).** Myrisiotis, *One-Way Functions and Local
Descriptions of Random Data*, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e),
Theorem B.2, p.38: "draw the points Xi = (Bi, X̃i) … where Bi is the first bit and X̃i is the
remaining suffix. Set Yi = Bi+1, with Bm+1 = B1, so that each label is the first bit of the next
point, cyclically."

**Formalization Note.** Indices are `Fin m` (zero-based); `finRotate m` sends `i` to `i + 1`
modulo `m`, so label `i` is the first bit (index `0`, which exists since `n ≥ 1`) of point
`i + 1 mod m`. -/
def cyclicLabels {m n : ℕ} (hn : 0 < n) (X : Fin m → Fin n → Bool) : Fin m → Bool :=
  fun i => X (finRotate m i) ⟨0, hn⟩

end OWFLocalDesc.Supplement


