-- Prove2me | Definitions.Def_SampleRemoval_Supplement_IsRadonPartition
-- name    : SampleRemoval_Supplement_IsRadonPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:19:57.967187+00:00
-- url     : https://prove2.me/theorems/e8682f72-a9aa-42ea-ba98-70ac9052b27b
-- title:
--   Radon partition of five saddle lifts
-- statement:
--   A pair $(A,B)$ is the **Radon partition** of the saddle lifts indexed by $\Omega$ when $A$ and $B$ are nonempty disjoint parts covering $\Omega$, and strictly positive convex weights on their lifts have the same barycenter.
--
--   Under LGP for five points, the affine dependence is unique and has no zero coefficient, so these two sides are exactly the Radon partition used in Theorem 5.7.
-- source:
--   Xu, Gao, Hu, Rounding, Ranges, and Exact Sample-Removal Audits for Least Squares, STOC 2027 submission (manuscript sha256 dcd33acebc1ccdc626c7ee41bfabc29795abe2e1cd9267d8cbd66d98f81c4b26), Theorem 5.7 and proof, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_SampleRemoval_Supplement_saddleLift

set_option autoImplicit false

namespace SampleRemoval.Supplement

/-- `(A,B)` is the Radon partition of the saddle lifts indexed by `Ω`: `A` and `B` are a
nonempty disjoint partition of `Ω`, and strictly positive convex weights on the two sides have
the same lifted barycenter (Xu, Gao, Hu, STOC 2027 submission, Theorem 5.7, p.12
(PDF p.14)). Under LGP on five points the affine dependence is unique and has no zero entry,
so this is exactly the page's two-sided Radon partition. -/
def IsRadonPartition {n : ℕ} (p : Fin n → ℝ × ℝ) (Ω A B : Finset (Fin n)) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = Ω ∧
    ∃ (α : A → ℝ) (γ : B → ℝ),
      (∀ i, 0 < α i) ∧ (∀ i, 0 < γ i) ∧
      ∑ i, α i = 1 ∧ ∑ i, γ i = 1 ∧
      (∑ i, α i • saddleLift p i) = ∑ i, γ i • saddleLift p i

end SampleRemoval.Supplement


