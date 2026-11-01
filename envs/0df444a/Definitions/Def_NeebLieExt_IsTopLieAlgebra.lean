-- Prove2me | Definitions.Def_NeebLieExt_IsTopLieAlgebra
-- name    : NeebLieExt_IsTopLieAlgebra
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:17.909402+00:00
-- url     : https://prove2.me/theorems/7673fbe0-3986-4e57-9ab4-fe6448dde90f
-- title:
--   Topological Lie algebra (continuous bracket)
-- statement:
--   A **topological Lie algebra** over a topological field $\mathbb K$ is a $\mathbb K$-Lie algebra $L$ which is a topological vector space (a Hausdorff topology for which addition and scalar multiplication are continuous) and for which the Lie bracket
--   $$
--   L\times L\to L,\qquad (x,y)\mapsto [x,y]
--   $$
--   is continuous for the product topology.
--
--   This is the standing class of objects of the paper: the kernel $\mathfrak n$, the quotient $\mathfrak g$ and the middle term $\widehat{\mathfrak g}$ of every extension are topological Lie algebras.
--
--   **Formalization Note** The class records only the continuity of the bracket. The vector-space topology, its compatibility with the linear structure and the Hausdorff property are the instance arguments `[TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul K L] [T2Space L]` written wherever the class is used.
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, §I, p. 4 ("A topological Lie algebra g is a K-Lie algebra which is a topological vector space for which the Lie bracket is a continuous bilinear map")

import Mathlib

namespace NeebLieExt

/-- **Topological Lie algebra** (continuity of the bracket). Neeb, *Non-abelian extensions of
topological Lie algebras*, arXiv:math/0411256v1, §I, p. 4: "A *topological Lie algebra* g is a
K-Lie algebra which is a topological vector space for which the Lie bracket is a continuous
bilinear map."

`IsTopLieAlgebra L` says that the bracket `L × L → L, (x, y) ↦ ⁅x, y⁆` is continuous for the
product topology.

**Formalization Note** Only the continuity of the bracket is bundled here. The rest of the
paper's definition — a Hausdorff topological K-vector space (p. 4) — is written at each use as the
instance binders `[TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul K L]
[T2Space L]`, over a topological field `K` (`[IsTopologicalDivisionRing K]`, `[CharZero K]`). -/
class IsTopLieAlgebra (L : Type*) [LieRing L] [TopologicalSpace L] : Prop where
  continuous_bracket : Continuous fun p : L × L => ⁅p.1, p.2⁆

end NeebLieExt


