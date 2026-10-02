-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeWT
-- name    : DiscreteConvex_NetworkFlowsC_InducedGTildeWT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:03:22.985318+00:00
-- url     : https://prove2.me/theorems/0e551886-8746-4f61-85c9-43c943413678
-- title:
--   InducedGTildeWT
-- statement:
--   $\tilde g$ projected to $\mathbb R\cup\{+\infty\}$ (assuming properness).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.269, Eq. (9.82), projected.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.269, Eq. (9.82), projected

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTilde

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def InducedGTildeWT (tail head : A → V) (S T : Finset V) (ga : A → ℤ → WithTop ℝ)
    (g : (V → ℤ) → WithTop ℝ) (q : V → ℤ) : WithTop ℝ :=
  FromEReal (InducedGTilde tail head S T ga g q)

-- ===== Network transformation apparatus (§9.6), real domain =====

end DiscreteConvex.NetworkFlowsC


