-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeRWT
-- name    : DiscreteConvex_NetworkFlowsC_InducedGTildeRWT
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:03:55.527804+00:00
-- url     : https://prove2.me/theorems/72da19f5-167e-41d0-99ca-6488b8090730
-- title:
--   InducedGTildeRWT
-- statement:
--   $\tilde g$ projected to $\mathbb R\cup\{+\infty\}$, real domain.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, projected, real version.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, projected, real version

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_FromEReal
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeR

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
noncomputable def InducedGTildeRWT (tail head : A → V) (S T : Finset V) (ga : A → ℝ → WithTop ℝ)
    (g : (V → ℝ) → WithTop ℝ) (q : V → ℝ) : WithTop ℝ :=
  FromEReal (InducedGTildeR tail head S T ga g q)

-- ===== Bipartite matching and the unique-min condition (§9.5.2) =====

end DiscreteConvex.NetworkFlowsC


