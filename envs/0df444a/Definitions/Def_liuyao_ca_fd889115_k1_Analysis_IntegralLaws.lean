-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralLaws
-- name    : liuyao_ca_fd889115_k1_Analysis_IntegralLaws
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:00:32.903657+00:00
-- url     : https://prove2.me/theorems/612fe986-90a4-47dc-961a-aafa8c591a3d
-- title:
--   Computable analysis · IntegralLaws · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/IntegralLaws.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralLinearity
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralScaling
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_IntegralAdditivity

set_option autoImplicit true

/-! The four public algebra/order law types are proved for the current
rectangle-based sufficient integral relation. No existence theorem or
method-independent uniqueness claim is implied. -/
namespace ComputableAnalysis.Integral

theorem linear : LinearFor := by
  intro F G H h I J K hI hJ hK
  exact HasIntegral.add_identity hI hJ hK h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem compatibleWithScaleRat : CompatibleWithScaleRatFor := by
  intro r F G h I J hI hJ
  exact hI.scaleRat_identity hJ r h

theorem orderPreserving : OrderPreservingFor := by
  intro F G h I J hI hJ
  exact hI.mono hJ h.1 h.2.1 h.2.2

theorem additiveOnAdjacentIntervals : AdditiveOnAdjacentIntervalsFor := by
  intro F a b c ha hab hbc hc I J K hI hJ hK
  let G := F.restrict a c ha (Rat.le_trans hab hbc) hc
  have hI' : HasIntegral (G.restrict a b (Rat.le_refl) hab hbc) I := hI
  have hJ' : HasIntegral (G.restrict b c hab hbc (Rat.le_refl)) J := hJ
  exact HasIntegral.append_identity (F := G) b hab hbc hI' hJ' hK

end ComputableAnalysis.Integral


