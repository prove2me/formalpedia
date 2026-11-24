-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
-- name    : Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:28.927825+00:00
-- url     : https://prove2.me/theorems/e512dd27-b095-4c20-a16e-aaa95458b5bb
-- title:
--   Large Constant Le Param Cube
-- statement:
--   Definitions and structural lemmas for Large Constant Le Param Cube, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/LargeConstantLeParamCube.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
structure Bs (A k b sb PP TO rd : ℝ) : Prop where
  forty_eight_le_constant : 48 ≤ A
  k8 : 8 ≤ k
  Ak : A ≤ 2 * k ^ 2
  sb_sq : sb * sb = b
  PPA : 10 ^ 60 * A ≤ PP
  h32 : PP ^ 3 * TO ^ 2 ≤ sb
  hTP : TO * PP ≤ sb
  one_le_order_alt : 1 ≤ TO
  rd1 : 1 ≤ rd
  rd8 : rd ^ 8 ≤ sb
namespace Bs
variable {A k b sb PP TO rd : ℝ} (h : Bs A k b sb PP TO rd)
include h
end Bs
structure Rn (A k b sb PP TO rd r D2 nW nP q0 : ℝ) : Prop extends Bs A k b sb PP TO rd where
  r6 : 6 ≤ r
  rA : 8 * r ≤ A
  two_le_degree_alt : 2 ≤ D2
  W : D2 * nW + 2 * r ≤ TO
  forty_mul_degree_le_order : 40 * D2 ≤ TO
  forty_le_weight_count : 40 ≤ nW
  projectivePointSizes : 0 ≤ nP
  nPW : nP ≤ nW
  q0lo : b ≤ TO * q0
  q0hi : TO * q0 ≤ b + TO
namespace Rn
variable {A k b sb PP TO rd r D2 nW nP q0 : ℝ} (h : Rn A k b sb PP TO rd r D2 nW nP q0)
include h
end Rn
namespace Rn
variable {A k b sb PP TO rd r D2 nW nP q0 : ℝ} (h : Rn A k b sb PP TO rd r D2 nW nP q0)
include h
end Rn
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num


