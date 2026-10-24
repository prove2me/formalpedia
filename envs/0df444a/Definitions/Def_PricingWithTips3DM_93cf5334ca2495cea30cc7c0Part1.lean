-- Prove2me | Definitions.Def_PricingWithTips3DM_93cf5334ca2495cea30cc7c0Part1
-- name    : PricingWithTips3DM_93cf5334ca2495cea30cc7c0Part1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:28:06.347082+00:00
-- url     : https://prove2.me/theorems/20aecf61-9cd7-46f7-98a6-36c90ab60cc5
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.QueryNormalizer.Basic.Part1
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_88801654eeed9b1dbb21ce0f
import Mathlib.Tactic.DeriveFintype
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer
open PolyBuilder

inductive EndpointOrder
  | leftLess | equal | rightLess
deriving DecidableEq, Fintype

def normalizeQuery (edge : Nat × Nat) : Nat × Nat :=
  if edge.1 ≤ edge.2 then edge else (edge.2, edge.1)

def encodeNormalizedQueries (edges : List (Nat × Nat)) : List CliqueSym :=
  edges.flatMap (encodeCliqueEdge ∘ normalizeQuery)

inductive Label
  | scan | left | incrementLeft | right | incrementRight
  | compareLeft | compareRight | saveMatched | probeRight
  | restoreMatched (order : EndpointOrder)
  | restoreLeft (order : EndpointOrder)
  | restoreRight (order : EndpointOrder)
  | restoreExtraLeft | restoreExtraRight
  | pushEdgeMark (order : EndpointOrder)
  | lower (order : EndpointOrder) | pushLowerTick (order : EndpointOrder)
  | pushPairSeparator (order : EndpointOrder)
  | upper (order : EndpointOrder) | pushUpperTick (order : EndpointOrder)
  | pushRecordEnd | halt | invalid
deriving DecidableEq, Fintype

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer


