-- Prove2me | Definitions.Def_PricingWithTips3DM_93cf5334ca2495cea30cc7c0Part3
-- name    : PricingWithTips3DM_93cf5334ca2495cea30cc7c0Part3
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-23T06:31:49.050112+00:00
-- url     : https://prove2.me/theorems/207746e4-f783-4e43-97ef-fea62f3bea46
-- title:
--   PricingWithTips 3DM dependency: CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.QueryNormalizer.Basic.Part3
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/tanktechnology/CLRS-Lean

import Definitions.Def_PricingWithTips3DM_93cf5334ca2495cea30cc7c0Part2
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer
open PolyBuilder

def cfg (label : Label) (buffer : Option CliqueSym) (test : Bool)
    (input output : List CliqueSym) (left right scratch : List Unit) :
    BuilderCfg revProgram where
  label := some label
  buffer₁ := buffer
  buffer₂ := none
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := left
  counter₂ := right
  counter₃ := scratch

end CLRS.Chapter34.Turing.GeneralCliqueVerifier.QueryNormalizer


