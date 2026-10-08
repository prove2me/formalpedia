-- Prove2me | Definitions.Def_MazurTransfer_Order18KernelGeneratorSupportCertificate
-- name    : MazurTransfer_Order18KernelGeneratorSupportCertificate
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-07T16:12:42.704069+00:00
-- url     : https://prove2.me/theorems/277c7107-ce17-40a0-9235-fcd55e64303d
-- title:
--   Order18: a certificate that the four explicit generators are supported above two
-- statement:
--   Let \(K=\mathbb{Q}[T]/(T^3-3T-1)\) and \(M=K[S]/(S^3-3S-10)\), with the four explicit compositum generators \(h_1,h_2,h_3,h_4\) from the published data. This structure bundles evidence that each class \([h_i]\in M^\times/(M^\times)^2\) belongs to the supported squareclass group: its valuation is even at every prime not above two. The existence of this certificate is supplied by a separate theorem.
-- source:
--   Exact original KernelGeneratorSupportCertificate structure from user WIP54d43d8dda8a6fcf069cc02a815f850d762c5c0c, selected by typed declaration ownership and complete original Lean AST command ranges. Original copyright, author list and Apache-2.0 header retained. The structure has only proof fields over the already published original ambient Selmer data. Inhabitation, cardinality and all global/local arithmetic are separate theorems. Named downstream consumer: the unchanged unconditional original cubic quotient doubling-surjectivity theorem, MazurTransfer.order18_original_quotient_doubling_surjective.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/
/- Copyright (c) 2026 Vasily Ilin. Released under Apache-2.0.
Exact pure certificate structure from the original WIP, staged locally only. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order18AmbientSelmer
namespace MazurTorsion.XOneEighteenGlobalSelmerBridge
/-- Membership of the four explicit norm-kernel generators in the dyadic
Selmer group.  This is the global support certificate consumed by the
masked-product enumeration. -/
structure KernelGeneratorSupportCertificate where
  generator_mem : ∀ i : Fin 4, kernelGenerator i ∈ DyadicSelmerM
end MazurTorsion.XOneEighteenGlobalSelmerBridge


