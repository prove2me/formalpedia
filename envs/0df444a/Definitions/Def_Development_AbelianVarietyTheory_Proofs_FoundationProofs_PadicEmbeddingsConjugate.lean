-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicEmbeddingsConjugate
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicEmbeddingsConjugate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:58.436139+00:00
-- url     : https://prove2.me/theorems/61d8ded7-a831-4dbe-b12d-a70cd85e18c0
-- title:
--   Padic Embeddings Conjugate
-- statement:
--   Definitions and structural lemmas for Padic Embeddings Conjugate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicEmbeddingsConjugate.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace GlobalTheory.EmbUnitBallConj
variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E]
noncomputable def ext (a : E →+* PadicAlgCl l) : ℚ_[l] ⊗[ℤ] E →ₐ[ℚ_[l]] PadicAlgCl l :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) a.toIntAlgHom (fun _ _ => Commute.all _ _)
end GlobalTheory.EmbUnitBallConj


