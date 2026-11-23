-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PBlocksAlg
-- name    : Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_InfinitesimalCharacterLimits_LieSumDecompositions_PBlocksAlg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:47.284499+00:00
-- url     : https://prove2.me/theorems/c66290a5-ec49-4a12-89bb-ad22f666ed6d
-- title:
--   PBlocks Alg
-- statement:
--   Definitions and structural lemmas for PBlocks Alg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/InfinitesimalCharacterLimits/LieSumDecompositions/PBlocksAlg.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
section Ker
variable {M : Type} [AddCommGroup M] [Module ℂ M]
end Ker
section Poly
variable {M : Type} [AddCommGroup M] [Module ℂ M]
end Poly
section Piece
variable {M : Type} [AddCommGroup M] [Module ℂ M]
def spoly (n : ℕ) (χ : ℕ → ℂ) : ℂ[X] := X ^ n + ∑ i : Fin n, C (χ i) * X ^ (i : ℕ)
end Piece
section Main
end Main
end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAlgebra
end


