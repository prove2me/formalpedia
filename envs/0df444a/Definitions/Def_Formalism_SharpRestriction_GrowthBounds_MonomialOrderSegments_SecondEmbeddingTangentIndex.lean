-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
-- name    : Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:54.309483+00:00
-- url     : https://prove2.me/theorems/c9eeeeab-68b0-406b-97bd-748497b8c6bf
-- title:
--   Second Embedding Tangent Index
-- statement:
--   Definitions and structural lemmas for Second Embedding Tangent Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
namespace TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
def Marked (o : Finset (Fin (D.nB j + D.r))) : Prop := ∃ l ∈ o, l.val < D.nB j
open Classical in

def fk (o : Finset (Fin (D.nB j + D.r))) : Fin (D.nB j + D.r) → D.ML :=
  if D.Marked j o then D.e1 j else D.e0 j
def cnt (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) : ℕ :=
  ∑ l, if D.fk j o l = i then (if l ∈ o then 1 else 0) else 0
def PsiP {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r))) : MvPolynomial (D.ML × Fin D.r) K :=
  ∏ k, rename (Prod.map (D.fk j (occ k)) id) (col k)
end TwistData
end Formalism.MainNotions.PlaneGram


