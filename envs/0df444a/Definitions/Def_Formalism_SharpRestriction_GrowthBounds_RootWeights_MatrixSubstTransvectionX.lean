-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
-- name    : Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:25:02.191825+00:00
-- url     : https://prove2.me/theorems/a2b61872-6bde-46ba-bbbc-dbce40d9f3e4
-- title:
--   Matrix Subst Transvection X
-- statement:
--   Definitions and structural lemmas for Matrix Subst Transvection X, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionX.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst
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
namespace Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
def sourceVar {ι : Type*} {n : ℕ} (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n :=
  if LL.vec l then (l, b) else (l, a)
def targetVar {ι : Type*} {n : ℕ} (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n :=
  if LL.vec l then (l, a) else (l, b)
def letterSign (B : Type*) [CommRing B] {ι : Type*} (LL : Letters ι) (l : ι) : B := if LL.vec l then 1 else -1
section X
variable {R B : Type*} [CommRing R] [CommRing B] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
  (φ : R →+* B) (a b : Fin n) (t : B)
end X
section fs
variable {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (a b : Fin n)
end fs
end Formalism.MainNotions.G.GLWeightTheory


