-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst
-- name    : Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:18:37.9258+00:00
-- url     : https://prove2.me/theorems/68048246-b605-4430-84a0-b8531ce1b524
-- title:
--   Twist Sub Eq Matrix Subst
-- statement:
--   Definitions and structural lemmas for Twist Sub Eq Matrix Subst, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/TwistSubEqMatrixSubst.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
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
open Classical in

def matrixSubst {R B : Type*} [CommRing R] [CommRing B] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
    (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) :
    MvPolynomial (ι × Fin n) R →+* MvPolynomial (ι × Fin n) B :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp φ) fun v =>
    if v.1 ∈ S then
      (if LL.vec v.1 then ∑ b : Fin n, MvPolynomial.C (m b v.2) * X (v.1, b)
       else ∑ b : Fin n, MvPolynomial.C (m' v.2 b) * X (v.1, b))
    else X v
section basic
variable {R B B' : Type*} [CommRing R] [CommRing B] [CommRing B'] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
end basic
def TransvectionExpansion : Prop :=
  ∀ (R B : Type) [CommRing R] [CommRing B] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) (S : Set ι)
    (φ : R →+* B) (a b : Fin n), a ≠ b → ∀ (t : B) (F : MvPolynomial (ι × Fin n) R) (N : ℕ), F.totalDegree < N →
      matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) F =
        ∑ k ∈ Finset.range N, C (t ^ k) * MvPolynomial.map φ (divPow R LL S a b k F)
end Formalism.MainNotions.G.GLWeightTheory


