-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_HermitianTensor_ShapeCovering_StatementY
-- name    : Formalism_SharpRestriction_GrowthBounds_HermitianTensor_ShapeCovering_StatementY
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:41.126499+00:00
-- url     : https://prove2.me/theorems/4a2a87a0-699e-43ba-9380-f4e86101c5df
-- title:
--   Statement Y
-- statement:
--   Definitions and structural lemmas for Statement Y, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/HermitianTensor/ShapeCovering/StatementY.lean

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.flipOneThree.Pf.ShapeCovering
open MvPolynomial Formalism.GradedWeylDivisibility
def covY (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K :=
  (-1) ^ (i : ℕ) * Matrix.det (fun a b : Fin m => (X (i.succAbove a, b.castSucc) : MvPolynomial _ K))
def FirstColumnPolynomialsSpan : Prop :=
  ∀ (K : Type) [Field K] (m P : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K), 1 ≤ m →
    (F ∈ dualWeyl K (m + 1) (m + 1) (fun t => if t = 0 then P else 0) ↔
      ∃ f : MvPolynomial (Fin (m + 1)) K, f.IsHomogeneous P ∧ rename (fun i => (i, (0 : Fin (m + 1)))) f = F)
def SignedMinorPolynomialsSpan : Prop :=
  ∀ (K : Type) [Field K] (m Q : ℕ) (F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K), 1 ≤ m →
    (F ∈ dualWeyl K (m + 1) (m + 1) (fun t => if t = Fin.last m then 0 else Q) ↔
      ∃ f : MvPolynomial (Fin (m + 1)) K, f.IsHomogeneous Q ∧ aeval (covY K m) f = F)
def SignedMinorsAlgIndependent : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ), 1 ≤ m → AlgebraicIndependent K (covY K m)
def IncidenceRelation : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ), 1 ≤ m → ∑ i, X (i, (0 : Fin (m + 1))) * covY K m i = 0
def SignedMinorsCofactorTransform : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)), IsUnit g.det →
    rowAct K g (covY K m i) = C g.det * ∑ j, C (g⁻¹ j i) * covY K m j
def CovL5adj : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (i : Fin (m + 1)),
    rowAct K g (covY K m i) = ∑ j, C (g.adjugate j i) * covY K m j
end Formalism.MainNotions.flipOneThree.Pf.ShapeCovering


