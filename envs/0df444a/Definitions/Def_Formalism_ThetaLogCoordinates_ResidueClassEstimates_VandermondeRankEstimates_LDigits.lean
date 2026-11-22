-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LDigits
-- name    : Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LDigits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:31:10.428491+00:00
-- url     : https://prove2.me/theorems/e225e8a1-8e13-421a-aa64-7977da815b1f
-- title:
--   LDigits
-- statement:
--   Definitions and structural lemmas for LDigits, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/VandermondeRankEstimates/LDigits.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.BranchingDimensions
section Digits
variable {I1 I2 : Type}
def cTgt : CoarseVar I1 I2 → I1 ⊕ I2
  | Sum.inl i => Sum.inl i
  | Sum.inr (Sum.inl i) => Sum.inr i
  | Sum.inr (Sum.inr i) => Sum.inr i
def cWt (P : I1 ⊕ I2 → ℕ) (Q : I2 → ℕ) : CoarseVar I1 I2 → ℕ
  | Sum.inl i => P (Sum.inl i)
  | Sum.inr (Sum.inl i) => P (Sum.inr i)
  | Sum.inr (Sum.inr i) => P (Sum.inr i) * Q i
def cExp (P : I1 ⊕ I2 → ℕ) (Q : I2 → ℕ) : (CoarseVar I1 I2 →₀ ℕ) →+ ((I1 ⊕ I2) →₀ ℕ) :=
  Finsupp.liftAddHom fun x => (Finsupp.singleAddHom (cTgt x)).comp (AddMonoidHom.mulRight (cWt P Q x))
def digM (P : I1 ⊕ I2 → ℕ) (Q : I2 → ℕ) (e : (I1 ⊕ I2) →₀ ℕ) : CoarseVar I1 I2 →₀ ℕ :=
  Finsupp.sumElim
    (Finsupp.onFinset (e.comapDomain Sum.inl Sum.inl_injective.injOn).support
      (fun i => e (Sum.inl i) / P (Sum.inl i)) (by
        intro i hi
        rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply]
        intro h0; rw [h0] at hi; simp at hi))
    (Finsupp.sumElim
      (Finsupp.onFinset (e.comapDomain Sum.inr Sum.inr_injective.injOn).support
        (fun i => (e (Sum.inr i) / P (Sum.inr i)) % Q i) (by
          intro i hi
          rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply]
          intro h0; rw [h0] at hi; simp at hi))
      (Finsupp.onFinset (e.comapDomain Sum.inr Sum.inr_injective.injOn).support
        (fun i => (e (Sum.inr i) / P (Sum.inr i)) / Q i) (by
          intro i hi
          rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply]
          intro h0; rw [h0] at hi; simp at hi)))
def digL (P : I1 ⊕ I2 → ℕ) (e : (I1 ⊕ I2) →₀ ℕ) : (I1 ⊕ I2) →₀ ℕ :=
  Finsupp.onFinset e.support (fun i => e i % P i) (by
    intro i hi
    rw [Finsupp.mem_support_iff]
    intro h0; rw [h0] at hi; simp at hi)
end Digits
section Residue
def cnt (T Q r c : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin r → Fin T)).filter (fun u => (∑ l, (u l : ℕ)) % Q = c % Q)).card
end Residue
section Exact
end Exact
end Formalism.InvariantFactorPaths.BranchingDimensions


