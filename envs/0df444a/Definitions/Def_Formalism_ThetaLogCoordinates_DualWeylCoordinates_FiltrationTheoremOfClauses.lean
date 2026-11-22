-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_FiltrationTheoremOfClauses
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:53.022018+00:00
-- url     : https://prove2.me/theorems/78ca67f6-a70d-4571-9ea5-fdb8dada91b7
-- title:
--   Filtration Theorem Of Clauses
-- statement:
--   Definitions and structural lemmas for Filtration Theorem Of Clauses, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/FiltrationTheoremOfClauses.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementB
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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
def FiltrationStandardSpan : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    CF.Mpi pi = Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ x = CF.vec j I}
def FiltrationTypeIntersection : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    ∀ x : M.ι → ℤ, x ∈ CF.Mpi pi ↔ (fun i => (x i : ℚ)) ∈ typeSum M pi
def FiltrationCoactionStable : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    ∀ x ∈ CF.Mpi pi, ∀ ℓ : GLCoord ℤ n →ₗ[ℤ] ℤ,
      (fun i => ℓ (Matrix.mulVec M.A (fun j => ((x j : ℤ) : GLCoord ℤ n)) i)) ∈ CF.Mpi pi
def FiltrationDirectSummand : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    ∃ C : Submodule ℤ (M.ι → ℤ), IsCompl (CF.Mpi pi) C
def FiltrationMaximalQuotient : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    ∀ mu ∈ pi, (∀ nu ∈ pi, DomLE mu nu → nu = mu) →
      ∃ Φ : (↥(CF.Mpi pi) ⧸ (CF.Mpi (pi \ {mu})).comap (CF.Mpi pi).subtype) ≃ₗ[ℤ]
          TensorProduct ℤ ↥(SMu mu) ↥(CF.MM mu),
        ∀ (j : CF.J) (I : TIdx (CF.mu j)) (x : ↥(CF.Mpi pi)) (y : ↥(SMu mu)) (z : ↥(CF.MM mu)),
          CF.mu j = mu → StdT I → x.1 = CF.vec j I → y.1 = brk (CF.mu j) I → z.1 = CF.vec j (canT (CF.mu j)) →
          Φ (Submodule.Quotient.mk x) = y ⊗ₜ z
def HighestVectorsEqLattice : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (mu : Fin n → ℤ), Dominant mu →
    (CF.MM mu : Set (M.ι → ℤ)) = {x | IsHighest M ℤ mu x}
def HighestVectorsRationalSpan : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (mu : Fin n → ℤ), Dominant mu →
    ∀ x : M.ι → ℚ, IsHighest M ℚ mu x →
      x ∈ Submodule.span ℚ {y | ∃ j, CF.mu j = mu ∧ y = fun i => (CF.vec j (canT (CF.mu j)) i : ℚ)}
end Formalism.InvariantFactorPaths.ColumnFamilies


