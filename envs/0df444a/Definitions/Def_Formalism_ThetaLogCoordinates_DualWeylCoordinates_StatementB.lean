-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementB
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:20.660496+00:00
-- url     : https://prove2.me/theorems/7c2e220e-5260-43a0-982b-0809b03bcd65
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/StatementB.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
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
def ColumnFamilyStandardVectorsBasis : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M),
    (LinearIndependent ℤ (fun x : (Σ j, {I : TIdx (CF.mu j) // StdT I}) => CF.vec x.1 x.2.1) ∧
      Submodule.span ℤ (Set.range fun x : (Σ j, {I : TIdx (CF.mu j) // StdT I}) => CF.vec x.1 x.2.1) = ⊤) ∧
    ∀ (R : Type) [CommRing R],
      LinearIndependent R (fun x : (Σ j, {I : TIdx (CF.mu j) // StdT I}) => fun i => (CF.vec x.1 x.2.1 i : R)) ∧
      Submodule.span R (Set.range fun x : (Σ j, {I : TIdx (CF.mu j) // StdT I}) =>
        fun i => (CF.vec x.1 x.2.1 i : R)) = ⊤
def ColumnFamilyFiltrationProperties : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    CF.Mpi pi = Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ x = CF.vec j I} ∧
    (∀ x : M.ι → ℤ, x ∈ CF.Mpi pi ↔ (fun i => (x i : ℚ)) ∈ typeSum M pi) ∧
    (∀ x ∈ CF.Mpi pi, ∀ ℓ : GLCoord ℤ n →ₗ[ℤ] ℤ,
      (fun i => ℓ (Matrix.mulVec M.A (fun j => ((x j : ℤ) : GLCoord ℤ n)) i)) ∈ CF.Mpi pi) ∧
    (∃ C : Submodule ℤ (M.ι → ℤ), IsCompl (CF.Mpi pi) C) ∧
    ∀ mu ∈ pi, (∀ nu ∈ pi, DomLE mu nu → nu = mu) →
      (∃ Φ : (↥(CF.Mpi pi) ⧸ (CF.Mpi (pi \ {mu})).comap (CF.Mpi pi).subtype) ≃ₗ[ℤ]
          TensorProduct ℤ ↥(SMu mu) ↥(CF.MM mu),
        ∀ (j : CF.J) (I : TIdx (CF.mu j)) (x : ↥(CF.Mpi pi)) (y : ↥(SMu mu)) (z : ↥(CF.MM mu)),
          CF.mu j = mu → StdT I → x.1 = CF.vec j I → y.1 = brk (CF.mu j) I → z.1 = CF.vec j (canT (CF.mu j)) →
          Φ (Submodule.Quotient.mk x) = y ⊗ₜ z) ∧
      (CF.MM mu : Set (M.ι → ℤ)) = {x | IsHighest M ℤ mu x}
def FiltrationGenericPointCriterion : Prop :=
  ∀ (n : ℕ) [NeZero n] (M : GLMod n) (CF : ColFam M) (pi : Set (Fin n → ℤ)), DomLowerSet pi →
    ∀ (F : Type) [Field F] (x : M.ι → F),
      x ∈ Submodule.span F {y | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), StdT I ∧ y = fun i => (CF.vec j I i : F)} ↔
      ∀ mu, Dominant mu → mu ∉ pi →
        Matrix.mulVec ((prMu M mu).map (Int.castRingHom (GLCoord F n)))
          (Matrix.mulVec (M.A.map (mapCoord F)) (fun i => algebraMap F (GLCoord F n) (x i))) = 0
end Formalism.InvariantFactorPaths.ColumnFamilies


