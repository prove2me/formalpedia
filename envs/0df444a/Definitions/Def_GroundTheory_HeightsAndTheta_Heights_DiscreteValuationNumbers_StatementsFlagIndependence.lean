-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:07.86556+00:00
-- url     : https://prove2.me/theorems/1c409431-d965-474f-a785-b43b234147df
-- title:
--   Statements Flag Independence
-- statement:
--   Definitions and structural lemmas for Statements Flag Independence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsFlagIndependence.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBundles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def PairNumberExpansionIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (f g : Fin n → MRing ι O),
      (∀ i, IsVerticalDivisor P ϖ (z i - z' i) (f i) (g i)) →
    ∀ (m : ℕ) (A : MvPolynomial (Fin n) ℤ), A.IsHomogeneous m →
    ∀ (As Bs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ), IsPairExpansion m A As →
      IsPairExpansion m A Bs →
    ∀ Q : List (K → ℤ), Q.length + m = d + 1 →
      pairNum P z z' f g As Q = pairNum P z z' f g Bs Q
def hsymmTimes (N n a : ℕ) (R : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin (N + n)) ℤ :=
  rename (Fin.castAdd n) (hsymm (Fin N) ℤ a) * rename (Fin.natAdd N) R
def HsymmPairFlagIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' →
    ∀ (w w' v v' : Module.Basis (Fin N) Ω E) (x x' u u' : Fin N → K → ℤ)
      (f g f₂ g₂ : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g → IsFlagPair ϖ y B B' v v' u u' f₂ g₂ →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (fz gz : Fin n → MRing ι O),
      (∀ j, IsVerticalDivisor (pointIdeal O y) ϖ (z j - z' j) (fz j) (gz j)) →
    ∀ (a r : ℕ) (R : MvPolynomial (Fin n) ℤ), R.IsHomogeneous r →
    ∀ (As Bs : Fin (N + n) → MvPolynomial (Fin (N + n) ⊕ Fin (N + n)) ℤ),
      IsPairExpansion (a + r) (hsymmTimes N n a R) As →
      IsPairExpansion (a + r) (hsymmTimes N n a R) Bs →
    ∀ Q : List (K → ℤ), Q.length + (a + r) = d + 1 →
      pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz)
          (Fin.append g gz) As Q =
        pairNum (pointIdeal O y) (Fin.append u z) (Fin.append u' z') (Fin.append f₂ fz)
          (Fin.append g₂ gz) Bs Q
def SymmetricSpanHsymm.Statement : Prop :=
  ∀ (N m : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsHomogeneous m → G.IsSymmetric →
    G ∈ Submodule.span ℤ (Set.range fun μ : m.Partition => hsymmPart (Fin N) ℤ μ)
section Examples
def psumExpansionKoszul : Fin 2 → MvPolynomial (Fin 2 ⊕ Fin 2) ℤ :=
  ![psumExpansion 2 2 0 + (X (Sum.inl 1) - X (Sum.inr 1)),
    psumExpansion 2 2 1 - (X (Sum.inl 0) - X (Sum.inr 0))]
def hsymmOneExpansion : Fin (2 + 1) → MvPolynomial (Fin (2 + 1) ⊕ Fin (2 + 1)) ℤ :=
  fun i => if (i : ℕ) < 2 then 1 else 0
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


