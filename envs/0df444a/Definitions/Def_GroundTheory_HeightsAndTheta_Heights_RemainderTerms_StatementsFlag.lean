-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:10.112021+00:00
-- url     : https://prove2.me/theorems/c050012e-1a17-4515-9298-ee0b354960fd
-- title:
--   Statements Flag
-- statement:
--   Definitions and structural lemmas for Statements Flag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StatementsFlag.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
namespace RestTerms
open MvPolynomial Finset
noncomputable section
def IsBlockAlternating (f N : ℕ) (P : RootRing f N) : Prop :=
  ∀ w : Fin f → Equiv.Perm (Fin N), blockPermute f N w P = blockSign f N w • P
def IsBlockSymmetric (f N : ℕ) (P : RootRing f N) : Prop :=
  ∀ w : Fin f → Equiv.Perm (Fin N), blockPermute f N w P = P
def FlagCoeffBlockPermute.Statement : Prop :=
  ∀ (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (P : RootRing f N) (α : Fin f × Fin N →₀ ℕ),
    coeff α (blockPermute f N w P) =
      coeff (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2)) P
def FlagAltCoeffInjective.Statement : Prop :=
  ∀ (f N : ℕ) (P : RootRing f N) (α : Fin f × Fin N →₀ ℕ),
    IsBlockAlternating f N P → coeff α P ≠ 0 → ∀ τ : Fin f, Function.Injective fun i : Fin N => α (τ, i)
def FlagInjSumBound.Statement : Prop :=
  ∀ (N : ℕ) (g : Fin N → ℕ), Function.Injective g →
    N * (N - 1) / 2 ≤ ∑ i, g i ∧ (∑ i, g i = N * (N - 1) / 2 → ∀ i, g i < N)
def FlagStaircaseOrbit.Statement : Prop :=
  ∀ (f N : ℕ) (α β : Fin f × Fin N →₀ ℕ), (∀ τ i, α (τ, i) < N) → (∀ τ i, β (τ, i) < N) →
    (∀ τ, Function.Injective fun i : Fin N => α (τ, i)) →
    (∀ τ, Function.Injective fun i : Fin N => β (τ, i)) →
    ∃ w : Fin f → Equiv.Perm (Fin N), ∀ τ i, α (τ, w τ i) = β (τ, i)
def FlagVandermondeHomogeneous.Statement : Prop :=
  ∀ f N : ℕ, (blockVandermonde f N).IsHomogeneous (topDegree f N)
def FlagAltTopDegree.Statement : Prop :=
  ∀ (f N : ℕ) (P : RootRing f N), IsBlockAlternating f N P → P.IsHomogeneous (topDegree f N) →
    ∃ e : ℚ, P = C e * blockVandermonde f N
def FlagIntegralPermute.Statement : Prop :=
  ∀ (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (H : RootRing f N),
    flagIntegral f N (blockPermute f N w H) = blockSign f N w * flagIntegral f N H
def FlagIntegralAntisymmetrize.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N),
    flagIntegral f N (antisymmetrize f N H) = (N.factorial : ℚ) ^ f * flagIntegral f N H
def FlagIntegralVandermondePos.Statement : Prop :=
  ∀ f N : ℕ, 0 < flagIntegral f N (blockVandermonde f N)
def FlagAntisymHomogeneous.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N) (d : ℕ), H.IsHomogeneous d → (antisymmetrize f N H).IsHomogeneous d
def FlagHomogeneousComponentMul.Statement : Prop :=
  ∀ (σ : Type) (P G : MvPolynomial σ ℚ) (k n : ℕ), P.IsHomogeneous k →
    homogeneousComponent n (P * G) = if k ≤ n then P * homogeneousComponent (n - k) G else 0
def FlagIntegralTopComponent.Statement : Prop :=
  ∀ (f N : ℕ) (Φ : RootRing f N),
    flagIntegral f N Φ = flagIntegral f N (homogeneousComponent (topDegree f N) Φ)
def FlagIntegralVandermondeMul.Statement : Prop :=
  ∀ (f N : ℕ) (R : RootRing f N),
    flagIntegral f N (blockVandermonde f N * R) = constantCoeff R * flagIntegral f N (blockVandermonde f N)
def FlagIntegralViaQuotient.Statement : Prop :=
  ∀ (f N : ℕ) (H R : RootRing f N), antisymmetrize f N H = blockVandermonde f N * R →
    flagIntegral f N H =
      flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f * constantCoeff R
def FlagIntegralTopDegree.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N), H.IsHomogeneous (topDegree f N) →
    algebraMap ℚ (FractionRing (RootRing f N)) (flagIntegral f N H) =
      algebraMap ℚ (FractionRing (RootRing f N))
          (flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f) *
        dividedDifference f N H
def FlagSymmetricMulAntisym.Statement : Prop :=
  ∀ (f N : ℕ) (P H : RootRing f N), IsBlockSymmetric f N P →
    antisymmetrize f N (P * H) = P * antisymmetrize f N H
def FlagPowerSumSymmetric.Statement : Prop :=
  ∀ (f N k : ℕ) (τ : Fin f), IsBlockSymmetric f N (blockPowerSum f N k τ)
def FlagSwapDivisible.Statement : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (P : MvPolynomial σ ℚ) (a b : σ), a ≠ b →
    rename (Equiv.swap a b) P = -P → (X a - X b : MvPolynomial σ ℚ) ∣ P
def FlagDiffPrime.Statement : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (a b : σ), a ≠ b → Prime (X a - X b : MvPolynomial σ ℚ)
def FlagDiffNotDvd.Statement : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (a b c d : σ), a ≠ b → c ≠ d → ¬ (a = c ∧ b = d) →
    ¬ (a = d ∧ b = c) → ¬ (X a - X b : MvPolynomial σ ℚ) ∣ (X c - X d)
def FlagProdPrimesDvd.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ι : Type) (s : Finset ι) (p : ι → R) (x : R),
    (∀ i ∈ s, Prime (p i)) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ p i ∣ p j) → (∀ i ∈ s, p i ∣ x) →
      (∏ i ∈ s, p i) ∣ x
def FlagVandermondeDvd.Statement : Prop :=
  ∀ (f N : ℕ) (P : RootRing f N), IsBlockAlternating f N P → blockVandermonde f N ∣ P
def FlagDividedDifferencePoly.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N), ∃ R : RootRing f N,
    antisymmetrize f N H = blockVandermonde f N * R ∧ IsBlockSymmetric f N R
def FlagQuotientHomogeneous.Statement : Prop :=
  ∀ (σ : Type) (A R : MvPolynomial σ ℚ) (m k : ℕ), A ≠ 0 → A.IsHomogeneous m →
    (A * R).IsHomogeneous (m + k) → R.IsHomogeneous k
def FlagRestrictSymmetric.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : RootRing f N), IsBlockSymmetric f N R →
    (restrictToBlock f N τ R).IsSymmetric
def FlagRestrictPowerSum.Statement : Prop :=
  ∀ (f N k : ℕ) (τ σ : Fin f), 1 ≤ k →
    restrictToBlock f N τ (blockPowerSum f N k σ) = if σ = τ then psum (Fin N) ℚ k else 0
def FlagRestrictConstantCoeff.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : RootRing f N),
    constantCoeff (restrictToBlock f N τ R) = constantCoeff R
def FlagRestrictHomogeneous.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : RootRing f N) (k : ℕ), R.IsHomogeneous k →
    (restrictToBlock f N τ R).IsHomogeneous k
def FlagRestrictDecomposition.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : ℕ → Fin f → RootRing f N),
    restrictToBlock f N τ (∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f, blockPowerSum f N l σ * R l σ) =
      ∑ l ∈ Finset.Icc 1 N, psum (Fin N) ℚ l * restrictToBlock f N τ (R l τ)
def FlagPowerSumPreimage.Statement : Prop :=
  ∀ (N : ℕ) (T : ℕ → MvPolynomial (Fin N) ℚ), (∀ l, (T l).IsSymmetric) →
    ∃ S : MvPolynomial (Fin N) ℚ,
      powerSumHom N S = ∑ l ∈ Finset.Icc 1 N, psum (Fin N) ℚ l * T l ∧
      ∀ (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N),
        coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) S = constantCoeff (T k)
def FlagAntisymDecomposition.Statement : Prop :=
  ∀ (f N : ℕ) (F G : RootRing f N) (Q R : ℕ → Fin f → RootRing f N),
    IsPowerSumDecomposition f N F Q →
    (∀ l σ, antisymmetrize f N (G * Q l σ) = blockVandermonde f N * R l σ) →
    antisymmetrize f N (G * F) =
      blockVandermonde f N * ∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f, blockPowerSum f N l σ * R l σ
end
end RestTerms
end GroundTheory.Heights₂.Heights


