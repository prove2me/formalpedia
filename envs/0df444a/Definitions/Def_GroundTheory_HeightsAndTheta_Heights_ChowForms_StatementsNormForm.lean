-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsNormForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:11.116376+00:00
-- url     : https://prove2.me/theorems/ae3c9356-927a-440c-82cc-6c689e6b94ef
-- title:
--   Statements Norm Form
-- statement:
--   Definitions and structural lemmas for Statements Norm Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/StatementsNormForm.lean

import Mathlib
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
open MvPolynomial
noncomputable section
def normForm (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S] {n : ℕ}
    (η : Fin n → S) : MvPolynomial (Fin n) R := by
  classical
  exact (Matrix.of fun i j =>
    ∑ m, X m * C (Algebra.leftMulMatrix (Module.Free.chooseBasis R S) (η m) i j)).det
def NormFormEval.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S] (n : ℕ)
    (η : Fin n → S) (u : Fin n → R),
    eval u (normForm R S η) = Algebra.norm R (∑ m, u m • η m)
def NormFormEmbeddings.Statement : Prop :=
  ∀ (K L Ω : Type) [Field K] [Infinite K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (n : ℕ) (η : Fin n → L),
    map (algebraMap K Ω) (normForm K L η) = ∏ σ : L →ₐ[K] Ω, ∑ m, X m * C (σ (η m))
def LinearFormPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (a : Fin n → F), a ≠ 0 →
    Prime (∑ m, X m * C (a m) : MvPolynomial (Fin n) F)
def MapDvdDescent.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (σ : Type) (f g : MvPolynomial σ K),
    map (algebraMap K Ω) f ∣ map (algebraMap K Ω) g → f ∣ g
def NormFormDvd.Statement : Prop :=
  ∀ (K L : Type) [Field K] [Infinite K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (n : ℕ) (η : Fin n → L) (t : Fin n → K) (P : MvPolynomial (Fin n) K),
    Algebra.adjoin K (Set.range η) = ⊤ → ∑ m, t m • η m = 1 →
      (∑ m, X m * C (η m)) ∣ map (algebraMap K L) P → normForm K L η ∣ P
def PrimeMapFractionRing.Statement : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (n : ℕ)
    (P : MvPolynomial (Fin n) O),
    Prime P → (∀ a : O, P ≠ C a) → Prime (map (algebraMap O K) P)
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights


