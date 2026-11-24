-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_DualWeylIn
-- name    : Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_DualWeylIn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:29.779328+00:00
-- url     : https://prove2.me/theorems/c42ae030-1811-4fe2-9621-0320d1b919db
-- title:
--   Dual Weyl In
-- statement:
--   Definitions and structural lemmas for Dual Weyl In, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/FockModels/TransposeWords/DualWeylIn.lean

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_SandwichModelDomains_StatementW
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility Formalism.InvariantFactorPaths.INST
def WeylPair : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
    (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∀ P ∈ (weyl O r n hn ν).map (toK O K), ∀ Q ∈ (dualWeyl O r n ν).map (toK O K),
      ∃ z : O, fockR P Q = algebraMap O K z * fockR (hw K hn ν) (hw K hn ν)
def DualWeylIn : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] [CharZero K]
    (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ Q ∈ dualWeyl K r n ν,
    (∀ P ∈ (weyl O r n hn ν).map (toK O K), ∃ z : O, fockR P Q = algebraMap O K z * fockR (hw K hn ν) (hw K hn ν)) →
    Q ∈ (dualWeyl O r n ν).map (toK O K)
def NondegK : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (r n : ℕ) (_hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν → ∀ Q ∈ dualWeyl K r n ν,
    (∀ P ∈ dualWeyl K r n ν, fockR P Q = 0) → Q = 0
def FormCoreG : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CharZero K], ¬ IsUnit ((p : ℕ) : O) →
    ∀ (r n : ℕ) (_hn : n ≤ r) (ν : Fin n → ℕ), Antitone ν →
    ∃ B : MvPolynomial (Fin r × Fin n) K →ₗ[K] MvPolynomial (Fin r × Fin n) K →ₗ[K] K,
      (∀ (g : Matrix (Fin r) (Fin r) K) (P Q : MvPolynomial (Fin r × Fin n) K),
        B (rowAct K g P) Q = B P (rowAct K g.transpose Q)) ∧
      (∀ Q ∈ dualWeyl K r n ν, (∀ P ∈ dualWeyl K r n ν, B P Q = 0) → Q = 0) ∧
      (∀ Q ∈ dualWeyl K r n ν,
        (∀ P ∈ (dualWeyl O r n ν).map (toK O K), B P Q ∈ Set.range (algebraMap O K)) → Q ∈ (dualWeyl O r n ν).map (toK O K)) ∧
      (∀ l : ℕ, LBound r ν l → ∀ Q ∈ (dualWeyl O r n ν).map (toK O K), ∀ P ∈ (dualWeyl O r n ν).map (toK O K),
        B P (((p : K) ^ sExp p r l) • Q) ∈ Set.range (algebraMap O K)) ∧
      ((∀ t, ν t = 0) → ∀ Q ∈ (dualWeyl O r n ν).map (toK O K), ∀ P ∈ (dualWeyl O r n ν).map (toK O K),
        B P Q ∈ Set.range (algebraMap O K))
end Formalism.L2.G.Model.TS


