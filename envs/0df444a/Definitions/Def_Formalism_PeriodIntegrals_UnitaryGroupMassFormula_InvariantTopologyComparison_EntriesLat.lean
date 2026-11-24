-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:57:51.582293+00:00
-- url     : https://prove2.me/theorems/6ce66da2-ae03-4631-b295-41d70a311382
-- title:
--   Entries Lat
-- statement:
--   Definitions and structural lemmas for Entries Lat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/EntriesLat.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdBridgeSteps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.InvTopW
open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge
def KgMat (I : AutInst) (g : ℕ) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) :
    Prop :=
  (∀ y, y ∈ I.Lf ↔ M *ᵥ y ∈ I.Lf) ∧
    ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, (M - 1) *ᵥ y = (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • z
def InNInt (I : AutInst) (N : ℕ) (x : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) : Prop :=
  ∃ z ∈ Formalism.MainNotions.S.IntAf I.F I.E, x = (N : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * z
def ThetaCont : Prop :=
  ∀ (I : AutInst) (v : InfinitePlace I.F), Continuous (thetaV I v)
def NhdFin : Prop :=
  ∀ (I : AutInst) (N : ℕ), 1 ≤ N →
    ∀ᶠ t in 𝓝 (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E), InNInt I N (tauF I t)
def NhdInv : Prop :=
  ∀ (I : AutInst), ∀ U ∈ 𝓝 (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E),
    ∃ W ∈ 𝓝 (0 : ℂ), ∃ N : ℕ, 1 ≤ N ∧
      ∀ t, (∀ v, thetaV I v t ∈ W) → InNInt I N (tauF I t) → t ∈ U
def LatEntries : Prop :=
  ∀ (I : AutInst) (N : ℕ), 1 ≤ N → ∃ g : ℕ, 1 ≤ g ∧
    ∀ M, KgMat I g M → ∀ i j, InNInt I N ((M - 1) i j)
def EntriesLat : Prop :=
  ∀ (I : AutInst) (g : ℕ), 1 ≤ g → ∃ N : ℕ, 1 ≤ N ∧
    ∀ M M' : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), M * M' = 1 →
      (∀ i j, InNInt I N ((M - 1) i j)) → (∀ i j, InNInt I N ((M' - 1) i j)) → KgMat I g M
def FinNhdA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), 1 ≤ N →
    {a : FiniteAdeleRing (𝓞 F) F | ∃ z ∈ Formalism.UG.intAd F, a = (N : FiniteAdeleRing (𝓞 F) F) * z} ∈
      𝓝 (0 : FiniteAdeleRing (𝓞 F) F)
def FinNhdB : Prop :=
  ∀ (F : Type) [Field F] [NumberField F], ∀ U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F),
    ∃ N : ℕ, 1 ≤ N ∧ ∀ z ∈ Formalism.UG.intAd F, (N : FiniteAdeleRing (𝓞 F) F) * z ∈ U
end PI.InvTopW


