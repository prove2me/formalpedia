-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDensityCorank_SplitCount
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDensityCorank_SplitCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:31.183032+00:00
-- url     : https://prove2.me/theorems/24d8fb27-99bf-43d9-8c2e-4e2bd7de0bab
-- title:
--   Split Count
-- statement:
--   Definitions and structural lemmas for Split Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDensityCorank/SplitCount.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDensCorank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Classical
noncomputable section
namespace PI.UnitaryGroupMassFormula.LocDensCorank
open Formalism.MainNotions.S
def CongStep : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) (ϖ : 𝒪[F])
      (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι E) (a : ι → 𝒪[F]),
        (∀ i j, A i j ∈ M.L.O) → (∃ y ∈ M.L.O, A.det * y = 1) →
          H.dens ϖ Λ ((A.map M.L.cj).transpose * Matrix.diagonal (fun i => algebraMap F E (a i : F)) * A) =
            H.dens ϖ Λ (Matrix.diagonal (fun i => algebraMap F E (a i : F)))
def FieldCount : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    (∀ x : E, x ≠ 0 → IsUnit x) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (a : ι → 𝒪[F]),
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ (Matrix.diagonal (fun i => algebraMap F E (a i : F))) =
            Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) (-1)
              (Module.finrank E V) (Fintype.card ι) (Finset.univ.filter fun i => ϖ ∣ a i).card
def SplitCount : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    (∃ e : E ≃ₐ[F] F × F, ∀ x, e (M.L.cj x) = (e x).swap) →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (a : ι → 𝒪[F]),
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ (Matrix.diagonal (fun i => algebraMap F E (a i : F))) =
            Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) 1
              (Module.finrank E V) (Fintype.card ι) (Finset.univ.filter fun i => ϖ ∣ a i).card
end PI.UnitaryGroupMassFormula.LocDensCorank


