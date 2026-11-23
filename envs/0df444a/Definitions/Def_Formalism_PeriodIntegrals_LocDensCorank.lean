-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_LocDensCorank
-- name    : Formalism_PeriodIntegrals_LocDensCorank
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:20:40.636943+00:00
-- url     : https://prove2.me/theorems/f219763b-7b16-4544-a305-bd24a6e46686
-- title:
--   Loc Dens Corank
-- statement:
--   Definitions and structural lemmas for Loc Dens Corank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/LocDensCorank.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_LinQRawRange
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
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
namespace PI.LocDensCorank
open Formalism.MainNotions.S
def LocDensCorank : Prop :=
  ∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E),
    IsNonarchimedeanLocalField F → CharZero F →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V),
      H.IsSelfDual Λ → ∀ ϖ : 𝒪[F], Irreducible ϖ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι E) (a : ι → 𝒪[F]),
        (∀ i j, A i j ∈ M.L.O) → (∃ y ∈ M.L.O, A.det * y = 1) →
        Fintype.card ι ≤ Module.finrank E V →
          H.dens ϖ Λ ((A.map M.L.cj).transpose * Matrix.diagonal (fun i => algebraMap F E (a i : F)) * A) =
            Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) (if ∀ x : E, x ≠ 0 → IsUnit x then -1 else 1)
              (Module.finrank E V) (Fintype.card ι) (Finset.univ.filter fun i => ϖ ∣ a i).card
end PI.LocDensCorank


