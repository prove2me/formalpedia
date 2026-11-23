-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:48.691658+00:00
-- url     : https://prove2.me/theorems/f1ed0ec4-4e5a-4ed8-9eb1-1cff41f00c4c
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularGenus/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnimodGenus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace PI.UG.W
section Defs
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
def locR (p : Ideal R) : Submodule R K := loc (K := K) p (1 : Submodule R K)
def dualAt (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) : Submodule R V :=
  ⨅ y ∈ L, (locR (K := K) p).comap ((h y).restrictScalars R)
def IsUnimodularAt (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) : Prop :=
  dualAt h p (loc (K := K) p L) = loc (K := K) p L
end Defs
def UnimodLocal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ),
    ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → IsUnimodular (hStd E n) N →
      ∀ p : Ideal (𝓞 E), p.IsMaximal → IsUnimodularAt (hStd E n) p N
def IsomLocStd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ), IsCMUnram E →
    ∀ N : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N →
      ∀ p : Ideal (𝓞 E), p.IsMaximal → IsUnimodularAt (hStd E n) p N →
        ∃ g ∈ isom (hStd E n), gmap g (loc (K := E) p (stdLat E n)) = loc (K := E) p N
end PI.UG.W


