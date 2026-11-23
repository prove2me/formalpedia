-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:07.166171+00:00
-- url     : https://prove2.me/theorems/c80f9169-1114-4d3a-ba9a-93f85bd749a3
-- title:
--   Calc Add
-- statement:
--   Definitions and structural lemmas for Calc Add, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CalcAdd.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
def AddLinSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (f : PS k 1 d),
    ev (n := 2) ![pt k d 0 + pt k d 1] f = ev (n := 2) ![pt k d 0] f + ev (n := 2) ![pt k d 1] f →
      ∀ n : Fin 1 × Fin d →₀ ℕ, n.degree ≠ 1 → coeff n f = 0
def AddLinFstSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (f : PS k 2 d),
    ev (n := 3) ![pt k d 0 + pt k d 1, pt k d 2] f = ev (n := 3) ![pt k d 0, pt k d 2] f + ev (n := 3) ![pt k d 1, pt k d 2] f →
      ∀ n : Fin 2 × Fin d →₀ ℕ, (∑ i, n (0, i)) ≠ 1 → coeff n f = 0
def AddLinSndSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (f : PS k 2 d),
    ev (n := 3) ![pt k d 0, pt k d 1 + pt k d 2] f = ev (n := 3) ![pt k d 0, pt k d 1] f + ev (n := 3) ![pt k d 0, pt k d 2] f →
      ∀ n : Fin 2 × Fin d →₀ ℕ, (∑ i, n (1, i)) ≠ 1 → coeff n f = 0
def BiaddBilinSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (f : PS k 2 d),
    ev (n := 3) ![pt k d 0 + pt k d 1, pt k d 2] f = ev (n := 3) ![pt k d 0, pt k d 2] f + ev (n := 3) ![pt k d 1, pt k d 2] f →
    ev (n := 3) ![pt k d 0, pt k d 1 + pt k d 2] f = ev (n := 3) ![pt k d 0, pt k d 1] f + ev (n := 3) ![pt k d 0, pt k d 2] f →
      ∀ n : Fin 2 × Fin d →₀ ℕ, ¬ ((∑ i, n (0, i)) = 1 ∧ (∑ i, n (1, i)) = 1) → coeff n f = 0
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing


