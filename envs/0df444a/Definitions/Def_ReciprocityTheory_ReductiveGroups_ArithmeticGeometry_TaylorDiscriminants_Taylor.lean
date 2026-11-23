-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:36.403007+00:00
-- url     : https://prove2.me/theorems/00b1e939-95f6-418b-b4cb-8ae4b75abb6e
-- title:
--   Taylor
-- statement:
--   Definitions and structural lemmas for Taylor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
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
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff
section Sym
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
def lD (φ : V → ℂ) (x : V) (l : List V) : ℂ := iteratedFDeriv ℂ l.length φ x (fun i => l.get i)
def mD (φ : V → ℂ) (x : V) (s : Multiset V) : ℂ := lD φ x s.toList
end Sym
section Add
variable (R : Type) [CommRing R]
def addF (g : ℕ) : Fin g → PS R 2 g := fun i => X ((0 : Fin 2), i) + X ((1 : Fin 2), i)
variable {R}
end Add
section Tay
variable {g : ℕ}
def dirs (n : Fin 1 × Fin g →₀ ℕ) : Multiset (Fin g → ℂ) :=
  (Finsupp.toMultiset n).map fun p => Pi.single p.2 1
def fct (n : Fin 1 × Fin g →₀ ℕ) : ℂ := ∏ p, ((n p).factorial : ℂ)
def tay (θ : (Fin g → ℂ) → ℂ) (s : Multiset (Fin g → ℂ)) : MvPowerSeries (Fin 1 × Fin g) ℂ :=
  fun n => mD θ 0 (dirs n + s) / fct n
end Tay
section TaySt
def TaylorMulSt : Prop :=
  (∀ (g : ℕ) (f h : (Fin g → ℂ) → ℂ), ContDiffAt ℂ ω f 0 → ContDiffAt ℂ ω h 0 →
    tay (f * h) 0 = tay f 0 * tay h 0 ∧ tay (f + h) 0 = tay f 0 + tay h 0) ∧
  (∀ (g : ℕ) (c : ℂ), tay (g := g) (fun _ => c) 0 = C c) ∧
  (∀ (g : ℕ) (f h : (Fin g → ℂ) → ℂ), f =ᶠ[nhds 0] h → tay f 0 = tay h 0)
end TaySt
end ReciprocityTheory.ChartRestriction.G.PullbackSections


