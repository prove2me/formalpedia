-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:52.67+00:00
-- url     : https://prove2.me/theorems/08166efa-5e7e-4f64-b441-f4fbc440a267
-- title:
--   Taylor Comp
-- statement:
--   Definitions and structural lemmas for Taylor Comp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/TaylorComp.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
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
open MvPowerSeries
open scoped ContDiff
section TayN
variable {n g : ℕ}
def dirsN (k : Fin n × Fin g →₀ ℕ) : Multiset (Fin n × Fin g → ℂ) :=
  (Finsupp.toMultiset k).map fun q => Pi.single q 1
def fctN (k : Fin n × Fin g →₀ ℕ) : ℂ := ∏ q, ((k q).factorial : ℂ)
def tayN (Θ : (Fin n × Fin g → ℂ) → ℂ) : MvPowerSeries (Fin n × Fin g) ℂ :=
  fun k => mD Θ 0 (dirsN k) / fctN k
end TayN
def TaylorCompSt : Prop :=
  ∀ (g : ℕ) (f : (Fin g → ℂ) → ℂ), ContDiffAt ℂ ω f 0 →
    (∀ c : Fin g → ℂ, tay (fun z => f fun i => c i * z i) 0 =
      subst (fun p : Fin 1 × Fin g => C (c p.2) * X p) (tay f 0)) ∧
    tayN (n := 2) (fun z => f fun i => z ((0 : Fin 2), i) + z ((1 : Fin 2), i)) =
      subst (fun p : Fin 1 × Fin g =>
        (X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2) : MvPowerSeries (Fin 2 × Fin g) ℂ)) (tay f 0)
end ReciprocityTheory.ChartRestriction.G.PullbackSections


