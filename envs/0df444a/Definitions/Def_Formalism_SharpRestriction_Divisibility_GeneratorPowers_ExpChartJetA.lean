-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:14.480787+00:00
-- url     : https://prove2.me/theorems/cdd49300-76b3-4af1-b67d-683145f9e1c3
-- title:
--   Exp Chart Jet A
-- statement:
--   Definitions and structural lemmas for Exp Chart Jet A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExpChartJetA.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
theorem ker_fst_sq : RingHom.ker (TrivSqZeroExt.fstHom R R R) ^ (0 + 1 + 1) = ⊥ := by
  show RingHom.ker (TrivSqZeroExt.fstHom R R R) ^ 2 = ⊥
  rw [sq, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  have hx' : x.fst = 0 := by simpa using hx
  have hy' : y.fst = 0 := by simpa using hy
  rw [Ideal.mem_bot]
  ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, hx', hy']
def tp {κ : Type} (g : κ → R) : Jet R κ (0 + 1) →ₐ[R] DualNumber R :=
  liftJet (MvPolynomial.aeval fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) (by
    apply le_bot_iff.1
    refine (Ideal.pow_right_mono (Ideal.span_le.2 ?_) _).trans (le_of_eq ker_fst_sq)
    rintro _ ⟨q, rfl⟩
    simp)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA


