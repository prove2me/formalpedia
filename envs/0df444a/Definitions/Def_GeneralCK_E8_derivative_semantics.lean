-- Prove2me | Definitions.Def_GeneralCK_E8_derivative_semantics
-- name    : GeneralCK_E8_derivative_semantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T23:10:01.283173+00:00
-- url     : https://prove2.me/theorems/67b29f40-b07e-4c72-8b3d-6e29ea3de310
-- title:
--   Fifth-order jet soundness and the E8 change of parameter
-- statement:
--   For an order-five raw jet, SoundAt requires that each of its first five components has the next component as its derivative at the chosen point. SoundOn requires these links throughout a set, and EqAt states equality of all six components. Jet composition gives the explicit chain-rule expressions through order five. The exact qdata5 recurrence changes from a parameter coordinate to the slope coordinate; atParam evaluates each derivative component at that parameter value. These original interfaces let separate theorems express canonical inverse-jet soundness and the checked interval change of parameter without assuming any numerical cell certificate.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/tree/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.MonotoneContinuity
import Definitions.Def_GeneralCK_E8_canonical_inverse_jet

open GeneralCK GeneralCK.Certificates Set GeneralCK.Certificates.DyadicInterval

section
namespace GeneralCK.Certificates



namespace Jet5

def SoundAt (j : Jet5) (t : ℝ) : Prop :=
  HasDerivAt j.d0 (j.d1 t) t ∧ HasDerivAt j.d1 (j.d2 t) t ∧
  HasDerivAt j.d2 (j.d3 t) t ∧ HasDerivAt j.d3 (j.d4 t) t ∧
  HasDerivAt j.d4 (j.d5 t) t

def SoundOn (j : Jet5) (s : Set ℝ) : Prop := ∀ t ∈ s, j.SoundAt t






























end Jet5
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates
namespace Jet5

def comp (f g : Jet5) : Jet5 :=
  ⟨fun a => f.d0 (g.d0 a),
   fun a => f.d1 (g.d0 a) * g.d1 a,
   fun a => f.d2 (g.d0 a) * g.d1 a ^ 2 + f.d1 (g.d0 a) * g.d2 a,
   fun a => f.d3 (g.d0 a) * g.d1 a ^ 3 +
     3 * f.d2 (g.d0 a) * g.d1 a * g.d2 a + f.d1 (g.d0 a) * g.d3 a,
   fun a => f.d4 (g.d0 a) * g.d1 a ^ 4 +
     6 * f.d3 (g.d0 a) * g.d1 a ^ 2 * g.d2 a +
     3 * f.d2 (g.d0 a) * g.d2 a ^ 2 +
     4 * f.d2 (g.d0 a) * g.d1 a * g.d3 a + f.d1 (g.d0 a) * g.d4 a,
   fun a => f.d5 (g.d0 a) * g.d1 a ^ 5 +
     10 * f.d4 (g.d0 a) * g.d1 a ^ 3 * g.d2 a +
     15 * f.d3 (g.d0 a) * g.d1 a * g.d2 a ^ 2 +
     10 * f.d3 (g.d0 a) * g.d1 a ^ 2 * g.d3 a +
     10 * f.d2 (g.d0 a) * g.d2 a * g.d3 a +
     5 * f.d2 (g.d0 a) * g.d1 a * g.d4 a + f.d1 (g.d0 a) * g.d5 a⟩



def EqAt (f g : Jet5) (a : ℝ) : Prop :=
  f.d0 a = g.d0 a ∧ f.d1 a = g.d1 a ∧ f.d2 a = g.d2 a ∧
    f.d3 a = g.d3 a ∧ f.d4 a = g.d4 a ∧ f.d5 a = g.d5 a



end Jet5

namespace E8TAxisReparamJet5



/-- Exactly the raw derivative formulas in the retained C++ `qdata5`. -/
noncomputable def qdata5 (x y : Jet5) : Jet5 :=
  let p := y.d1
  let p2 := y.d2
  let p3 := y.d3
  let p4 := y.d4
  let p5 := y.d5
  ⟨x.d0,
   fun a => x.d1 a / p a,
   fun a => (p a * x.d2 a - p2 a * x.d1 a) / p a ^ 3,
   fun a => (p a ^ 2 * x.d3 a - 3 * p a * p2 a * x.d2 a -
     p a * p3 a * x.d1 a + 3 * p2 a ^ 2 * x.d1 a) / p a ^ 5,
   fun a => (p a ^ 3 * x.d4 a - 6 * p a ^ 2 * p2 a * x.d3 a -
     4 * p a ^ 2 * p3 a * x.d2 a - p a ^ 2 * p4 a * x.d1 a +
     15 * p a * p2 a ^ 2 * x.d2 a + 10 * p a * p2 a * p3 a * x.d1 a -
     15 * p2 a ^ 3 * x.d1 a) / p a ^ 7,
   fun a => (p a ^ 4 * x.d5 a - 10 * p a ^ 3 * p2 a * x.d4 a -
     10 * p a ^ 3 * p3 a * x.d3 a - 5 * p a ^ 3 * p4 a * x.d2 a -
     p a ^ 3 * p5 a * x.d1 a + 45 * p a ^ 2 * p2 a ^ 2 * x.d3 a +
     60 * p a ^ 2 * p2 a * p3 a * x.d2 a +
     15 * p a ^ 2 * p2 a * p4 a * x.d1 a +
     10 * p a ^ 2 * p3 a ^ 2 * x.d1 a -
     105 * p a * p2 a ^ 3 * x.d2 a -
     105 * p a * p2 a ^ 2 * p3 a * x.d1 a +
     105 * p2 a ^ 4 * x.d1 a) / p a ^ 9⟩

/-- Component evaluation at the parameter value; this is not jet composition. -/
def atParam (f y : Jet5) : Jet5 :=
  ⟨f.d0 ∘ y.d0, f.d1 ∘ y.d0, f.d2 ∘ y.d0,
    f.d3 ∘ y.d0, f.d4 ∘ y.d0, f.d5 ∘ y.d0⟩








end E8TAxisReparamJet5
end GeneralCK.Certificates
end


