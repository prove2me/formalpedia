-- Prove2me | Definitions.Def_GeneralCK_E8_canonical_inverse_jet
-- name    : GeneralCK_E8_canonical_inverse_jet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T22:41:07.202437+00:00
-- url     : https://prove2.me/theorems/6860b8af-e96d-4375-9106-3cffdd7134a4
-- title:
--   Canonical E8 inverse jets and exact interval reparametrization
-- statement:
--   An order-five raw jet stores a real function and five proposed derivative functions. Its interval Contains predicate bounds all six components at a parameter. The E8 slope is $\Theta(x)=\frac{d}{dr}F(r,1)|_{r=2x}$, and its positive range is $\Theta((0,\infty))$. The function $Q$ chooses a positive preimage on that range and is zero outside it. The canonical slope jet contains $\Theta$ and its first five derivatives; the inverse-jet recurrence constructs the corresponding proposed jet for $Q$. Exact dyadic interval reparametrization computes outward enclosures for this recurrence, and xBox evaluates the stable horizontal parameter graph. These are the original definitions only: derivative identities, uniqueness, and enclosure soundness are proved in separate theorem nodes.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/tree/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.MonotoneContinuity
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_bellman

open GeneralCK GeneralCK.Certificates Set GeneralCK.Certificates.DyadicInterval

section
namespace GeneralCK.Certificates

structure Jet5 where
  d0 : ℝ → ℝ
  d1 : ℝ → ℝ
  d2 : ℝ → ℝ
  d3 : ℝ → ℝ
  d4 : ℝ → ℝ
  d5 : ℝ → ℝ

namespace Jet5


































end Jet5
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates



namespace DyadicJet5Enclosure



def Contains {p : ℕ} (b : DyadicJet5Enclosure p) (j : Jet5) (t : ℝ) : Prop :=
  b.d0.Contains (j.d0 t) ∧ b.d1.Contains (j.d1 t) ∧
  b.d2.Contains (j.d2 t) ∧ b.d3.Contains (j.d3 t) ∧
  b.d4.Contains (j.d4 t) ∧ b.d5.Contains (j.d5 t)





















end DyadicJet5Enclosure
end GeneralCK.Certificates
end

section
namespace GeneralCK

/-- The manuscript's bit-normalized radial slope, expressed through the
unit-entropy radial derivative already used by the formalization. -/
noncomputable def e8Theta (x : ℝ) : ℝ :=
  deriv (fun r => F r 1) (2 * x)































end GeneralCK
end

section
namespace GeneralCK










/-- The actual positive range of the normalized slope. -/
def e8SlopeRange : Set ℝ := e8Theta '' Ioi 0





/-- The unique positive preimage on the slope range, filled by zero outside
that range. -/
noncomputable def e8Q (y : ℝ) : ℝ :=
  by
    classical
    exact if hy : y ∈ e8SlopeRange then Classical.choose hy else 0















end GeneralCK
end

section
namespace GeneralCK.Certificates.E8InverseJet5Bridge





/-- The canonical raw-derivative jet of `e8Theta`. -/
noncomputable def e8ThetaCanonicalJet5 : Jet5 :=
  ⟨e8Theta,
   deriv e8Theta,
   deriv (deriv e8Theta),
   deriv (deriv (deriv e8Theta)),
   deriv (deriv (deriv (deriv e8Theta))),
   deriv (deriv (deriv (deriv (deriv e8Theta))))⟩





















noncomputable def e8QJet5 (θ : Jet5) : Jet5 :=
  let A := fun y => θ.d1 (e8Q y)
  let B := fun y => θ.d2 (e8Q y)
  let C := fun y => θ.d3 (e8Q y)
  let D := fun y => θ.d4 (e8Q y)
  let E := fun y => θ.d5 (e8Q y)
  let r := fun y => (A y)⁻¹
  ⟨e8Q, r,
   fun y => -B y*r y^3,
   fun y => 3*B y^2*r y^5-C y*r y^4,
   fun y => -15*B y^3*r y^7+10*B y*C y*r y^6-D y*r y^5,
   fun y => 105*B y^4*r y^9-105*B y^2*C y*r y^8+
     (10*C y^2+15*B y*D y)*r y^7-E y*r y^6⟩











end GeneralCK.Certificates.E8InverseJet5Bridge
end

section
namespace GeneralCK.Certificates.E8TAxisReparamInterval



def powI {p : ℕ} (x : DyadicInterval p) : ℕ → DyadicInterval p
  | 0 => ofInt p 1
  | n + 1 => (powI x n).mul x



def eval {p : ℕ} (x y : DyadicJet5Enclosure p) : DyadicJet5Enclosure p :=
  ⟨x.d0,
   (x.d1.mul y.d1.recip),
   (((y.d1.mul x.d2).sub (y.d2.mul x.d1)).mul (powI y.d1.recip 3)),
   ((((((powI y.d1 2).mul x.d3).sub ((((ofInt p 3).mul y.d1).mul y.d2).mul x.d2)).sub ((y.d1.mul y.d3).mul x.d1)).add (((ofInt p 3).mul (powI y.d2 2)).mul x.d1)).mul (powI y.d1.recip 5)),
   (((((((((powI y.d1 3).mul x.d4).sub ((((ofInt p 6).mul (powI y.d1 2)).mul y.d2).mul x.d3)).sub ((((ofInt p 4).mul (powI y.d1 2)).mul y.d3).mul x.d2)).sub (((powI y.d1 2).mul y.d4).mul x.d1)).add ((((ofInt p 15).mul y.d1).mul (powI y.d2 2)).mul x.d2)).add (((((ofInt p 10).mul y.d1).mul y.d2).mul y.d3).mul x.d1)).sub (((ofInt p 15).mul (powI y.d2 3)).mul x.d1)).mul (powI y.d1.recip 7)),
   ((((((((((((((powI y.d1 4).mul x.d5).sub ((((ofInt p 10).mul (powI y.d1 3)).mul y.d2).mul x.d4)).sub ((((ofInt p 10).mul (powI y.d1 3)).mul y.d3).mul x.d3)).sub ((((ofInt p 5).mul (powI y.d1 3)).mul y.d4).mul x.d2)).sub (((powI y.d1 3).mul y.d5).mul x.d1)).add ((((ofInt p 45).mul (powI y.d1 2)).mul (powI y.d2 2)).mul x.d3)).add (((((ofInt p 60).mul (powI y.d1 2)).mul y.d2).mul y.d3).mul x.d2)).add (((((ofInt p 15).mul (powI y.d1 2)).mul y.d2).mul y.d4).mul x.d1)).add ((((ofInt p 10).mul (powI y.d1 2)).mul (powI y.d3 2)).mul x.d1)).sub ((((ofInt p 105).mul y.d1).mul (powI y.d2 3)).mul x.d2)).sub (((((ofInt p 105).mul y.d1).mul (powI y.d2 2)).mul y.d3).mul x.d1)).add (((ofInt p 105).mul (powI y.d2 4)).mul x.d1)).mul (powI y.d1.recip 9))⟩










end GeneralCK.Certificates.E8TAxisReparamInterval
end

section
namespace GeneralCK.Certificates.E8TAxisStableInterval























def xBox {p : ℕ} (i : Inputs p) :=
  ((constant i.logTwo).mul (rBox i)).mul
    ((DyadicJet5Enclosure.const p 2).mul (hBox i)).inv

























end GeneralCK.Certificates.E8TAxisStableInterval
end


