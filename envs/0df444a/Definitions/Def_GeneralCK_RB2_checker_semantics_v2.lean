-- Prove2me | Definitions.Def_GeneralCK_RB2_checker_semantics_v2
-- name    : GeneralCK_RB2_checker_semantics_v2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T22:41:26.283132+00:00
-- url     : https://prove2.me/theorems/6da6d16c-386c-4920-bde1-7c9a083c92c4
-- title:
--   RB2 interval checkers, jet semantics, and correction kernels
-- statement:
--   At arbitrary dyadic precisions, these definitions specify real interval containment, first- and second-order jet consistency, outward interval jet operations, and bivariate Taylor lower bounds. The instruction-validity and accepted-program predicates record the arithmetic, logarithm, and reflection-contact obligations used by RB2 certificates. Real program evaluation is connected by definition to the source's natural-coordinate correction kernels and factored determinant. The bundle preserves the original formulas and predicates; separate soundness theorems establish their mathematical guarantees. It contains no numerical cell data or additional positivity assumption.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/tree/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK

import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_MixedBounds
import Definitions.Def_GeneralCK_RB2_program_data
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_correction_entries
import Definitions.Def_GeneralCK_statement
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
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
import Mathlib.Topology.Order.MonotoneContinuity

section
namespace GeneralCK.Certificates



namespace Jet2
open scoped Topology

/-- Both derivative assertions are required; no totalized derivative is used.
Use `SoundOn` on a neighborhood to identify the actual second derivative. -/
def SoundAt (j : Jet2) (t : ℝ) : Prop :=
  HasDerivAt j.value (j.first t) t ∧ HasDerivAt j.first (j.second t) t

/-- Soundness throughout a domain, with unrestricted local derivatives at its points. -/
def SoundOn (j : Jet2) (s : Set ℝ) : Prop := ∀ t ∈ s, j.SoundAt t

def const (c : ℝ) : Jet2 := ⟨fun _ => c, fun _ => 0, fun _ => 0⟩
def variableJet : Jet2 := ⟨id, fun _ => 1, fun _ => 0⟩

def add (j k : Jet2) : Jet2 :=
  ⟨fun t => j.value t+k.value t, fun t => j.first t+k.first t,
    fun t => j.second t+k.second t⟩

def neg (j : Jet2) : Jet2 :=
  ⟨fun t => -j.value t, fun t => -j.first t, fun t => -j.second t⟩

def mul (j k : Jet2) : Jet2 :=
  ⟨fun t => j.value t*k.value t,
    fun t => j.first t*k.value t+j.value t*k.first t,
    fun t => j.second t*k.value t+2*j.first t*k.first t+j.value t*k.second t⟩

noncomputable def inv (j : Jet2) : Jet2 :=
  ⟨fun t => (j.value t)⁻¹,
    fun t => -j.first t/(j.value t)^2,
    fun t => 2*(j.first t)^2/(j.value t)^3-j.second t/(j.value t)^2⟩

noncomputable def log (j : Jet2) : Jet2 :=
  ⟨fun t => Real.log (j.value t),
    fun t => j.first t/j.value t,
    fun t => j.second t/j.value t-(j.first t)^2/(j.value t)^2⟩



































end Jet2
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.Jet2

/-- Composition, including the second-order chain rule. -/
def comp (j k : Jet2) : Jet2 :=
  ⟨fun t => j.value (k.value t),
    fun t => j.first (k.value t)*k.first t,
    fun t => j.second (k.value t)*(k.first t)^2+j.first (k.value t)*k.second t⟩





end GeneralCK.Certificates.Jet2
end

section
namespace GeneralCK.Certificates.Reflection

def Bounds (l u x : ℝ) : Prop := l ≤ x ∧ x ≤ u

















noncomputable def biasE (c : ℝ) : ℝ := Real.log 2 -
  ((1+c)*Real.log (1+c)+(1-c)*Real.log (1-c))/2



noncomputable def biasS (c a e : ℝ) : ℝ :=
  biasE c * (2*biasB c-c*c) * (biasE c+c*(Real.log ((1+a)/(1-a))/2))^2 /
    (2*e*(1-c*c)^2*(biasB c)^3) + c*c/((1-a*a)*(1-c*c)*biasB c)









end GeneralCK.Certificates.Reflection
end

section
namespace GeneralCK.Certificates.JetBounds

/-- Endpoint arithmetic is independent of the representation used by a certificate. -/
structure Interval where
  lo : ℝ
  hi : ℝ

namespace Interval

def Contains (i : Interval) (x : ℝ) : Prop := Reflection.Bounds i.lo i.hi x
































end Interval

structure JetEnclosure where
  value : Interval
  first : Interval
  second : Interval

namespace JetEnclosure





















































end JetEnclosure
end GeneralCK.Certificates.JetBounds
end

section
namespace GeneralCK.Certificates

namespace DyadicInterval

noncomputable def toReal {p : ℕ} (a : DyadicInterval p) : JetBounds.Interval :=
  ⟨(a.lo:ℝ)/(scale p:ℝ),(a.hi:ℝ)/(scale p:ℝ)⟩





end DyadicInterval



namespace DyadicJetEnclosure
open DyadicInterval



def Contains {p : ℕ} (b : DyadicJetEnclosure p) (j : Jet2) (t : ℝ) : Prop :=
  b.value.Contains (j.value t) ∧ b.first.Contains (j.first t) ∧ b.second.Contains (j.second t)








def variableJet {p : ℕ} (i : DyadicInterval p) : DyadicJetEnclosure p := ⟨i,ofInt p 1,ofInt p 0⟩



def inv {p : ℕ} (b : DyadicJetEnclosure p) : DyadicJetEnclosure p :=
  let r := b.value.recip
  let r2 := r.mul r
  let r3 := r2.mul r
  ⟨r,b.first.neg.mul r2,
   (((ofInt p 2).mul (b.first.mul b.first)).mul r3).sub (b.second.mul r2)⟩
















def subsetCheck {p : ℕ} (b out : DyadicJetEnclosure p) : Bool :=
  b.value.subsetCheck out.value && b.first.subsetCheck out.first && b.second.subsetCheck out.second










end DyadicJetEnclosure
end GeneralCK.Certificates
end

section
namespace GeneralCK
open Set Filter
open scoped Topology















namespace Certificates.Mixed











end Certificates.Mixed

open Certificates.Mixed

noncomputable def radialSlope (v : ℝ) : ℝ :=
  J v + (1 - 2 * v) * hn v / (2 * Real.log 2 * v * (1 - v) * kap v)













end GeneralCK
end

section
namespace GeneralCK.SmallMean
open Set

/-- Natural-unit entropy deficit at bias r. -/
noncomputable def Cn (r : ℝ) : ℝ := Real.log 2 * (1 - H ((1-r)/2))
noncomputable def A (r : ℝ) : ℝ := Real.log ((1+r)/(1-r))/2






























end GeneralCK.SmallMean
end

section
namespace GeneralCK
open Certificates.Mixed

/-- Contact expression for natural-unit curvature along the reflection curve.
The entropy argument `e` is in bits; `v` is the lower-half probability contact. -/
noncomputable def reflectionS (v e A b0 : ℝ) : ℝ :=
  hn v*(2*kap v-(1-2*v)^2)*(hn v+(1-2*v)*A)^2 /
    (2*(Real.log 2*e)*(4*v*(1-v))^2*(kap v)^3) +
  (1-2*v)^2*b0/((4*v*(1-v))*kap v)



end GeneralCK
end

section
namespace GeneralCK.Reflection
open Set Filter
open scoped Topology

/-- Entropy in bits of the lower-half representative of a bias. -/
noncomputable def E (a : ℝ) : ℝ := H ((1-a)/2)

noncomputable def meanEntropy (a b : ℝ) : ℝ := (E a+E b)/2

/-- The manuscript reflection difference, in natural units. -/
noncomputable def D (a b : ℝ) : ℝ :=
  a*SmallMean.A b+b*SmallMean.A a
    -Real.log 2*F ((a+b)/2) (meanEntropy a b)
    +Real.log 2*F ((a-b)/2) (meanEntropy a b)



















/-- Exact contact expression certified by the reflection leaves. -/
noncomputable def curvature (a b : ℝ) : ℝ :=
  2*a*b/(1-a^2)^2
    -reflectionS (radialContact ((a+b)/2) (meanEntropy a b)) (meanEntropy a b)
      (SmallMean.A a) (1/(1-a^2))

    +reflectionS (radialContact ((a-b)/2) (meanEntropy a b)) (meanEntropy a b)
      (SmallMean.A a) (1/(1-a^2))



















end GeneralCK.Reflection
end

section
namespace GeneralCK.Reflection
open Certificates.Reflection Set Filter
open scoped Topology

noncomputable def biasR (c : ℝ) : ℝ := biasE c/c
































end GeneralCK.Reflection
end

section
namespace GeneralCK.Certificates.ReflectionExpression
open Set
open GeneralCK.Certificates.Reflection
noncomputable section

def sub (j k : Jet2) : Jet2 := j.add k.neg
def div (j k : Jet2) : Jet2 := j.mul k.inv
def pow (j : Jet2) : ℕ → Jet2
  | 0 => Jet2.const 1
  | n+1 => j.mul (pow j n)









def entropy (j : Jet2) : Jet2 :=
  sub (Jet2.const (Real.log 2))
    (div (((Jet2.const 1).add j).mul ((Jet2.const 1).add j).log |>.add
      ((sub (Jet2.const 1) j).mul (sub (Jet2.const 1) j).log)) (Jet2.const 2))
def bfun (j : Jet2) : Jet2 :=
  sub (Jet2.const (Real.log 2)) (div (sub (Jet2.const 1) (pow j 2)).log (Jet2.const 2))
def atanh (j : Jet2) : Jet2 :=
  div (div ((Jet2.const 1).add j) (sub (Jet2.const 1) j)).log (Jet2.const 2)











def secant (c a e : Jet2) : Jet2 :=
  (div (((entropy c).mul (sub ((Jet2.const 2).mul (bfun c)) (pow c 2))).mul
      (pow ((entropy c).add (c.mul (atanh a))) 2))
    ((((Jet2.const 2).mul e).mul (pow (sub (Jet2.const 1) (pow c 2)) 2)).mul (pow (bfun c) 3))).add
  (div (pow c 2) (((sub (Jet2.const 1) (pow a 2)).mul
    (sub (Jet2.const 1) (pow c 2))).mul (bfun c)))





def meanEntropy (a z : Jet2) : Jet2 :=
  div ((entropy a).add (entropy (a.mul z))) (Jet2.const 2)
def radiusMinus (a z : Jet2) : Jet2 :=
  div (a.mul (sub (Jet2.const 1) z)) (Jet2.const 2)
def radiusPlus (a z : Jet2) : Jet2 :=
  div (a.mul ((Jet2.const 1).add z)) (Jet2.const 2)
def contactMinus (a z : Jet2) : Jet2 :=
  reflectionContactJet.comp (div (meanEntropy a z) (radiusMinus a z))
def contactPlus (a z : Jet2) : Jet2 :=
  reflectionContactJet.comp (div (meanEntropy a z) (radiusPlus a z))

/-- A compositional jet for the normalized natural-entropy reflection curvature. -/
def normalized (a z : Jet2) : Jet2 :=
  div (sub ((div (((Jet2.const 2).mul a).mul (a.mul z))
    (pow (sub (Jet2.const 1) (pow a 2)) 2)).add
    (secant (contactMinus a z) a (meanEntropy a z)))
    (secant (contactPlus a z) a (meanEntropy a z))) ((pow a 3).mul (a.mul z))

/-- The source expression with its actual implicit bias contacts. -/
def normalizedValue (a z : ℝ) : ℝ :=
  let b := a*z
  let e := (biasE a+biasE b)/2
  let cm := GeneralCK.Reflection.biasContact (e/(a*(1-z)/2))
  let cp := GeneralCK.Reflection.biasContact (e/(a*(1+z)/2))
  (2*a*b/(1-a^2)^2+biasS cm a e-biasS cp a e)/(a^3*b)







end
end GeneralCK.Certificates.ReflectionExpression
end

section
namespace GeneralCK.Certificates
open Set

namespace Jet2

/-- The exact jet along a segment, with parameter zero at `c` and one at `x`. -/
def segment (c x : ℝ) : Jet2 :=
  ⟨fun t => c+t*(x-c),fun _ => x-c,fun _ => 0⟩









end Jet2

namespace ReflectionExpression

/-- The full normalized curvature restricted to a line through a proposed certificate box. -/
noncomputable def segmentJet (ac zc a z : ℝ) : Jet2 :=
  normalized (Jet2.segment ac a) (Jet2.segment zc z)















end ReflectionExpression
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates



namespace BivariateJet2

def projection (j : BivariateJet2) (da dz : ℝ) : Jet2 :=
  ⟨j.value, fun t => j.firstA t*da+j.firstZ t*dz,
    fun t => j.secondAA t*da^2+2*j.secondAZ t*da*dz+j.secondZZ t*dz^2⟩
















































abbrev DirectionalSoundAt (j : BivariateJet2) (da dz t : ℝ) : Prop :=
  (j.projection da dz).SoundAt t

abbrev DirectionalSoundOn (j : BivariateJet2) (da dz : ℝ) (s : Set ℝ) : Prop :=
  (j.projection da dz).SoundOn s



















end BivariateJet2
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates
open JetBounds

/-- Coordinate coefficients are enclosed before contracting with a segment direction. -/
structure BivariateJetEnclosure where
  value : Interval
  firstA : Interval
  firstZ : Interval
  secondAA : Interval
  secondAZ : Interval
  secondZZ : Interval

namespace BivariateJetEnclosure

def Contains (b : BivariateJetEnclosure) (j : BivariateJet2) (t : ℝ) : Prop :=
  b.value.Contains (j.value t) ∧ b.firstA.Contains (j.firstA t) ∧
  b.firstZ.Contains (j.firstZ t) ∧ b.secondAA.Contains (j.secondAA t) ∧
  b.secondAZ.Contains (j.secondAZ t) ∧ b.secondZZ.Contains (j.secondZZ t)

def ContainsOn (b : BivariateJetEnclosure) (j : BivariateJet2) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, b.Contains j t





















end BivariateJetEnclosure
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.DyadicLog

























/-- Computable log jet arithmetic; the value interval comes from `check`. -/
def jetLog {p : ℕ} (b : DyadicJetEnclosure p) (out : DyadicInterval p) : DyadicJetEnclosure p :=
  let r := b.value.recip
  ⟨out,b.first.mul r,(b.second.mul r).sub ((b.first.mul b.first).mul (r.mul r))⟩





























end GeneralCK.Certificates.DyadicLog
end

section
namespace GeneralCK.Certificates.DyadicEntropy
open DyadicInterval



def half (p : ℕ) : DyadicInterval p := (ofInt p 2).recip

















end GeneralCK.Certificates.DyadicEntropy
end

section
namespace GeneralCK.Certificates.DyadicContact
open DyadicInterval
open GeneralCK.Reflection

def point {p : ℕ} (z : ℤ) : DyadicInterval p := ⟨z,z⟩















def gap {p : ℕ} (c : DyadicInterval p) : DyadicInterval p := (ofInt p 1).sub (c.mul c)

def enclosure {p : ℕ} (c B : DyadicInterval p) : DyadicJetEnclosure p :=
  let c2 := c.mul c
  let c3 := c2.mul c
  let r := B.recip
  let r2 := r.mul r
  let r3 := r2.mul r
  ⟨c,(c2.mul r).neg,
   (((ofInt p 2).mul c3).mul r2).sub (((c3.mul c2).mul (gap c).recip).mul r3)⟩











end GeneralCK.Certificates.DyadicContact
end

section
namespace GeneralCK.Certificates
open DyadicInterval

namespace DyadicInterval.Contains







end DyadicInterval.Contains



namespace DyadicBivariateJetEnclosure
variable {p : ℕ}


def Contains (b : DyadicBivariateJetEnclosure p) (j : BivariateJet2) (t : ℝ) : Prop :=
  b.value.Contains (j.value t) ∧ b.firstA.Contains (j.firstA t) ∧
  b.firstZ.Contains (j.firstZ t) ∧ b.secondAA.Contains (j.secondAA t) ∧
  b.secondAZ.Contains (j.secondAZ t) ∧ b.secondZZ.Contains (j.secondZZ t)

def ContainsOn (b : DyadicBivariateJetEnclosure p) (j : BivariateJet2) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, b.Contains j t

noncomputable def toReal (b : DyadicBivariateJetEnclosure p) : BivariateJetEnclosure :=
  ⟨b.value.toReal,b.firstA.toReal,b.firstZ.toReal,b.secondAA.toReal,b.secondAZ.toReal,b.secondZZ.toReal⟩





def coordinateA (value : DyadicInterval p) : DyadicBivariateJetEnclosure p :=
  ⟨value,ofInt p 1,ofInt p 0,ofInt p 0,ofInt p 0,ofInt p 0⟩

def coordinateZ (value : DyadicInterval p) : DyadicBivariateJetEnclosure p :=
  ⟨value,ofInt p 0,ofInt p 1,ofInt p 0,ofInt p 0,ofInt p 0⟩





def const (p : ℕ) (c : ℤ) : DyadicBivariateJetEnclosure p :=
  ⟨ofInt p c,ofInt p 0,ofInt p 0,ofInt p 0,ofInt p 0,ofInt p 0⟩

def add (b c : DyadicBivariateJetEnclosure p) : DyadicBivariateJetEnclosure p :=
  ⟨b.value.add c.value,b.firstA.add c.firstA,b.firstZ.add c.firstZ,
    b.secondAA.add c.secondAA,b.secondAZ.add c.secondAZ,b.secondZZ.add c.secondZZ⟩

def neg (b : DyadicBivariateJetEnclosure p) : DyadicBivariateJetEnclosure p :=
  ⟨b.value.neg,b.firstA.neg,b.firstZ.neg,b.secondAA.neg,b.secondAZ.neg,b.secondZZ.neg⟩

def mul (b c : DyadicBivariateJetEnclosure p) : DyadicBivariateJetEnclosure p :=
  ⟨b.value.mul c.value,
    (b.firstA.mul c.value).add (b.value.mul c.firstA),
    (b.firstZ.mul c.value).add (b.value.mul c.firstZ),
    ((b.secondAA.mul c.value).add (((ofInt p 2).mul b.firstA).mul c.firstA)).add
      (b.value.mul c.secondAA),
    (((b.secondAZ.mul c.value).add (b.firstA.mul c.firstZ)).add (b.firstZ.mul c.firstA)).add
      (b.value.mul c.secondAZ),
    ((b.secondZZ.mul c.value).add (((ofInt p 2).mul b.firstZ).mul c.firstZ)).add
      (b.value.mul c.secondZZ)⟩

/-- The outer Jet2 enclosure is evaluated at the actual inner value. -/
def outerCompose (outer : DyadicJetEnclosure p) (b : DyadicBivariateJetEnclosure p) :
    DyadicBivariateJetEnclosure p :=
  ⟨outer.value,outer.first.mul b.firstA,outer.first.mul b.firstZ,
    ((outer.second.mul b.firstA).mul b.firstA).add (outer.first.mul b.secondAA),
    ((outer.second.mul b.firstA).mul b.firstZ).add (outer.first.mul b.secondAZ),
    ((outer.second.mul b.firstZ).mul b.firstZ).add (outer.first.mul b.secondZZ)⟩











def subsetCheck (b out : DyadicBivariateJetEnclosure p) : Bool :=
  b.value.subsetCheck out.value && b.firstA.subsetCheck out.firstA &&
  b.firstZ.subsetCheck out.firstZ && b.secondAA.subsetCheck out.secondAA &&
  b.secondAZ.subsetCheck out.secondAZ && b.secondZZ.subsetCheck out.secondZZ



def inv (b : DyadicBivariateJetEnclosure p) : DyadicBivariateJetEnclosure p :=
  outerCompose (DyadicJetEnclosure.variableJet b.value).inv b



def invCheck (b out : DyadicBivariateJetEnclosure p) : Bool :=
  b.value.positiveCheck && b.inv.subsetCheck out





def log (b : DyadicBivariateJetEnclosure p) (value : DyadicInterval p) : DyadicBivariateJetEnclosure p :=
  outerCompose (DyadicLog.jetLog (DyadicJetEnclosure.variableJet b.value) value) b















end DyadicBivariateJetEnclosure
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.BivariateJetProgram



def zeroBox (p : ℕ) : DyadicBivariateJetEnclosure p := DyadicBivariateJetEnclosure.const p 0






namespace Op













end Op

structure Instruction (p : ℕ) where
  op : Op p
  proposed : DyadicBivariateJetEnclosure p









noncomputable def executeShapes : List Shape → List BivariateJet2 → List BivariateJet2
  | [], jets => jets
  | op::rest, jets => executeShapes rest (op.eval jets::jets)





def RegistersContain {p : ℕ} (boxes : List (DyadicBivariateJetEnclosure p)) (jets : List BivariateJet2) (t : ℝ) : Prop :=
  boxes.length=jets.length ∧ ∀ i, (boxes.getD i (zeroBox p)).Contains (jets.getD i zeroJet) t

def RegistersSound (jets : List BivariateJet2) (da dz t : ℝ) : Prop :=
  ∀ i, (jets.getD i zeroJet).DirectionalSoundAt da dz t





































end GeneralCK.Certificates.BivariateJetProgram
end

section
namespace GeneralCK.Certificates
open Set JetBounds

namespace JetBounds.Interval

noncomputable def magnitude (i : Interval) : ℝ := max |i.lo| |i.hi|





end JetBounds.Interval

namespace BivariateJetEnclosure

/-- Contract coordinate gradient and Hessian bounds only at the final step. -/
noncomputable def taylorLower (center whole : BivariateJetEnclosure) (ra rz : ℝ) : ℝ :=
  center.value.lo-center.firstA.magnitude*ra-center.firstZ.magnitude*rz-
    (whole.secondAA.magnitude*ra^2+2*whole.secondAZ.magnitude*ra*rz+
      whole.secondZZ.magnitude*rz^2)/2





end BivariateJetEnclosure
end GeneralCK.Certificates
end

section
namespace GeneralCK.Certificates.ProvedTranscendental
open DyadicInterval GeneralCK.Reflection GeneralCK.Certificates.Reflection

/-- A semantic enclosure proved in Lean, independent of the logarithm backend. -/
def LogEncloses {p : ℕ} (input out : DyadicInterval p) : Prop :=
  ∀ x : ℝ, input.Contains x → out.Contains (Real.log x)







def entropyRaw {p : ℕ} (c two plus minus : DyadicInterval p) : DyadicInterval p :=
  two.sub (((ofInt p 1).add c |>.mul plus).add
    ((ofInt p 1).sub c |>.mul minus) |>.mul (DyadicEntropy.half p))



def denominatorRaw {p : ℕ} (two gapLog : DyadicInterval p) : DyadicInterval p :=
  two.sub (gapLog.mul (DyadicEntropy.half p))







end GeneralCK.Certificates.ProvedTranscendental
end

section
namespace GeneralCK.Certificates.BivariateProvedProgram
open BivariateJetProgram Set







/-- Each arithmetic comparison is kernel-evaluated. Nonlinear enclosures are
Lean proofs; no external acceptance flag can fill either proof obligation. -/
def StepValid {p : ℕ} (shape : Shape) (boxes : List (DyadicBivariateJetEnclosure p))
    (out : DyadicBivariateJetEnclosure p) : Prop :=
  InRange shape boxes.length ∧ match shape with
  | .add i j => ((boxes.getD i (zeroBox p)).add (boxes.getD j (zeroBox p))).subsetCheck out=true
  | .neg i => (boxes.getD i (zeroBox p)).neg.subsetCheck out=true
  | .mul i j => ((boxes.getD i (zeroBox p)).mul (boxes.getD j (zeroBox p))).subsetCheck out=true
  | .inv i => (boxes.getD i (zeroBox p)).invCheck out=true
  | .log i =>
      let b := boxes.getD i (zeroBox p)
      0<b.value.lo ∧ ProvedTranscendental.LogEncloses b.value out.value ∧
        (b.log out.value).subsetCheck out=true
  | .contact i =>
      let b := boxes.getD i (zeroBox p)
      0<b.value.lo ∧ ∃ outer : DyadicJetEnclosure p,
        (∀ y : ℝ, b.value.Contains y → outer.Contains reflectionContactJet y) ∧
        (DyadicBivariateJetEnclosure.outerCompose outer b).subsetCheck out=true

def Accepted {p : ℕ} : List (Instruction p) → List (DyadicBivariateJetEnclosure p) → Prop
  | [], _ => True
  | ins::rest, boxes => StepValid ins.shape boxes ins.proposed ∧ Accepted rest (ins.proposed::boxes)

def finalBoxes {p : ℕ} : List (Instruction p) → List (DyadicBivariateJetEnclosure p) → List (DyadicBivariateJetEnclosure p)
  | [], boxes => boxes
  | ins::rest, boxes => finalBoxes rest (ins.proposed::boxes)



def shapes {p : ℕ} (program : List (Instruction p)) : List Shape := program.map Instruction.shape





















noncomputable def evalReal (shape : Shape) (values : List ℝ) : ℝ := match shape with
  | .add i j => values.getD i 0+values.getD j 0
  | .neg i => -values.getD i 0
  | .mul i j => values.getD i 0*values.getD j 0
  | .inv i => (values.getD i 0)⁻¹
  | .log i => Real.log (values.getD i 0)
  | .contact i => GeneralCK.Reflection.biasContact (values.getD i 0)



noncomputable def evalRealProgram {p : ℕ} : List (Instruction p) → List ℝ → List ℝ
  | [], values => values
  | ins::rest, values => evalRealProgram rest (evalReal ins.shape values::values)





end GeneralCK.Certificates.BivariateProvedProgram
end

section
namespace GeneralCK.Correction

/-- Natural-log entropy slope, rather than the bit-entropy slope `J`. -/
noncomputable def naturalJ (f : ℝ) : ℝ := Real.log 2 * J (entropyInverse f)

noncomputable def rankWeight (e f : ℝ) : ℝ :=
  2 * Real.log 2 * deriv (deriv (fun r => F r (mid e f))) (gap e f)

/-- Numerator of `Aright`; this expression has no division by `naturalJ f`. -/
noncomputable def rightNumerator (e f : ℝ) : ℝ :=
  q f * (naturalJ e + naturalJ f -
    2 * Real.log 2 * deriv (fun r => F r 1) (normalized e f)) +
  gap e f * (1 - naturalJ f * (1 - 2 * entropyInverse f))

/-- Denominator-cleared determinant with the quadratic rank-one terms cancelled. -/
noncomputable def Kfactored (e f : ℝ) : ℝ :=
  Aleft e f * rightNumerator e f - naturalJ f * (q e + q f)^2 -
  rankWeight e f * (naturalJ f * Aleft e f * (Zright e f)^2 +
    rightNumerator e f * (Zleft e f)^2 +
    2 * naturalJ f * (q e + q f) * Zleft e f * Zright e f)

















end GeneralCK.Correction
end

section
namespace GeneralCK.Correction.Natural
open Certificates.Mixed Certificates.Reflection Reflection







/-- The source's natural-unit first radial derivative, with mu=2*biasB c. -/
noncomputable def Fs (c : ℝ) : ℝ :=
  2*SmallMean.A c + biasE c*c / (((1-c^2)/4)*(2*biasB c))

/-- The source's natural-unit second radial derivative; S is the sum of natural entropies. -/
noncomputable def Fss (c S : ℝ) : ℝ :=
  2*(biasE c)^3*(2*biasB c-c^2) /
    (S*((1-c^2)/4)^2*(2*biasB c)^3)







noncomputable def jn (u : ℝ) : ℝ := Real.log ((1-u)/u)
noncomputable def qp (u : ℝ) : ℝ := u*(1-u)
noncomputable def entropySum (u w : ℝ) : ℝ := hn u+hn w
noncomputable def contact (u w : ℝ) : ℝ := biasContact (entropySum u w/(2*(w-u)))

/-- Exact source `zu`, `zw`, `Au`, `Nw`, with all entropy units natural. -/
noncomputable def zu (u w : ℝ) : ℝ := -qp u-(w-u)*qp u*jn u/entropySum u w
noncomputable def zw (u w : ℝ) : ℝ := qp w*(1-(w-u)*jn w/entropySum u w)
noncomputable def au (u w : ℝ) : ℝ :=
  (qp u*(jn u+jn w+2*Fs (contact u w))+(w-u)*(jn u*(1-2*u)-1))/jn u
noncomputable def nw (u w : ℝ) : ℝ :=
  qp w*(jn u+jn w-2*Fs (contact u w))+(w-u)*(1-jn w*(1-2*w))
noncomputable def weight (u w : ℝ) : ℝ := 2*Fss (contact u w) (entropySum u w)
noncomputable def m11 (u w : ℝ) : ℝ := au u w-weight u w*(zu u w)^2
noncomputable def kdet (u w : ℝ) : ℝ :=
  au u w*nw u w-jn w*(qp u+qp w)^2-
  weight u w*(jn w*au u w*(zw u w)^2+nw u w*(zu u w)^2+
    2*jn w*(qp u+qp w)*zu u w*zw u w)





















end GeneralCK.Correction.Natural
end

section
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

namespace GeneralCK.Certificates.CorrectionFactorizedProgramKernel
open BivariateJetProgram (zeroBox zeroJet)
open BivariateProvedProgram
noncomputable def kernelProgram : List (Instruction 0) := [
  ⟨.inv 3, zeroBox 0⟩,
  ⟨.mul 3 0, zeroBox 0⟩,
  ⟨.neg 2, zeroBox 0⟩,
  ⟨.add 1 0, zeroBox 0⟩,
  ⟨.mul 5 0, zeroBox 0⟩,
  ⟨.add 5 0, zeroBox 0⟩,
  ⟨.add 0 3, zeroBox 0⟩,
  ⟨.log 7, zeroBox 0⟩,
  ⟨.mul 8 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 12 7, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 4 0, zeroBox 0⟩,
  ⟨.log 9, zeroBox 0⟩,
  ⟨.mul 10 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.neg 12, zeroBox 0⟩,
  ⟨.add 21 0, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 5 0, zeroBox 0⟩,
  ⟨.add 9 0, zeroBox 0⟩,
  ⟨.mul 28 18, zeroBox 0⟩,
  ⟨.inv 0, zeroBox 0⟩,
  ⟨.mul 2 0, zeroBox 0⟩,
  ⟨.contact 0, zeroBox 0⟩,
  ⟨.log 32, zeroBox 0⟩,
  ⟨.add 32 1, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.neg 4, zeroBox 0⟩,
  ⟨.add 36 0, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.add 4 0, zeroBox 0⟩,
  ⟨.mul 0 37, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 10 0, zeroBox 0⟩,
  ⟨.mul 12 12, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 45 0, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 0 44, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 17 0, zeroBox 0⟩,
  ⟨.mul 51 51, zeroBox 0⟩,
  ⟨.inv 0, zeroBox 0⟩,
  ⟨.mul 6 0, zeroBox 0⟩,
  ⟨.mul 54 3, zeroBox 0⟩,
  ⟨.inv 17, zeroBox 0⟩,
  ⟨.mul 22 0, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 14 26, zeroBox 0⟩,
  ⟨.mul 5 4, zeroBox 0⟩,
  ⟨.inv 0, zeroBox 0⟩,
  ⟨.mul 2 0, zeroBox 0⟩,
  ⟨.add 4 0, zeroBox 0⟩,
  ⟨.mul 19 19, zeroBox 0⟩,
  ⟨.mul 20 0, zeroBox 0⟩,
  ⟨.mul 65 0, zeroBox 0⟩,
  ⟨.add 11 20, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.mul 14 14, zeroBox 0⟩,
  ⟨.mul 41 0, zeroBox 0⟩,
  ⟨.mul 15 15, zeroBox 0⟩,
  ⟨.mul 16 0, zeroBox 0⟩,
  ⟨.mul 2 0, zeroBox 0⟩,
  ⟨.inv 0, zeroBox 0⟩,
  ⟨.mul 6 0, zeroBox 0⟩,
  ⟨.mul 75 0, zeroBox 0⟩,
  ⟨.inv 73, zeroBox 0⟩,
  ⟨.mul 63 0, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.inv 70, zeroBox 0⟩,
  ⟨.mul 57 0, zeroBox 0⟩,
  ⟨.log 0, zeroBox 0⟩,
  ⟨.mul 79 68, zeroBox 0⟩,
  ⟨.mul 74 60, zeroBox 0⟩,
  ⟨.add 5 2, zeroBox 0⟩,
  ⟨.mul 85 22, zeroBox 0⟩,
  ⟨.add 1 0, zeroBox 0⟩,
  ⟨.mul 4 0, zeroBox 0⟩,
  ⟨.mul 88 85, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 89 0, zeroBox 0⟩,
  ⟨.mul 12 0, zeroBox 0⟩,
  ⟨.neg 91, zeroBox 0⟩,
  ⟨.add 1 0, zeroBox 0⟩,
  ⟨.mul 84 0, zeroBox 0⟩,
  ⟨.add 7 0, zeroBox 0⟩,
  ⟨.inv 17, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.neg 12, zeroBox 0⟩,
  ⟨.add 14 0, zeroBox 0⟩,
  ⟨.mul 16 0, zeroBox 0⟩,
  ⟨.mul 101 92, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 102 0, zeroBox 0⟩,
  ⟨.mul 22 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 105 0, zeroBox 0⟩,
  ⟨.mul 97 0, zeroBox 0⟩,
  ⟨.add 7 0, zeroBox 0⟩,
  ⟨.neg 26, zeroBox 0⟩,
  ⟨.mul 100 27, zeroBox 0⟩,
  ⟨.mul 0 32, zeroBox 0⟩,
  ⟨.inv 84, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 5 0, zeroBox 0⟩,
  ⟨.mul 106 34, zeroBox 0⟩,
  ⟨.mul 0 4, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 118 0, zeroBox 0⟩,
  ⟨.mul 36 0, zeroBox 0⟩,
  ⟨.mul 5 5, zeroBox 0⟩,
  ⟨.mul 46 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 26 0, zeroBox 0⟩,
  ⟨.mul 49 43, zeroBox 0⟩,
  ⟨.mul 5 5, zeroBox 0⟩,
  ⟨.mul 1 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 20 0, zeroBox 0⟩,
  ⟨.add 47 46, zeroBox 0⟩,
  ⟨.mul 55 15, zeroBox 0⟩,
  ⟨.mul 0 11, zeroBox 0⟩,
  ⟨.add 2 0, zeroBox 0⟩,
  ⟨.mul 9 4, zeroBox 0⟩,
  ⟨.mul 1 1, zeroBox 0⟩,
  ⟨.mul 54 0, zeroBox 0⟩,
  ⟨.neg 0, zeroBox 0⟩,
  ⟨.add 3 0, zeroBox 0⟩
]
noncomputable def scalarCore (a z : ℝ) : ℝ × ℝ :=
  let v0 : ℝ := (2:ℝ)⁻¹
  let v1 : ℝ := (1:ℝ)*v0
  let v2 : ℝ := -a
  let v3 : ℝ := v1+v2
  let v4 : ℝ := z*v3
  let v5 : ℝ := a+v4
  let v6 : ℝ := v5+v2
  let v7 : ℝ := Real.log a
  let v8 : ℝ := a*v7
  let v9 : ℝ := -v8
  let v10 : ℝ := (1:ℝ)+v2
  let v11 : ℝ := Real.log v10
  let v12 : ℝ := v10*v11
  let v13 : ℝ := -v12
  let v14 : ℝ := v9+v13
  let v15 : ℝ := Real.log v5
  let v16 : ℝ := v5*v15
  let v17 : ℝ := -v16
  let v18 : ℝ := -v5
  let v19 : ℝ := (1:ℝ)+v18
  let v20 : ℝ := Real.log v19
  let v21 : ℝ := v19*v20
  let v22 : ℝ := -v21
  let v23 : ℝ := v17+v22
  let v24 : ℝ := v14+v23
  let v25 : ℝ := (2:ℝ)*v6
  let v26 : ℝ := v25⁻¹
  let v27 : ℝ := v24*v26
  let v28 : ℝ := GeneralCK.Reflection.biasContact v27
  let v29 : ℝ := Real.log (2:ℝ)
  let v30 : ℝ := (1:ℝ)+v28
  let v31 : ℝ := Real.log v30
  let v32 : ℝ := v30*v31
  let v33 : ℝ := -v28
  let v34 : ℝ := (1:ℝ)+v33
  let v35 : ℝ := Real.log v34
  let v36 : ℝ := v34*v35
  let v37 : ℝ := v32+v36
  let v38 : ℝ := v37*v0
  let v39 : ℝ := -v38
  let v40 : ℝ := v29+v39
  let v41 : ℝ := v28*v28
  let v42 : ℝ := -v41
  let v43 : ℝ := (1:ℝ)+v42
  let v44 : ℝ := Real.log v43
  let v45 : ℝ := v44*v0
  let v46 : ℝ := -v45
  let v47 : ℝ := v29+v46
  let v48 : ℝ := (2:ℝ)*(2:ℝ)
  let v49 : ℝ := v48⁻¹
  let v50 : ℝ := v43*v49
  let v51 : ℝ := (2:ℝ)*v47
  let v52 : ℝ := v34⁻¹
  let v53 : ℝ := v30*v52
  let v54 : ℝ := Real.log v53
  let v55 : ℝ := v40*v28
  let v56 : ℝ := v50*v51
  let v57 : ℝ := v56⁻¹
  let v58 : ℝ := v55*v57
  let v59 : ℝ := v54+v58
  let v60 : ℝ := v40*v40
  let v61 : ℝ := v40*v60
  let v62 : ℝ := (2:ℝ)*v61
  let v63 : ℝ := v51+v42
  let v64 : ℝ := v62*v63
  let v65 : ℝ := v50*v50
  let v66 : ℝ := v24*v65
  let v67 : ℝ := v51*v51
  let v68 : ℝ := v51*v67
  let v69 : ℝ := v66*v68
  let v70 : ℝ := v69⁻¹
  let v71 : ℝ := v64*v70
  let v72 : ℝ := (2:ℝ)*v71
  let v73 : ℝ := a⁻¹
  let v74 : ℝ := v10*v73
  let v75 : ℝ := Real.log v74
  let v76 : ℝ := v5⁻¹
  let v77 : ℝ := v19*v76
  let v78 : ℝ := Real.log v77
  let v79 : ℝ := a*v10
  let v80 : ℝ := v5*v19
  let v81 : ℝ := v75+v78
  let v82 : ℝ := (2:ℝ)*v59
  let v83 : ℝ := v81+v82
  let v84 : ℝ := v79*v83
  let v85 : ℝ := (2:ℝ)*a
  let v86 : ℝ := -v85
  let v87 : ℝ := (1:ℝ)+v86
  let v88 : ℝ := v75*v87
  let v89 : ℝ := -(1:ℝ)
  let v90 : ℝ := v88+v89
  let v91 : ℝ := v6*v90
  let v92 : ℝ := v84+v91
  let v93 : ℝ := v75⁻¹
  let v94 : ℝ := v92*v93
  let v95 : ℝ := -v82
  let v96 : ℝ := v81+v95
  let v97 : ℝ := v80*v96
  let v98 : ℝ := (2:ℝ)*v5
  let v99 : ℝ := -v98
  let v100 : ℝ := (1:ℝ)+v99
  let v101 : ℝ := v78*v100
  let v102 : ℝ := -v101
  let v103 : ℝ := (1:ℝ)+v102
  let v104 : ℝ := v6*v103
  let v105 : ℝ := v97+v104
  let v106 : ℝ := -v79
  let v107 : ℝ := v6*v79
  let v108 : ℝ := v107*v75
  let v109 : ℝ := v24⁻¹
  let v110 : ℝ := v108*v109
  let v111 : ℝ := -v110
  let v112 : ℝ := v106+v111
  let v113 : ℝ := v6*v78
  let v114 : ℝ := v113*v109
  let v115 : ℝ := -v114
  let v116 : ℝ := (1:ℝ)+v115
  let v117 : ℝ := v80*v116
  let v118 : ℝ := v112*v112
  let v119 : ℝ := v72*v118
  let v120 : ℝ := -v119
  let v121 : ℝ := v94+v120
  let v122 : ℝ := v72*v78
  let v123 : ℝ := v117*v117
  let v124 : ℝ := v122*v123
  let v125 : ℝ := -v124
  let v126 : ℝ := v105+v125
  let v127 : ℝ := v79+v80
  let v128 : ℝ := v72*v112
  let v129 : ℝ := v128*v117
  let v130 : ℝ := v127+v129
  let v131 : ℝ := v121*v126
  let v132 : ℝ := v130*v130
  let v133 : ℝ := v78*v132
  let v134 : ℝ := -v133
  let v135 : ℝ := v131+v134
  (v121,v135)








noncomputable def inputJets (ac zc a z : ℝ) : List BivariateJet2 :=
  [BivariateJet2.affineA ac a,BivariateJet2.affineZ zc z,BivariateJet2.const 1,BivariateJet2.const 2]




end GeneralCK.Certificates.CorrectionFactorizedProgramKernel
end


