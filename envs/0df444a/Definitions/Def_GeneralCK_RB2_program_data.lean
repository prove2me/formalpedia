-- Prove2me | Definitions.Def_GeneralCK_RB2_program_data
-- name    : GeneralCK_RB2_program_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T21:54:03.132753+00:00
-- url     : https://prove2.me/theorems/816035cc-feb4-42d8-b198-d69296beb6ea
-- title:
--   Shared jet records and program semantics for RB2 certificates
-- statement:
--   A bivariate second-order jet records six real-valued coefficient functions: a value, two first derivatives, and three symmetric second derivatives. The interface defines constant and affine-coordinate jets and their exact algebraic sum, product, reciprocal, logarithm, and outer-composition semantics. Dyadic records hold six interval proposals at precision $p$; witness records store the finite log-series, contact-bracket, and entropy-bound data used by existing checkers. A program instruction combines an operation shape with a proposed interval jet. Its finalJets function evaluates the sequence using the exact real semantics, including the source reflection-contact profile. All structures, decidability instances, and definitions are preserved from the source. These definitions supply shared types and evaluation rules for RB2 certificates; successful interval checks and correction-matrix positivity are established by separate theorems.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/tree/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK

import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_bellman
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

namespace GeneralCK.Certificates

/-- A scalar or directional second-order jet with explicit derivative functions. -/
structure Jet2 where
  value : ℝ → ℝ
  first : ℝ → ℝ
  second : ℝ → ℝ

namespace Jet2
open scoped Topology




















































end Jet2
end GeneralCK.Certificates

namespace GeneralCK.Certificates.Reflection





















noncomputable def biasB (c : ℝ) : ℝ := Real.log 2 - Real.log (1-c*c)/2











end GeneralCK.Certificates.Reflection

namespace GeneralCK.Certificates

namespace DyadicInterval







end DyadicInterval

/-- Computable fixed-scale enclosures of the three explicit jet components. -/
structure DyadicJetEnclosure (p : ℕ) where
  value : DyadicInterval p
  first : DyadicInterval p
  second : DyadicInterval p
  deriving DecidableEq, Repr

namespace DyadicJetEnclosure
open DyadicInterval












































end DyadicJetEnclosure
end GeneralCK.Certificates

namespace GeneralCK.Reflection
open Certificates.Reflection Set Filter
open scoped Topology


noncomputable def biasRprime (c : ℝ) : ℝ := -biasB c/c^2
noncomputable def biasRsecond (c : ℝ) : ℝ := 2*biasB c/c^3-1/(c*(1-c^2))
noncomputable def biasContact (y : ℝ) : ℝ := 1-2*radialContact 1 (y/Real.log 2)





























end GeneralCK.Reflection

namespace GeneralCK.Certificates
open Set Filter
open scoped Topology

/-- The inverse of the decreasing natural-entropy bias ratio, with explicit
first and second inverse-function derivatives. -/
noncomputable def reflectionContactJet : Jet2 where
  value := Reflection.biasContact
  first := fun y => (Reflection.biasRprime (Reflection.biasContact y))⁻¹
  second := fun y => -Reflection.biasRsecond (Reflection.biasContact y) /
    (Reflection.biasRprime (Reflection.biasContact y))^3









end GeneralCK.Certificates

namespace GeneralCK.Certificates

/-- A symmetric coordinate Hessian, evaluated along a parameterized path.
The component functions alone assert no differentiability; soundness is supplied
by projection to the existing explicit two-derivative `Jet2` contract. -/
structure BivariateJet2 where
  value : ℝ → ℝ
  firstA : ℝ → ℝ
  firstZ : ℝ → ℝ
  secondAA : ℝ → ℝ
  secondAZ : ℝ → ℝ
  secondZZ : ℝ → ℝ

namespace BivariateJet2



def const (c : ℝ) : BivariateJet2 :=
  ⟨fun _ => c,fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0⟩

def coordinateA (a : ℝ → ℝ) : BivariateJet2 :=
  ⟨a,fun _ => 1,fun _ => 0,fun _ => 0,fun _ => 0,fun _ => 0⟩

def coordinateZ (z : ℝ → ℝ) : BivariateJet2 :=
  ⟨z,fun _ => 0,fun _ => 1,fun _ => 0,fun _ => 0,fun _ => 0⟩

def affineA (c x : ℝ) : BivariateJet2 := coordinateA (fun t => c+t*(x-c))
def affineZ (c x : ℝ) : BivariateJet2 := coordinateZ (fun t => c+t*(x-c))

def add (j k : BivariateJet2) : BivariateJet2 :=
  ⟨fun t => j.value t+k.value t,
    fun t => j.firstA t+k.firstA t,fun t => j.firstZ t+k.firstZ t,
    fun t => j.secondAA t+k.secondAA t,fun t => j.secondAZ t+k.secondAZ t,
    fun t => j.secondZZ t+k.secondZZ t⟩

def neg (j : BivariateJet2) : BivariateJet2 :=
  ⟨fun t => -j.value t,fun t => -j.firstA t,fun t => -j.firstZ t,
    fun t => -j.secondAA t,fun t => -j.secondAZ t,fun t => -j.secondZZ t⟩

def mul (j k : BivariateJet2) : BivariateJet2 :=
  ⟨fun t => j.value t*k.value t,
    fun t => j.firstA t*k.value t+j.value t*k.firstA t,
    fun t => j.firstZ t*k.value t+j.value t*k.firstZ t,
    fun t => j.secondAA t*k.value t+2*j.firstA t*k.firstA t+j.value t*k.secondAA t,
    fun t => j.secondAZ t*k.value t+j.firstA t*k.firstZ t+j.firstZ t*k.firstA t+
      j.value t*k.secondAZ t,
    fun t => j.secondZZ t*k.value t+2*j.firstZ t*k.firstZ t+j.value t*k.secondZZ t⟩

noncomputable def inv (j : BivariateJet2) : BivariateJet2 :=
  ⟨fun t => (j.value t)⁻¹,
    fun t => -j.firstA t/(j.value t)^2,fun t => -j.firstZ t/(j.value t)^2,
    fun t => 2*(j.firstA t)^2/(j.value t)^3-j.secondAA t/(j.value t)^2,
    fun t => 2*j.firstA t*j.firstZ t/(j.value t)^3-j.secondAZ t/(j.value t)^2,
    fun t => 2*(j.firstZ t)^2/(j.value t)^3-j.secondZZ t/(j.value t)^2⟩

noncomputable def log (j : BivariateJet2) : BivariateJet2 :=
  ⟨fun t => Real.log (j.value t),
    fun t => j.firstA t/j.value t,fun t => j.firstZ t/j.value t,
    fun t => j.secondAA t/j.value t-(j.firstA t)^2/(j.value t)^2,
    fun t => j.secondAZ t/j.value t-j.firstA t*j.firstZ t/(j.value t)^2,
    fun t => j.secondZZ t/j.value t-(j.firstZ t)^2/(j.value t)^2⟩

/-- The ordinary scalar outer chain rule, retaining both coordinates. -/
def outerCompose (outer : Jet2) (j : BivariateJet2) : BivariateJet2 :=
  ⟨fun t => outer.value (j.value t),
    fun t => outer.first (j.value t)*j.firstA t,
    fun t => outer.first (j.value t)*j.firstZ t,
    fun t => outer.second (j.value t)*(j.firstA t)^2+outer.first (j.value t)*j.secondAA t,
    fun t => outer.second (j.value t)*j.firstA t*j.firstZ t+outer.first (j.value t)*j.secondAZ t,
    fun t => outer.second (j.value t)*(j.firstZ t)^2+outer.first (j.value t)*j.secondZZ t⟩

















































end BivariateJet2
end GeneralCK.Certificates

namespace GeneralCK.Certificates.DyadicLog

/-- All data are untrusted until `checkEndpoint` accepts. -/
structure Witness where
  reciprocal : Bool
  exponent : ℕ
  w : ℚ
  terms : ℕ
  lo : ℚ
  hi : ℚ
  twoTerms : ℕ
  twoLo : ℚ
  twoHi : ℚ
  deriving DecidableEq, Repr





















































end GeneralCK.Certificates.DyadicLog

namespace GeneralCK.Certificates.DyadicEntropy
open DyadicInterval

/-- Logarithm intervals and witnesses for the natural entropy formula. -/
structure Witness (p : ℕ) where
  logTwo : DyadicInterval p
  logPlus : DyadicInterval p
  logMinus : DyadicInterval p
  two : DyadicLog.Witness
  plusLo : DyadicLog.Witness
  plusHi : DyadicLog.Witness
  minusLo : DyadicLog.Witness
  minusHi : DyadicLog.Witness











/-- The two logarithms occurring in the positive contact denominator `B(c)`. -/
structure BWitness (p : ℕ) where
  logTwo : DyadicInterval p
  logGap : DyadicInterval p
  two : DyadicLog.Witness
  gapLo : DyadicLog.Witness
  gapHi : DyadicLog.Witness







end GeneralCK.Certificates.DyadicEntropy

namespace GeneralCK.Certificates.DyadicContact
open DyadicInterval
open GeneralCK.Reflection









structure BracketWitness (p : ℕ) where
  entropyLo : DyadicInterval p
  entropyHi : DyadicInterval p
  loWitness : DyadicEntropy.Witness p
  hiWitness : DyadicEntropy.Witness p





















end GeneralCK.Certificates.DyadicContact

namespace GeneralCK.Certificates
open DyadicInterval

namespace DyadicInterval.Contains







end DyadicInterval.Contains

/-- Coordinate coefficients are enclosed before contracting with a segment direction. -/
structure DyadicBivariateJetEnclosure (p : ℕ) where
  value : DyadicInterval p
  firstA : DyadicInterval p
  firstZ : DyadicInterval p
  secondAA : DyadicInterval p
  secondAZ : DyadicInterval p
  secondZZ : DyadicInterval p

namespace DyadicBivariateJetEnclosure
variable {p : ℕ}






































































end DyadicBivariateJetEnclosure
end GeneralCK.Certificates

namespace GeneralCK.Certificates.BivariateJetProgram

/-- Every nonlinear witness is checked; none is a semantic hypothesis. -/
inductive Op (p : ℕ) where
  | add (left right : ℕ)
  | neg (arg : ℕ)
  | mul (left right : ℕ)
  | inv (arg : ℕ)
  | log (arg : ℕ) (lower upper : DyadicLog.Witness)
  | contact (arg : ℕ) (c B : DyadicInterval p) (outer : DyadicJetEnclosure p)
      (bracket : DyadicContact.BracketWitness p) (denominator : DyadicEntropy.BWitness p)


def zeroJet : BivariateJet2 := BivariateJet2.const 0

/-- The computational shape contains no interval proposals or witnesses. -/
inductive Shape where
  | add (left right : ℕ)
  | neg (arg : ℕ)
  | mul (left right : ℕ)
  | inv (arg : ℕ)
  | log (arg : ℕ)
  | contact (arg : ℕ)
  deriving DecidableEq

noncomputable def Shape.eval (shape : Shape) (jets : List BivariateJet2) : BivariateJet2 :=
  match shape with
  | .add i j => (jets.getD i zeroJet).add (jets.getD j zeroJet)
  | .neg i => (jets.getD i zeroJet).neg
  | .mul i j => (jets.getD i zeroJet).mul (jets.getD j zeroJet)
  | .inv i => (jets.getD i zeroJet).inv
  | .log i => (jets.getD i zeroJet).log
  | .contact i => BivariateJet2.outerCompose reflectionContactJet (jets.getD i zeroJet)

namespace Op



def InRange {p : ℕ} (op : Op p) (n : ℕ) : Prop := match op with
  | .add i j | .mul i j => i<n ∧ j<n
  | .neg i | .inv i | .log i _ _ | .contact i _ _ _ _ _ => i<n

instance {p : ℕ} (op : Op p) (n : ℕ) : Decidable (op.InRange n) := by
  cases op <;> unfold InRange <;> infer_instance







end Op

























































end GeneralCK.Certificates.BivariateJetProgram

namespace GeneralCK.Certificates.BivariateProvedProgram
open BivariateJetProgram Set

/-- Numerical proof data are kept in separate theorems rather than copied into
every instruction. The operation itself remains the old witness-free shape. -/
structure Instruction (p : ℕ) where
  shape : Shape
  proposed : DyadicBivariateJetEnclosure p

def InRange (shape : Shape) (n : ℕ) : Prop := match shape with
  | .add i j | .mul i j => i<n ∧ j<n
  | .neg i | .inv i | .log i | .contact i => i<n

instance (shape : Shape) (n : ℕ) : Decidable (InRange shape n) := by
  cases shape <;> unfold InRange <;> infer_instance







noncomputable def finalJets {p : ℕ} : List (Instruction p) → List BivariateJet2 → List BivariateJet2
  | [], jets => jets
  | ins::rest, jets => finalJets rest (ins.shape.eval jets::jets)

































end GeneralCK.Certificates.BivariateProvedProgram


