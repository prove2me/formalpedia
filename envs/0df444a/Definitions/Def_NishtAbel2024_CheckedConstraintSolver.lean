-- Prove2me | Definitions.Def_NishtAbel2024_CheckedConstraintSolver
-- name    : NishtAbel2024_CheckedConstraintSolver
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-02T03:14:23.419197+00:00
-- url     : https://prove2.me/theorems/b952d27f-867e-41d5-87a6-896211841661
-- title:
--   Fuel-bounded checked constraint solver
-- statement:
--   Define an executable fuel-bounded strict size-comparison test and a conservative checked wrapper around the existing NishtAbel2024 constraint solver. The wrapper computes the existing candidate, checks finite-support well-formedness, rigid-variable identity, and all constraints in the existing CoherentSubst interpretation, and returns the candidate only if all checks pass. Failure returns none and is inconclusive. The strict test uses raw bounds; constraint satisfaction follows the existing CoherentSubst right-bound normalization. This is an auxiliary partial certifier, not a replacement claimed complete for Algorithm 1, and it does not check separate raw function-call bounds.
-- source:
--   Auxiliary construction for the existing Lean definitions, inspired by K. Nisht, Type-Based Termination Checking in Agda (2024), §6.4, pp. 56–58, https://knisht.github.io/agda/msc.pdf. This particular checked wrapper and finite-fuel procedure are not claimed to be the original thesis algorithm.

import Definitions.Def_NishtAbel2024_Inference

namespace NishtAbel2024.RawSizeLtCheck

def usable : Polarity → Bool
  | .mixed => true
  | .pos => true
  | .neg => false
  | .top => false

def hasBound (Ψ : SizeCtx) (i : SizeVar) : Bool :=
  Ψ.any (fun d => (d.var == i) && usable d.pol)

def hasBoundEq (Ψ : SizeCtx) (i : SizeVar) (a : SizeExp) : Bool :=
  Ψ.any (fun d => (d.var == i) && usable d.pol && (d.bound == a))

def checkWf (Ψ : SizeCtx) : SizeExp → Bool
  | .inf _ => true
  | .meet a => a.toList.all (fun sv => hasBound Ψ sv.var)

def direct (Ψ : SizeCtx) : SizeExp → SizeExp → Bool
  | .inf n, b =>
      match b with
      | .inf m => decide (n < m)
      | .meet _ => false
  | .meet am, b =>
      match am.tail with
      | _ :: _ => false
      | [] =>
        match b with
        | .inf _ => hasBoundEq Ψ am.head.var .infty
        | .meet bm =>
          match bm.tail with
          | _ :: _ => false
          | [] => (am.head.var == bm.head.var) &&
              decide (am.head.shift < bm.head.shift) && hasBound Ψ am.head.var

def checkSizeLt : Nat → SizeCtx → SizeExp → SizeExp → Bool
  | 0, _, _, _ => false
  | fuel + 1, Ψ, a, b =>
    direct Ψ a b ||
    (match b with
     | .meet bm =>
         if bm.tail.isEmpty then false
         else bm.toList.all (fun sv => checkSizeLt fuel Ψ a (.var sv.var sv.shift))
     | .inf _ => false) ||
    (match a with
     | .meet am =>
         if am.tail.isEmpty then false
         else checkWf Ψ (.meet am) &&
           am.toList.any (fun sv => checkSizeLt fuel Ψ (.var sv.var sv.shift) b)
     | .inf _ => false) ||
    (match a with
     | .inf _ => false
     | .meet am =>
       match am.tail with
       | _ :: _ => false
       | [] => Ψ.any (fun d => (d.var == am.head.var) && usable d.pol &&
           checkSizeLt fuel Ψ (d.bound.shift am.head.shift) (b.shift 1)))

end NishtAbel2024.RawSizeLtCheck

namespace NishtAbel2024.CheckedConstraintSolver

def support (Ψ : SizeCtx) (C : List SizeConstraint) (T : List SizeVar) : List SizeVar :=
  Ψ.dom ++ C.flatMap (fun c => c.lhs.vars ++ c.rhs.vars) ++ T

def constraintCheck (fuel : Nat) (Ψ : SizeCtx) (φ : FlexSubst) (c : SizeConstraint) : Bool :=
  match c.rel with
  | .lt => RawSizeLtCheck.checkSizeLt fuel Ψ (c.lhs.applyFlex φ) (c.rhs.applyFlex φ).boundNorm
  | .le => RawSizeLtCheck.checkSizeLt fuel Ψ (c.lhs.applyFlex φ) ((c.rhs.applyFlex φ).boundNorm.shift 1)

/-- Finite certificate for the original candidate. False is inconclusive:
the primitive comparisons are sound but fuel-bounded and incomplete. -/
def certificate (fuel : Nat) (Ψ : SizeCtx) (C : List SizeConstraint) (T : List SizeVar) : Bool :=
  let φ := solveConstraintGraph Ψ C T
  Ψ.dom.all (fun k => φ k == .var k 0) &&
    (support Ψ C T).all (fun k => RawSizeLtCheck.checkWf Ψ (φ k)) &&
    C.all (constraintCheck fuel Ψ φ)

/-- Return the original candidate only when its finite certificate succeeds. -/
def checkedSolve (fuel : Nat) (Ψ : SizeCtx) (C : List SizeConstraint) (T : List SizeVar) : Option FlexSubst :=
  if certificate fuel Ψ C T then some (solveConstraintGraph Ψ C T) else none

end NishtAbel2024.CheckedConstraintSolver


