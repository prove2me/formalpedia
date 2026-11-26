-- Prove2me | Definitions.Def_O3_Foundation
-- name    : O3_Foundation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:51:16.002797+00:00
-- url     : https://prove2.me/theorems/4ea86c79-7cbf-585d-ae44-804ef99eb109
-- title:
--   Foundation
-- statement:
--   Definitions and structural lemmas for Foundation, from Yuning Yang (yuningyang19/parameter_free_gradient_p; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Parameter-free gradient minimization in l_p geometry development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Foundation.lean

import Definitions.Def_O3_Geometry
set_option autoImplicit true
namespace O3
abbrev Vec (d : ℕ) := Point d
structure PairOracle (d : ℕ) where
  value : Vec d → ℝ
  gradient : Vec d → Vec d
structure Observation (d : ℕ) where
  point : Vec d
  value : ℝ
  gradient : Vec d
def PairOracle.observe {d : ℕ} (oracle : PairOracle d) (x : Vec d) : Observation d :=
  ⟨x, oracle.value x, oracle.gradient x⟩
structure MethodInput (d : ℕ) where
  p : ℝ
  eps : ℝ
  x0 : Vec d
  z0 : Vec d
  M0 : ℝ
inductive Action (d : ℕ) (State : Type) where
  | done (point : Vec d)
  | query (point : Vec d) (next : Observation d → State)
structure FirstOrderMethod (d : ℕ) where
  State : Type
  initial : MethodInput d → State
  action : State → Action d State
structure RunResult (d : ℕ) where
  returned : Vec d
  queries : List (Observation d)
def FirstOrderMethod.runFuel {d : ℕ} (method : FirstOrderMethod d)
    (oracle : PairOracle d) : ℕ → method.State → List (Observation d) → Option (RunResult d)
  | 0, _, _ => none
  | fuel + 1, state, history =>
      match method.action state with
      | .done x => some ⟨x, history⟩
      | .query x next =>
          let obs := oracle.observe x
          method.runFuel oracle fuel (next obs) (history ++ [obs])
def FirstOrderMethod.run {d : ℕ} (method : FirstOrderMethod d)
    (oracle : PairOracle d) (input : MethodInput d) (fuel : ℕ) : Option (RunResult d) :=
  method.runFuel oracle fuel (method.initial input) []
def RunResult.callCount {d : ℕ} (result : RunResult d) : ℕ := result.queries.length
def RunResult.returnedWasQueried {d : ℕ} (result : RunResult d) : Prop :=
  result.returned ∈ result.queries.map Observation.point
def IsCoordinateGradient {d : ℕ} (f : Vec d → ℝ) (grad : Vec d → Vec d) : Prop :=
  ∀ x, DifferentiableAt ℝ f x ∧ ∀ h, fderiv ℝ f x h = pairing (grad x) h
def MinimizerSet {d : ℕ} (f : Vec d → ℝ) : Set (Vec d) :=
  {x | ∀ y, f x ≤ f y}
noncomputable def minimizerDistance {d : ℕ} (p : ℝ) (f : Vec d → ℝ) (x0 : Vec d) : ℝ :=
  sInf ((fun x => lpNorm p (x - x0)) '' MinimizerSet f)
def IsLpSmooth {d : ℕ} (p q L : ℝ) (grad : Vec d → Vec d) : Prop :=
  ∀ x y, lpNorm q (grad x - grad y) ≤ L * lpNorm p (x - y)
def SecantWitness {d : ℕ} (p q M0 : ℝ) (grad : Vec d → Vec d)
    (x0 z0 : Vec d) : Prop :=
  z0 ≠ x0 ∧ grad z0 ≠ grad x0 ∧
    M0 = lpNorm q (grad z0 - grad x0) / lpNorm p (z0 - x0) ∧ 0 < M0
def IsConvexObjective {d : ℕ} (f : Vec d → ℝ) : Prop := ConvexOn ℝ Set.univ f
structure AdmissibleInstance (d : ℕ) (p : ℝ) where
  f : Vec d → ℝ
  grad : Vec d → Vec d
  L : ℝ
  eps : ℝ
  x0 : Vec d
  z0 : Vec d
  M0 : ℝ
  p_gt_one : 1 < p
  L_pos : 0 < L
  eps_pos : 0 < eps
  gradient_spec : IsCoordinateGradient f grad
  convex : IsConvexObjective f
  minimizer_nonempty : (MinimizerSet f).Nonempty
  smooth : IsLpSmooth p (conjugateExponent p) L grad
  secant : SecantWitness p (conjugateExponent p) M0 grad x0 z0
def AdmissibleInstance.oracle {d : ℕ} {p : ℝ} (P : AdmissibleInstance d p) : PairOracle d :=
  ⟨P.f, P.grad⟩
def AdmissibleInstance.methodInput {d : ℕ} {p : ℝ} (P : AdmissibleInstance d p) : MethodInput d :=
  ⟨p, P.eps, P.x0, P.z0, P.M0⟩
noncomputable def AdmissibleInstance.radius {d : ℕ} {p : ℝ} (P : AdmissibleInstance d p) : ℝ :=
  minimizerDistance p P.f P.x0
noncomputable def AdmissibleInstance.condition {d : ℕ} {p : ℝ}
    (P : AdmissibleInstance d p) : ℝ := P.L * P.radius / P.eps
noncomputable def AdmissibleInstance.conditionBar {d : ℕ} {p : ℝ}
    (P : AdmissibleInstance d p) : ℝ := max 1 P.condition
def RunResult.hasTargetGradient {d : ℕ} {p : ℝ} (P : AdmissibleInstance d p)
    (result : RunResult d) : Prop := lpNorm (conjugateExponent p) (P.grad result.returned) ≤ P.eps
end O3


