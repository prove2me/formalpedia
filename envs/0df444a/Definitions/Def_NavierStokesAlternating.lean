-- Prove2me | Definitions.Def_NavierStokesAlternating
-- name    : NavierStokesAlternating
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:19.68204+00:00
-- url     : https://prove2.me/theorems/62c1972b-0138-4a34-8326-696d2f0d575f
-- statement:
--   This block sets up a Turing-machine halting criterion and a family of forced Navier–Stokes problems in R³, and defines a proposition AlternatingConclusion(ν) linking them. A Machine is a tuple encoding a number of states (first entry plus one), an alphabet size (plus one), an initial state, a list of halting states, and a transition table of optional rules (new state, written symbol, move in {0,1,2}, meaning head shift of −1, 0, or +1). WellFormed requires the initial state, halting states and all rule targets and symbols to be in range; ValidInput requires input symbols below the alphabet size. A configuration has a state, an integer head position and a two-way infinite tape ℤ→ℕ; the initial tape holds the input from cell 0 and zeros elsewhere. A configuration is halting if its state is a halting state or the special state equal to the state count; a step does nothing when halting, moves to that special state when no rule applies, and otherwise applies the rule. Halts(M,w) means some iterate is halting. On the PDE side, fields are maps (t,x) ↦ value on ℝ×ℝ³, with spatial derivatives, time derivative one-sided at t=0, mixed derivatives ∂ₜˡ∂ˣ^α, divergence, gradient, Laplacian, advection (u·∇)u, and residual(ν,u)=∂ₜu+(u·∇)u−νΔu. Further predicates are: Smooth (C^∞ on t≥0); ClassicalRegularity; ContinuousInH(k) (spatial derivatives up to order k are continuous in time into L²); C1InL2; CompetitorEnergyClass (those L² regularity conditions plus local-in-time boundedness of u); EnergyClass (that plus a bound on |u|+|Du| on each finite time interval); NavierStokes(ν,f,u,p) (classical regularity, zero initial velocity, divergence-free, and ∂ₜu+(u·∇)u=−∇p+νΔu+f for t≥0); Rapid (every mixed derivative decays faster than any polynomial in 1+t+|x|, uniformly); SupportedIn K; and IsTrajectory (a C¹ path γ from a with γ′=u(t,γ)). Computability is expressed via Nat.Partrec codes: ProgramFor(c,F) says three programs respectively approximate each mixed derivative at rational points to dyadic accuracy 2⁻ᵏ, give moduli of uniform continuity on balls, and give integer bounds for the weighted derivative norms. AlternatingConclusion(ν) is then the defined proposition, not a proved theorem, that there exist computable compilers from (M,w) to program triples for a force and a velocity, and a single compact K, such that for every well-formed M and valid input w there are smooth, rapidly decaying fields f and U supported in K, computed by those programs, with f=residual(ν,U), U solving Navier–Stokes with force f and zero pressure in the energy class, U unique among solutions in the competitor energy class (pressure also zero), all trajectories of U unique and globally existing, and the trajectory from the point (−1,0,0) has a positive first coordinate at some time t≥0 exactly when M halts on w.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NavierStokesAlternating.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/NavierStokesAlternating.lean; bytes 16..9089
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

open scoped BigOperators ENNReal Topology ContDiff
open MeasureTheory

namespace AlternatingNS

abbrev Rule := ℕ × ℕ × Fin 3

abbrev Machine := ℕ × ℕ × ℕ × List ℕ × List (Option Rule)

namespace Machine

def states (M : Machine) : ℕ := M.1 + 1

def alphabet (M : Machine) : ℕ := M.2.1 + 1

def initialState (M : Machine) : ℕ := M.2.2.1

def haltingStates (M : Machine) : List ℕ := M.2.2.2.1

def table (M : Machine) : List (Option Rule) := M.2.2.2.2

def instruction (M : Machine) (q a : ℕ) : Option Rule :=
  (M.table[q * M.alphabet + a]?).join

def WellFormed (M : Machine) : Prop :=
  M.initialState < M.states ∧
  (∀ q ∈ M.haltingStates, q < M.states) ∧
  ∀ q a r, q < M.states → a < M.alphabet → M.instruction q a = some r →
    r.1 < M.states ∧ r.2.1 < M.alphabet

def ValidInput (M : Machine) (w : List ℕ) : Prop :=
  ∀ a ∈ w, a < M.alphabet

structure Configuration where
  state : ℕ
  head : ℤ
  tape : ℤ → ℕ

def isHalting (M : Machine) (c : Configuration) : Bool :=
  decide (c.state = M.states ∨ c.state ∈ M.haltingStates)

def initial (M : Machine) (w : List ℕ) : Configuration where
  state := M.initialState
  head := 0
  tape := fun i => if 0 ≤ i then w[i.toNat]?.getD 0 else 0

def step (M : Machine) (c : Configuration) : Configuration :=
  if M.isHalting c then c else
    match M.instruction c.state (c.tape c.head) with
    | none => { c with state := M.states }
    | some r =>
      { state := r.1
        head := c.head + ((r.2.2.val : ℤ) - 1)
        tape := Function.update c.tape c.head r.2.1 }

def run (M : Machine) (w : List ℕ) (n : ℕ) : Configuration :=
  (M.step)^[n] (M.initial w)

def Halts (M : Machine) (w : List ℕ) : Prop :=
  ∃ n : ℕ, M.isHalting (M.run w n) = true

end Machine

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Field (E : Type*) := ℝ → Space → E
abbrev Velocity := Field Space
abbrev Pressure := Field ℝ
abbrev MultiIndex := Fin 3 → ℕ

noncomputable section

def e (i : Fin 3) : Space := EuclideanSpace.single i 1

def dx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : Fin 3) (F : Field E) : Field E :=
  fun t x => fderiv ℝ (F t) x (e i)

def dt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) : Field E :=
  fun t x => fderivWithin ℝ (fun s => F s x) (Set.Ici 0) t 1

def spatial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : MultiIndex) (F : Field E) : Field E :=
  (dx 0)^[α 0] ((dx 1)^[α 1] ((dx 2)^[α 2] F))

def mixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : ℕ) (α : MultiIndex) (F : Field E) : Field E :=
  dt^[l] (spatial α F)

def div (u : Velocity) (t : ℝ) (x : Space) : ℝ :=
  ∑ i : Fin 3, dx i u t x i

def grad (p : Pressure) (t : ℝ) (x : Space) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => dx i p t x)

def laplacian (u : Velocity) (t : ℝ) (x : Space) : Space :=
  ∑ i : Fin 3, dx i (dx i u) t x

def advection (u : Velocity) (t : ℝ) (x : Space) : Space :=
  fderiv ℝ (u t) x (u t x)

def residual (ν : ℝ) (u : Velocity) : Velocity :=
  fun t x => dt u t x + advection u t x - ν • laplacian u t x

def timeCylinder (T : ℝ) : Set (ℝ × Space) := Set.Icc 0 T ×ˢ Set.univ

def Smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Field E) : Prop :=
  ContDiffOn ℝ (∞) (Function.uncurry F) (Set.Ici 0 ×ˢ Set.univ)

def ClassicalRegularity (u : Velocity) (p : Pressure) : Prop :=
  (∀ x, DifferentiableOn ℝ (fun t => u t x) (Set.Ici 0)) ∧
  (∀ t, 0 ≤ t → Differentiable ℝ (u t)) ∧
  (∀ t, 0 ≤ t → ∀ i, Differentiable ℝ (dx i u t)) ∧
  (∀ t, 0 ≤ t → Differentiable ℝ (p t)) ∧
  ∀ T, 0 ≤ T →
    ContinuousOn (Function.uncurry u) (timeCylinder T) ∧
    ContinuousOn (Function.uncurry (dt u)) (timeCylinder T) ∧
    (∀ i, ContinuousOn (Function.uncurry (dx i u)) (timeCylinder T)) ∧
    (∀ i j, ContinuousOn (Function.uncurry (dx i (dx j u))) (timeCylinder T)) ∧
    ContinuousOn (Function.uncurry p) (timeCylinder T) ∧
    (∀ i, ContinuousOn (Function.uncurry (dx i p)) (timeCylinder T))

def ContinuousInH {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : ℕ) (F : Field E) (T : ℝ) : Prop :=
  ∀ α : MultiIndex, (∑ i, α i) ≤ k →
    ∃ g : ℝ → Lp E 2 (volume : Measure Space),
      ContinuousOn g (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T,
        ∀ᵐ x ∂(volume : Measure Space), (g t) x = spatial α F t x

def C1InL2 (u : Velocity) (T : ℝ) : Prop :=
  ∃ g g' : ℝ → Lp Space 2 (volume : Measure Space),
    ContinuousOn g (Set.Icc 0 T) ∧
    ContinuousOn g' (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Icc 0 T, HasDerivWithinAt g (g' t) (Set.Icc 0 T) t) ∧
    (∀ t ∈ Set.Icc 0 T, ∀ᵐ x ∂(volume : Measure Space), (g t) x = u t x) ∧
    (∀ t ∈ Set.Icc 0 T, ∀ᵐ x ∂(volume : Measure Space), (g' t) x = dt u t x)

def CompetitorEnergyClass (u : Velocity) (p : Pressure) : Prop :=
  ∀ T, 0 ≤ T →
    ContinuousInH 2 u T ∧ C1InL2 u T ∧ ContinuousInH 1 p T ∧
    ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ x, ‖u t x‖ ≤ C

def EnergyClass (u : Velocity) (p : Pressure) : Prop :=
  CompetitorEnergyClass u p ∧
  ∀ T, 0 ≤ T → ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ x,
    ‖u t x‖ + ‖fderiv ℝ (u t) x‖ ≤ C

def NavierStokes (ν : ℝ) (f u : Velocity) (p : Pressure) : Prop :=
  ClassicalRegularity u p ∧
  (∀ x, u 0 x = 0) ∧
  ∀ t, 0 ≤ t → ∀ x,
    div u t x = 0 ∧
    dt u t x + advection u t x = -grad p t x + ν • laplacian u t x + f t x

def Rapid (F : Velocity) : Prop :=
  ∀ J l : ℕ, ∀ α : MultiIndex, ∃ C : ℝ, 0 ≤ C ∧
    ∀ t, 0 ≤ t → ∀ x,
      (1 + t + ‖x‖) ^ J * ‖mixed l α F t x‖ ≤ C

def SupportedIn (F : Velocity) (K : Set Space) : Prop :=
  ∀ t, 0 ≤ t → Function.support (F t) ⊆ K

def IsTrajectory (u : Velocity) (a : Space) (γ : ℝ → Space) : Prop :=
  γ 0 = a ∧ ∀ t, 0 ≤ t → HasDerivWithinAt γ (u t (γ t)) (Set.Ici 0) t

def observedParticle : Space := (EuclideanSpace.equiv (Fin 3) ℝ).symm ![-1, 0, 0]

abbrev RationalPoint := ℚ × ℚ × ℚ × ℚ
abbrev RationalVector := ℚ × ℚ × ℚ
abbrev IndexCode := ℕ × ℕ × ℕ
abbrev Program := Nat.Partrec.Code
abbrev FieldProgram := Program × Program × Program

def Returns {A B : Type*} [Encodable A] [Encodable B]
    (c : Program) (a : A) (b : B) : Prop :=
  Encodable.encode b ∈ c.eval (Encodable.encode a)

def index (α : IndexCode) : MultiIndex := ![α.1, α.2.1, α.2.2]

def rationalVector (q : RationalVector) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![(q.1 : ℝ), (q.2.1 : ℝ), (q.2.2 : ℝ)]

def rationalPoint (q : RationalPoint) : ℝ × Space :=
  ((q.1 : ℝ), rationalVector q.2)

def dyadicError (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

def ComputableReal (r : ℝ) : Prop :=
  ∃ a : ℕ → ℚ, Computable (fun n => ((a n).num, (a n).den)) ∧
    ∀ n, |r - (a n : ℝ)| ≤ dyadicError n

def ProgramFor (c : FieldProgram) (F : Velocity) : Prop :=
  (∀ (l : ℕ) (α : IndexCode) (q : RationalPoint) (k : ℕ),
    ∃ v : RationalVector, Returns c.1 (l, α, q, k) v ∧
      (0 ≤ q.1 →
        ‖rationalVector v - mixed l (index α) F (rationalPoint q).1 (rationalPoint q).2‖
          ≤ dyadicError k)) ∧
  (∀ (l : ℕ) (α : IndexCode) (R k : ℕ),
    ∃ m : ℕ, Returns c.2.1 (l, α, R, k) m ∧
      ∀ z z' : ℝ × Space,
        0 ≤ z.1 → 0 ≤ z'.1 → ‖z‖ ≤ R → ‖z'‖ ≤ R →
        ‖z - z'‖ ≤ dyadicError m →
        ‖mixed l (index α) F z.1 z.2 - mixed l (index α) F z'.1 z'.2‖ ≤ dyadicError k) ∧
  (∀ (J l : ℕ) (α : IndexCode),
    ∃ B : ℕ, Returns c.2.2 (J, l, α) B ∧
      ∀ t, 0 ≤ t → ∀ x,
        (1 + t + ‖x‖) ^ J * ‖mixed l (index α) F t x‖ ≤ B)

def AlternatingConclusion (ν : ℝ) : Prop :=
  ∃ (compileForce compileVelocity : Machine × List ℕ → FieldProgram),
    Computable compileForce ∧ Computable compileVelocity ∧
    ∃ K : Set Space, IsCompact K ∧
      ∀ (M : Machine) (w : List ℕ), M.WellFormed → M.ValidInput w →
        ∃ (f U : Velocity) (X : Space → ℝ → Space),
          ProgramFor (compileForce (M, w)) f ∧
          ProgramFor (compileVelocity (M, w)) U ∧
          Smooth f ∧ Smooth U ∧
          SupportedIn f K ∧ SupportedIn U K ∧ Rapid f ∧ Rapid U ∧
          f = residual ν U ∧
          NavierStokes ν f U (fun _ _ => 0) ∧ EnergyClass U (fun _ _ => 0) ∧
          (∀ (v : Velocity) (p : Pressure),
            NavierStokes ν f v p → CompetitorEnergyClass v p →
            ∀ t, 0 ≤ t → ∀ x, v t x = U t x ∧ p t x = 0) ∧
          (∀ a, IsTrajectory U a (X a)) ∧
          (∀ a γ, IsTrajectory U a γ → ∀ t, 0 ≤ t → γ t = X a t) ∧
          ((∃ t : ℝ, 0 ≤ t ∧ 0 < X observedParticle t 0) ↔ M.Halts w)

end
end AlternatingNS

namespace AlternatingNS



end AlternatingNS
end OAI


