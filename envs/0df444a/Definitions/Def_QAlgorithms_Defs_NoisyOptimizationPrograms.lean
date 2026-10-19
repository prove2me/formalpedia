-- Prove2me | Definitions.Def_QAlgorithms_Defs_NoisyOptimizationPrograms
-- name    : QAlgorithms_Defs_NoisyOptimizationPrograms
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:27:17.827872+00:00
-- url     : https://prove2.me/theorems/4cb50c4e-f1d7-4293-abb0-590a79356a69
-- title:
--   NoisyOptimizationPrograms
-- statement:
--   NoisyOptimizationPrograms
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\NoisyOptimizationPrograms.lean

import Definitions.Def_QAlgorithms_Defs_GridSubgradientPrograms
import Definitions.Def_QAlgorithms_Defs_MirrorGeometry
import Definitions.Def_QAlgorithms_Defs_CircuitResources
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
noncomputable section

namespace QAlgorithms.NoisyOptimization

variable {n m d k b w M K N c out : ℕ}

/-- Query and elementary-gate realization of a finite-grid estimation round
(2503.17356 pp.22–23). The physical circuit is chosen before the oracle;
the equality certifies its exact operation, including known initial-state
preparation from clean qubits, never its estimation success. -/
structure OptimizationRound (d : ℕ) (J I : Type) [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] where
  procedure : ValueAccess.RandomizedQueryProcedure d J I
  qubits : ℕ
  gates : Fin procedure.seeds →
    OracleCircuit oneTwoQubitGateSet (fun _ : Fin 1 => Nat.clog 2 (Fintype.card J)) qubits
  fits : Nat.clog 2 (Fintype.card I) ≤ qubits
  uncontrolled : ∀ s, ∀ step ∈ gates s, match step with
    | .gate _ => True
    | .query _ _ control _ _ => control = none
  implements : ∀ s, ∀ U : Matrix J J ℂ, U ∈ Matrix.unitaryGroup J ℂ →
    let Ju := Matrix.of fun (z : Qubits (Nat.clog 2 (Fintype.card J))) (j : J) =>
      if z = natToBits (Nat.clog 2 (Fintype.card J)) ((Fintype.equivFin J) j) then 1 else 0
    act ((gates s).unitary (fun _ => extendEncodedUnitary Ju U)) (zeroKet qubits) =
      padState qubits (WithLp.toLp 2 fun j : Fin (Fintype.card I) =>
        act ((procedure.circuit s).unitary (fun _ => U)) (procedure.initial s)
          ((Fintype.equivFin I).symm j))

/-- Adaptive finite-horizon hybrid program, 2503.17356 pp.22–23,29–34.
Grid queries depend on previously measured outcomes; the unknown f is never
a program parameter. Geometric operations have separately counted traces. -/
inductive AdaptiveOptimizationProgram (d : ℕ) (J I : Type) [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] where
  | output (x : Fin d → ℝ)
  | round (P : OptimizationRound d J I)
      (next : (Fin d → ℝ) → AdaptiveOptimizationProgram d J I)
  | geometry (operations : List ((Fin d → ℝ) → (Fin d → ℝ))) (input : Fin d → ℝ)
      (next : (Fin d → ℝ) → AdaptiveOptimizationProgram d J I)

/-- Terminal leaf carries the output, query/gate/geometry counts and actual
Born weight (2503.17356 pp.29–34). -/
abbrev OptimizationLeaf (d : ℕ) := ((Fin d → ℝ) × (Fin 3 → ℕ)) × ℝ

/-- Conditional finite execution, 2503.17356 pp.22–23,29–34.
The lists retain every branch, including zero-probability branches; no
independence between successive history-dependent estimates is assumed. -/
def executionLaw {d : ℕ} {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : Matrix J J ℂ) :
    AdaptiveOptimizationProgram d J I → List (OptimizationLeaf d)
  | .output x => [((x,0),1)]
  | .geometry ops x next =>
      (executionLaw U (next (ops.foldl (fun z op => op z) x))).map
        (fun leaf => ((leaf.1.1, leaf.1.2 + fun j => if j = 2 then ops.length else 0),leaf.2))
  | .round P next => (List.finRange P.procedure.seeds).flatMap fun s =>
      (List.finRange (Fintype.card I)).flatMap fun z =>
        let outcome := (Fintype.equivFin I).symm z
        let weight := (P.procedure.seeds : ℝ)⁻¹ *
          prob (act ((P.procedure.circuit s).unitary (fun _ => U)) (P.procedure.initial s)) outcome
        (executionLaw U (next (P.procedure.decode s outcome))).map fun leaf =>
          ((leaf.1.1, leaf.1.2 + fun j =>
            if j = 0 then (P.gates s).queryCount 0
            else if j = 1 then (P.gates s).gateCount else 0),weight * leaf.2)

/-- Full positive noise budget with independent diameter K and start-radius R,
2503.17356 pp.29–30,33. mirror=false is Euclidean; mirror=true retains
mu and the two p-norm conversion constants. -/
def IsPermittedPrecision (mirror : Bool) (d T : ℕ)
    (theta G R K rho r1 mu vartheta varthetaDual eps : ℝ) : Prop :=
  0 < d ∧ 0 < T ∧ 0 ≤ R ∧ 0 ≤ K ∧ 0 < eps ∧ 0 < theta ∧ 0 < G ∧ 0 < rho ∧ rho ≤ 1 / 3 ∧ 0 < r1 ∧
    theta ≤ r1 * d * G / rho ∧
    if mirror then 0 < mu ∧ 0 < vartheta ∧ 0 < varthetaDual ∧
      2 * G * R / Real.sqrt (mu * T) +
        23 ^ 2 * varthetaDual * K * Real.sqrt (theta * (d : ℝ) ^ 3 * G / (rho*r1)) +
        2 * G * vartheta * r1 +
        23 ^ 4 * varthetaDual ^ 2 * (R / Real.sqrt (mu*T)) *
          theta * (d : ℝ) ^ 3 / (rho*r1) ≤ eps
    else 23 ^ 4 * theta * (d : ℝ) ^ 4 * R / (Real.sqrt T * rho*r1) +
      (23 * (d : ℝ)) ^ 2 * K * Real.sqrt (theta*G/(rho*r1)) ≤ eps/3

/-- Source projected-subgradient updates and iterate averaging
(2503.17356 pp.29–30), on an actual round factory and supplied geometric
implementation. T is positive and counts completed noisy-query rounds. -/
def projectedLoop {d : ℕ} {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (roundAt : (Fin d → ℝ) → OptimizationRound d J I)
    (projectOps : (Fin d → ℝ) → List ((Fin d → ℝ) → (Fin d → ℝ)))
    (eta : ℝ) (T : ℕ) :
    ℕ → (Fin d → ℝ) → (Fin d → ℝ) → AdaptiveOptimizationProgram d J I
  | 0, _, total => .output ((T : ℝ)⁻¹ • total)
  | fuel+1, x, total => .round (roundAt x) fun g =>
      .geometry (projectOps (x-eta • g)) (x-eta • g) fun xn =>
        projectedLoop roundAt projectOps eta T fuel xn (total+x)

/-- Completed-update count for QPSM, 2503.17356 pp.29–30. -/
def projectedIterations (G R eps : ℝ) : ℕ := max 1 ⌈(3*G*R/eps)^2⌉₊

/-- Exact source Euclidean update on coordinates, 2503.17356 p.29.
The nearest point is constructed by attained distance minimization. -/
def projectedPoint {d : ℕ} (X : Set (EuclideanSpace ℝ (Fin d)))
    (hn : X.Nonempty) (hc : IsClosed X) (hv : Convex ℝ X)
    (z : Fin d → ℝ) : Fin d → ℝ :=
  WithLp.ofLp (euclideanProjection X hn hc hv (WithLp.toLp 2 z))

/-- Finite-history reachable centers, 2503.17356 pp.29–30.
Only seed/outcome branches of the actual round are used. This avoids an
impossible requirement to fit every real center in one finite hypergrid. -/
def reachableCenters {d : ℕ} {J I : Type} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I]
    (roundAt : (Fin d → ℝ) → OptimizationRound d J I)
    (nextPoint : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ))
    (x1 : Fin d → ℝ) : ℕ → Set (Fin d → ℝ)
  | 0 => {x1}
  | t+1 => {y | ∃ x ∈ reachableCenters roundAt nextPoint x1 t,
      ∃ s : Fin (roundAt x).procedure.seeds, ∃ z : I,
        y = nextPoint x ((roundAt x).procedure.decode s z)}

/-- Source circuit certificate at a reachable center, 2503.17356 pp.22–23.
This identifies executed operations and public parameters only; no
subgradient success probability or cost rate is assumed. -/
def IsSourceRound {d b : ℕ} {X I : Type} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I] (P : OptimizationRound d (X × Qubits b) I)
    (x : Fin d → ℝ) (G theta rho r1 : ℝ) : Prop :=
  ∃ repeats : ℕ, ∃ C : ValueAccess.JordanCompilation d b repeats X I,
    P.procedure = C.procedure ∧ C.grid.x = x ∧ C.L = G ∧ C.delta = theta ∧
      C.rho = rho ∧ C.grid.r1 = r1

/-- Known compilation data for QPSM, 2503.17356 pp.22–23,29–30.
Exact source rounds are certified only at the finite reachable histories.
Projection is the attained source projection, not an arbitrary map.
No field assumes optimization success or a resource bound. -/
structure ProjectedImplementation (d b : ℕ) (X I : Type)
    [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
    (G R eps theta : ℝ) (x1 : Fin d → ℝ) where
  feasible : Set (EuclideanSpace ℝ (Fin d))
  nonempty : feasible.Nonempty
  closed : IsClosed feasible
  convex : Convex ℝ feasible
  initial_feasible : WithLp.toLp 2 x1 ∈ feasible
  roundAt : (Fin d → ℝ) → OptimizationRound d (X × Qubits b) I
  projectOps : (Fin d → ℝ) → List ((Fin d → ℝ) → (Fin d → ℝ))
  projects : ∀ z, (projectOps z).foldl (fun x op => op x) z =
    projectedPoint feasible nonempty closed convex z
  sourceRounds : 0 < G → 0 < R → 0 < eps → eps < G*R →
    ∀ t < projectedIterations G R eps, ∀ x ∈
      reachableCenters roundAt (fun x g =>
        projectedPoint feasible nonempty closed convex
          (x-(R/(G*Real.sqrt (projectedIterations G R eps))) • g)) x1 t,
      IsSourceRound (roundAt x) x G theta (1/(3*(projectedIterations G R eps : ℝ)))
        (eps/(6*G*Real.sqrt d))

/-- Concrete public QPSM, 2503.17356 pp.29–30.
T=ceil((3GR/eps)^2), eta=R/(G sqrt(T)), r1=eps/(6G sqrt(d)),
rho=1/(3T); compiled rounds have delta=theta. The final output averages
x1,...,xT. Trivial cases return the given feasible x1 before division. -/
def projectedSubgradientProgram {d b : ℕ} {X I : Type} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I] {G R eps theta : ℝ} {x1 : Fin d → ℝ}
    (C : ProjectedImplementation d b X I G R eps theta x1) :
    AdaptiveOptimizationProgram d (X × Qubits b) I :=
  if 0 < G ∧ 0 < R ∧ 0 < eps ∧ eps < G*R then
    let T := projectedIterations G R eps
    projectedLoop C.roundAt C.projectOps (R/(G*Real.sqrt T)) T T x1 0
  else .output x1

/-- Completed-update count for QMD, 2503.17356 pp.33–34. -/
def mirrorIterations (G R mu eps : ℝ) : ℕ :=
  max 1 ⌈(6*G*R/(Real.sqrt mu*eps))^2⌉₊

/-- Computed mirror update, 2503.17356 pp.31–33.
At x in P it is projection of inverse-gradient(gradient(x)-eta*g).
The zero extension outside P is never used by a source implementation. -/
def mirrorNextPoint {d : ℕ} (D : MirrorProjectionDomain (EuclideanSpace ℝ (Fin d)))
    (eta : ℝ) (x g : Fin d → ℝ) : Fin d → ℝ := by
  classical
  exact if hx : WithLp.toLp 2 x ∈ D.mirror.domain then
    WithLp.ofLp (mirrorProjection D (D.mirror.inverseGradient
      (fderiv ℝ D.mirror.Phi (WithLp.toLp 2 x) -
        eta • innerSL ℝ (WithLp.toLp 2 g))))
  else 0

/-- Known QMD compilation, 2503.17356 pp.22–23,31–34.
The inverse derivative and Bregman projection are computed from Phi.
Source round certificates constrain reachable histories only; theta is the
actual value-oracle precision, not a performance assumption. -/
structure MirrorImplementation (d b : ℕ) (X I : Type)
    [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
    (G R mu vartheta eps theta : ℝ) (x1 : Fin d → ℝ) where
  domain : MirrorProjectionDomain (EuclideanSpace ℝ (Fin d))
  initial_feasible : WithLp.toLp 2 x1 ∈ domain.mirror.feasible ∩ domain.mirror.domain
  roundAt : (Fin d → ℝ) → OptimizationRound d (X × Qubits b) I
  nextOps : ℝ → (Fin d → ℝ) → (Fin d → ℝ) →
    List ((Fin d → ℝ) → (Fin d → ℝ))
  executes : ∀ eta x g, WithLp.toLp 2 x ∈ domain.mirror.domain →
    (nextOps eta x g).foldl (fun z op => op z) x = mirrorNextPoint domain eta x g
  sourceRounds : 0 < G → 0 < R → 0 < mu → 0 < vartheta → 0 < eps →
    eps < G*R*Real.sqrt (2/mu) →
    ∀ t < mirrorIterations G R mu eps, ∀ x ∈ reachableCenters roundAt
      (mirrorNextPoint domain (R/G * Real.sqrt (mu/(mirrorIterations G R mu eps : ℝ)))) x1 t,
      WithLp.toLp 2 x ∈ domain.mirror.domain ∧
      IsSourceRound (roundAt x) x G theta (1/(3*(mirrorIterations G R mu eps : ℝ)))
        (eps/(6*G*vartheta))

/-- Concrete QMD averaging program, 2503.17356 pp.31–34.
eta=(R/G)sqrt(mu/T), T=ceil((6GR/(sqrt(mu)eps))^2),
r1=eps/(6G*vartheta), rho=1/(3T), with actual source Jordan rounds.
The trivial radius/constant/already-accurate branches precede divisions. -/
def mirrorDescentProgram {d b : ℕ} {X I : Type} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I] {G R mu vartheta eps theta : ℝ} {x1 : Fin d → ℝ}
    (C : MirrorImplementation d b X I G R mu vartheta eps theta x1) :
    AdaptiveOptimizationProgram d (X × Qubits b) I :=
  let T := mirrorIterations G R mu eps
  let eta := R/G * Real.sqrt (mu/T)
  let loop := Nat.rec (motive := fun _ => (Fin d → ℝ) → (Fin d → ℝ) →
      AdaptiveOptimizationProgram d (X × Qubits b) I)
    (fun _ total => .output ((T : ℝ)⁻¹ • total))
    (fun _ rec x total => .round (C.roundAt x) fun g =>
      .geometry (C.nextOps eta x g) x fun xn => rec xn (total+x))
  if 0 < G ∧ 0 < R ∧ 0 < mu ∧ 0 < vartheta ∧ 0 < eps ∧ eps < G*R*Real.sqrt (2/mu) then
    loop T x1 0
  else .output x1

/-- Uniform polylogarithmic gate/resource bound, 2503.17356 pp.5,22,29,32.
The absolute constant, degree and threshold precede public parameters. -/
def PolylogResourceBound {Input : ℕ → ℕ → ℝ → Type*}
    (cost : (d T : ℕ) → (theta : ℝ) → Input d T theta → ℕ)
    (scale : ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∃ threshold : ℝ, 1 ≤ threshold ∧
    ∀ d T theta, 1 ≤ d → 1 ≤ T → 0 < theta → threshold ≤ scale d T theta →
      ∀ input : Input d T theta,
      (cost d T theta input : ℝ) ≤ C * scale d T theta *
        max 1 (Real.log (2+d+T) + |Real.log theta|)^p

/-- Sanity check for the modeled source objects (arxiv-2503.17356v2, PDF pp.5,6,22,29,30,31,32,33,34). -/
example {d : ℕ} {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : Matrix J J ℂ) (x : Fin d → ℝ) :
    executionLaw U (.output x : AdaptiveOptimizationProgram d J I) = [((x,0),1)] := rfl

end QAlgorithms.NoisyOptimization


