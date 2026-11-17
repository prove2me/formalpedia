-- Prove2me | Definitions.Def_CorrelatedLocalSearch_Supplement_RestartSynthesis
-- name    : CorrelatedLocalSearch_Supplement_RestartSynthesis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:02:45.604557+00:00
-- url     : https://prove2.me/theorems/95e07210-6f05-4b11-a294-304588c13c37
-- title:
--   Same-tape restarts and finite-state powered-transition synthesis
-- statement:
--   A one-symbol deterministic algorithm is represented by its prefix-closed live histories. A same-tape restart policy makes one deterministic decision from each observed prefix before the next source-consuming step. For a finite live state space $X$, every state has finitely many nonempty update choices and transitions to another live state or termination. The powered row is $R_f(y,z)=\sum_{a:T_f(y,a)=z}\pi(a)^s$. The layer defines the first LP (15), tight actions, the tie-breaking LP (33), history-dependent selectors and controlled restart stopping times.
--
--   **Formalization Note** Policy types build in nonanticipation, availability of updates and resetting only to the fixed initial state.
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), §6 pp.15–16 and App. D.2 pp.34–36 (PDF pp.17–18, 36–38)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_GeneralSource

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- A deterministic one-symbol-per-step algorithm, represented by its live finite histories. -/
structure OneSymbolAlgorithm (A : Type*) where
  live : List A -> Prop
  live_nil : live []
  prefix_closed : ∀ u v, u <+: v -> live v -> live u

/-- Its closed nontermination event. -/
def nonterminationEvent {A : Type*} (M : OneSymbolAlgorithm A) : Set (Nat -> A) :=
  {omega | ∀ t, M.live (tapePrefix omega t)}

/-- `alpha_s(x)=C_s(N_x)`; the initial configuration is built into `M`. -/
noncomputable def restartCapacity {A : Type*} (pi : A -> Real) (s : Real)
    (M : OneSymbolAlgorithm A) : ENNReal :=
  prefixCapacity pi s (nonterminationEvent M)

/-- A same-tape restart policy: one Boolean decision from the consumed prefix before each next
source-consuming step. Its type builds in determinism, nonanticipation, and at most one reset
between successive steps. -/
structure SameTapeRestartPolicy (A : Type*) (M : OneSymbolAlgorithm A) where
  restartAfter : List A -> Bool

def restartAttemptFrom {A : Type*} {M : OneSymbolAlgorithm A}
    (rho : SameTapeRestartPolicy A M) : List A -> List A -> List A -> List A
  | _, attempt, [] => attempt
  | pre, attempt, a :: rest =>
      let attempt' := if rho.restartAfter pre then [] else attempt
      restartAttemptFrom rho (pre ++ [a]) (attempt' ++ [a]) rest

def restartAttempt {A : Type*} {M : OneSymbolAlgorithm A}
    (rho : SameTapeRestartPolicy A M) (w : List A) : List A :=
  restartAttemptFrom rho [] [] w

noncomputable def sameTapeRestartTau {A : Type*} {M : OneSymbolAlgorithm A}
    (rho : SameTapeRestartPolicy A M) (omega : Nat -> A) : ℕ∞ :=
  ⨅ (t : Nat) (_h : ¬ M.live (restartAttempt rho (tapePrefix omega t))), (t : ℕ∞)

/-- An explicit finite-state one-symbol process; `none` is termination. -/
structure FiniteProcess (A X : Type*) [Fintype A] [Fintype X] where
  actions : X -> Finset Nat
  actions_nonempty : ∀ y, (actions y).Nonempty
  transition : X -> Nat -> A -> Option X

open Classical in
/-- The powered live transition coefficient `R_f(y,z)`. -/
noncomputable def poweredTransition {A X : Type*} [Fintype A] [Fintype X]
    (M : FiniteProcess A X) (pi : A -> Real) (s : Real) (y : X) (f : Nat) (z : X) : Real :=
  ∑ a, if M.transition y f a = some z then pi a ^ s else 0

abbrev ProcessSelector (A X : Type*) := List A -> X -> Nat

def IsValidProcessSelector {A X : Type*} [Fintype A] [Fintype X]
    (M : FiniteProcess A X) (sel : ProcessSelector A X) : Prop :=
  ∀ w y, sel w y ∈ M.actions y

noncomputable def processRunFrom {A X : Type*} [Fintype A] [Fintype X]
    (M : FiniteProcess A X) (sel : ProcessSelector A X) :
    List A -> Option X -> List A -> Option X
  | _, none, _ => none
  | _, some y, [] => some y
  | pre, some y, a :: rest =>
      processRunFrom M sel (pre ++ [a]) (M.transition y (sel pre y) a) rest

noncomputable def processState {A X : Type*} [Fintype A] [Fintype X]
    (M : FiniteProcess A X) (sel : ProcessSelector A X) (x : X) (w : List A) : Option X :=
  processRunFrom M sel [] (some x) w

def processNonterminationEvent {A X : Type*} [Fintype A] [Fintype X]
    (M : FiniteProcess A X) (sel : ProcessSelector A X) (x : X) : Set (Nat -> A) :=
  {omega | ∀ t, processState M sel x (tapePrefix omega t) ≠ none}

/-- Feasibility in the first LP (15). -/
def FirstLPFeasible {A X : Type*} [Fintype A] [Fintype X]
    (M : FiniteProcess A X) (pi : A -> Real) (s : Real) (v : X -> Real) : Prop :=
  (∀ y, 0 ≤ v y ∧ v y ≤ 1) ∧
    ∀ y f, f ∈ M.actions y ->
      v y ≤ ∑ z, poweredTransition M pi s y f z * v z

/-- `V` is the unique optimizer of the first LP. -/
def IsFirstLPOptimizer {A X : Type*} [Fintype A] [Fintype X]
    (M : FiniteProcess A X) (pi : A -> Real) (s : Real) (V : X -> Real) : Prop :=
  FirstLPFeasible M pi s V ∧
    (∀ v, FirstLPFeasible M pi s v -> (∑ y, v y) ≤ ∑ y, V y) ∧
    ∀ v, FirstLPFeasible M pi s v -> (∑ y, v y) = ∑ y, V y -> v = V

def IsTightAction {A X : Type*} [Fintype A] [Fintype X]
    (M : FiniteProcess A X) (pi : A -> Real) (s : Real) (V : X -> Real)
    (y : X) (f : Nat) : Prop :=
  f ∈ M.actions y ∧ (∑ z, poweredTransition M pi s y f z * V z) = V y

/-- Feasibility and optimality in the tie-breaking LP (33), on `U={y|V(y)<1}`. -/
def IsSecondLPOptimizer {A X : Type*} [Fintype A] [Fintype X]
    (M : FiniteProcess A X) (pi : A -> Real) (s : Real) (V psi : X -> Real) : Prop :=
  (∀ y, V y < 1 -> 0 ≤ psi y) ∧
  (∀ y, V y < 1 -> ∀ f, IsTightAction M pi s V y f ->
    psi y ≤ 1 + ∑ z, if V z < 1 then poweredTransition M pi s y f z * psi z else 0) ∧
  ∀ (phi : X -> Real), (∀ y, V y < 1 -> 0 ≤ phi y) ->
    (∀ y, V y < 1 -> ∀ f, IsTightAction M pi s V y f ->
      phi y ≤ 1 + ∑ z, if V z < 1 then poweredTransition M pi s y f z * phi z else 0) ->
    (∑ y, if V y < 1 then phi y else 0) ≤ ∑ y, if V y < 1 then psi y else 0

/-- A controlled restart policy chooses an available update and a possible reset from the consumed
prefix. Its type builds in deterministic nonanticipation and resetting only to `x0`. -/
structure ControlledRestartPolicy {A X : Type*} [Fintype A] [Fintype X]
    (M : FiniteProcess A X) (x0 : X) where
  action : List A -> X -> Nat
  action_mem : ∀ w y, action w y ∈ M.actions y
  restartBefore : List A -> Bool

noncomputable def controlledRestartRunFrom {A X : Type*} [Fintype A] [Fintype X]
    {M : FiniteProcess A X} {x0 : X} (rho : ControlledRestartPolicy M x0) :
    List A -> Option X -> List A -> Option X
  | _, none, _ => none
  | _, some y, [] => some y
  | pre, some y, a :: rest =>
      let y' := if rho.restartBefore pre then x0 else y
      controlledRestartRunFrom rho (pre ++ [a]) (M.transition y' (rho.action pre y') a) rest

noncomputable def controlledRestartState {A X : Type*} [Fintype A] [Fintype X]
    {M : FiniteProcess A X} {x0 : X} (rho : ControlledRestartPolicy M x0)
    (w : List A) : Option X :=
  controlledRestartRunFrom rho [] (some x0) w

noncomputable def controlledRestartTau {A X : Type*} [Fintype A] [Fintype X]
    {M : FiniteProcess A X} {x0 : X} (rho : ControlledRestartPolicy M x0)
    (omega : Nat -> A) : ℕ∞ :=
  ⨅ (t : Nat) (_h : controlledRestartState rho (tapePrefix omega t) = none), (t : ℕ∞)

/-- The synthesized policy uses the stationary action `mu` and resets exactly on entry to `S`.
The equivalence is stated from the consumed prefix, so it also enforces the paper's timing: the
reset decision is made before the next source symbol is inspected. -/
def UsesStationaryResetRule {A X : Type*} [Fintype A] [Fintype X]
    {M : FiniteProcess A X} {x0 : X} (rho : ControlledRestartPolicy M x0)
    (mu : X -> Nat) (S : Set X) : Prop :=
  (∀ w y, rho.action w y = mu y) ∧
    ∀ w, rho.restartBefore w = true ↔
      ∃ y, controlledRestartState rho w = some y ∧ y ∈ S

/-- One action row in the explicit rational input of Theorem 6.2(iii). -/
structure RationalActionRow where
  label : Nat
  weights : List Rat

/-- A finite rational powered-transition table.  The outer list is the state list; each inner
list is the finite nonempty action list at that state; each action carries one rational weight per
state. -/
structure RationalProcessDescription where
  rows : List (List RationalActionRow)

def IsValidRationalProcessDescription (I : RationalProcessDescription) : Prop :=
  ∀ y < I.rows.length,
    I.rows.getD y [] ≠ [] ∧
      (I.rows.getD y []).Pairwise (fun a b => a.label ≠ b.label) ∧
      ∀ a ∈ I.rows.getD y [], a.weights.length = I.rows.length

/-- Exact rational output requested in Theorem 6.2(iii), including the second-LP potential and
one contraction potential and pair of tail constants for every possible reset state. -/
structure RationalSynthesisOutput where
  values : List Rat
  secondPotential : List Rat
  selector : List Nat
  restartSet : List Bool
  tailPotential : List (List Rat)
  tailK : List Rat
  tailGamma : List Rat

def rationalValue (O : RationalSynthesisOutput) (y : Nat) : Rat := O.values.getD y 0
def rationalPsi (O : RationalSynthesisOutput) (y : Nat) : Rat := O.secondPotential.getD y 0

def rationalActionWeight (I : RationalProcessDescription) (O : RationalSynthesisOutput)
    (y z : Nat) : Rat :=
  ((I.rows.getD y []).map (fun a =>
    if a.label = O.selector.getD y 0 then a.weights.getD z 0 else 0)).sum

def RationalFirstLPFeasible (I : RationalProcessDescription) (v : List Rat) : Prop :=
  v.length = I.rows.length ∧
  (∀ y < I.rows.length, 0 ≤ v.getD y 0 ∧ v.getD y 0 ≤ 1) ∧
  ∀ y < I.rows.length, ∀ a ∈ I.rows.getD y [],
    v.getD y 0 ≤ ∑ z ∈ Finset.range I.rows.length, a.weights.getD z 0 * v.getD z 0

def IsRationalFirstLPOptimizer (I : RationalProcessDescription) (V : List Rat) : Prop :=
  RationalFirstLPFeasible I V ∧
  (∀ v, RationalFirstLPFeasible I v ->
    (∑ y ∈ Finset.range I.rows.length, v.getD y 0) ≤
      ∑ y ∈ Finset.range I.rows.length, V.getD y 0) ∧
  ∀ v, RationalFirstLPFeasible I v ->
    (∑ y ∈ Finset.range I.rows.length, v.getD y 0) =
      ∑ y ∈ Finset.range I.rows.length, V.getD y 0 -> v = V

def IsRationalTightAction (I : RationalProcessDescription) (O : RationalSynthesisOutput)
    (y : Nat) (a : RationalActionRow) : Prop :=
  a ∈ I.rows.getD y [] ∧
    (∑ z ∈ Finset.range I.rows.length,
      a.weights.getD z 0 * rationalValue O z) = rationalValue O y

def RationalSecondLPFeasible (I : RationalProcessDescription) (O : RationalSynthesisOutput)
    (psi : List Rat) : Prop :=
  psi.length = I.rows.length ∧
  (∀ y < I.rows.length, rationalValue O y < 1 -> 0 ≤ psi.getD y 0) ∧
  ∀ y < I.rows.length, rationalValue O y < 1 -> ∀ a,
    IsRationalTightAction I O y a ->
      psi.getD y 0 ≤ 1 + ∑ z ∈ Finset.range I.rows.length,
        if rationalValue O z < 1 then a.weights.getD z 0 * psi.getD z 0 else 0

def IsRationalSecondLPOptimizer (I : RationalProcessDescription)
    (O : RationalSynthesisOutput) : Prop :=
  RationalSecondLPFeasible I O O.secondPotential ∧
  ∀ psi, RationalSecondLPFeasible I O psi ->
    (∑ y ∈ Finset.range I.rows.length,
      if rationalValue O y < 1 then psi.getD y 0 else 0) ≤
    ∑ y ∈ Finset.range I.rows.length,
      if rationalValue O y < 1 then rationalPsi O y else 0

def rationalRestartMatrix (I : RationalProcessDescription) (O : RationalSynthesisOutput)
    (x0 y z : Nat) : Rat :=
  (if rationalValue O z < 1 then rationalActionWeight I O y z else 0) +
    if z = x0 then
      ∑ q ∈ Finset.range I.rows.length,
        if rationalValue O q = 1 then rationalActionWeight I O y q else 0
    else 0

/-- The output is an exact certificate for both LPs, a binding stationary action, the set
`{V=1}`, and explicit geometric-tail constants certified by a positive contraction potential. -/
def IsCorrectRationalSynthesis (I : RationalProcessDescription)
    (O : RationalSynthesisOutput) : Prop :=
  O.values.length = I.rows.length ∧ O.secondPotential.length = I.rows.length ∧
  O.selector.length = I.rows.length ∧ O.restartSet.length = I.rows.length ∧
  O.tailPotential.length = I.rows.length ∧ O.tailK.length = I.rows.length ∧
  O.tailGamma.length = I.rows.length ∧
  IsRationalFirstLPOptimizer I O.values ∧ IsRationalSecondLPOptimizer I O ∧
  (∀ y < I.rows.length,
    ∃ a ∈ I.rows.getD y [], a.label = O.selector.getD y 0 ∧
      (rationalValue O y < 1 -> IsRationalTightAction I O y a ∧
        rationalPsi O y = 1 + ∑ z ∈ Finset.range I.rows.length,
          if rationalValue O z < 1
          then a.weights.getD z 0 * rationalPsi O z else 0)) ∧
  (∀ y < I.rows.length,
    (O.restartSet.getD y false = true ↔ rationalValue O y = 1)) ∧
  ∀ x0 < I.rows.length, rationalValue O x0 < 1 ->
    0 ≤ O.tailK.getD x0 0 ∧ 0 < O.tailGamma.getD x0 0 ∧
    O.tailGamma.getD x0 0 < 1 ∧
    O.tailK.getD x0 0 = (O.tailPotential.getD x0 []).getD x0 0 ∧
    (∀ y < I.rows.length, rationalValue O y < 1 ->
      1 ≤ (O.tailPotential.getD x0 []).getD y 0 ∧
      (∑ z ∈ Finset.range I.rows.length,
        rationalRestartMatrix I O x0 y z *
          (O.tailPotential.getD x0 []).getD z 0) ≤
        O.tailGamma.getD x0 0 * (O.tailPotential.getD x0 []).getD y 0)

def frameBits (w : List Bool) : List Bool :=
  List.replicate w.length true ++ false :: w

def encodeNatBits (n : Nat) : List Bool := frameBits (Computability.encodeNat n)

def encodeRatBits (q : Rat) : List Bool :=
  decide (q.num < 0) :: encodeNatBits q.num.natAbs ++ encodeNatBits q.den

def encodeRationalActionRow (a : RationalActionRow) : List Bool :=
  encodeNatBits a.label ++ frameBits (a.weights.flatMap encodeRatBits)

def encodeRationalProcessDescription (I : RationalProcessDescription) : List Bool :=
  frameBits (I.rows.flatMap (fun row => frameBits (row.flatMap encodeRationalActionRow)))

def encodeRationalSynthesisOutput (O : RationalSynthesisOutput) : List Bool :=
  frameBits (O.values.flatMap encodeRatBits) ++
  frameBits (O.secondPotential.flatMap encodeRatBits) ++
  frameBits (O.selector.flatMap encodeNatBits) ++ frameBits O.restartSet ++
  frameBits (O.tailPotential.flatMap (fun row => frameBits (row.flatMap encodeRatBits))) ++
  frameBits (O.tailK.flatMap encodeRatBits) ++ frameBits (O.tailGamma.flatMap encodeRatBits)

/-- A single Turing-machine procedure works for every finite rational transition table, returns
an exact certificate, and runs in polynomial time in the canonical explicit encodings above. -/
structure RationalSynthesisProcedure where
  solve : RationalProcessDescription -> RationalSynthesisOutput
  correct : ∀ I, IsValidRationalProcessDescription I -> IsCorrectRationalSynthesis I (solve I)
  polytime : Nonempty (Turing.TM2ComputableInPolyTime
    encodeRationalProcessDescription encodeRationalSynthesisOutput solve)

/-- A rational table/output pair represents the current finite process and the selected real
objects, up to an enumeration of the finite state type. -/
def RepresentsCurrentSynthesis {A X : Type*} [Fintype A] [Fintype X]
    (M : FiniteProcess A X) (pi : A -> Real) (s : Real) (V : X -> Real)
    (mu : X -> Nat) (S : Set X) (I : RationalProcessDescription)
    (O : RationalSynthesisOutput) : Prop :=
  ∃ e : X ≃ Fin I.rows.length,
    (∀ y, (O.values.getD (e y).val 0 : Real) = V y ∧
      O.selector.getD (e y).val 0 = mu y ∧
      (O.restartSet.getD (e y).val false = true ↔ y ∈ S)) ∧
    ∀ y f, f ∈ M.actions y ↔
      ∃ a ∈ I.rows.getD (e y).val [], a.label = f ∧
        ∀ z, (a.weights.getD (e z).val 0 : Real) = poweredTransition M pi s y f z

/-- Exact polynomial-time synthesis in the explicit rational state-action representation. -/
def PolynomialTimeSynthesizable {A X : Type*} [Fintype A] [Fintype X]
    (M : FiniteProcess A X) (pi : A -> Real) (s : Real) (V : X -> Real)
    (mu : X -> Nat) (S : Set X) : Prop :=
  ∃ P : RationalSynthesisProcedure, ∃ I : RationalProcessDescription,
    IsValidRationalProcessDescription I ∧
      RepresentsCurrentSynthesis M pi s V mu S I (P.solve I)

/-- Main catalog declaration for the restart and finite-state synthesis model. -/
abbrev RestartSynthesis (A : Type*) := OneSymbolAlgorithm A

end CorrelatedLocalSearch.Supplement


