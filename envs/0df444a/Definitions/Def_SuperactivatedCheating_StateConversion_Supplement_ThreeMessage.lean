-- Prove2me | Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_ThreeMessage
-- name    : SuperactivatedCheating_StateConversion_Supplement_ThreeMessage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:21:00.985206+00:00
-- url     : https://prove2.me/theorems/3084a526-b8fe-49b3-939e-13557524ded2
-- title:
--   Three-message verifier protocols with retained private memory
-- statement:
--   A three-message protocol has arbitrary finite nonempty message and referee registers. The provers first send $A_1,B_1$ while retaining arbitrary private memories. The verifier applies a joint CPTP channel $N:A_1B_1\to A_2B_2R$, returns $A_2,B_2$, and retains $R$. The provers apply local CPTP maps on the received registers and their retained memories, return $A_3,B_3$, and the verifier measures an orthogonal accepting projection on $A_3B_3R$.
--
--   An assisted strategy chooses a unit pure state jointly on first messages and private memories, and the two final channels. The entangled value is the supremum over every finite private dimension and every such strategy. Product initial resources define the local value. Products of protocols tensor the two verifier channels and projections with canonical regrouping, while allowing arbitrary prior entanglement and joint local responses across instances. No restriction to state-preparation channels, product verifier channels across provers, or equal protocols is made. Physical validity is separate from the circuit data and carries no value inequality.
-- source:
--   Bhattacharyya, Mančinska, Zhao, Quantum interaction can superactivate cheating under parallel repetition, STOC 2027 submission #399 (October 2026), §2.1 p. 12; Definition 38 and Theorem 39 p. 27.

import Definitions.Def_SuperactivatedCheating_StateConversion_Supplement_Protocols

noncomputable section

namespace SuperactivatedCheating.StateConversion.Supplement
open scoped Matrix ComplexConjugate

/-- Definition 38 p.27. The verifier's joint channel is unrestricted and retains R. -/
structure ThreeMessage where
  A₁ : Type
  B₁ : Type
  A₂ : Type
  B₂ : Type
  R : Type
  A₃ : Type
  B₃ : Type
  [fa1 : Fintype A₁] [fb1 : Fintype B₁] [fa2 : Fintype A₂] [fb2 : Fintype B₂]
  [fr : Fintype R] [fa3 : Fintype A₃] [fb3 : Fintype B₃]
  [da1 : DecidableEq A₁] [db1 : DecidableEq B₁] [da2 : DecidableEq A₂] [db2 : DecidableEq B₂]
  [dr : DecidableEq R] [da3 : DecidableEq A₃] [db3 : DecidableEq B₃]
  middle : Map (A₁ × B₁) (A₂ × B₂ × R)
  acc : Op (A₃ × B₃ × R)
attribute [instance] ThreeMessage.fa1 ThreeMessage.fb1 ThreeMessage.fa2 ThreeMessage.fb2
  ThreeMessage.fr ThreeMessage.fa3 ThreeMessage.fb3 ThreeMessage.da1 ThreeMessage.db1
  ThreeMessage.da2 ThreeMessage.db2 ThreeMessage.dr ThreeMessage.da3 ThreeMessage.db3

def ThreeMessage.Valid (K : ThreeMessage) : Prop :=
  QAlgorithms.IsChannel K.middle ∧ IsProjection K.acc ∧ Nonempty K.A₁ ∧ Nonempty K.B₁ ∧
    Nonempty K.A₂ ∧ Nonempty K.B₂ ∧ Nonempty K.R ∧ Nonempty K.A₃ ∧ Nonempty K.B₃

/-- Initial messages together with arbitrary retained memories can be jointly entangled. -/
structure ThreeMessage.Strategy (K : ThreeMessage) where
  eA : ℕ
  eB : ℕ
  ψ : (K.A₁ × Fin eA) × (K.B₁ × Fin eB) → ℂ
  unit : unitVector ψ
  E : Map (K.A₂ × Fin eA) K.A₃
  F : Map (K.B₂ × Fin eB) K.B₃
  hE : QAlgorithms.IsChannel E
  hF : QAlgorithms.IsChannel F

def ThreeMessage.Strategy.product {K : ThreeMessage} (S : K.Strategy) : Prop :=
  ∃ u : K.A₁ × Fin S.eA → ℂ, ∃ v : K.B₁ × Fin S.eB → ℂ,
    unitVector u ∧ unitVector v ∧ ∀ x y, S.ψ (x,y) = u x * v y

def ThreeMessage.win (K : ThreeMessage) (S : K.Strategy) : ℝ :=
  let X := relabel (fun x : (K.A₁ × K.B₁) × (Fin S.eA × Fin S.eB) =>
    ((x.1.1,x.2.1),(x.1.2,x.2.2))) (pureState S.ψ)
  let Y := tensorId K.middle X
  let Z := relabel (fun x : (K.A₂ × Fin S.eA) × (K.B₂ × Fin S.eB) × K.R =>
    ((x.1.1,x.2.1.1,x.2.2),(x.1.2,x.2.1.2))) Y
  (K.acc * localStep S.E S.F Z).trace.re

def ThreeMessage.entangledValue (K : ThreeMessage) : ℝ := sSup (Set.range K.win)
def ThreeMessage.localValue (K : ThreeMessage) : ℝ :=
  sSup {p | ∃ S : K.Strategy, S.product ∧ K.win S = p}

/-- Independent verifier channels and accepting projections; strategies remain unrestricted. -/
def ThreeMessage.prod (K L : ThreeMessage) : ThreeMessage where
  A₁ := K.A₁ × L.A₁; B₁ := K.B₁ × L.B₁
  A₂ := K.A₂ × L.A₂; B₂ := K.B₂ × L.B₂; R := K.R × L.R
  A₃ := K.A₃ × L.A₃; B₃ := K.B₃ × L.B₃
  middle X := relabel (fun x => ((x.1.1,x.2.1.1,x.2.2.1),(x.1.2,x.2.1.2,x.2.2.2)))
    (tensorMap K.middle L.middle (relabel (fun x => ((x.1.1,x.2.1),(x.1.2,x.2.2))) X))
  acc := relabel (fun x => ((x.1.1,x.2.1.1,x.2.2.1),(x.1.2,x.2.1.2,x.2.2.2))) (tensor K.acc L.acc)

end SuperactivatedCheating.StateConversion.Supplement


