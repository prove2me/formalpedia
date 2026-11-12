-- Prove2me | Definitions.Def_LocalSweepFT_IdealCircuit
-- name    : LocalSweepFT_IdealCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:40:21.41273+00:00
-- url     : https://prove2.me/theorems/aa39f0b4-8d9b-4608-9fcf-39d9b9fde5d6
-- title:
--   Quantum circuits over $\{X,Z,CX,H,S,T\}$ and measurements, and their output $C(|0^w\rangle\langle0^w|)$
-- statement:
--   A quantum circuit $C$ of depth $\mu$ and width $w$ is, for each time $t\in[\mu]$, a list of gates placed on ordered tuples of distinct qubits, the gates of one time step having pairwise disjoint supports. The gates are
--   $$X,\ Z,\ CX,\ H,\ S=\mathrm{diag}(1,i),\ T=\mathrm{diag}(1,e^{i\pi/4}),$$
--   and measurement in the computational or the phase basis. The output of $C$ is the result of applying its layers in time order to $|0^w\rangle\langle0^w|$. $C$ is the identity circuit if it has no gates.
--
--   This is the circuit that the Toric encoded circuit simulates.
--
--   **Formalization Note** $C$ has only qubit wires, so a measurement is the dephasing channel in its basis (Kraus operators the two basis projectors) and its outcome stays in the qubit.
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Definitions 3.1–3.3, pp.12–13

import Mathlib
import Definitions.Def_LocalSweepFT_liftOn

open Matrix

namespace LocalSweepFT

/-! Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…), Definitions 3.1–3.3 (pp.12–13): quantum circuits of depth `μ`
and width `w` over the gate set `{X, Z, CX, H, S, T}` and measurements, and their action on
`|0^w⟩⟨0^w|`. -/

/-- The gate set of the paper (p.13: "we will restrict G to contain X, Z, CX, H, S, T, and
measurements"): measurement in the computational (`measZ`) and in the phase (`measX`) basis. -/
inductive IGate
  | X | Z | H | S | T | CX | measZ | measX
  deriving DecidableEq

/-- Number of qubits a gate acts on. -/
def IGate.arity : IGate → ℕ
  | .CX => 2
  | _ => 1

/-- A one-qubit operator from its `2 × 2` matrix of entries. -/
def oneQ (f : ZMod 2 → ZMod 2 → ℂ) : Op (Fin 1) := fun a b => f (a 0) (b 0)

/-- `CX : |a, b⟩ ↦ |a, a + b⟩`, the first qubit being the control. -/
def cxMat : Op (Fin 2) := fun a b => if a 0 = b 0 ∧ a 1 = b 1 + b 0 then 1 else 0

/-- The Kraus family of a gate on its own qubits (`H, S, T` as on p.12). A measurement in `C` has no
classical output: it is the dephasing channel in its basis, with Kraus operators the two basis
projectors. -/
noncomputable def IGate.kraus : (g : IGate) → List (Op (Fin g.arity))
  | .X => [xOn (fun _ => 1)]
  | .Z => [zOn (fun _ => 1)]
  | .H => [hadOn]
  | .S => [oneQ fun a b => if a = b then (if b = 1 then Complex.I else 1) else 0]
  | .T => [oneQ fun a b => if a = b then
      (if b = 1 then Complex.exp (Complex.I * ((Real.pi / 4 : ℝ) : ℂ)) else 1) else 0]
  | .CX => [cxMat]
  | .measZ => [oneQ fun a b => if a = b ∧ b = 0 then 1 else 0,
               oneQ fun a b => if a = b ∧ b = 1 then 1 else 0]
  | .measX => [hadOn * oneQ (fun a b => if a = b ∧ b = 0 then 1 else 0) * hadOn,
               hadOn * oneQ (fun a b => if a = b ∧ b = 1 then 1 else 0) * hadOn]

/-- A gate placed on an ordered tuple of distinct qubits of a width-`w` circuit (Def 3.1, p.12): the
`k`-th input of the gate is the qubit `loc k`. -/
structure IGateLoc (w : ℕ) where
  g : IGate
  loc : Fin g.arity ↪ Fin w

/-- A quantum circuit `C` of depth `μ` and width `w` (Def 3.1, p.12): for each time `t ∈ [μ]` the
gates applied at time `t`, whose supports are pairwise disjoint (the compatibility condition). -/
structure IdealCircuit (w μ : ℕ) where
  layer : Fin μ → List (IGateLoc w)
  disjoint : ∀ t, (layer t).Pairwise (fun u v => Disjoint (Set.range u.loc) (Set.range v.loc))

/-- The Kraus family of a placed gate on all `w` qubits. -/
noncomputable def IGateLoc.krausOn {w : ℕ} (u : IGateLoc w) : List (Op (Fin w)) :=
  u.g.kraus.map (liftOn u.loc)

/-- The Kraus family of one layer: its gates applied one after the other (they commute, since their
supports are disjoint). -/
noncomputable def layerKrausI {w : ℕ} (L : List (IGateLoc w)) : List (Op (Fin w)) :=
  L.foldl (fun acc u => compK acc u.krausOn) [1]

/-- The output `C ∘ |0^w⟩⟨0^w|` of the circuit (Def 3.3, p.13): its layers applied in time order to
the all-zero state. -/
noncomputable def idealOut {w μ : ℕ} (C : IdealCircuit w μ) : Op (Fin w) :=
  (List.finRange μ).foldl (fun ρ t => applyK (layerKrausI (C.layer t)) ρ) (zeroState (Fin w))

/-- `C` is the identity circuit: it has no gates. -/
def IdealCircuit.IsIdentity {w μ : ℕ} (C : IdealCircuit w μ) : Prop := ∀ t, C.layer t = []

end LocalSweepFT


