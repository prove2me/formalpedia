-- Prove2me | Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
-- name    : QuantumBipartiteTesting_Bipartiteness_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:11:40.798376+00:00
-- url     : https://prove2.me/theorems/2d22590a-df1f-479e-91f8-0e3f83eb3fb5
-- title:
--   The explicit seven-vertex-per-input reduction and coherent oracle simulation
-- statement:
--   For each original vertex $u$ and color $j$, allocate two distinct auxiliary vertices $a_{u,j},p_{u,j}$. Orient each constraint from its smaller endpoint. A sign-zero constraint becomes $u-a_{u,j}-v$; a sign-one constraint becomes $u-a_{u,j}-p_{u,j}-v$. Unused auxiliary vertices remain isolated. Padding adds isolated vertices. The ordinary adjacency oracle sorts the actual neighbor set and returns its requested entry.
--
--   A simulation is an input-independent finite sequence of free unitaries and signed XOR-oracle gates. Its query cost counts exactly the latter gates. The simulation condition demands equality of linear maps on every logical input state, under a fixed injective clean basis embedding, uniformly over all signed inputs. The embedding and gates are chosen before the unknown graph. No balance, distance, or simulation property is assumed by the construction.
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), §3.6, Lemma 3.16 and Theorem 3.1 proof, PDF = printed page 20–21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Polynomials

namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

def Original {n : ℕ} (u : Fin n) : Fin (7*n) := ⟨u.val, by omega⟩
def AuxiliaryA {n : ℕ} (u : Fin n) (j : Fin 3) : Fin (7*n) :=
  ⟨n + 6*u.val + 2*j.val, by omega⟩
def AuxiliaryP {n : ℕ} (u : Fin n) (j : Fin 3) : Fin (7*n) :=
  ⟨n + 6*u.val + 2*j.val + 1, by omega⟩

def UEdge {n : ℕ} (u v : Fin n) : Edge n := (min u v, max u v)

def Gadget {n : ℕ} (F : Finset (ColoredEdge n)) (b : ColoredEdge n → Bool) : Finset (Edge (7*n)) :=
  F.biUnion fun e =>
    let u := Original e.1
    let v := Original e.2.1
    let a := AuxiliaryA e.1 e.2.2
    let p := AuxiliaryP e.1 e.2.2
    if b e then {UEdge u a, UEdge a p, UEdge p v} else {UEdge u a, UEdge a v}

def Pad {n : ℕ} (G : Finset (Edge n)) (r : ℕ) : Finset (Edge (n+r)) :=
  G.image fun e => (Fin.castAdd r e.1, Fin.castAdd r e.2)

/-- Sorted packing of the actual neighbor set; no graph information is supplied separately. -/
def PackedOracle {n : ℕ} (G : Finset (Edge n)) (a : Fin n × Fin 3) : Option (Fin n) :=
  ((Neighbors G a.1).sort (· ≤ ·))[a.2.val]?

abbrev SimulationBasis (n k w : ℕ) := (Address n 3 × Bits k) × Fin w
abbrev SimulationGate (n k w : ℕ) := Sum (Matrix.unitaryGroup (SimulationBasis n k w) ℂ) Unit

def QueryGateCount {n k w : ℕ} (gates : List (SimulationGate n k w)) : ℕ :=
  gates.countP (fun g => g.isRight)

def CircuitMatrix {n k w : ℕ} (O : Matrix (Address n 3 × Bits k) (Address n 3 × Bits k) ℂ) :
    List (SimulationGate n k w) → Matrix (SimulationBasis n k w) (SimulationBasis n k w) ℂ
  | [] => 1
  | Sum.inl U :: gs => CircuitMatrix O gs * (U : Matrix _ _ ℂ)
  | Sum.inr _ :: gs => CircuitMatrix O gs * Matrix.kronecker O (1 : Matrix (Fin w) (Fin w) ℂ)

/-- Clean basis embedding; injectivity is required by the simulation conclusion. -/
def EmbedState {S T : Type*} [Fintype S] (e : S → T) (ψ : S → ℂ) : T → ℂ :=
  fun t => ∑ s, if e s = t then ψ s else 0

/-- Uniform exact oracle-unitary simulation, including all answer-register states and clean return. -/
def CoherentSimulation (K : ℕ) : Prop :=
  ∀ n kS kT : ℕ, ∀ ES : Encoding (Fin n × Bool) kS, ∀ ET : Encoding (Fin (7*n)) kT,
  ∃ w : ℕ, ∃ gates : List (SimulationGate n kS w),
  ∃ embed : (Address (7*n) 3 × Bits kT) → SimulationBasis n kS w,
    Function.Injective embed ∧ QueryGateCount gates ≤ K ∧
    ∀ F : Finset (ColoredEdge n), Consistent F → ∀ b : ColoredEdge n → Bool,
    ∀ ψ : (Address (7*n) 3 × Bits kT) → ℂ,
      (CircuitMatrix (QAlgorithms.xorOracle (ES.code ∘ LiftOracle (SignedResponse F b))) gates).mulVec
        (EmbedState embed ψ) =
      EmbedState embed
        ((QAlgorithms.xorOracle (ET.code ∘ LiftOracle (PackedOracle (Gadget F b)))).mulVec ψ)

end
end QuantumBipartiteTesting.Bipartiteness


