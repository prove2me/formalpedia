-- Prove2me | Definitions.Def_SignFreeOracle_Separation_Circuit
-- name    : SignFreeOracle_Separation_Circuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:10.121611+00:00
-- url     : https://prove2.me/theorems/35ce513c-5dfb-47e4-88ea-15e7c07a5b46
-- title:
--   Restricted stoquastic circuits and Born acceptance
-- statement:
--   A circuit has input wires, arbitrary complex witness amplitudes, zero ancillas and plus ancillas. Its only gates are $X$, CNOT, Toffoli, and Boolean XOR queries $|y,c\rangle\mapsto|y,c\oplus O(y)\rangle$. Distinct control, address and target wires are enforced in the gate constructors. Each gate acts by its actual basis permutation. Acceptance is one final projection on the designated output wire:
--   $$p_{\rm acc}=\|(|+\rangle\langle+|_{\rm out}\otimes I)U(|x\rangle\otimes|\psi\rangle\otimes|0\rangle^{\otimes m_0}\otimes|+\rangle^{\otimes m_+})\|_2^2.$$
--   The equivalent amplitude formula sums over both values of the measured bit and divides by four. A single finite deterministic transducer prints prefix-free circuit descriptions from unary input lengths in polynomial time. Choosing a designated output wire instead of the first wire is equivalent by reversible swaps. The construction defines both actual quantum semantics and classical uniformity; it assumes no acceptance or spectral identity.
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Definition 2.2, p. 7 (PDF p. 7)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QAdvFew_PoQOracle_OTM

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- Exactly the reversible gates of Definition 2.2 and the standard Boolean XOR oracle.
Wire distinctness is built into the constructors. -/
inductive StoqGate (N : ℕ) where
  | x (t : Fin N)
  | cnot (c t : Fin N) (distinct : c ≠ t)
  | toffoli (a b t : Fin N) (ab : a ≠ b) (hat : a ≠ t) (bt : b ≠ t)
  | query (address : List (Fin N)) (target : Fin N)
      (distinct : address.Nodup) (separate : target ∉ address)

/-- Every gate is a basis involution. Pulling amplitudes back along it is its unitary action. -/
def StoqGate.flip {N : ℕ} (O : Oracle) : StoqGate N → Bits N → Bits N
  | .x t, z => Function.update z t (!z t)
  | .cnot c t _, z => Function.update z t (xor (z t) (z c))
  | .toffoli a b t _ _ _, z => Function.update z t (xor (z t) (z a && z b))
  | .query address target _ _, z =>
      Function.update z target (xor (z target) (O (address.map z)))

def StoqGate.apply {N : ℕ} (O : Oracle) (g : StoqGate N) (ψ : QState N) : QState N :=
  fun z => ψ (g.flip O z)

/-- Input, arbitrary complex witness, zero ancillas, and plus ancillas, in that order.
The designated measured wire can be moved to the first position by reversible SWAPs. -/
structure StoqCircuit (m : ℕ) where
  witness : ℕ
  zeros : ℕ
  plus : ℕ
  output : Fin (m + witness + zeros + plus)
  gates : List (StoqGate (m + witness + zeros + plus))

def bitAt {N : ℕ} (z : Bits N) (i : ℕ) : Bool := if h : i < N then z ⟨i, h⟩ else false

noncomputable def StoqCircuit.initial {m : ℕ} (C : StoqCircuit m) (x : Bits m)
    (ψ : QState C.witness) : QState (m + C.witness + C.zeros + C.plus) := by
  classical
  exact fun z => if (∀ i : Fin m, bitAt z i = x i) ∧
      (∀ j : Fin C.zeros, bitAt z (m + C.witness + j) = false) then
    ψ (fun i => bitAt z (m + i)) / (Real.sqrt ((2 : ℝ) ^ C.plus) : ℂ) else 0

/-- Born acceptance: squared norm of the final |+><+| projection on one output wire.
Summing over both values of that wire contributes the factor 1/4. -/
noncomputable def StoqCircuit.accept {m : ℕ} (C : StoqCircuit m) (O : Oracle)
    (x : Bits m) (ψ : QState C.witness) : ℝ :=
  let v := C.gates.foldl (fun st g => g.apply O st) (C.initial x ψ)
  (∑ z, ‖v z + v (Function.update z C.output (!z C.output))‖ ^ 2) / 4

/-- Prefix-free unary natural-number code; wire indices and gate arities determine parsing. -/
def codeNat (n : ℕ) : Str := List.replicate n true ++ [false]

def StoqGate.code {N : ℕ} : StoqGate N → Str
  | .x t => codeNat 0 ++ codeNat t
  | .cnot c t _ => codeNat 1 ++ codeNat c ++ codeNat t
  | .toffoli a b t _ _ _ => codeNat 2 ++ codeNat a ++ codeNat b ++ codeNat t
  | .query address target _ _ => codeNat 3 ++ codeNat address.length ++
      (address.map fun i => codeNat i).flatten ++ codeNat target

def StoqCircuit.code {m : ℕ} (C : StoqCircuit m) : Str :=
  codeNat m ++ codeNat C.witness ++ codeNat C.zeros ++ codeNat C.plus ++
    codeNat C.output ++ codeNat C.gates.length ++ (C.gates.map StoqGate.code).flatten

/-- One finite classical transducer, without an oracle, prints all circuit descriptions.
There is one clock polynomial for the whole family, preceding every input length. -/
def UniformStoq (C : ∀ m, StoqCircuit m) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ), ∀ m,
    M.result (fun _ => false) (List.replicate m true) (p.eval m) ≠ none ∧
    M.output (fun _ => false) (List.replicate m true) (p.eval m) = (C m).code

/-- A universal spectral-verifier constructor: m and d are explicit unary parameters.
Polynomial time in m+d specializes to polynomial time in m for every polynomially bounded d. -/
def UniformStoqParameters (C : ∀ m, ℕ → StoqCircuit m) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ), ∀ m d,
    M.result (fun _ => false) (tup [List.replicate m true, List.replicate d true])
      (p.eval (m + d)) ≠ none ∧
    M.output (fun _ => false) (tup [List.replicate m true, List.replicate d true])
      (p.eval (m + d)) = (C m d).code

end SignFreeOracle.Separation


