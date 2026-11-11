-- Prove2me | Definitions.Def_EFI1PRS_Uniform_CliffordSampler
-- name    : EFI1PRS_Uniform_CliffordSampler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:43:06.762967+00:00
-- url     : https://prove2.me/theorems/2807aceb-ea42-4f1c-a53b-06b596ff3c4e
-- title:
--   Concrete symplectic indexing and exact Clifford circuits
-- statement:
--   The phase-quotiented Clifford carrier is the published normalizer quotient by equality of physical conjugation maps. Its finiteness is not assumed by these definitions. A concrete symplectic transvection indexing algorithm follows Figure 2 of Koenig–Smolin. Each transvection is lifted to an exact $H,S,\mathrm{CNOT}$ circuit by reducing its Hermitian Pauli to a single $Z$, applying $S$, and undoing that reduction. Independent Pauli labels complete the index.
--
--   The group-size formula and seed length are
--
--   $$K_t=2^{t^2+2t}\prod_{j=1}^t(4^j-1),\qquad a=\lceil\log_2K_t\rceil+\lambda^2.$$
--
--   The raw seed is interpreted as an integer and reduced modulo $K_t$ before indexing. The definitions assert neither efficiency, exact correspondence with the entire phase quotient nor any statistical estimate; these are explicit obligations of Lemma 2.17. No dense unitary is treated as a unit-cost gate. The tensor unit at $t=0$ has $K_0=1$.
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, Lemma 2.17, p.10; Koenig–Smolin, arXiv:1406.2170v1, Fig.2

import Definitions.Def_EFI1PRS_Uniform_Windows
import Definitions.Def_QAlgorithms_Defs_ProjectiveCliffords

/-! Candidate concrete Clifford-indexing implementation. Batra, Lemma 2.17,
p.10; Koenig–Smolin, arXiv:1406.2170v1, Figure 2. Its algorithmic and
phase-quotient correspondence still need a source audit before use in statements. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate
attribute [local instance] Classical.propDecidable Classical.decEq

def singleInstruction {n : ℕ} (s : Fin 5) (i : Fin n) : Instruction n := by
  let symbol : Fin 6 := ⟨s.val, by omega⟩
  have arity : (elementary symbol).arity = 1 := by
    fin_cases s <;> rfl
  refine ⟨symbol, ⟨fun _ => i, ?_⟩⟩
  letI : Subsingleton (Fin (elementary symbol).arity) := by rw [arity]; infer_instance
  intro a b _
  exact Subsingleton.elim a b

def cnotInstruction {n : ℕ} (i j : Fin n) (h : i ≠ j) : Instruction n := by
  refine ⟨5, ⟨fun k => if k.val = 0 then i else j, ?_⟩⟩
  intro a b hab
  have ha : a.val < 2 := a.isLt
  have hb : b.val < 2 := b.isLt
  apply Fin.ext
  by_cases h0 : a.val = 0 <;> by_cases h1 : b.val = 0
  · omega
  · simp only [h0, h1, if_true, if_false] at hab; exact False.elim (h hab)
  · simp only [h0, h1, if_true, if_false] at hab; exact False.elim (h hab.symm)
  · omega

def singleAt (n : ℕ) (s : Fin 5) (i : ℕ) : List (Instruction n) :=
  if h : i < n then [singleInstruction s ⟨i,h⟩] else []

def cnotAt (n i j : ℕ) : List (Instruction n) :=
  if h : i < n ∧ j < n ∧ i ≠ j then
    [cnotInstruction ⟨i,h.1⟩ ⟨j,h.2.1⟩ (fun he => h.2.2 (Fin.mk.inj he))]
  else []

def zeroBits (n : ℕ) : Qubits n := fun _ => false
def xorBits {n : ℕ} (x y : Qubits n) : Qubits n := fun j => xor (x j) (y j)

def symplectic {n : ℕ} (x y : Qubits (2*n)) : Bool :=
  decide ((∑ j : Fin n,
    ((if bitAt x (2*j.val) && bitAt y (2*j.val+1) then 1 else 0) +
    (if bitAt x (2*j.val+1) && bitAt y (2*j.val) then 1 else 0))) % 2 = 1)

def transvection {n : ℕ} (h v : Qubits (2*n)) : Qubits (2*n) :=
  if symplectic v h then xorBits v h else v

def applyTransvections {n : ℕ} (hs : List (Qubits (2*n))) (v : Qubits (2*n)) :=
  hs.foldl (fun w h => transvection h w) v

/-- Polynomial-size search for a vector supported on at most two qubits. -/
def shortVectors (n : ℕ) : List (Qubits (2*n)) :=
  (List.range n).flatMap fun j => (List.range n).flatMap fun k =>
    (List.range 16).map fun a => fun i =>
      xor (if i.val/2 = j then Nat.testBit a (i.val%2) else false)
        (if i.val/2 = k then Nat.testBit a (2+i.val%2) else false)

def connectingTransvections {n : ℕ} (x y : Qubits (2*n)) : List (Qubits (2*n)) :=
  if x = y then [] else if symplectic x y then [xorBits x y] else
    let z := ((shortVectors n).find? fun z => symplectic x z && symplectic y z).getD (zeroBits (2*n))
    [xorBits x z, xorBits z y]

/-- Figure 2, in execution order. Recursive transformations act on the final
n−1 qubits before the two coset transformations. -/
def symplecticIndex : (n : ℕ) → ℕ → List (Qubits (2*n))
  | 0, _ => []
  | n+1, index =>
    let size := 2^(2*(n+1))-1
    let f := fun j : Fin (2*(n+1)) => Nat.testBit (index%size+1) j.val
    let e := fun j : Fin (2*(n+1)) => decide (j.val = 0)
    let hs := connectingTransvections e f
    let quotient := index/size
    let ep := fun j : Fin (2*(n+1)) =>
      if j.val = 0 then true else if j.val = 1 then false else Nat.testBit quotient (j.val-1)
    let h0 := applyTransvections hs ep
    let smaller := (symplecticIndex n (quotient / 2^(2*(n+1)-1))).map fun h =>
      fun j : Fin (2*(n+1)) => if j.val < 2 then false else bitAt h (j.val-2)
    smaller ++ hs ++ (if Nat.testBit quotient 0 then [h0] else [h0,f])

/-- Gate list mapping a nonidentity Hermitian Pauli to Z on its first support wire.
Both-active bits mean Y; S† followed by H maps Y to Z. -/
def pauliToZ {n : ℕ} (h : Qubits (2*n)) : List (Instruction n) :=
  let support := (List.range n).filter fun j => bitAt h (2*j) || bitAt h (2*j+1)
  let localGates := (List.range n).flatMap fun j =>
    if bitAt h (2*j) then
      (if bitAt h (2*j+1) then List.replicate 3 (singleAt n 1 j) |>.flatten else []) ++
        singleAt n 0 j
    else []
  localGates ++ support.tail.flatMap (fun j => cnotAt n j (support.headD 0))

def inverseInstruction {n : ℕ} (g : Instruction n) : List (Instruction n) :=
  if g.symbol.val = 1 then List.replicate 3 g
  else if g.symbol.val = 2 then List.replicate 7 g else [g]

def transvectionCircuit {n : ℕ} (h : Qubits (2*n)) : List (Instruction n) :=
  let support := (List.range n).filter fun j => bitAt h (2*j) || bitAt h (2*j+1)
  if support.isEmpty then [] else
    let B := pauliToZ h
    B ++ singleAt n 1 (support.headD 0) ++ B.reverse.flatMap inverseInstruction

def pauliCircuit (n : ℕ) (index : ℕ) : List (Instruction n) :=
  (List.range n).flatMap fun j =>
    (if Nat.testBit index (2*j+1) then singleAt n 4 j else []) ++
    (if Nat.testBit index (2*j) then singleAt n 3 j else [])

def cliffordIndex (n index : ℕ) : List (Instruction n) :=
  (symplecticIndex n (index/4^n)).flatMap transvectionCircuit ++ pauliCircuit n (index%4^n)

def cliffordCount (n : ℕ) : ℕ := 2^(n^2+2*n) * ∏ j ∈ Finset.range n, (4^(j+1)-1)
def ceilLog2 (x : ℕ) : ℕ := if x ≤ 1 then 0 else Nat.log2 (x-1)+1
def seedLength (n sec : ℕ) : ℕ := ceilLog2 (cliffordCount n) + sec^2

def bitsInteger {a : ℕ} (s : Qubits a) : ℕ :=
  (List.ofFn s).foldl (fun v b => 2*v + if b then 1 else 0) 0

def sampledCircuit (n sec : ℕ) (s : Qubits (seedLength n sec)) : Circuit gateVocabulary n :=
  (cliffordIndex n (bitsInteger s % cliffordCount n)).map Instruction.application

end EFI1PRS.Uniform


