-- Prove2me | Definitions.Def_HypercliqueRefutation_FourClique_Supplement_ScalarMachine
-- name    : HypercliqueRefutation_FourClique_Supplement_ScalarMachine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T09:25:13.282871+00:00
-- url     : https://prove2.me/theorems/e76d628f-82dd-4a2a-8446-ffc24ebbe61a
-- title:
--   Exact scalar programs with bounded bookkeeping words
-- statement:
--   A program is a finite list of rational-code instructions, interpreted over the scalar field. The published field-register core supplies exact scalar arithmetic, individual memory reads and writes, natural arithmetic, branches, individual output symbols and halt. The extension supplies indexed natural input, indirect natural load and store, and a natural-to-field cast. There is no matrix-product instruction, arbitrary-function instruction, or answer oracle.
--
--   Every run begins with zero registers and work memory and only its displayed natural and scalar input lists. The predicate for a run requires successful explicit halt and exactly the specified output lists. All natural registers along the run are bounded by $B$. For execution fuel $t$ the charged upper cost is
--
--   $$
--   (\operatorname{codeSize}+\operatorname{codeLength}+t)(1+\lfloor\log_2(B+2)\rfloor)^2.
--   $$
--
--   The quadratic factor pays a schoolbook bignum upper cost for bounded natural-word arithmetic; it also overcharges scalar operations by this factor. Scalar values remain exact field elements rather than finite-precision approximations. The budget is a bound on an actual execution, never an arbitrary annotation on a function. Polynomial powers of $\log(S)$ bound word lengths and absorb this overhead. This interface supports the costed reduction of Theorem 2.6, separately from the published word-RAM model for hypergraph inputs.
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, The 3-Uniform Hyperclique Hypothesis is False, STOC 2027 submission #1431 (October 2026); Theorem 2.6 and operand-entry construction, printed/PDF p.5; coefficient construction and bit lengths, Lemma 2.4, p.4 and pp.6–7. The instruction set is an operational encoding of exact scalar arithmetic; the imported core retains its original source.

import Definitions.Def_SubspaceEvasion312_Explicit_machine

set_option autoImplicit false

namespace HypercliqueRefutation.FourClique.Supplement
namespace ScalarMachine

/- Operational reading of exact scalar arithmetic in Theorem 2.6, p.5.
   Reuse the published field-register core, adding indexed natural memory and a
   natural-to-field cast. Code has rational constants and is independent of K.
   There are no functions, multiplication oracles, or result certificates in code. -/

inductive Instruction where
  | core (i : SubspaceEvasion312.Explicit.Instruction ℚ)
  | inputNatAt (dst address : ℕ)
  | loadNat (dst address : ℕ)
  | storeNat (address src : ℕ)
  | castNat (dst src : ℕ)

abbrev Program := List Instruction
abbrev State (K : Type) := SubspaceEvasion312.Explicit.MachineState K

def castCore {K : Type} [Field K] :
    SubspaceEvasion312.Explicit.Instruction ℚ → SubspaceEvasion312.Explicit.Instruction K
  | .halt => .halt
  | .literal d v => .literal d v
  | .inputNat d i => .inputNat d i
  | .addNat d a b => .addNat d a b
  | .subNat d a b => .subNat d a b
  | .mulNat d a b => .mulNat d a b
  | .divNat d a b => .divNat d a b
  | .modNat d a b => .modNat d a b
  | .branchNat a b y n => .branchNat a b y n
  | .constant d v => .constant d (v : K)
  | .add d a b => .add d a b
  | .sub d a b => .sub d a b
  | .mul d a b => .mul d a b
  | .inv d a => .inv d a
  | .load d a => .load d a
  | .store a b => .store a b
  | .input d a => .input d a
  | .branch a b y n => .branch a b y n
  | .jump p => .jump p
  | .output a => .output a
  | .outputNat a => .outputNat a

def coreCode {K : Type} [Field K] (P : Program) : SubspaceEvasion312.Explicit.Program K :=
  P.map fun op => match op with
    | .core i => castCore i
    | _ => .halt

noncomputable def step {K : Type} [Field K] (P : Program)
    (ns : List ℕ) (xs : List K) (s : State K) : Option (State K) :=
  let next := {s with pc := s.pc + 1}
  match P[s.pc]? with
  | none => none
  | some (.core _) => SubspaceEvasion312.Explicit.step (coreCode P) ns xs s
  | some (.inputNatAt d a) =>
      some {next with natReg := Function.update s.natReg d (ns.getD (s.natReg a) 0)}
  | some (.loadNat d a) =>
      some {next with natReg := Function.update s.natReg d (s.natReg (s.natReg a))}
  | some (.storeNat a b) =>
      some {next with natReg := Function.update s.natReg (s.natReg a) (s.natReg b)}
  | some (.castNat d a) =>
      some {next with fieldReg := Function.update s.fieldReg d (s.natReg a : K)}

/-- The bound B limits every bookkeeping word, including indirectly addressed cells.
    The scalar cells have arbitrary field values. Only explicit halt succeeds. -/
noncomputable def runFrom {K : Type} [Field K] (P : Program)
    (ns : List ℕ) (xs : List K) (B : ℕ) : ℕ → State K → Option (State K)
  | 0, _ => none
  | t + 1, s => by
      classical
      exact if (∀ i, s.natReg i ≤ B) then
        match P[s.pc]? with
        | some (.core .halt) => some s
        | _ => (step P ns xs s).bind (runFrom P ns xs B t)
      else none

/-- A quadratic bignum upper charge for each executed instruction on bounded
    natural words; scalar arithmetic remains exact unit-cost arithmetic. Charging
    the same factor to scalar instructions is a harmless polylog overhead.
    t is execution fuel, never a freely supplied running-time label. -/
noncomputable def Runs {K : Type} [Field K] (P : Program) (ns : List ℕ)
    (xs : List K) (T B : ℕ) (ys : List K) (outN : List ℕ := []) : Prop :=
  ∃ t s, (SubspaceEvasion312.Explicit.programSize (coreCode (K := ℚ) P) + P.length + t) *
      (1 + Nat.log2 (B + 2)) ^ 2 ≤ T ∧
    runFrom P ns xs B t SubspaceEvasion312.Explicit.initialState = some s ∧
    s.out.reverse = ys ∧ s.natOut.reverse = outN

/-- Polylog word lengths, including the source's polynomial-in-m-bit rational
    coefficients. S includes every dimension, m and k; S is always at least two. -/
def wordBound (S d : ℕ) : ℕ := 2 ^ ((1 + Nat.log2 S) ^ d)
def softBound (C d S volume : ℕ) : ℕ := C * (1 + volume) * (1 + Nat.log2 S) ^ d

end ScalarMachine
end HypercliqueRefutation.FourClique.Supplement


