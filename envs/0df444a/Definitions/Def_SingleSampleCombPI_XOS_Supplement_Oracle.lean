-- Prove2me | Definitions.Def_SingleSampleCombPI_XOS_Supplement_Oracle
-- name    : SingleSampleCombPI_XOS_Supplement_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:39:34.971034+00:00
-- url     : https://prove2.me/theorems/c7387f61-d500-4346-8401-3cfef73bb04a
-- title:
--   Finite real-oracle programs and actual four-counter continuous-greedy implementation semantics
-- statement:
--   A finite real-register program has rational constants, arithmetic, square roots, memory reads/writes, branches, jumps, valuation queries, supergradient queries, supporting-price queries and a halt instruction. It has no instruction that evaluates an arbitrary function for free. The execution interpreter counts actual primitive operations and each of the three oracle query kinds separately. Query safety requires cube points for value/support queries, interior points for supergradients, nonzero divisors, nonnegative square-root arguments, and integer nonnegative memory addresses. Thus total-function junk cannot supply an implementation.
--
--   The source unit-cost real-oracle model is used. Input arrays contain $n,m,\epsilon$, the largest full-bundle value seen so far, and the frozen history's amounts and prices. The clock and the four counters use a uniform polynomial in $n,m,1+\lceil\max\{0,\log(1/\epsilon)\}\rceil$. A bounded-clock run that does not halt still has a total fallback allocation, but a successful implementation must halt and obey every safety check.
--
--   Approximate Algorithm 5 updates its running maximum, executes the finite program, reads/clamps its output in the cube and freezes supporting prices there. Its operation and query costs come from execution, encoding, the full-bundle value query and the supporting query. ApproxImplementation is a specification that is asserted in theorem conclusions: it requires halting, safe calls and additive surrogate accuracy $\min\{\epsilon,1/2\}M_i/[C(n+1)^2]$ at every reachable step. It is not an algorithm field or an assumed complexity certificate. Full run and Algorithms 1/2/3 composition costs sum actual calls, with value and supergradient counts kept separate from demand counts. A finite program witness and uniform constants must be established in the theorem proof. No program proof or computational claim is hidden in this definition.
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Theorem 4.6 and its oracle-implementation proof, printed pp. 20, 23–24 / PDF pp. 22, 25–26; §3.4, printed p. 17 / PDF p. 19; Theorem 6.2, printed p. 33 / PDF p. 35.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_GreedyDR
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Knapsack

namespace SingleSampleCombPI.XOS.Supplement

/-- Four actual counters: primitive, value, supergradient, supporting-price. -/
abbrev QCost := ℕ × ℕ × ℕ × ℕ

def QCost.Bounded (c : QCost) (K N : ℕ) : Prop :=
  c.1 ≤ K*(N+1)^K ∧ c.2.1 ≤ K*(N+1)^K ∧
  c.2.2.1 ≤ K*(N+1)^K ∧ c.2.2.2 ≤ K*(N+1)^K

/-- Logarithmic precision, valid at every positive epsilon. -/
noncomputable def precision (ε : ℝ) : ℕ :=
  1 + ⌈max 0 (Real.log (1/ε))⌉₊

def interior {m : ℕ} (x : Vec m) : Prop := ∀ j, 0 < x j ∧ x j < 1

/-- First-order access is needed only in the relative interior. This does not
exclude continuous concave functions such as sqrt(x), which have no finite
supergradient at zero. Every actual query must respect this domain. -/
def SupergradientOracle {m : ℕ} (b : Buyer m) (g : Vec m → Vec m) : Prop :=
  ∀ x, interior x → ∀ y, InDom .divisible y → b.v y ≤ b.v x + dot (g x) (y-x)

/-- A finite register program for unit-cost real arithmetic and oracle calls.
There is no arbitrary function-computation instruction or cost certificate. -/
inductive RInstr
  | constant (dst : ℕ) (q : ℚ)
  | copy (dst src : ℕ)
  | add (dst a b : ℕ)
  | sub (dst a b : ℕ)
  | mul (dst a b : ℕ)
  | div (dst a b : ℕ)
  | sqrt (dst src : ℕ)
  | load (dst address : ℕ)
  | store (address src : ℕ)
  | input (dst address : ℕ)
  | branch (a b yes no : ℕ)
  | jump (target : ℕ)
  | value (point dst : ℕ)
  | gradient (point dst : ℕ)
  | support (point dst : ℕ)
  | halt (output : ℕ)

abbrev RProgram := List RInstr

structure RState where
  pc : ℕ
  mem : ℕ → ℝ
  output : Option ℕ

noncomputable def rVector (m : ℕ) (s : RState) (base : ℕ) : Vec m :=
  fun j => s.mem (base+j.val)

noncomputable def rWrite (m : ℕ) (s : RState) (base : ℕ) (x : Vec m) : RState :=
  {s with mem := fun k => if h : base ≤ k ∧ k-base < m then x ⟨k-base,h.2⟩ else s.mem k}

/-- One executed instruction, and its actual counters. Vector transfer costs
m+1 primitives and one query of the indicated kind. -/
noncomputable def rStep {m : ℕ} (P : RProgram) (input : ℕ → ℝ)
    (b : Buyer m) (g : Vec m → Vec m) (s : RState) : RState × QCost := by
  classical
  let instr := P[s.pc]?.getD (.halt 0)
  let next := {s with pc := s.pc+1}
  let put := fun dst val => {next with mem := Function.update s.mem dst val}
  exact match instr with
  | .constant d q => (put d q, (1,0,0,0))
  | .copy d a => (put d (s.mem a), (1,0,0,0))
  | .add d a c => (put d (s.mem a+s.mem c), (1,0,0,0))
  | .sub d a c => (put d (s.mem a-s.mem c), (1,0,0,0))
  | .mul d a c => (put d (s.mem a*s.mem c), (1,0,0,0))
  | .div d a c => (put d (s.mem a/s.mem c), (1,0,0,0))
  | .sqrt d a => (put d (Real.sqrt (s.mem a)), (1,0,0,0))
  | .load d a => (put d (s.mem ⌊s.mem a⌋₊), (1,0,0,0))
  | .store a v => ({next with mem := Function.update s.mem ⌊s.mem a⌋₊ (s.mem v)}, (1,0,0,0))
  | .input d a => (put d (input ⌊s.mem a⌋₊), (1,0,0,0))
  | .branch a c y n => ({s with pc := if s.mem a ≤ s.mem c then y else n}, (1,0,0,0))
  | .jump t => ({s with pc := t}, (1,0,0,0))
  | .value a d => (put d (b.v (rVector m s a)), (m+1,1,0,0))
  | .gradient a d => (rWrite m next d (g (rVector m s a)), (m+1,0,1,0))
  | .support a d => (rWrite m next d (b.q (rVector m s a)), (m+1,0,0,1))
  | .halt a => ({s with output := some a}, (1,0,0,0))

/-- Query validity at a visited instruction, so no total-function behavior
outside the oracle domain can be used by the implementation. -/
def rSafe {m : ℕ} (P : RProgram) (s : RState) : Prop :=
  match P[s.pc]? with
  | some (.div _ _ a) => s.mem a ≠ 0
  | some (.sqrt _ a) => 0 ≤ s.mem a
  | some (.load _ a) | some (.store a _) | some (.input _ a) =>
      ∃ k : ℕ, s.mem a = (k:ℝ)
  | some (.gradient a _) => interior (rVector m s a)
  | some (.value a _) | some (.support a _) => InDom .divisible (rVector m s a)
  | _ => True

noncomputable def rRun {m : ℕ} (P : RProgram) (input : ℕ → ℝ)
    (b : Buyer m) (g : Vec m → Vec m) : ℕ → RState → RState × QCost × Prop
  | 0, s => (s,0,True)
  | t+1, s => if s.output.isSome then (s,0,True) else
    let z := rStep P input b g s
    let rest := rRun P input b g t z.1
    (rest.1, z.2+rest.2.1, rSafe (m := m) P s ∧ rest.2.2)

/-- Explicit input layout: n,m,epsilon,maximum full-bundle value,history length,
then all frozen allocation coordinates and price coordinates in arrival order. -/
noncomputable def optimizerInput {m : ℕ} (n : ℕ) (ε M : ℝ) (H : FrozenHistory m) : ℕ → ℝ :=
  let L := [(n:ℝ),(m:ℝ),ε,M,(H.length:ℝ)] ++ H.flatMap (fun e =>
    (List.finRange m).map (fun j => e.amount.1 j) ++
    (List.finRange m).map (fun j => e.price j))
  fun k => L[k]?.getD 0

/-- A terminating implementation must produce its output from actual memory.
The clock is a uniform polynomial; termination, safe queries, accuracy and
competitive guarantees are theorem conclusions, never program fields. -/
noncomputable def optimize {m : ℕ} (P : RProgram) (K n : ℕ) (ε M : ℝ)
    (H : FrozenHistory m) (b : Buyer m) (g : Vec m → Vec m) : RState × QCost × Prop :=
  rRun P (optimizerInput n ε M H) b g (K*(n+m+precision ε+1)^K) ⟨0,fun _ => 0,none⟩

noncomputable def optimizerPoint {m : ℕ} (z : RState × QCost × Prop) : Cube m :=
  ⟨fun j => max 0 (min 1 (z.1.mem (z.1.output.getD 0+j.val))),
    fun _j => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩⟩

/-- Approximate Algorithm 5: the history plus the largest v(1) so far. -/
abbrev ApproxState (m : ℕ) := FrozenHistory m × ℝ

noncomputable def optimizerCall {m : ℕ} (P : RProgram) (K n : ℕ) (ε : ℝ)
    (g : Buyer m → Vec m → Vec m) (s : ApproxState m) (b : Buyer m) :=
  optimize P K n ε (max s.2 (b.v 1)) s.1 b (g b)

/-- Actual full step cost includes evaluating v(1), encoding the previous
records, reading/clamping the output, and freezing the new supporting prices. -/
noncomputable def approxStepCost {m : ℕ} (P : RProgram) (K n : ℕ) (ε : ℝ)
    (g : Buyer m → Vec m → Vec m) (s : ApproxState m) (b : Buyer m) : QCost :=
  (optimizerCall P K n ε g s b).2.1 + (2*m*(s.1.length+1)+m+10,1,0,1)

noncomputable def approx5 (P : RProgram) (K : ℕ) (ε : ℝ) (n m : ℕ)
    (g : Buyer m → Vec m → Vec m) : FDAlg .divisible n m where
  State := ApproxState m
  Ω := Unit
  seed := RandomSource.ofPMF (PMF.pure ())
  init := fun _ => ([],0)
  step := fun s _ b =>
    let M := max s.2 (b.v 1)
    let x := optimizerPoint (optimize P K n ε M s.1 b (g b))
    (x,(s.1 ++ [freeze b x], M))
  seedCost := 0
  stepCost := fun s _ b =>
    let c := approxStepCost P K n ε g s b
    (c.1,0,c.2.2.2)

/-- Prefix-correct execution and source-scaled error at every visited step. -/
def ApproxImplementation (P : RProgram) (K C : ℕ) : Prop :=
  ∀ (n m : ℕ) (ε : ℝ), 0 < ε → ∀ g : Buyer m → Vec m → Vec m,
    (∀ b, ConcaveBuyer b → SupergradientOracle b (g b)) →
    ∀ v : Fin n → Buyer m, (∀ i, ConcaveBuyer (v i)) → ∀ ρ i,
      let s := savedState (approx5 P K ε n m g) () ρ v i
      let z := optimizerCall P K n ε g s (v i)
      z.1.output.isSome ∧ z.2.2 ∧
      (∀ y : Cube m, surrogate s.1 (v i) y.1 ≤
        surrogate s.1 (v i) (optimizerPoint z).1 +
          min ε (1/2) * max s.2 ((v i).v 1) / ((C:ℝ)*(n+1)^2)) ∧
      QCost.Bounded (approxStepCost P K n ε g s (v i)) K (n+m+precision ε)

/-- Total four-counter cost over the n processed buyers. -/
noncomputable def approxRunCost (P : RProgram) (K : ℕ) (ε : ℝ) (n m : ℕ)
    (g : Buyer m → Vec m → Vec m) (ρ : Equiv.Perm (Fin n)) (v : Fin n → Buyer m) : QCost :=
  ∑ i, approxStepCost P K n ε g (savedState (approx5 P K ε n m g) () ρ v i) (v i)

/-- Full four-counter cost of the composed Algorithms 1/2/3. -/
noncomputable def approx3Cost (P : RProgram) (K : ℕ) (ε : ℝ) (n m : ℕ)
    (g : Buyer m → Vec m → Vec m) (H : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (ωs : Fin m → (alg8 n).Ω) (ρ : Equiv.Perm (Fin n)) (s r : Fin n → Buyer m) : QCost :=
  let F := approx5 P K ε n m g
  let sc := roleSc H s
  let s1 := roleS1 H s
  let rr := roleR H r
  let calls := ∑ i, (
    approxStepCost P K n ε g (savedState F () π sc i) (sc i) +
    approxStepCost P K n ε g (savedState F () π sc i) (s1 i) +
    approxStepCost P K n ε g (savedState F () π sc i) (rr i))
  let base := alg3Cost F (alg8 n) H π () ωs ρ s r
  (base.1,calls.2.1,calls.2.2.1,base.2.2)

end SingleSampleCombPI.XOS.Supplement


