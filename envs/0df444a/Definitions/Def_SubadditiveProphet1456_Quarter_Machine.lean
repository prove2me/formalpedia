-- Prove2me | Definitions.Def_SubadditiveProphet1456_Quarter_Machine
-- name    : SubadditiveProphet1456_Quarter_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:05.336017+00:00
-- url     : https://prove2.me/theorems/908f720e-afe5-4d56-8056-a4def4f3501b
-- title:
--   Costed randomized rational programs, demand-only online ports and sparse LP output
-- statement:
--   A program is one finite list of two-stack rational instructions. Its allowed operations push or move a word, duplicate or discard the top word, add, subtract, multiply or divide two rationals, branch, draw a fresh fair bit, call an external port, or halt. No instruction contains a Lean function or an optimization routine. The interpreter executes every instruction and accumulates a fixed polynomial bit charge for its operands, stack handling, oracle call, and full answer. The state initially contains only the explicitly given dimensions, support probabilities, accuracy parameters and a public upper bound on the bit length of every rational valuation value; it contains no realized future types and no valuation table.
--
--   The generic program and oracle-port interfaces are separate from the allocation instance. The paper-specific port allows demand queries for any public support valuation, sequential revelation of the next realized type, and irrevocable commitment of a bundle of remaining items. Another revelation is unavailable until commitment. The demand answer contains only an arbitrary maximizing bundle for
--   $$
--   v_{i,\tau}(A)-\sum_{j\in A}p_j.
--   $$
--   Every tie choice is allowed. Oracle and port bookkeeping have fixed charges; arithmetic, coins, preprocessing and all online steps are executed by the same interpreter. Rational representations require exact equality to the given probabilities and valuations and certify that every valuation value obeys the public bit bound; every finite rational instance admits such a bound, and any larger bound is allowed. They restrict only the computational specialization, leaving the real mathematical instance unrestricted.
--
--   The output mass is the increasing supremum of the probabilities of having halted with a completed allocation. An implementation must match a probability law on allocations, so it cannot conceal nontermination or failed commitments. Expected bit cost is the increasing supremum of the expected accumulated work over all finite runs, in extended nonnegative reals. Infinite cost cannot collapse to zero.
--
--   An LP preprocessing program has a demand-only port and outputs a list of records $(i,\tau,\mathrm{mask}(A),x_{i,\tau,A})$. Decoding sums repeated records to obtain the actual fractional solution. Polynomial output length implies polynomial support. The numerical size uses the total explicitly listed support size and numerical bit lengths, including the supplied valuation bit bound; it never charges for enumeration or storage of an exponential valuation table. The generic polynomial bound is
--   $$
--   C(1+L+a)^d,
--   $$
--   where $C,d$ must be fixed before every input and $a$ is the accuracy dependence.
--
--   **Formalization Note** The instruction charges are a fixed polynomial overhead version of the standard rational bit/oracle model. The demand oracle supplies only a maximizing bundle, not an exact LP solution or a value table. Halted states stutter; invalid program counters continue to accrue positive work. Theorems assert program existence and its output/cost properties together, rather than accepting a runtime certificate as an input.
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, §2 (printed pp.7–9, PDF pp.8–10), §3 (printed pp.9–10, PDF pp.10–11), §4.3 Algorithm 1 (printed pp.15–17, PDF pp.16–18), Appendix A (printed pp.31–34, PDF pp.32–35).

import Definitions.Def_SubadditiveProphet1456_Quarter_Model

open scoped BigOperators NNReal ENNReal

namespace SubadditiveProphet1456.Quarter

/-- A generic finite two-stack rational program. Every primitive has an operational cost.
No instruction contains a Lean function or an LP solver. -/
inductive BitInstruction where
  | push (x : ℚ)
  | drop
  | copy
  | toRight
  | toLeft
  | add
  | sub
  | mul
  | div
  | jump (label : ℕ)
  | jumpNonpositive (label : ℕ)
  | coin
  | call
  | halt
  deriving Inhabited

abbrev BitProgram := List BitInstruction

structure BitState (E : Type) where
  pc : ℕ
  left : List ℚ
  right : List ℚ
  external : E
  halted : Bool
  work : ℕ

/-- Sign bit, binary numerator and denominator lengths, including zero. -/
def rationalBits (x : ℚ) : ℕ := 3 + Nat.log2 (x.num.natAbs + 1) + Nat.log2 (x.den + 1)
def wordBits (xs : List ℚ) : ℕ := (xs.map rationalBits).sum

/-- Generic oracle port. Its state is inaccessible except through the call instruction. -/
abbrev BitPort (E : Type) := E → List ℚ → E × List ℚ × ℕ

/-- Squared bit length is a uniform upper charge for the elementary rational operations.
The call branch additionally charges for the full oracle answer. -/
noncomputable def bitStep {E : Type} (P : BitProgram) (O : BitPort E)
    (s : BitState E) : PMF (BitState E) := by
  classical
  let base := 1 + (1 + wordBits s.left + wordBits s.right + Nat.log2 (s.pc+1))^2
  let t := {s with pc := s.pc+1, work := s.work+base}
  let hd := s.left.headD 0
  let rest := s.left.drop 1
  let hd2 := rest.headD 0
  let arith := fun (z : ℚ) => {t with left := z :: s.left.drop 2}
  exact if s.halted then PMF.pure s else
    match P[s.pc]? with
    | none => PMF.pure {s with work := s.work+base}
    | some (.push x) => PMF.pure {t with left := x :: s.left, work := t.work + rationalBits x}
    | some .drop => PMF.pure {t with left := rest}
    | some .copy => PMF.pure {t with left := hd :: s.left}
    | some .toRight => PMF.pure {t with left := rest, right := hd :: s.right}
    | some .toLeft => PMF.pure {t with left := s.right.headD 0 :: s.left, right := s.right.drop 1}
    | some .add => PMF.pure (arith (hd2+hd))
    | some .sub => PMF.pure (arith (hd2-hd))
    | some .mul => PMF.pure (arith (hd2*hd))
    | some .div => PMF.pure (arith (hd2/hd))
    | some (.jump label) => PMF.pure {t with pc := label}
    | some (.jumpNonpositive label) => PMF.pure {t with pc := if hd ≤ 0 then label else t.pc}
    | some .coin => (PMF.uniformOfFintype Bool).map fun b => {t with left := (if b then 1 else 0) :: s.left}
    | some .call =>
        let answer := O s.external s.left
        PMF.pure {t with external := answer.1, left := answer.2.1, work := t.work + answer.2.2 + 1 + (1+wordBits answer.2.1)^2}
    | some .halt => PMF.pure {t with halted := true}

noncomputable def bitRun {E : Type} (P : BitProgram) (O : BitPort E) (s : BitState E) :
    ℕ → PMF (BitState E)
  | 0 => PMF.pure s
  | k+1 => (bitRun P O s k).bind (bitStep P O)

noncomputable def expectedBitCost {E : Type} (P : BitProgram) (O : BitPort E)
    (s : BitState E) : ℝ≥0∞ :=
  ⨆ k : ℕ, ∑' z : BitState E, bitRun P O s k z * (z.work : ℝ≥0∞)

/-- Numerical data for the rational specialization. No valuation table is supplied to the machine. -/
structure RationalData {n m : ℕ} (I : Instance n m) where
  probability : (i : Fin n) → Fin (I.types i+1) → ℚ
  valuation : (i : Fin n) → Fin (I.types i+1) → Bundle m → ℚ
  probability_eq : ∀ i t, (probability i t : ℝ) = I.probability i t
  valuation_eq : ∀ i t A, (valuation i t A : ℝ) = I.valuation i t A
  /-- Public numerical encoding bound in the rational-input oracle model.
  Any upper bound is admissible; no valuation table is supplied to the program. -/
  valuationBitBound : ℕ
  valuation_bits_le : ∀ i t A, rationalBits (valuation i t A) ≤ valuationBitBound

abbrev DemandOracle {n m : ℕ} (I : Instance n m) :=
  (i : Fin n) → Fin (I.types i+1) → (Fin m → ℚ) → Bundle m

/-- Every maximizing tie choice is admissible. -/
def CorrectDemand {n m : ℕ} (I : Instance n m) (O : DemandOracle I) : Prop :=
  ∀ i t p A, I.valuation i t A - ∑ j ∈ A, (p j : ℝ) ≤
    I.valuation i t (O i t p) - ∑ j ∈ O i t p, (p j : ℝ)

noncomputable def publicWords {n m : ℕ} {I : Instance n m} (R : RationalData I)
    (parameters : List ℚ) : List ℚ :=
  [(n:ℚ),(m:ℚ),(R.valuationBitBound:ℚ)] ++ parameters ++ (List.finRange n).flatMap (fun i =>
    (I.types i+1 : ℚ) :: (List.finRange (I.types i+1)).map (R.probability i))

/-- Total explicit support size plus the public numerical bit bound.
This does not count or supply an exponential valuation table. -/
noncomputable def inputSize {n m : ℕ} {I : Instance n m} (R : RationalData I)
    (parameters : List ℚ) : ℕ :=
  1+n+m+(∑ i, (I.types i+1)) + wordBits (publicWords R parameters) + R.valuationBitBound

structure OnlinePortState (n m : ℕ) where
  next : ℕ
  active : Bool
  allocations : Allocation n m
  fault : Bool

noncomputable def demandAnswer {n m : ℕ} {I : Instance n m} (_R : RationalData I)
    (O : DemandOracle I) (a b : ℚ) (ps : List ℚ) : List ℚ := by
  classical
  exact if hi : a.den = 1 ∧ 0 ≤ a.num ∧ a.num.toNat < n then
    let i : Fin n := ⟨a.num.toNat, hi.2.2⟩
    if ht : b.den = 1 ∧ 0 ≤ b.num ∧ b.num.toNat < I.types i+1 then
      let t : Fin (I.types i+1) := ⟨b.num.toNat, ht.2.2⟩
      let A := O i t (fun j => ps[j.val]?.getD 0)
      (List.finRange m).map (fun j => if j ∈ A then 1 else 0)
    else []
  else []

/-- Port tags: 0 = demand query, 1 = reveal the next type, 2 = commit that buyer's
bundle. A second revelation requires a commitment, so no future realized type leaks.
The demand port returns only a maximizing bundle. -/
noncomputable def onlinePortCore {n m : ℕ} {I : Instance n m} (R : RationalData I)
    (O : DemandOracle I) (profile : Profile I) : OnlinePortState n m → List ℚ → OnlinePortState n m × List ℚ := by
  classical
  exact fun s request =>
    if s.fault then (s, []) else
    match request with
    | 0 :: a :: b :: ps => (s, demandAnswer R O a b ps)
    | 1 :: _ =>
        if h : s.next < n ∧ s.active = false then
          ({s with active := true}, [((profile ⟨s.next,h.1⟩).val : ℚ)])
        else ({s with fault := true}, [])
    | 2 :: mask =>
        if h : s.next < n ∧ s.active = true then
          let i : Fin n := ⟨s.next,h.1⟩
          let A := Finset.univ.filter fun j : Fin m =>
            mask[j.val]?.getD 0 ≠ 0 ∧ ∀ k, j ∉ s.allocations k
          ({s with next := s.next+1, active := false, allocations := Function.update s.allocations i A}, [])
        else ({s with fault := true}, [])
    | _ => ({s with fault := true}, [])

/-- Port bookkeeping scans the finite item/buyer indices; this fixed charge covers it. -/
noncomputable def onlinePort {n m : ℕ} {I : Instance n m} (R : RationalData I)
    (O : DemandOracle I) (t : Profile I) : BitPort (OnlinePortState n m) :=
  fun s request => let z := onlinePortCore R O t s request
    (z.1,z.2,1+(1+n+m+(∑ i, I.types i+1))^2)

noncomputable def onlineInit {n m : ℕ} {I : Instance n m} (R : RationalData I)
    (ε : ℚ) : BitState (OnlinePortState n m) :=
  ⟨0, publicWords R [ε], [], ⟨0,false,fun _ => ∅,false⟩, false,0⟩

instance {E : Type} : MeasurableSpace (BitState E) := ⊤

noncomputable def onlineOutputMass {n m : ℕ} {I : Instance n m} (P : BitProgram)
    (R : RationalData I) (ε : ℚ) (O : DemandOracle I) (t : Profile I)
    (A : Allocation n m) : ℝ≥0∞ :=
  ⨆ k : ℕ, (bitRun P (onlinePort R O t) (onlineInit R ε) k).toMeasure
    {z | z.halted = true ∧ z.external.fault = false ∧ z.external.next = n ∧
      z.external.active = false ∧ z.external.allocations = A}

noncomputable def ImplementsOnline {n m : ℕ} {I : Instance n m} (P : BitProgram)
    (R : RationalData I) (ε : ℚ) (O : DemandOracle I) (law : Policy I) : Prop :=
  ∀ t A, onlineOutputMass P R ε O t A = law t A

noncomputable def onlineCost {n m : ℕ} {I : Instance n m} (P : BitProgram)
    (R : RationalData I) (ε : ℚ) (O : DemandOracle I) : ℝ≥0∞ :=
  ∑ t : Profile I, ENNReal.ofReal (profileMass I t) *
    expectedBitCost P (onlinePort R O t) (onlineInit R ε)

/-- Sparse LP output consists of records (buyer,type,binary bundle mask,joint mass). -/
noncomputable def bundleCode {m : ℕ} (A : Bundle m) : ℕ := ∑ j ∈ A, 2^j.val

def readRecords (i t a : ℕ) : List ℚ → ℚ
  | b :: u :: v :: mass :: rest =>
      (if b = (i:ℚ) ∧ u = (t:ℚ) ∧ v = (a:ℚ) then mass else 0) + readRecords i t a rest
  | _ => 0

noncomputable def decodedLP {n m : ℕ} (I : Instance n m) (words : List ℚ) : Fractional I :=
  fun v => (readRecords v.1.val v.2.1.val (bundleCode v.2.2.val) words : ℝ)

/-- Demand-only preprocessing port; arrival and commitment are unavailable. -/
noncomputable def preprocessingPortCore {n m : ℕ} {I : Instance n m} (R : RationalData I)
    (O : DemandOracle I) : Unit → List ℚ → Unit × List ℚ :=
  fun s request => match request with
    | a :: b :: ps => (s, demandAnswer R O a b ps)
    | _ => (s, [])

noncomputable def preprocessingPort {n m : ℕ} {I : Instance n m} (R : RationalData I)
    (O : DemandOracle I) : BitPort Unit :=
  fun s request => let z := preprocessingPortCore R O s request
    (z.1,z.2,1+(1+n+m+(∑ i, I.types i+1))^2)

noncomputable def preprocessingInit {n m : ℕ} {I : Instance n m} (R : RationalData I)
    (θ η : ℚ) : BitState Unit := ⟨0,publicWords R [θ,η],[],(),false,0⟩

noncomputable def ApproximateLPOutput {n m : ℕ} (I : Instance n m) (θ η : ℝ)
    (B : ℕ) (words : List ℚ) : Prop :=
  words.length ≤ 4*B ∧ Feasible I θ (decodedLP I words) ∧
    (1-η)*lpValue I θ ≤ objective I (decodedLP I words)

/-- A single fixed polynomial dominates all input parameters; coefficients/degrees
are chosen before every instance. -/
noncomputable def polyBound (C : ℝ) (d : ℕ) (size : ℕ) (accuracy : ℝ) : ℝ :=
  C * (1+(size:ℝ)+accuracy)^d

end SubadditiveProphet1456.Quarter


