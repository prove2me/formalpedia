-- Prove2me | Definitions.Def_ZLIPPadding_Padding_Supplement_Programs
-- name    : ZLIPPadding_Padding_Supplement_Programs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:15:56.714345+00:00
-- url     : https://prove2.me/theorems/ae544126-39e0-4052-a39f-9ec58382e8ea
-- title:
--   Rational input encodings and executable statistical programs
-- statement:
--   Extend the published finite bit-stack instruction language with a public bit-string oracle interface. Its instructions push or pop one bit, draw a fresh fair coin, make a request, or halt. Requests disclose only their encoded data; all hidden orthogonal and unimodular matrices occur in mathematical correctness witnesses. Rational bases and vectors use exact numerator/denominator and self-delimiting binary encodings.
--
--   $$B=OM,\qquad O^\top O=I,\quad M\in\mathrm{GL}_n(\mathbb Z).$$
--
--   Define genuine fresh-query execution laws, termination and bit/space/sample budgets, the efficiently computable profile-family promise, exact orbit-sampling and basis-oracle validity, and coordinate transport of shell laws. The deterministic label-program contract computes the empirical statistics, fails at zero estimated contrast, approximates all ordered eigenvalues within $1/8$ and rounds them to integers. Its numerical specification does not assume a correct label. Uniform polynomial resource witnesses are supplied only by subsequent theorems.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed pp. 7, 11, 13–14, 16–21 (PDF pp. 8, 12, 14–15, 17–22), Sections 2.1, 2.5, 3.2 and 4

import Definitions.Def_ZLIPPadding_Padding_BitMachine
import Definitions.Def_ZLIPPadding_Padding_Supplement_Statistics

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal

abbrev QMat (n : ℕ) := Matrix (Fin n) (Fin n) ℚ
def gramQ {n : ℕ} (B : QMat n) : Matrix (Fin n) (Fin n) ℚ := B.transpose * B
def PromisedBasis {n : ℕ} (B : QMat n) : Prop :=
  0 < n ∧ ∃ (O : RMat n) (M : ZMat n),
    Orthogonal O ∧ Unimodular M ∧ B.map (fun q => (q : ℝ)) =
      O * M.map (fun z => (z : ℝ))
def basisGram {n : ℕ} (B : QMat n) : ZMat n := fun i j => (gramQ B i j).num
def basisPoint {n : ℕ} (B : QMat n) (z : ZVec n) : EVec n :=
  WithLp.toLp 2 ((B.map (fun q => (q : ℝ))).mulVec (fun i => (z i : ℝ)))
def BasisWitness {n : ℕ} (B : QMat n) (O : RMat n) (M : ZMat n) : Prop :=
  Orthogonal O ∧ Unimodular M ∧
  B.map (fun q => (q : ℝ)) = O * M.map (fun z => (z : ℝ))
def encRat (q : ℚ) : Bits := encInt q.num ++ encNat q.den
def readRat (w : Bits) : Option (ℚ × Bits) := do
  let (a, r) ← readInt w
  let (b, r') ← readNat r
  if b = 0 then none else pure ((a : ℚ)/b, r')
def encBasis {n : ℕ} (B : QMat n) : Bits :=
  encNat n ++ ((List.ofFn (fun i => List.ofFn (fun j => encRat (B i j)))).flatten).flatten
def encBlock (b : Bits) : Bits := encNat b.length ++ b
def encBlocks (bs : List Bits) : Bits := encNat bs.length ++ (bs.map encBlock).flatten
def encBatch {n : ℕ} (zs : List (ZVec n)) : Bits := encBlocks (zs.map encVec)
def encLabel (l : Multiset ℤ) : Bits := encInts l.sort

abbrev Kernel := Bits → PMF Bits
structure RunState where
  core : Configuration
  queries : List Bits := []
  replyBits : ℕ := 0

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The published bit-stack instructions, with public bit-string requests for sampling
or exact search. A query sees only its request and fresh independent oracle randomness. -/
def statStep (P : Program) (A : Kernel) (s : RunState) : PMF RunState :=
  let c := s.core
  if !c.running then PMF.pure s else
  let c := { c with ticks := c.ticks+1, bitCost := c.bitCost+P.length+1 }
  match (P[c.pc]? : Option Instruction) with
  | none => PMF.pure { s with core := { c with running := false, output := [] } }
  | some (.halt r) => PMF.pure { s with core := { c with running := false, output := c.tapes r } }
  | some (.push r b j) => PMF.pure { s with core := { store c r (b :: c.tapes r) with pc := j } }
  | some (.pop r e z o) => match c.tapes r with
    | [] => PMF.pure { s with core := { c with pc := e } }
    | b :: w => PMF.pure { s with core := { store c r w with pc := if b then o else z } }
  | some (.coin r j) => (PMF.bernoulli (1/2) (by norm_num)).map fun b =>
    { s with core := { store c r (b :: c.tapes r) with pc := j, randomBits := c.randomBits+1 } }
  | some (.query src dst j) => (A (c.tapes src)).map fun w =>
    { core := { store c dst w with pc := j, bitCost := c.bitCost+(c.tapes src).length+w.length },
      queries := c.tapes src :: s.queries, replyBits := s.replyBits+w.length }
def statFrom (P : Program) (A : Kernel) : ℕ → RunState → PMF RunState
  | 0, s => PMF.pure s
  | t+1, s => (statStep P A s).bind (statFrom P A t)
def run (P : Program) (A : Kernel) (fuel : ℕ) (input : Bits) : PMF RunState :=
  statFrom P A fuel { core := initial input }
def decoded {α : Type} (D : Bits → Option α) (P : Program) (A : Kernel)
    (fuel : ℕ) (input : Bits) : PMF (Option α) :=
  (run P A fuel input).map (fun s => if s.core.running then none else D s.core.output)
def silent : Kernel := fun _ => PMF.pure []
def Budget (bound : ℕ) (s : RunState) : Prop :=
  TraceBound bound s.core ∧ s.queries.length ≤ bound
def powerBound (c d x : ℕ) : ℕ := c*(x+1)^d
def errorBits (delta : ℝ) : ℕ := max 1 ⌈Real.log (1/delta)/Real.log 2⌉₊
def invSize (r : ℝ) : ℕ := ⌈r⁻¹⌉₊
def sampleInput {n : ℕ} (B : QMat n) (m k : ℕ) : Bits :=
  encBasis B ++ encNat m ++ encNat k
def recoverInput {n : ℕ} (B : QMat n) (k : ℕ) : Bits := encBasis B ++ encNat k

/-- Only basis coordinates are returned. Hidden rotations and factors are proof witnesses. -/
def OrbitSampler (a : (n : ℕ) → ZVec n) (A : Kernel) : Prop :=
  ∀ n (B : QMat n) O M, BasisWitness B O M → ∀ z : ZVec n,
    (A (encBasis B)) (encVec z) =
      (if M.mulVec z ∈ orbit (a n) then ((orbit (a n)).card : ℝ≥0∞)⁻¹ else 0)
def BasisOracle (A : Kernel) : Prop :=
  ∀ n (B : QMat n), PromisedBasis B → ∀ w, A (encBasis B) w ≠ 0 →
    ∃ U, decMat n w = some U ∧ BasisAnswer (basisGram B) U
def correctBasisOutput {n : ℕ} (B : QMat n) (s : RunState) : Prop :=
  s.core.running = false ∧ ∃ U, decMat n s.core.output = some U ∧
    BasisAnswer (basisGram B) U
def EfficientProfiles (a : (n : ℕ) → ZVec n) : Prop :=
  ∃ (P : Program) (c d : ℕ), 0 < c ∧ NoCoins P ∧ NoQueries P ∧
    ∀ n, 2 ≤ n → normSq (a n) ≤ powerBound c d n ∧
      ∀ s, run P silent (powerBound c d n) (encNat n) s ≠ 0 →
        Budget (powerBound c d n) s ∧ s.core.output = encVec (a n)

/-- Exact marginal coordinate law relative to an arbitrary rational input basis. -/
def CoordLaw {n : ℕ} (B : QMat n) (O : RMat n) (M : ZMat n)
    (μ : PMF (ZVec n)) (ν : PMF (ZVec n)) : Prop :=
  BasisWitness B O M ∧ ν.map M.mulVec = μ
def listBitSize {n : ℕ} (B : QMat n) (x : ZVec n)
    (us ys : List (ZVec n)) : ℕ :=
  (encBasis B).length + (encVec x).length + (encBatch us).length + (encBatch ys).length
def labelInput {n : ℕ} (B : QMat n) (m : ℕ) (positive : Bool)
    (x : ZVec n) (us ys : List (ZVec n)) : Bits :=
  encBasis B ++ encNat m ++ [positive] ++ encBlock (encVec x) ++
    encBlock (encBatch us) ++ encBatch ys
def decodeLabel (w : Bits) : Option (Multiset ℤ) :=
  if w = [] then none else (readInts w).map (fun l => (l : Multiset ℤ))

/-- Ordered symmetric eigenvalues, including multiplicity, via orthogonal diagonalization. -/
def OrderedSpectrum {n : ℕ} (D : RMat n) (lam : Fin n → ℝ) : Prop :=
  Monotone lam ∧ ∃ Q : RMat n, Orthogonal Q ∧
    D * Q = Q * Matrix.diagonal lam
def RoundedSpectrum {n : ℕ} (D : RMat n) (l : Multiset ℤ) : Prop :=
  ∃ (lam : Fin n → ℝ) (approx : Fin n → ℚ), OrderedSpectrum D lam ∧
    (∀ i, |(approx i : ℝ)-lam i| ≤ 1/8) ∧
    l = ↑(List.ofFn (fun i => round (approx i)))
def LabelNumerics {n : ℕ} (B : QMat n) (m : ℕ) (positive : Bool)
    (x : ZVec n) (us ys : List (ZVec n)) (l : Option (Multiset ℤ)) : Prop :=
  let u := us.map (basisPoint B)
  let y := ys.map (basisPoint B)
  let sign : ℝ := if positive then 1 else if 0 < shellKappa n m then 1
    else if shellKappa n m = 0 then 0 else -1
  let kh := estimateKappa n m sign (empiricalPair u)
  if kh = 0 then l = none else
    ∃ label, l = some label ∧ RoundedSpectrum
      (estimateD m (basisPoint B x) (empiricalC (basisPoint B x) y) kh) label
def LabelProgram (P : Program) (c d : ℕ) : Prop :=
  NoQueries P ∧ NoCoins P ∧ 0 < c ∧
  ∀ (n m : ℕ) (B : QMat n) positive x us ys, 2 ≤ n → 1 ≤ m → PromisedBasis B →
    2 ≤ us.length → 0 < ys.length →
    (∀ z ∈ us ++ ys, qnorm (basisGram B) z = m) → qnorm (basisGram B) x = m →
    let bound := powerBound c d (n+m+listBitSize B x us ys)
    ∀ s, run P silent bound (labelInput B m positive x us ys) s ≠ 0 →
      Budget bound s ∧ LabelNumerics B m positive x us ys (decodeLabel s.core.output)
def labelLaw {n : ℕ} (P : Program) (c d : ℕ) (B : QMat n) (m : ℕ)
    (positive : Bool) (x : ZVec n) (ν : PMF (ZVec n)) (N4 Nx : ℕ) : PMF (Option (Multiset ℤ)) :=
  (iid ν N4).bind fun us => (iid ν Nx).bind fun ys =>
    decoded decodeLabel P silent (powerBound c d (n+m+listBitSize B x us ys))
      (labelInput B m positive x us ys)
def LabelGuarantee (P : Program) (c d : ℕ) (positive : Bool)
    (n m : ℕ) (μ : PMF (ZVec n)) (kap0 : ℝ) : Prop :=
  ∀ (B : QMat n) O M ν x (eta : ℝ) N4 Nx,
    CoordLaw B O M μ ν → M.mulVec x ∈ shell n m → 0 < eta → eta < 1 →
    labelSamples n m kap0 eta N4 Nx →
    prob (labelLaw P c d B m positive x ν N4 Nx)
      {l | l = some (profile (M.mulVec x))} ≥ 1-eta

end
end ZLIPPadding.Padding.Supplement


