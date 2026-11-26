-- Prove2me | Definitions.Def_DirectedHamiltonicity_ParitySampler
-- name    : DirectedHamiltonicity_ParitySampler
-- status  : Definition
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:17:58.846847+00:00
-- url     : https://prove2.me/theorems/ddb6ddd7-1048-4ae1-9ba6-a0e647ba0ee4
-- title:
--   The finite-coin estimator for weighted Hamiltonian path parity
-- statement:
--   For a directed multigraph with labelled arcs and nonnegative integer weights, group arcs by tail, head and weight and reduce their multiplicities modulo two. A shared random mask and a sequence of finite random ranks specify affine systems on subsets of the internal vertices. The bounded collection of the reported words is used to evaluate the determinant sum modulo two.
--
--   The definitions connect the sampling spaces, finite coin strings, target field and normalized graph to a Boolean estimator on the encoded input. The number of trials depends on the normalized graph's incoming-weight degree.
-- source:
--   Auxiliary result for the log-cost RAM formalization of Proposition 4 in T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission 811, PDF pp. 5 and 8–11. https://prove2.me/theorems/aa04b14a-8225-48c8-904c-8725ebdcac66

import Definitions.Def_AffineCounting_RAMInterfaces
import Definitions.Def_DirectedHamiltonicity_Main_DetSum

set_option autoImplicit false

section BoundedBinaryInput

/-! A bounded reader for little-endian self-delimiting naturals. Each payload bit is
preceded by a one; a zero marker terminates the field. -/

namespace BoundedBinaryInput

def read : ℕ → List Bool → Option ℕ
  | _, false :: _ => some 0
  | k + 1, true :: bit :: rest => (read k rest).map (Nat.bit bit)
  | _, _ => none

/-- Reading with the bit length of a known upper bound also works when the input is
an unrestricted integer magnitude. -/
def readAtMost (cap : ℕ) (xs : List Bool) : Option ℕ :=
  (read cap.size xs).bind fun x => if x ≤ cap then some x else none

end BoundedBinaryInput

end BoundedBinaryInput

section HamiltonianParityNormalization

namespace DirectedHamiltonicity.Main.Multidigraph

open Polynomial Classical

open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E]

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V) {W : ℕ} (hw : ∀ e, w e ≤ W)

abbrev ArcType (V : Type) (W : ℕ) := V × V × Fin (W + 1)

def arcType (e : E) : ArcType V W := (H.tail e, H.head e, ⟨w e, Nat.lt_succ_of_le (hw e)⟩)

 def allArcs (V : Type) (W : ℕ) : Multidigraph V (ArcType V W) :=
  ⟨Prod.fst, fun q => q.2.1⟩

noncomputable def retainArc (q : ArcType V W) : Prop :=
  q.1 ≠ q.2.1 ∧ q.2.1 ≠ s ∧ q.1 ≠ t ∧ Odd (Nat.card {e : E // H.arcType w hw e = q})

abbrev RetainedArc := {q : ArcType V W // H.retainArc w s t hw q}

def normalizedGraph : Multidigraph V (H.RetainedArc w s t hw) :=
  (allArcs V W).restrictArcs (H.retainArc w s t hw)

def normalizedWeight (e : H.RetainedArc w s t hw) : ℕ := e.1.2.2.val

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianParityNormalization

section DyadicSampling

namespace FiniteSampling

open Classical

variable {A U X : Type*}

/-- A string outside the image reports nothing. Any concrete injection can be used. -/
noncomputable def padded (code : A ↪ U) (family : A → Finset X) (u : U) : Finset X :=
  if h : ∃ a, code a = u then family h.choose else ∅

variable [Fintype A] [Fintype U]

abbrev CoinBlock (A : Type*) [Fintype A] := Fin (Nat.clog 2 (Fintype.card A)) → Bool

end FiniteSampling

end DyadicSampling

section HamiltonianParitySampling

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling Classical

open scoped BigOperators

/-- The number of trials per amplification block. Rational arithmetic computes the ceiling exactly. -/
def samplingBlockSize (n d : ℕ) : ℕ := 2 * ⌈(2 - (1 / 2 : ℚ) ^ d) ^ (n - 2)⌉₊

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V)

abbrev RandomMasks := (i : Internal s t) → Finset (H.incomingWeights w i.1)

/-- The actual degree parameter can be obtained from the graph; the supplied bound need
not be encoded on the tape. -/
noncomputable def samplingDegree : ℕ :=
  max 1 (Finset.univ.sup fun v => (H.incomingWeights w v).card)

noncomputable def coinFamily
    (code : H.NonzeroCoeffs w s t ↪ CoinBlock (H.NonzeroCoeffs w s t))
    (r : H.RandomMasks w s t) :
    CoinBlock (H.NonzeroCoeffs w s t) → Finset (Finset (Internal s t)) :=
  padded code fun a => H.sampled w s t (fun i => (a i).1) r

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianParitySampling

section HamiltonianRAMSchedule

namespace DirectedHamiltonicity.Main.Multidigraph

open TargetedSamplers.Structured TargetedSamplers.Structured.Word

/-- Registers 0 and 1 hold n and the degree. Register 11 receives the amplification
block size and register 13 the total trial count. -/
def trialSchedule : List Assignment := [
  ⟨2,.literal 2⟩, ⟨3,.literal 1⟩, ⟨4,.literal 4⟩, ⟨5,.arithmetic .pow 2 1⟩,
  ⟨6,.add 5 5⟩, ⟨6,.sub 6 3⟩, ⟨7,.sub 0 2⟩, ⟨8,.arithmetic .pow 6 7⟩,
  ⟨9,.arithmetic .pow 5 7⟩, ⟨10,.add 8 9⟩, ⟨10,.sub 10 3⟩, ⟨10,.arithmetic .div 10 9⟩,
  ⟨11,.add 10 10⟩, ⟨12,.add 0 4⟩, ⟨13,.arithmetic .mul 12 11⟩]

def scheduleWidth (n d : ℕ) := (d+1)*(n-2)+n+d+16

def scheduleSteps (n d : ℕ) :=
  let w := scheduleWidth n d
  (d+2*(n-2)+15)*(w*(5*w+9)+15)

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianRAMSchedule

section RankedCoinSampling

/-! Explicit ranks for tuples of nonzero binary words, and fixed-length fair-bit decoding. -/

namespace FiniteSampling

open scoped BigOperators

/-- Interpret a tape block as a binary integer, least significant bit first. -/
def binaryRank (k : ℕ) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  (Equiv.piCongrRight fun _ => finTwoEquiv.symm).trans finFunctionFinEquiv

/-- The increasing bijection which deletes the zero rank, also on an empty domain. -/
def positiveRank (N : ℕ) : {x : Fin N // x.val ≠ 0} ≃ Fin (N-1) where
  toFun x := ⟨x.1.val-1, by have := x.1.isLt; have := x.2; omega⟩
  invFun i := ⟨⟨i.val+1, by have := i.isLt; omega⟩, Nat.succ_ne_zero _⟩
  left_inv x := by apply Subtype.ext; apply Fin.ext; have := x.2; dsimp; omega
  right_inv i := by apply Fin.ext; simp

/-- Each nonzero k-bit row has rank equal to its binary value minus one. -/
def nonzeroRowRank {I : Type*} {k : ℕ} (cols : I ≃ Fin k) :
    {x : I → Fin 2 // x ≠ 0} ≃ Fin (2^k-1) := by
  let e : (I → Fin 2) ≃ Fin (2^k) := (cols.arrowCongr (Equiv.refl _)).trans finFunctionFinEquiv
  have hz : (e 0).val = 0 := by simp [e]
  refine (Equiv.subtypeEquiv e (fun x => not_congr ?_)).trans (positiveRank _)
  exact ⟨fun h => h ▸ hz, fun h => e.injective (Fin.ext (h.trans hz.symm))⟩

/-- Mixed-radix ranking from ordered rows. The inverse in mathlib extracts each digit by
division by the prefix product and reduction modulo that row's radix. -/
def tupleRank {I : Type*} {k : ℕ} {A : I → Type*} (order : I ≃ Fin k)
    (radix : I → ℕ) (row : ∀ i, A i ≃ Fin (radix i)) :
    (∀ i, A i) ≃ Fin (∏ j : Fin k, radix (order.symm j)) :=
  (Equiv.piCongrLeft' A order).trans ((Equiv.piCongrRight fun j => row (order.symm j)).trans finPiFinEquiv)

variable {A : Type*} [Fintype A] {N : ℕ}

/-- Each block is inspected once. Values outside the rank interval denote an empty trial. -/
def decodeRank (rank : A ≃ Fin N) (bits : CoinBlock A) : Option A :=
  let v := binaryRank _ bits
  if h : v.val < N then some (rank.symm ⟨v.val,h⟩) else none

end FiniteSampling

end RankedCoinSampling

section FiniteCoinTape

namespace FiniteSampling

open Classical

variable {A B : Type*} [Fintype A] [Fintype B]

/-- Split a tape at a known position. The first component is exactly the prefix of that length. -/
def splitCoins (r s : ℕ) : (Fin (r + s) → Bool) ≃ (Fin r → Bool) × (Fin s → Bool) :=
  (finSumFinEquiv.symm.arrowCongr (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

/-- Assign a mask to each row by reading a fixed number of bits per trial. -/
def trialBlocks (m width : ℕ) : (Fin (m * width) → Bool) ≃ (Fin m → Fin width → Bool) :=
  (finProdFinEquiv.symm.arrowCongr (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

end FiniteSampling

end FiniteCoinTape

section RAMRankedCoins

namespace FiniteSampling

open TargetedSamplers TargetedSamplers.Structured

open scoped BigOperators

def readRank (r : Fin 5 ↪ ℕ) : Cmd := .seq (.op (.const (r 4) 0)) (CoinRead.loop r)

end FiniteSampling

end RAMRankedCoins

section BoundedEnumeration

/-! Output-sensitive enumeration from a binary prefix-feasibility test. -/

namespace BoundedEnumeration

structure Result where
  words : List (List Bool)
  probes : ℕ

/-- Stop after `limit` answers, also inside a single prolific trial. A feasibility probe
is issued only for a node which has some output quota left. -/
def search (viable : ℕ → List Bool → Bool) : ℕ → List Bool → ℕ → Result
  | _, _, 0 => ⟨[], 0⟩
  | 0, pref, _ + 1 => if viable 0 pref then ⟨[pref], 1⟩ else ⟨[], 1⟩
  | k + 1, pref, cap + 1 =>
      if viable (k + 1) pref then
        let left := search viable k (false :: pref) (cap + 1)
        let right := search viable k (true :: pref) (cap + 1 - left.words.length)
        ⟨left.words ++ right.words, 1 + left.probes + right.probes⟩
      else ⟨[], 1⟩

end BoundedEnumeration

end BoundedEnumeration

section HamiltonianParityEstimator

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling Classical Polynomial

open scoped BigOperators

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V)

abbrev MaskIndex := Σ i : Internal s t, H.incomingWeights w i.1

 noncomputable def boolSet (S : Type) [Fintype S] : (S → Bool) ≃ Finset S where
  toFun f := Finset.univ.filter fun i => f i = true
  invFun xs i := decide (i ∈ xs)
  left_inv f := by funext i; cases h : f i <;> simp [h]
  right_inv xs := by ext i; simp

/-- A fixed ordering of the incident weight classes assigns one independent tape bit to each
pair consisting of an internal vertex and one of its incoming weights. -/
noncomputable def masksOfBits
    (index : H.MaskIndex w s t ≃ Fin (Fintype.card (H.MaskIndex w s t))) :
    (Fin (Fintype.card (H.MaskIndex w s t)) → Bool) ≃ H.RandomMasks w s t :=
  (index.symm.arrowCongr (Equiv.refl Bool)).trans <|
    (Equiv.piCurry (fun (_ : Internal s t) _ => Bool)).trans <|
      Equiv.piCongrRight (fun i => boolSet (H.incomingWeights w i.1))

noncomputable def parityCoinCount (m : ℕ) : ℕ :=
  Fintype.card (H.MaskIndex w s t) + m * Nat.clog 2 (Fintype.card (H.NonzeroCoeffs w s t))

noncomputable def parityCoinBlocks
    (index : H.MaskIndex w s t ≃ Fin (Fintype.card (H.MaskIndex w s t))) (m : ℕ) :
    (Fin (H.parityCoinCount w s t m) → Bool) ≃
      H.RandomMasks w s t × (Fin m → CoinBlock (H.NonzeroCoeffs w s t)) :=
  (splitCoins _ _).trans <| (H.masksOfBits w s t index).prodCongr (trialBlocks _ _)

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianParityEstimator

section HamiltonianCoinEncoding

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling

open scoped BigOperators

variable {n : ℕ} {E : Type} [Fintype E]

variable (H : Multidigraph (Fin n) E) (w : E → ℕ) (s t : Fin n)

/-- Internal vertices are indexed in increasing order of their input label. -/
def internalLabels : Finset (Fin n) := Finset.univ.filter fun v => v ≠ s ∧ v ≠ t

def internalOrder : Internal s t ≃ Fin (internalLabels s t).card :=
  (Equiv.subtypeEquivRight (fun v => (show v ≠ s ∧ v ≠ t ↔ v ∈ internalLabels s t by
    simp [internalLabels]))).trans ((internalLabels s t).orderIsoOfFin rfl).toEquiv.symm

/-- The leading coordinate has index zero and the remaining weights are in increasing order. -/
noncomputable def weightColumns (v : Fin n) : Option (H.incomingWeights w v) ≃
    Fin ((H.incomingWeights w v).card+1) :=
  (((H.incomingWeights w v).orderIsoOfFin rfl).toEquiv.symm.optionCongr).trans (finSuccEquiv _).symm

noncomputable def coeffRadix (v : Internal s t) : ℕ := 2^((H.incomingWeights w v.val).card+1)-1

/-- This product is computed from the individual row widths, without enumerating tuples. -/
noncomputable def coeffRadixProduct : ℕ :=
  ∏ j, H.coeffRadix w s t ((internalOrder s t).symm j)

noncomputable def coefficientRank : H.NonzeroCoeffs w s t ≃ Fin (H.coeffRadixProduct w s t) :=
  tupleRank (internalOrder s t) (H.coeffRadix w s t) fun i => nonzeroRowRank (H.weightColumns w i.val)

/-- A shared mask bit is located by the sum of earlier row widths and the rank of its weight. -/
noncomputable def orderedMaskIndex : H.MaskIndex w s t ≃ Fin (Fintype.card (H.MaskIndex w s t)) := by
  let e := (internalOrder s t).symm
  let first := (Equiv.sigmaCongrLeft (β := fun v : Internal s t => ↥(H.incomingWeights w v.1)) e).symm
  let rows := Equiv.sigmaCongrRight fun j => ((H.incomingWeights w (e j).1).orderIsoOfFin rfl).toEquiv.symm
  let all := first.trans (rows.trans finSigmaFinEquiv)
  exact all.trans (finCongr (by simpa using (Fintype.card_congr all).symm))

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianCoinEncoding

section HamiltonianSamplingRows

namespace DirectedHamiltonicity.Main.Multidigraph

open Classical Polynomial

open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E]

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V)

 noncomputable def tailCoordinate (u : V) : Option (Internal s t) :=
  if h : u ≠ s ∧ u ≠ t then some ⟨u,h⟩ else none

/-- Polynomially many entries determine a diagonal coefficient as an affine form. Each
original arc uses its tail coordinate. Each added arc contributes to the constant coordinate. -/
noncomputable def diagonalForm (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (i : Internal s t) (b : H.incomingWeights w i.1) : Option (Internal s t) → ZMod 2 :=
  (∑ e : E, if H.head e = i.1 ∧ w e = b.1
    then Pi.single (tailCoordinate s t (H.tail e)) 1 else 0) +
    ∑ e : H.AugArc w s t R, if e.1.1 = i.1 ∧ e.2.1.1 = b.1 then Pi.single none 1 else 0

/-- The row of the linear system acting on the indicator with its leading constant one. -/
noncomputable def samplingRow (R : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (a : (i : Internal s t) → H.CoeffVec w i.1) (i : Internal s t) :
    Option (Internal s t) → ZMod 2 :=
  a i none • Pi.single (some i) 1 + ∑ b, a i (some b) • H.diagonalForm w s t R i b

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianSamplingRows

section HamiltonianAffineEnumeration

namespace DirectedHamiltonicity.Main.Multidigraph

open EditGV897.Main AffinePrefixEnumeration BoundedEnumeration

open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E] {q : ℕ}

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V)

open Classical in
/-- Indicators turn a numbered subset into a binary word. -/
noncomputable def numberedIndicator (order : Fin q ≃ Internal s t) :
    Finset (Internal s t) ≃ Word q where
  toFun x j := if order j ∈ x then 1 else 0
  invFun a := Finset.univ.filter fun j => a (order.symm j) ≠ 0
  left_inv x := by ext j; simp
  right_inv a := by
    funext j
    have hb : ∀ v : ZMod 2, v = 0 ∨ v = 1 := by decide
    obtain h | h := hb (a j) <;> simp [h]

/-- One dense affine equation per internal vertex, in the registered Gaussian counter's format. -/
noncomputable def samplingSystem (order : Fin q ≃ Internal s t)
    (r : (i : Internal s t) → Finset (H.incomingWeights w i.1))
    (a : (i : Internal s t) → H.CoeffVec w i.1) : List (Equation q) :=
  List.ofFn fun i : Fin q =>
    (fun j => H.samplingRow w s t r a (order i) (some (order j)), 1 - H.samplingRow w s t r a (order i) none)

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianAffineEnumeration

section TabulatedDeterminant

/-! A tabulated Bird determinant, with counts of ring operations and bounds on polynomial degrees. -/

section

namespace BirdDet.Tabulated

open scoped BigOperators

/-- Each layer stores its entries before any entry of the next layer is evaluated. -/
abbrev Table (R : Type*) (n : ℕ) := Vector (Vector R n) n

def table {R : Type*} {n : ℕ} (f : Fin n → Fin n → R) : Table R n :=
  Vector.ofFn fun i => Vector.ofFn (f i)

def matrix {R : Type*} {n : ℕ} (v : Table R n) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => v[i.val][j.val]

/-- Scalar operation counts record each ring addition, multiplication, and negation once. -/
structure Counted (R : Type*) where
  value : R
  ops : ℕ

variable {R : Type*} {n : ℕ}

def sumList [Zero R] [Add R] {ι : Type*} (f : ι → Counted R) : List ι → Counted R
  | [] => ⟨0, 0⟩
  | i :: rest =>
    let a := f i
    let b := sumList f rest
    ⟨a.value + b.value, a.ops + b.ops + 1⟩

def diagonalTerm [Zero R] (F : Table R n) (i k : Fin n) : Counted R :=
  ⟨if i < k then matrix F k k else 0, 0⟩

def productTerm [Zero R] [Mul R] (A F : Table R n) (i j k : Fin n) : Counted R :=
  if i < k then ⟨matrix F i k * matrix A k j, 1⟩ else ⟨0,0⟩

def entry [Zero R] [Add R] [Mul R] [Neg R] (A F : Table R n) (i j : Fin n) : Counted R :=
  let diag := sumList (diagonalTerm F i) (List.finRange n)
  let row := sumList (productTerm A F i j) (List.finRange n)
  ⟨-diag.value * matrix A i j + row.value, diag.ops + row.ops + 3⟩

/-- The counter carried with a layer includes the operations of all preceding layers. -/
def layers [Zero R] [Add R] [Mul R] [Neg R] (A : Table R n) : ℕ → Counted (Table R n)
  | 0 => ⟨A,0⟩
  | k+1 =>
    let prev := layers A k
    let cells := table (entry A prev.value)
    ⟨table (fun i j => (matrix cells i j).value),
      prev.ops + ∑ i : Fin n, ∑ j : Fin n, (matrix cells i j).ops⟩

/-- A division-free determinant with two successive tables in the recurrence. -/
def determinant [Zero R] [One R] [Add R] [Mul R] [Neg R] {n : ℕ} (A : Table R n) : Counted R :=
  match n with
  | 0 => ⟨1,0⟩
  | k+1 =>
    let last := layers A k
    let v := matrix last.value 0 0
    if Even k then ⟨v,last.ops⟩ else ⟨-v,last.ops+1⟩

end BirdDet.Tabulated

end

end TabulatedDeterminant

section TruncatedPolynomialDeterminant

/-! Compute the low coefficients of a determinant using fixed-length arrays of coefficients. -/

namespace BirdDet.Tabulated

open scoped BigOperators

/-- Exactly the coefficients in degrees less than the width. -/
structure CoeffArray (K : Type*) (width : ℕ) where
  data : Vector K width

namespace CoeffArray

variable {K : Type*} {width : ℕ}

def ofFn (f : Fin width → K) : CoeffArray K width := ⟨Vector.ofFn f⟩

def get (u : CoeffArray K width) (i : Fin width) : K := u.data[i.val]

variable [CommRing K]

instance : Zero (CoeffArray K width) := ⟨ofFn fun _ => 0⟩

instance : One (CoeffArray K width) := ⟨ofFn fun i => if i.val = 0 then 1 else 0⟩

instance : Add (CoeffArray K width) := ⟨fun u v => ofFn fun i => u.get i + v.get i⟩

instance : Neg (CoeffArray K width) := ⟨fun u => ofFn fun i => -u.get i⟩

/-- Ordinary coefficient convolution. For output i this loop has i+1 terms. -/
def convolve (u v : CoeffArray K width) (i : Fin width) : Counted K :=
  sumList (fun j : Fin (i.val+1) =>
    ⟨u.get ⟨j.val, lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) i.isLt⟩ *
      v.get ⟨i.val-j.val, lt_of_le_of_lt (Nat.sub_le ..) i.isLt⟩, 1⟩) (List.finRange (i.val+1))

instance : Mul (CoeffArray K width) := ⟨fun u v => ofFn fun i => (convolve u v i).value⟩

def fromPolynomial (width : ℕ) (p : Polynomial K) : CoeffArray K width :=
  ofFn fun i => p.coeff i.val

end CoeffArray

end BirdDet.Tabulated

end TruncatedPolynomialDeterminant

section HamiltonianParityInput

namespace DirectedHamiltonicity.Main

/-- A negative target or an oversized nonnegative target is rejected; both have zero count. -/
def readTarget (cap : ℕ) : List Bool → Option ℕ
  | false :: digits => BoundedBinaryInput.readAtMost cap digits
  | _ => none

end DirectedHamiltonicity.Main

end HamiltonianParityInput

section HamiltonianParityDeterminant

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling Polynomial BirdDet.Tabulated

open scoped BigOperators

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V)

/-- Dense low-coefficient vectors for the entries of the numbered Laplacian. -/
noncomputable def laplacianCoefficients {q : ℕ} (e : Fin q ≃ {v // v ≠ s})
    (x : Finset (Internal s t)) (r : H.RandomMasks w s t) (width : ℕ) :
    Table (CoeffArray (ZMod 2) width) q :=
  table fun i j => CoeffArray.fromPolynomial width (H.augLaplacian w s t x r (e i) (e j))

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianParityDeterminant

section BoundedTrialCollection

/-! Stop a list of reporting trials at a global output limit. The extra report detects overflow. -/

namespace BoundedEnumeration

structure Collection where
  words : Option (List (List Bool))
  reported : ℕ
  probes : ℕ

variable {U : Type*}

/-- Only the remaining quota plus one is requested from each trial. A failed trial stops the
whole traversal immediately. -/
def collect (trial : U → ℕ → Result) : List U → ℕ → Collection
  | [], _ => ⟨some [],0,0⟩
  | u :: us, cap =>
    let first := trial u (cap+1)
    let used := first.words.length
    if cap < used then ⟨none,used,first.probes⟩ else
      let rest := collect trial us (cap-used)
      ⟨rest.words.map (first.words ++ ·), used + rest.reported, first.probes + rest.probes⟩

end BoundedEnumeration

end BoundedTrialCollection

section HamiltonianAffineTrials

namespace DirectedHamiltonicity.Main.Multidigraph

open BoundedEnumeration AffinePrefixEnumeration FiniteSampling BirdDet.Tabulated

open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] {q N : ℕ}

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V) (order : Fin q ≃ Internal s t)

variable (rank : H.NonzeroCoeffs w s t ≃ Fin N) (r : H.RandomMasks w s t)

/-- Arithmetic decoding is followed by capped DFS on the affine rows. The mathematical
row-construction input can be supplied by any implementation generating those rows. -/
noncomputable def affineTrial (bits : CoinBlock (H.NonzeroCoeffs w s t)) (cap : ℕ) : Result :=
  match decodeRank rank bits with
  | none => ⟨[],0⟩
  | some a => search (viable (H.samplingSystem w s t order r fun i => (a i).val)) q [] cap

noncomputable def subsetOfBits (word : List Bool) : Finset (Internal s t) :=
  (numberedIndicator s t order).symm (bitsWord q word)

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianAffineTrials

section HamiltonianRankedTrials

namespace DirectedHamiltonicity.Main.Multidigraph

open Classical BoundedEnumeration EditGV897.Main AffinePrefixEnumeration FiniteSampling

open scoped BigOperators

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] {q N : ℕ}

variable (H : Multidigraph V E) (w : E → ℕ) (s t : V) (order : Fin q ≃ Internal s t)

variable (rank : H.NonzeroCoeffs w s t ≃ Fin N) (r : H.RandomMasks w s t)

def wordsByRank (eqs : Option (List (Equation q))) : List (List Bool) :=
  eqs.elim [] (fun E => (List.range (affineCount E)).map (rankedSolution E))

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianRankedTrials

section HamiltonianStreamedParity

namespace DirectedHamiltonicity.Main.Multidigraph

open FiniteSampling BoundedEnumeration BirdDet.Tabulated

open scoped BigOperators

variable {n : ℕ} {E : Type} [Fintype E] (H : Multidigraph (Fin n) E) (w : E → ℕ) (s t : Fin n)

/-- Increasing order of the rows and columns left after deleting the source. -/
def reducedOrder (s : Fin n) : Fin ((Finset.univ.filter (fun v : Fin n => v ≠ s)).card) ≃ {v // v ≠ s} :=
  ((Finset.univ.filter (fun v : Fin n => v ≠ s)).orderIsoOfFin rfl).toEquiv.trans
    (Equiv.subtypeEquivRight fun _ => by simp)

noncomputable def streamedEstimate (W m : ℕ) (target : List Bool) (r : H.RandomMasks w s t)
    (tape : Fin m → CoinBlock (H.NonzeroCoeffs w s t)) : ZMod 2 :=
  match readTarget ((n-1)*W) target with
  | none => 0
  | some b =>
    let ord := (internalOrder s t).symm
    let out := collect (H.affineTrial w s t ord (H.coefficientRank w s t) r) (List.ofFn tape) (12*m)
    out.words.elim 0 fun xs => ∑ x ∈ xs.toFinset.image (subsetOfBits s t ord),
      (determinant (H.laplacianCoefficients w s t (reducedOrder s) x r (b+1))).value.get ⟨b,by omega⟩

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianStreamedParity

section HamiltonianInputEstimator

namespace DirectedHamiltonicity.Main.Multidigraph

open Classical FiniteSampling

variable {n m : ℕ} (H : Multidigraph (Fin n) (Fin m)) (w : Fin m → ℕ) (s t : Fin n)

/-- The weight bound used by the computation comes from the arc table itself. -/
def inputMaxWeight (w : Fin m → ℕ) : ℕ := Finset.univ.sup w

theorem le_inputMaxWeight (w : Fin m → ℕ) (e : Fin m) : w e ≤ inputMaxWeight w :=
  Finset.le_sup (Finset.mem_univ e)

 def coinAt (coins : List Bool) (i : ℕ) := coins[i]?.getD false

/-- The estimator takes the graph, the remaining target field, and a single finite coin
string. It determines all degree and weight parameters from the actual input. -/
noncomputable def inputEstimator (target coins : List Bool) : Bool :=
  let G := H.normalizedGraph w s t (le_inputMaxWeight w)
  let p := H.normalizedWeight w s t (le_inputMaxWeight w)
  let trials := samplingBlockSize n (G.samplingDegree p)*(n+4)
  let z := G.parityCoinBlocks p s t (G.orderedMaskIndex p s t) trials fun i => coinAt coins i.val
  decide (G.streamedEstimate p s t (inputMaxWeight w) trials target z.1 z.2 ≠ 0)

end DirectedHamiltonicity.Main.Multidigraph

end HamiltonianInputEstimator


