-- Prove2me | Definitions.Def_CorrelatedAuctionComplexity_Main_BinaryCodec
-- name    : CorrelatedAuctionComplexity_Main_BinaryCodec
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:01.339078+00:00
-- url     : https://prove2.me/theorems/1e86bf05-6237-4204-a2ec-52765f6c4e15
-- title:
--   Binary codecs for rational auction instances and profiles
-- statement:
--   A nonnegative integer is encoded by its little-endian binary digits preceded by the unary length of those digits. Thus numeric magnitude has binary cost. A rational uses a signed binary numerator and a positive binary denominator. Auction records list the bidders' rational values, every allowed bid, every prior atom or weighted hyperedge, and all incidences. Profiles explicitly list rational probability weights in sorted bidder/type/bid order.
--
--   $$\text{decode}(s)=\text{some instance}\quad\text{only when its complete canonical record re-encodes to }s.$$
--
--   Malformed or truncated records are rejected. Decoders guard dimensions by input length before constructing arrays. Pure profile coordinates not in the marginal support are absent. A positive rational accuracy is a separate binary prefix for the variable-accuracy problems. These codecs make the finite representation in Sections 3.1–3.2 explicit; they do not constrain the real profiles used in the analytical lemmas.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Sections 3.1–3.3, pp. 8–12; Lemmas 15, 16, 19, 20, pp. 19–25 (PDF same pages); explicit bit-model convention

import Mathlib
import Definitions.Def_CorrelatedAuctionComplexity_Main_HDFPA
import Definitions.Def_CorrelatedAuctionComplexity_Main_DFPA

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main


abbrev Bits := List Bool

/-- Little-endian binary payload with unary bit-length prefix, not unary numeric encoding. -/
def natBits (n : ℕ) : Bits := (Nat.digits 2 n).map fun d => d = 1

def encodeNat (n : ℕ) : Bits :=
  List.replicate (natBits n).length true ++ false :: natBits n

def bitsNat (s : Bits) : ℕ := s.foldr (fun b n => (if b then 1 else 0) + 2*n) 0

def prefixLength : Bits → Option (ℕ × Bits)
  | [] => none
  | false :: s => some (0,s)
  | true :: s => do
    let (n,t) ← prefixLength s
    pure (n+1,t)

def readNat (s : Bits) : Option (ℕ × Bits) := do
  let (k,t) ← prefixLength s
  if k ≤ t.length then
    let p := t.take k
    let n := bitsNat p
    if natBits n = p then pure (n,t.drop k) else none
  else none

def unpackAux : ℕ → Bits → Option (List ℕ)
  | 0, s => if s = [] then some [] else none
  | k+1, s => if s = [] then some [] else do
    let (n,t) ← readNat s
    let ns ← unpackAux k t
    pure (n::ns)

def pack (ns : List ℕ) : Bits := ns.flatMap encodeNat

def unpack (s : Bits) : Option (List ℕ) := unpackAux s.length s

/-- Signed numerator and positive denominator are individually binary encoded. -/
def intCode (z : ℤ) : ℕ := if z < 0 then 2*z.natAbs+1 else 2*z.natAbs

def intDecode (z : ℕ) : ℤ := if z % 2 = 0 then (z/2 : ℕ) else -(z/2 : ℕ)

def ratCode (q : ℚ) : List ℕ := [intCode q.num,q.den-1]
def ratAt (ns : List ℕ) (j : ℕ) : ℚ :=
  (intDecode (ns.getD j 0) : ℚ) / (ns.getD (j+1) 0 + 1 : ℕ)

def encodeRat (q : ℚ) : Bits := pack (ratCode q)

/-- Pairing used by the reused machine-based search reduction. -/
def inputAnswer (s t : Bits) : List (Option (Bool ⊕ Bool)) :=
  s.map (some ∘ Sum.inl) ++ none :: t.map (some ∘ Sum.inr)

/-- Sorted numerical enumeration fixes every profile coordinate order. -/
def ordered (S : Finset ℚ) : List {q // q ∈ S} := S.attach.sort (· ≤ ·)

/-- A wire record of an HDFPA uses n incidence bits per edge and two fields per rational. -/
def encodeH {n : ℕ} (H : HDFPA (Fin n)) : Bits := pack (
  [n,H.bids.card,H.edges.length] ++
  ((H.bids.sort (· ≤ ·)).flatMap ratCode) ++
  ((List.finRange n).flatMap fun i => ratCode (H.value i)) ++
  (H.edges.flatMap fun e => (List.finRange n).map (fun i => if i ∈ e.participants then 1 else 0)
    ++ ratCode e.weight))

def decodeH (s : Bits) : Option (Σ n : ℕ, HDFPA (Fin n)) := do
  let ns ← unpack s
  let n := ns.getD 0 0
  let b := ns.getD 1 0
  let m := ns.getD 2 0
  if n ≤ ns.length ∧ b ≤ ns.length ∧ m ≤ ns.length ∧
      ns.length = 3 + 2*b + 2*n + m*(n+2) then
    let H : HDFPA (Fin n) := {
      bids := ((List.range b).map fun j => ratAt ns (3+2*j)).toFinset
      value := fun i => ratAt ns (3+2*b+2*i.val)
      edges := (List.range m).map fun e => {
        participants := Finset.univ.filter fun i => ns.getD (3+2*b+2*n+e*(n+2)+i.val) 0 = 1
        weight := ratAt ns (3+2*b+2*n+e*(n+2)+n) } }
    if encodeH H = s then pure ⟨n,H⟩ else none
  else none

def encodeD {n : ℕ} (A : DFPA (Fin n)) : Bits := pack (
  [n,A.bids.card,A.prior.length] ++ ((A.bids.sort (· ≤ ·)).flatMap ratCode) ++
  (A.prior.flatMap fun d => ((List.finRange n).flatMap fun i => ratCode (d.value i)) ++ ratCode d.mass))

def decodeD (s : Bits) : Option (Σ n : ℕ, DFPA (Fin n)) := do
  let ns ← unpack s
  let n := ns.getD 0 0
  let b := ns.getD 1 0
  let m := ns.getD 2 0
  if n ≤ ns.length ∧ b ≤ ns.length ∧ m ≤ ns.length ∧
      ns.length = 3 + 2*b + m*(2*n+2) then
    let A : DFPA (Fin n) := {
      bids := ((List.range b).map fun j => ratAt ns (3+2*j)).toFinset
      prior := (List.range m).map fun d => {
        value := fun i => ratAt ns (3+2*b+d*(2*n+2)+2*i.val)
        mass := ratAt ns (3+2*b+d*(2*n+2)+2*n) } }
    if encodeD A = s then pure ⟨n,A⟩ else none
  else none

def encodeHProfile {n : ℕ} (H : HDFPA (Fin n)) (p : H.RatProfile) : Bits :=
  pack ((List.finRange n).flatMap fun i => (ordered H.bids).flatMap fun b => ratCode (p i b))

def decodeHProfile {n : ℕ} (H : HDFPA (Fin n)) (s : Bits) : Option H.RatProfile := do
  let ns ← unpack s
  if ns.length = 2*n*H.bids.card then
    let p : H.RatProfile := fun i b => ratAt ns (2*(i.val*H.bids.card + (ordered H.bids).idxOf b))
    if encodeHProfile H p = s then pure p else none
  else none

def typeOffset {n : ℕ} (A : DFPA (Fin n)) (i : Fin n) : ℕ :=
  ((List.finRange n).filter fun j => j.val < i.val).foldl (fun acc j => acc + (A.types j).card) 0

def encodeDProfile {n : ℕ} (A : DFPA (Fin n)) (p : A.RatProfile) : Bits :=
  pack ((List.finRange n).flatMap fun i => (ordered (A.types i)).flatMap fun v =>
    (ordered A.bids).flatMap fun b => ratCode (p i v b))

def decodeDProfile {n : ℕ} (A : DFPA (Fin n)) (s : Bits) : Option A.RatProfile := do
  let ns ← unpack s
  let count := ((List.finRange n).map fun i => (A.types i).card).sum
  if ns.length = 2*count*A.bids.card then
    let p : A.RatProfile := fun i v b => ratAt ns
      (2*((typeOffset A i + (ordered (A.types i)).idxOf v)*A.bids.card + (ordered A.bids).idxOf b))
    if encodeDProfile A p = s then pure p else none
  else none

/-- An accuracy prefix is a signed-numerator field and positive-denominator field. -/
def withAccuracy (ε : ℚ) (s : Bits) : Bits := encodeRat ε ++ s

def splitAccuracy (s : Bits) : Option (ℚ × Bits) := do
  let (a,t) ← readNat s
  let (b,r) ← readNat t
  let q := (intDecode a : ℚ) / (b+1 : ℕ)
  if ratCode q = [a,b] then pure (q,r) else none

end CorrelatedAuctionComplexity.Main


