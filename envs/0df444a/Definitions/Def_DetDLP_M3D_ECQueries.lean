-- Prove2me | Definitions.Def_DetDLP_M3D_ECQueries
-- name    : DetDLP_M3D_ECQueries
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T11:51:43.935915+00:00
-- url     : https://prove2.me/theorems/2f239b78-a68e-4d5c-9f41-2e85e369e3b5
-- title:
--   EC query wire-word helpers
-- statement:
--   Polynomial-time wire-word helpers for elliptic-curve queries, plan seed conversion, and tuple-prefix splitting.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3C_BlockLookup

set_option autoImplicit false
namespace DetDLP.M3D.ECQueries
open Groundwork OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Decode the top-level natural-number fields of the canonical EC-DLP input. -/
def inputFields (w : List Bool) : List ℕ := w5_M6Sort.decode w
/-- The prime field modulus in an EC-DLP input. -/
def primeField (w : List Bool) : ℕ := (inputFields w).getD 0 0
/-- The curve portion is the first six canonical natural fields. -/
def curveWord (w : List Bool) : List Bool := encodeNatListBin ((inputFields w).take 6)
/-- The first supplied affine point's canonical coordinates. -/
def firstPointCoords (w : List Bool) : List ℕ := ((inputFields w).drop 6).take 3
/-- The second supplied affine point's canonical coordinates. -/
def secondPointCoords (w : List Bool) : List ℕ := ((inputFields w).drop 9).take 3

/-- Affine negation has coordinates `(x,p-y mod p)`; infinity is fixed. -/
def negateCoords (p : ℕ) (v : List ℕ) : List ℕ :=
  if v.getD 0 1 = 1 then [1,0,0]
  else [0, v.getD 1 0, (p - v.getD 2 0) % p]
/-- The target `-Q` represented as the canonical coordinate list. -/
def negativeSecondPointCoords (w : List Bool) : List ℕ :=
  negateCoords (primeField w) (secondPointCoords w)

/-- Decode a published plan word into its two framed components. -/
def planFrames (w : List Bool) : List (List Bool) := W3C.BlockLookup.decodeFrames w
/-- The deterministic threshold component of a plan. -/
def planThreshold (w : List Bool) : ℕ := (w5_M6Sort.decode ((planFrames w).getD 0 [])).getD 0 0
/-- The packed seed bits component of a plan. -/
def planSeedBits (w : List Bool) : List Bool := (planFrames w).getD 1 []
/-- Decode a big-endian ecBits coordinate chunk. `bval` reads low-order first,
    whereas `packBits` stores the most significant bit first. -/
def seedChunk (b : ℕ) (bits : List Bool) (i : ℕ) : ℕ :=
  Groundwork.PolyT.bval ((bits.drop (i*b)).take b).reverse
/-- Convert the 4m packed seed-coordinate chunks into the native EC query format:
    alpha is already stored as `val+1`, followed by beta `val`. -/
def seedNatList (b m : ℕ) (bits : List Bool) : List ℕ :=
  (List.range m).flatMap fun i =>
    [seedChunk b bits (4*i), seedChunk b bits (4*i+1),
      seedChunk b bits (4*i+2), seedChunk b bits (4*i+3)]
/-- Encode the decoded seed list as required by `w3_ecQueries`. -/
def seedNatWord (b m : ℕ) (bits : List Bool) : List Bool := encodeNatListBin (seedNatList b m bits)
def seedBitsWord (w : List Bool) (b m : ℕ) : List Bool :=
  seedNatWord b m (planSeedBits w)

/-- Return the j-th element of the native EC basis target sequence: `P`, `-Q`, then
    the two entries of each enumerated factor block. -/
def basisTargetCoords (P minusQ : List ℕ) (blocks : List (List (List Bool))) (j : ℕ) : List Bool :=
  if j = 0 then encodeNatListBin P
  else if j = 1 then encodeNatListBin minusQ
  else
    let k := j - 2
    let block := blocks.getD (k / 2) []
    block.getD (k % 2) []

/-- Canonical identity representative for the initial affine coset. -/
def initialRep (M N : ℕ) : List Bool := encodeCosetRep (fun _ : Fin N => 0) (1 : Matrix (Fin N) (Fin N) ℤ)
/-- A seven-field EC native-query payload matching `w3_ecQueries`. -/
def queryPayload (curve target constants seed blocks rep pfx : List Bool) : List Bool :=
  Encoding.encodeList id [curve, target, constants, seed, blocks, rep, pfx]
/-- Width of one encoded block tuple: m blocks, two points per block, three b-bit
    point coordinates. -/
def tupleWidth (m b : ℕ) : ℕ := 2*m*(3*b)
/-- Split the full pair-code prefix into the X and Y tuple prefixes. -/
def splitTuplePrefix (m b : ℕ) (pre : List Bool) : List (List Bool) :=
  let width := tupleWidth m b
  [pre.take width, (pre.drop width).take width]

variable {α : Type} [Enc α]
attribute [local fun_prop] Groundwork.PolyT.comp Groundwork.PolyT.fst Groundwork.PolyT.snd
  Groundwork.PolyT.const Groundwork.PolyT.map Groundwork.PolyT.take Groundwork.PolyT.drop
  Groundwork.PolyT.getD Groundwork.PolyT.length Groundwork.PolyT.prodMk Groundwork.PolyT.mod
  Groundwork.PolyT.decide_eq Groundwork.PolyT.decide_lt Groundwork.PolyT.flatMap
  Groundwork.PolyT.bval' DetDLP_W1_Queries.frame_poly w5_M6Sort.encode_poly w5_M6Sort.decode_poly
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f
  P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_ite__226169acf219
  W3C.BlockLookup.decodeFrames_poly

@[fun_prop] theorem inputFields_poly : Groundwork.PolyT inputFields := by
  unfold inputFields; fun_prop
@[fun_prop] theorem primeField_poly : Groundwork.PolyT primeField := by
  unfold primeField; fun_prop
@[fun_prop] theorem curveWord_poly : Groundwork.PolyT curveWord := by
  unfold curveWord; fun_prop
@[fun_prop] theorem firstPointCoords_poly : Groundwork.PolyT firstPointCoords := by
  unfold firstPointCoords; fun_prop
@[fun_prop] theorem secondPointCoords_poly : Groundwork.PolyT secondPointCoords := by
  unfold secondPointCoords; fun_prop
@[fun_prop] theorem negateCoords_poly {p : α → ℕ} {v : α → List ℕ}
    (hp : Groundwork.PolyT p) (hv : Groundwork.PolyT v) :
    Groundwork.PolyT fun x => negateCoords (p x) (v x) := by
  unfold negateCoords; fun_prop
@[fun_prop] theorem negativeSecondPointCoords_poly : Groundwork.PolyT negativeSecondPointCoords := by
  unfold negativeSecondPointCoords; fun_prop
@[fun_prop] theorem planFrames_poly : Groundwork.PolyT planFrames := by
  unfold planFrames; exact W3C.BlockLookup.decodeFrames_poly Groundwork.PolyT.id'
@[fun_prop] theorem planThreshold_poly : Groundwork.PolyT planThreshold := by
  unfold planThreshold; fun_prop
@[fun_prop] theorem planSeedBits_poly : Groundwork.PolyT planSeedBits := by
  unfold planSeedBits; fun_prop
@[fun_prop] theorem queryPayload_poly {c t k s b r p : α → List Bool}
    (hc : Groundwork.PolyT c) (ht : Groundwork.PolyT t) (hk : Groundwork.PolyT k)
    (hs : Groundwork.PolyT s) (hb : Groundwork.PolyT b) (hr : Groundwork.PolyT r)
    (hp : Groundwork.PolyT p) :
    Groundwork.PolyT fun x => queryPayload (c x) (t x) (k x) (s x) (b x) (r x) (p x) := by
  unfold queryPayload; simp only [Encoding.encodeList, id_eq, ← DetDLP_W1_Queries.frame_correct]; fun_prop

end DetDLP.M3D.ECQueries


