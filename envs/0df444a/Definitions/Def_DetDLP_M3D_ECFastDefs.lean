-- Prove2me | Definitions.Def_DetDLP_M3D_ECFastDefs
-- name    : DetDLP_M3D_ECFastDefs
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T22:48:34.99981+00:00
-- url     : https://prove2.me/theorems/feb4e883-538b-415b-97ec-8fe6999557a3
-- title:
--   Fast EC controller definitions
-- statement:
--   Lightweight controller and EC-query definitions for the M3D elliptic-curve protocol. This declaration-only interface avoids the full W3C and M3D definition graph while preserving the protocol data structures and transition function.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3_Driver
import Definitions.Def_DetDLP_M89_S1_Queries
import Definitions.Def_DetDLP_W1_Queries
import Definitions.Def_DetDLP_S8G_FpMomentPoly

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace DetDLP.M3D.Fast

open Groundwork OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.Computation

abbrev Wd := List Bool
abbrev St := List (List Bool)

namespace BlockLookup
open DetDLP_W1_Queries
abbrev Blocks := List (List Wd)
private def step (n : ℕ) (c : List Wd × Wd) (_ : Bool) : List Wd × Wd :=
  if c.2.headD false = true then ((first c.2 |>.take n) :: c.1, (more c.2).take n) else c
def decodeFrames (w : Wd) := (w.foldl (step w.length) ([],w)).1.reverse
def decodeBlocks (w : Wd) : Blocks := (decodeFrames w).map decodeFrames
private def inds {α : Type} (xs : List α) := List.range xs.length
private def off (bs : Blocks) (i : ℕ) := ((inds bs).map fun t => if t < i then (bs.getD t []).length else 0).sum
private def hit (bs : Blocks) (xs : List Wd) (i s k : ℕ) := if off bs i + (bs.getD i []).idxOf (xs.getD (2*i+s) []) = k then 1 else 0
private def cnt (bs : Blocks) (xs : List Wd) (k : ℕ) := ((inds bs).map fun i => hit bs xs i 0 k + hit bs xs i 1 k).sum
private def coords (bs : Blocks) := inds ([] :: [] :: bs.flatten)
def initRowCounts (bs : Blocks) (u : List Wd) (j : ℕ) : List ℤ := (coords bs).map fun k => (if k=j then 1 else 0) - (cnt bs u k : ℤ)
def shiftRowCounts (bs : Blocks) (x y : List Wd) : List ℤ := (coords bs).map fun k => (cnt bs y k : ℤ) - (cnt bs x k : ℤ)
end BlockLookup

namespace NewtonPoly
open S8G.FpMoment.Code
def largeCheck (p M : ℕ) := decide (67 < p ∧ 64 ≤ M ∧ 4096 * slots (width p) ≤ M - 1)
private def fac (r : List ℕ) (k : ℕ) := ((r.take k).map (· + 1)).prod
private def bin (r : List ℕ) (j t : ℕ) := fac r j / (fac r t * fac r (j-t))
private def square (s M k t : ℕ) := ((t : ℤ) - (1 + (-(s:ℤ)+k)*M)).natAbs ^ 2
private def sign (a : ℕ) : ℤ := if a % 2 = 0 then 1 else -1
private def coeff (r : List ℕ) (s M j : ℕ) : ℤ := ((r.take (j+1)).map fun t =>
  sign (j-t) * (bin r j t : ℤ) * (((r.take (2*s+1)).map fun k => square s M k t).prod : ℕ)).sum
private def scalar (m M : ℕ) (c : List ℕ) :=
  let r := List.range c.length
  (r.map fun j => coeff r (2*m) M j * (c.getD j 0 : ℤ)).sum
private def nz (z : ℤ) (prec : ℕ) := let a := z.natAbs
  decide (0 < a ∧ a / 2^prec = (a-1) / 2^prec)
def massPosWord (m M prec : ℕ) (w : Wd) : Bool := nz (scalar m M (w5_M6Sort.decode w)) prec
def repLabels (rep : Wd) := w5_M6Sort.decode (DetDLP_W1_Queries.first rep)
private def field (w tail : Wd) := true :: (DetDLP_W1_Queries.frame w ++ tail)
def updateWord (M N : ℕ) (rep : Wd) (row : List ℕ) (rhs : ℕ) : Wd :=
  field (countWord M) (field (countWord N) (field rep (field (encodeNatListBin row) (field (countWord rhs) [false]))))
end NewtonPoly

namespace NineOracleLoop
abbrev Word := Wd
private def tag3 (i : Fin 3) (x : Word) := if i = 0 then false :: x else true :: decide (i = 2) :: x
private def row (j : Fin 9) : Fin 3 := ⟨j.val / 3, by omega⟩
private def col (j : Fin 9) : Fin 3 := ⟨j.val % 3, by omega⟩
def tag9 (j : Fin 9) (x : Word) := tag3 (row j) (tag3 (col j) x)
def pairWord (x y : Word) := x.flatMap (fun b => [true,b]) ++ [false] ++ y
def LoopRuns (step : Word → Word) (call : Word → Word → Prop) : ℕ → Word → Word → Word → ℕ → Prop :=
  Nat.rec (fun _ _ _ _ => False) (fun _ prev st ans out n =>
    (step (pairWord st ans) = true :: out ∧ (pairWord st ans).length ≤ n ∧ out.length ≤ n) ∨
    ∃ st' q ans', step (pairWord st ans) = false :: pairWord st' q ∧ (pairWord st ans).length ≤ n ∧
      (pairWord st' q).length ≤ n ∧ ans'.length ≤ n ∧ call q ans' ∧ prev st' ans' out n)
def NineCall (A : Fin 9 → PrimitiveMachine) (o : ∀ j, Fin (A j).tapeCount) (τ σ : ℝ) (w y : Word) :=
  ∃ j q, w = tag9 j q ∧ RunsWithin (A j) (o j) q y τ σ
end NineOracleLoop

/-- Canonical order-oracle request and scalar extraction. -/
def DetDLP_M3D_curve (w : Wd) := encodeNatListBin ((w5_M6Sort.decode w).take 6)
def DetDLP_M3D_orderQuery (w : Wd) := M89S1.queryWord 0 (DetDLP_M3D_curve w) []
def DetDLP_M3D_scalar (w : Wd) := (w5_M6Sort.decode w).getD 0 0
def DetDLP_M3D_dispatch (input answer : Wd) :=
  NewtonPoly.largeCheck (DetDLP_M3D_scalar input) (DetDLP_M3D_scalar answer)

namespace ECQueries
open BlockLookup
def inputFields (w : Wd) : List ℕ := w5_M6Sort.decode w
def primeField (w : Wd) : ℕ := (inputFields w).getD 0 0
def curveWord (w : Wd) : Wd := encodeNatListBin ((inputFields w).take 6)
def firstPointCoords (w : Wd) : List ℕ := ((inputFields w).drop 6).take 3
def secondPointCoords (w : Wd) : List ℕ := ((inputFields w).drop 9).take 3
def planFrames (w : Wd) : List Wd := decodeFrames w
def planThreshold (w : Wd) : ℕ := (w5_M6Sort.decode ((planFrames w).getD 0 [])).getD 0 0
def planSeedBits (w : Wd) : Wd := (planFrames w).getD 1 []
def seedChunk (b : ℕ) (bits : Wd) (i : ℕ) : ℕ := Groundwork.PolyT.bval ((bits.drop (i*b)).take b).reverse
def seedNatList (b m : ℕ) (bits : Wd) : List ℕ := (List.range m).flatMap fun i =>
  [seedChunk b bits (4*i), seedChunk b bits (4*i+1), seedChunk b bits (4*i+2), seedChunk b bits (4*i+3)]
def seedNatWord (b m : ℕ) (bits : Wd) : Wd := encodeNatListBin (seedNatList b m bits)
end ECQueries

namespace ECQueryOps
open ECQueries BlockLookup
def elemWord (inp : Wd) (bs : Blocks) (j : ℕ) : Wd :=
  if j < bs.flatten.length then bs.flatten.getD j [] else
  encodeNatListBin (if j = bs.flatten.length then firstPointCoords inp else secondPointCoords inp)
def unitGenRow (bs : Blocks) : List ℕ :=
  (List.range ([] :: [] :: bs.flatten).length).map fun j => if j = bs.flatten.length then 1 else 0
def planWord (ans : Wd) := (decodeFrames ans).getD 1 []
def threshold (ans : Wd) := Groundwork.PolyT.bval ((decodeFrames (planWord ans).tail).getD 0 [])
def seedBits (ans : Wd) := (decodeFrames (planWord ans).tail).getD 1 []
def coord0 (b : ℕ) (w : Wd) := Groundwork.PolyT.bval (w.take b)
def readPoint (b : ℕ) (w : Wd) := encodeNatListBin [coord0 b w,coord0 b (w.drop b),coord0 b ((w.drop b).drop b)]
def readMany (b n : ℕ) (w : Wd) := (List.range n).map fun i => readPoint b (w.drop (i*(3*b)))
def prefixToTupleWords (b m : ℕ) (pre : Wd) :=
  (readMany b (2*m) pre,readMany b (2*m) (pre.drop (2*m*(3*b))))
def queryPayload (curve target constants seed blocks rep pfx : Wd) : Wd :=
  Encoding.encodeList id [curve, target, constants, seed, blocks, rep, pfx]
def nativePayload (b m M : ℕ) (inp plan blk rep pre : Wd) : Wd :=
  queryPayload (curveWord inp) (encodeNatListBin (firstPointCoords inp)) (encodeNatListBin [M,threshold plan])
    (seedNatWord b m (seedBits plan)) blk (encodeNatListBin (NewtonPoly.repLabels rep)) pre
end ECQueryOps

namespace ECStep
open BlockLookup NineOracleLoop ECQueries ECQueryOps
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev St := List (List Bool)
abbrev Wd := List Bool
def get (s : St) (i : ℕ) := s.getD i []
def inp (s : St) := get s 1
def ord (s : St) := get s 2
def plan (s : St) := get s 3
def blk (s : St) := get s 4
def idx (s : St) := PolyT.bval (get s 5)
def rep (s : St) := get s 6
def pre (s : St) := get s 7
def aux (s : St) := get s 8
def bs (s : St) := decodeBlocks (blk s)
def m (s : St) := (bs s).length
def b (s : St) := S8G.FpMoment.Code.width (primeField (inp s))
def M (s : St) := DetDLP_M3D_scalar (ord s)
def n (s : St) := (bs s).flatten.length + 2
def packState (ph j : ℕ) (i o p k r f a : Wd) : Wd :=
  false :: Encoding.encodeList id [countWord ph,i,o,p,k,countWord j,r,f,a]
def send (slot : Fin 9) (state q : Wd) : Wd := false :: pairWord state (tag9 slot q)
def fr (ws : St) := Encoding.encodeList id ws
def basis (s : St) := fr [curveWord (inp s),elemWord (inp s) (bs s) (idx s)]
def ints (M : ℕ) (row : List ℤ) := row.map fun z => if z < 0 then (M-z.natAbs%M)%M else z.natAbs%M
def inds (bs : Blocks) := List.range ([] :: [] :: bs.flatten).length
def idRep (bs : Blocks) : Wd :=
  let r := inds bs
  fr [encodeNatListBin (r.map (fun _ => 0)),fr (r.flatMap fun i => r.map fun j => if i=j then encodeIntBin 1 else encodeIntBin 0)]
def payload (s : St) (r f : Wd) := nativePayload (b s) (m s) (M s) (inp s) (plan s) (blk s) r f
def beginRoot (s : St) (r : Wd) := send 6 (packState 8 0 (inp s) (ord s) (plan s) (blk s) r [] []) (payload s r [])
def decompose (s : St) (j : ℕ) (r : Wd) := send 5
  (packState 6 j (inp s) (ord s) (plan s) (blk s) r [] [])
  (fr [fr [curveWord (inp s),elemWord (inp s) (bs s) j],planWord (plan s)])
def cutOrChild (s : St) (f : Wd) :=
  if f.length < 4*m s*(3*b s) then send 6
    (packState 8 3 (inp s) (ord s) (plan s) (blk s) (rep s) f []) (payload s (rep s) (f++[false]))
  else let xy := prefixToTupleWords (b s) (m s) f
       let row := ints (M s) (shiftRowCounts (bs s) xy.1 xy.2)
       send 8 (packState 10 0 (inp s) (ord s) (plan s) (blk s) (rep s) [] [])
         (NewtonPoly.updateWord (M s) (n s) (rep s) row 1)
def massPhase (s : St) (a : Wd) :=
  let pos := NewtonPoly.massPosWord (m s) (M s) (PolyT.bval ((decodeFrames (aux s)).getD 6 [])) a
  if idx s = 1 then
    if pos then cutOrChild s []
    else true :: countWord ((NewtonPoly.repLabels (rep s)).getD ((bs s).flatten.length+1) 0)
  else cutOrChild s (pre s ++ [!pos])
def case0 (s : St) (a : Wd) := if DetDLP_M3D_dispatch (inp s) a then send 2 (packState 2 0 (inp s) a [] [] [] [] []) (curveWord (inp s))
    else send 1 (packState 1 0 (inp s) a [] [] [] [] []) (inp s)
def case1 (_s : St) (a : Wd) := true :: a
def case2 (s : St) (a : Wd) := send 3 (packState 3 0 (inp s) (ord s) a [] [] [] []) a
def case3 (s : St) (a : Wd) := let blocks := decodeBlocks a
    send 8 (packState 4 0 (inp s) (ord s) (plan s) a [] [] [])
      (NewtonPoly.updateWord (M s) (blocks.flatten.length+2) (idRep blocks) (unitGenRow blocks) 1)
def case4 (s : St) (a : Wd) := decompose s 0 a
def case6 (s : St) (a : Wd) := send 8 (packState 7 (idx s) (inp s) (ord s) (plan s) (blk s) (rep s) [] [])
    (NewtonPoly.updateWord (M s) (n s) (rep s) (ints (M s) (initRowCounts (bs s) (decodeFrames a) (idx s))) 0)
def case7 (s : St) (a : Wd) := if idx s+1 < n s then decompose s (idx s+1) a else beginRoot s a
def case8 (s : St) (a : Wd) := send 7
  (packState 9 (if idx s = 0 then 1 else if idx s = 3 then 3 else 2)
    (inp s) (ord s) (plan s) (blk s) (rep s) (pre s) a) a
def case9 (s : St) (a : Wd) := massPhase s a
def round (s : St) (a : Wd) :=
  let ph := PolyT.bval (get s 0)
  if ph=0 then case0 s a else if ph=1 then case1 s a else if ph=2 then case2 s a else if ph=3 then case3 s a
  else if ph=4 then case4 s a else if ph=6 then case6 s a else if ph=7 then case7 s a
  else if ph=8 then case8 s a else if ph=9 then case9 s a else beginRoot s a
def ecStep (w : Wd) :=
  let st := first (true :: w)
  if st.headD true then send 0 (packState 0 0 st [] [] [] [] [] []) (DetDLP_M3D_orderQuery st)
  else round (decodeFrames st.tail) (more (true :: w))
end ECStep

namespace ECRun
open ECStep NineOracleLoop ECQueryOps ECQueries BlockLookup DetDLP_W1_Queries
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev Wd := List Bool
abbrev Runs (call : Wd → Wd → Prop) (fuel : ℕ) (st ans out : Wd) := ∃ n, NineOracleLoop.LoopRuns ECStep.ecStep call fuel st ans out n
structure Context where
  i : Wd
  o : Wd
  p : Wd
  k : Wd
namespace Context
variable (c : Context)
abbrev state (ph j : ℕ) (r : Wd) (f a : Wd := []) := ECStep.packState ph j c.i c.o c.p c.k r f a
abbrev s (ph j : ℕ) (r : Wd) (f a : Wd := []) : St := [countWord ph,c.i,c.o,c.p,c.k,countWord j,r,f,a]
abbrev blocks := decodeBlocks c.k
abbrev size := c.blocks.flatten.length+2
abbrev modulus := DetDLP_M3D_scalar c.o
abbrev decQ (j : ℕ) := ECStep.fr [ECStep.fr [curveWord c.i,elemWord c.i c.blocks j],planWord c.p]
abbrev updQ (j : ℕ) (r u : Wd) := NewtonPoly.updateWord c.modulus c.size r
  (ECStep.ints c.modulus (initRowCounts c.blocks (decodeFrames u) j)) 0
abbrev genQ := NewtonPoly.updateWord c.modulus c.size (ECStep.idRep c.blocks) (unitGenRow c.blocks) 1
abbrev query (r f : Wd) := nativePayload (S8G.FpMoment.Code.width (primeField c.i)) c.blocks.length
  c.modulus c.i c.p c.k r f
abbrev repWord {M N : ℕ} (s : w3_Rep M N) := encodeCosetRep (fun i => (s.1 i).val) s.2
abbrev width := S8G.FpMoment.Code.width (primeField c.i)
abbrev depth := 4*c.blocks.length*(3*c.width)
abbrev massBit (packet result : Wd) := NewtonPoly.massPosWord c.blocks.length c.modulus
  (PolyT.bval ((decodeFrames packet).getD 6 [])) result
abbrev cutQ (r f : Wd) :=
  let xy := prefixToTupleWords c.width c.blocks.length f
  NewtonPoly.updateWord c.modulus c.size r (ECStep.ints c.modulus (shiftRowCounts c.blocks xy.1 xy.2)) 1
end Context
section Native
variable {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
local notation "m₀" => blockCount (bitLen p)
local notation "M₀" => @Fintype.card _ (ecPointFintype E)
local notation "T₀" => hashThreshold p (M₀-1) m₀ M₀
noncomputable def canonical (S : ECSeed p m₀) (B : Fin m₀ → List E.toAffine.Point) (P Q : E.toAffine.Point) : Context :=
  ⟨encodeECDLPInput p E P Q,encodeNatListBin [M₀],
    Encoding.encodeList id [encodeCurveInput p E,(true :: Encoding.encodeList id [countWord T₀,List.ofFn (M89S1.ecBits S)])],encodeECFactorBlocks B⟩
noncomputable def nativeQ (S : ECSeed p m₀) (B : Fin m₀ → List E.toAffine.Point) (P Q : E.toAffine.Point)
    (nz : 0 < M₀) (s : w3_Rep M₀ (IndexedFactorBase.mk B).totalCoords) (f : Wd) : w3_Query :=
  { V := E.toAffine.Point, M := M₀, nz := ⟨Nat.ne_of_gt nz⟩, b := bitLen p, m := m₀,
    k := Nat.clog 2 (2*T₀), FB := ⟨B⟩, P := P, y := s.1,
    code := w3_tupleWord ⟨B⟩ (fun A => (pointCoords A).flatMap (w3_bits (bitLen p))),
    pre := f, input := (canonical E S B P Q).query (Context.repWord s) f,
    addr := fun i r => match (B i).get r with
      | .zero => 2*T₀
      | .some x z _ => let sign := decide (z.val%2=1); let ab := S i sign
                       ((ab.1.val+1)*x.val+ab.2.val)%p + (if sign then T₀ else 0) }
end Native
namespace Bounds
open ECStep NineOracleLoop DetDLP_W1_Queries
abbrev BoundedCall (L : ℕ) (call : Wd → Wd → Prop) (q y : Wd) := call q y ∧ y.length ≤ L
def StateBounded (i : Wd) (L d : ℕ) (st : Wd) : Prop := st = i ∨
  ∃ ph j o p k r f a, st = ECStep.packState ph j i o p k r f a ∧ ph ≤ 10 ∧ j ≤ d+3 ∧
    o.length ≤ L ∧ p.length ≤ L ∧ k.length ≤ L ∧ r.length ≤ L ∧ f.length ≤ d ∧ a.length ≤ L
def inputBound (i L fuel : ℕ) := 200*(i+L+fuel+1)
def roundLimit (k l : ℕ) := l+k*(3*l+3)^k
end Bounds
namespace Assembly
open ECStep NineOracleLoop M89S1
abbrev Oracle := (A : PrimitiveMachine) × Fin A.tapeCount
def bank (order scan prep enum dec build contract update : Oracle) : Fin 9 → Oracle :=
  ![order,scan,prep,enum,enum,dec,build,contract,update]
abbrev Calls (B : Fin 9 → Oracle) (τ σ : ℝ) := NineOracleLoop.NineCall (fun j => (B j).1) (fun j => (B j).2) τ σ
section Trace
variable (c : Context) (q : w3_Query) (z : w3_Label q.M q.FB.totalCoords)
local notation "Rep" => w3_Rep q.M q.FB.totalCoords
local notation "rwrd" => Context.repWord
def request (s : Rep) (pre : Wd) : w3_Query :=
  {q with y := s.1, pre, input := c.query (rwrd s) pre}
end Trace
end Assembly
end ECRun

namespace Stage2Trace
variable {M N : ℕ} [NeZero M]
def Invariant (z : w3_Label M N) (s : w3_Rep M N) : Prop :=
  IsModularLatticeBasis M s.2 ∧ z ∈ w3_coset s
end Stage2Trace

end DetDLP.M3D.Fast


