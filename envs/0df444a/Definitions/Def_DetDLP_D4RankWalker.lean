-- Prove2me | Definitions.Def_DetDLP_D4RankWalker
-- name    : DetDLP_D4RankWalker
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:35:21.145324+00:00
-- url     : https://prove2.me/theorems/26cf9d65-f7c0-4f2b-9f6b-d7acbf425efb
-- title:
--   Adaptive 64-child padded-rank worklist walker
-- statement:
--   A depth-bounded Appendix D.4 traversal uses two node requests for each expansion. The prepared configuration includes the bounded schedule, root item and rank budget. The worklist preserves boundary pin identifiers and composes source-to-current port permutations; the accumulator uses the canonical residue multiplier. A separate mathematical choice tree formalizes the padded-rank decoding order.
-- source:
--   M14 rank-walker specification; Appendix D.4 node and child wire records, D4RankCode.Tree.read, and the M89 oracle-loop protocol.

import Definitions.Def_DetDLP_D4RankCode
import Definitions.Def_DetDLP_D4NodeQuery
import Definitions.Def_DetDLP_F9A2_BMul
import Definitions.Def_DetDLP_D3StoppedSchedule

set_option autoImplicit false
namespace DetDLP.D4RankWalker
open AppendixD4 DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Groundwork.PolyT (bval)

abbrev Wd := List Bool
def pack (xs : List Wd) : Wd := Encoding.encodeList id xs
abbrev Scan := Bool × Bool × Wd × List Wd
def scan (s : Scan) (b : Bool) : Scan :=
  bif s.1 then bif s.2.1 then s else (false,true,b :: s.2.2.1,s.2.2.2)
  else bif s.2.1 then bif b then (true,false,s.2.2.1,s.2.2.2)
    else (false,false,[],s.2.2.1.reverse :: s.2.2.2)
  else bif b then (false,true,[],s.2.2.2) else (true,true,[],s.2.2.2)
def unpack (w : Wd) : List Wd := (w.foldl scan (false,false,[],[])).2.2.2.reverse
def fld (w : Wd) (i : ℕ) := (unpack w).getD i []
def num (w : Wd) (i : ℕ) := bval (fld w i)
def ints := w5_M6Sort.decode

/-- The wire port map runs from source ports to current ports. An absent map is identity. -/
def mapped (spec perm : Wd) : Wd :=
  let s := unpack spec
  let p := ints perm
  let q := if s.length < 3 then perm else
    encodeNatListBin ((ints (s.getD 2 [])).map fun i => p.getD i 0)
  pack [s.getD 0 [],s.getD 1 [],q]

/-- Host records retain the original pin number as well as the current vertex. -/
structure WorkItem where
  depth : ℕ
  G : Graph
  pins : List (ℕ × Fin G.nV)
  pCurr : ℕ
  vSpecs : Fin G.nV → Wd

def WorkItem.bits (i : WorkItem) := pack [countWord i.depth,i.G.encode,countWord i.pCurr,
  pack (i.pins.map fun (j,v) => encodeNatListBin [j,v.val]),pack (List.ofFn i.vSpecs)]

def root (G : Graph) {b : ℕ} (host : Fin b → Fin G.nV) (p : ℕ) (spec : Fin G.nV → Wd) : WorkItem :=
  ⟨0,G,List.ofFn (fun i => (i.val,host i)),p,spec⟩

def row (S d : ℕ) :=
  let a := D3Stopped.shift S d
  pack [countWord a,countWord (D3Stopped.width S d),List.replicate (64^a) true]
/-- Exponents and palettes which must be expanded in unary are present in the context.
This bounds every allocation of the raw transition, including on malformed words. -/
def context (S m p guard l : ℕ) (fBits : Wd) :=
  let D := Nat.clog 32 (4*m)
  pack [countWord D,countWord (D3Stopped.threshold S),List.replicate (guard+p) true,
    List.replicate l true,fBits,pack ((List.range D).map (row S))]

def rowAt (ctx i : Wd) := fld (fld ctx 5) (num i 0)
def small (ctx i : Wd) : Bool := decide (num ctx 0 ≤ num i 0) || decide (num (fld i 1) 1 ≤ num ctx 1)
def ask (ctx i : Wd) (j : ℕ) :=
  let r := rowAt ctx i
  let host := encodeNatListBin ((unpack (fld i 3)).map fun pin => num pin 1)
  pack [pack [fld i 1,fld r 0,fld r 2,host],encodeNatListBin [num r 0,num r 1,num i 2,(fld ctx 3).length],
    fld ctx 4,countWord j]

def childWord (i : Wd) (p : ℕ) (ch : Wd) :=
  let records := unpack (fld ch 1)
  let keys := records.map fun r => if (fld r 0).headD false then 0 else num r 1 + 1
  let pins := ((unpack (fld i 3)).filter fun h => keys.any fun k => k == num h 1 + 1).map
    fun h => encodeNatListBin [num h 0, keys.idxOf (num h 1 + 1)]
  let vs := records.map fun r => if (fld r 0).headD false then pack [[true],fld r 2]
    else mapped (fld (fld i 4) (num r 1)) (fld r 2)
  pack [countWord (num i 0 + 1),fld ch 0,countWord p,pack pins,pack vs]

def children (i ans : Wd) : List Wd :=
  let p := num (fld ans 0) 4
  (List.range 64).map fun g => childWord i p (fld (fld ans 3) g)

/-- On valid schedule rows the clamp is inactive. It prevents binary exponents in a
malformed row from requesting exponential intermediate words. -/
def pow2 (fuel : Wd) (k : ℕ) := bval ((fuel.take k).map (fun _ => false) ++ [true])
def product (ctx i acc ans : Wd) : Wd :=
  let r := rowAt ctx i
  let a := num r 0; let u := num r 1; let M := num (fld i 1) 1
  let q := fld ctx 2; let f := fld ctx 4
  let loc := num i 2 + (6 * mult M u * pow2 (fld r 2) a + 4*M*(a+1))
  let fac := pow2 q (q.length-loc); let modulus := pow2 q q.length
  let wt := encodeNatListBin ((ints (fld ans 1)).map fun v => v*fac % modulus)
  F9A2.bMulRaw (pack [modulus.bits,fld ctx 3,f.map (fun _ => true),
    encodeNatListBin (f.map fun b => if b then 1 else 0),acc,wt])

/-- Prepared root state. Packets use `[true,descriptor]`; a core source uses `[false,source]`.
The final list is in depth-first visitation order. -/
def oneWord (ctx : Wd) := encodeNatListBin ((List.range ((fld ctx 3).length * (fld ctx 4).length)).map
  fun k => if k = 0 then 1 else 0)
def start (ctx : Wd) (i : WorkItem) (b u : ℕ) :=
  pack [[],ctx,pack [i.bits],pack [],countWord b,countWord u,oneWord ctx]

def pair (st q : Wd) := DetDLP_W1_Queries.frame st ++ q
def issue (st q : Wd) := false :: pair st q
/-- Each stopped prefix is drained inside one local step, not by dummy calls to the oracle. -/
def dispatch (ctx : Wd) (todo done_ : List Wd) (b u : ℕ) (acc : Wd) : Wd :=
  let k := (todo.map (small ctx)).idxOf false
  let pending := todo.drop k
  let done' := done_ ++ todo.take k
  if pending.isEmpty then
    if u = 0 then true :: true :: pack [acc,pack done'] else [true,false]
  else issue (pack [[true],ctx,pack pending,pack done',countWord b,countWord u,acc])
    (ask ctx (pending.headD []) 0)

def digitWidth (n : ℕ) := (n-1).size
/-- The radix itself has at most one more bit than the count word. -/
def countPhase (ctx : Wd) (todo done_ : List Wd) (b u : ℕ) (acc ans : Wd) :=
  let n := bval ans; let w := digitWidth n; let radix := 2^w; let d := u % radix
  if w ≤ b ∧ d < n then
    issue (pack [[false],ctx,pack todo,pack done_,countWord (b-w),countWord (u / radix),acc])
      (ask ctx (todo.headD []) (d+1))
  else [true,false]

def walkerStep (input : Wd) : Wd :=
  let st := first (true :: input); let ans := more (true :: input)
  let phase := fld st 0; let ctx := fld st 1
  let todo := unpack (fld st 2); let done_ := unpack (fld st 3)
  let b := num st 4; let u := num st 5; let acc := fld st 6
  if phase.isEmpty then dispatch ctx todo done_ b u acc
  else if phase.headD false then countPhase ctx todo done_ b u acc ans
  else let i := todo.headD []
       dispatch ctx (children i ans ++ todo.tail) done_ b u (product ctx i acc ans)

/-- A mathematical node response in the oracle's own digit order. -/
structure WalkerStep where
  n : ℕ
  branch : Fin n → Wd

/-- The continuation carries the whole pending forest. A node budget (not a depth budget)
is consumed on each expansion, so the siblings do not share a decreasing depth counter. -/
def unrollAux (ctx : Wd) (stepFn : Wd → WalkerStep) : ℕ → List Wd → List Wd → Wd → D4RankCode.Tree Wd
  | fuel,todo,done_,acc =>
    let k := (todo.map (small ctx)).idxOf false
    let todo' := todo.drop k; let done' := done_ ++ todo.take k
    match todo' with
    | [] => .leaf (pack [acc,pack done'])
    | i :: tail => match fuel with
      | 0 => .choice 0 Fin.elim0
      | fuel+1 => let s := stepFn i
                  .choice s.n fun d => let ans := s.branch d
                                       unrollAux ctx stepFn fuel (children i ans ++ tail) done' (product ctx i acc ans)

def unrollRankTree (ctx : Wd) (i : WorkItem) (stepFn : Wd → WalkerStep) :=
  unrollAux ctx stepFn (64^(num ctx 0)) [i.bits] [] (oneWord ctx)

end DetDLP.D4RankWalker


