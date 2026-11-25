-- Prove2me | Definitions.Def_DetDLP_D4RankWalkerV2
-- name    : DetDLP_D4RankWalkerV2
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T09:58:32.883222+00:00
-- url     : https://prove2.me/theorems/5265556e-92cc-44bb-8c90-f31fa4b3784d
-- title:
--   Guard-corrected padded rank walker
-- statement:
--   At each active node the walker multiplies by the unscaled coefficient word and adds the local dyadic loss to a binary counter. A successful leaf multiplies its coefficients by the single remaining power of two modulo the target precision.

import Definitions.Def_DetDLP_D4RankWalker

set_option autoImplicit false
namespace DetDLP.D4RankWalker
open AppendixD4 DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Groundwork.PolyT (bval)

/-- Exponents and palettes which must be expanded in unary are present in the context.
This bounds every allocation of the raw transition, including on malformed words. -/
def contextV2 (S m p guard l : ℕ) (fBits : Wd) :=
  let D := Nat.clog 32 (4*m)
  pack [countWord D,countWord (D3Stopped.threshold S),List.replicate (guard+p) true,
    List.replicate l true,fBits,pack ((List.range D).map (row S)),countWord guard]

/-- Accumulate raw factors in the fixed target ring, without dyadic rescaling. -/
def productV2 (ctx acc ans : Wd) : Wd :=
  let q := fld ctx 2; let f := fld ctx 4; let modulus := pow2 q q.length
  F9A2.bMulRaw (pack [modulus.bits,fld ctx 3,f.map (fun _ => true),
    encodeNatListBin (f.map fun b => if b then 1 else 0),acc,fld ans 1])

def stepLoss (ctx i : Wd) :=
  let r := rowAt ctx i; let a := num r 0; let u := num r 1; let M := num (fld i 1) 1
  6 * mult M u * pow2 (fld r 2) a + 4*M*(a+1)

/-- Shift only at the successful leaf, including when the root is stopped. -/
def finishWt (ctx acc : Wd) (lossSum : ℕ) :=
  let q := fld ctx 2; let fac := pow2 q (num ctx 6 - lossSum); let modulus := pow2 q q.length
  encodeNatListBin ((ints acc).map fun v => v * fac % modulus)

def startV2 (ctx : Wd) (i : WorkItem) (b u : ℕ) :=
  pack [[],ctx,pack [i.bits],pack [],countWord b,countWord u,oneWord ctx,countWord 0]

/-- Each stopped prefix is drained inside one local step, not by dummy calls to the oracle. -/
def dispatchV2 (ctx : Wd) (todo done_ : List Wd) (b u : ℕ) (acc : Wd) (lossSum : ℕ) : Wd :=
  let k := (todo.map (small ctx)).idxOf false
  let pending := todo.drop k
  let done' := done_ ++ todo.take k
  if pending.isEmpty then
    if u = 0 then true :: true :: pack [finishWt ctx acc lossSum,pack done'] else [true,false]
  else issue (pack [[true],ctx,pack pending,pack done',countWord b,countWord u,acc,countWord lossSum])
    (ask ctx (pending.headD []) 0)

def countPhaseV2 (ctx : Wd) (todo done_ : List Wd) (b u : ℕ) (acc ans : Wd) (lossSum : ℕ) :=
  let n := bval ans; let w := digitWidth n; let radix := 2^w; let d := u % radix
  if w ≤ b ∧ d < n then
    issue (pack [[false],ctx,pack todo,pack done_,countWord (b-w),countWord (u / radix),acc,countWord lossSum])
      (ask ctx (todo.headD []) (d+1))
  else [true,false]

def walkerStepV2 (input : Wd) : Wd :=
  let st := first (true :: input); let ans := more (true :: input)
  let phase := fld st 0; let ctx := fld st 1
  let todo := unpack (fld st 2); let done_ := unpack (fld st 3)
  let b := num st 4; let u := num st 5; let acc := fld st 6; let lossSum := num st 7
  if phase.isEmpty then dispatchV2 ctx todo done_ b u acc lossSum
  else if phase.headD false then countPhaseV2 ctx todo done_ b u acc ans lossSum
  else let i := todo.headD []
       dispatchV2 ctx (children i ans ++ todo.tail) done_ b u (productV2 ctx acc ans) (lossSum + stepLoss ctx i)

/-- The continuation carries the whole pending forest. A node budget (not a depth budget)
is consumed on each expansion, so the siblings do not share a decreasing depth counter. -/
def unrollAuxV2 (ctx : Wd) (stepFn : Wd → WalkerStep) : ℕ → List Wd → List Wd → Wd → ℕ → D4RankCode.Tree Wd
  | fuel,todo,done_,acc,lossSum =>
    let k := (todo.map (small ctx)).idxOf false
    let todo' := todo.drop k; let done' := done_ ++ todo.take k
    match todo' with
    | [] => .leaf (pack [finishWt ctx acc lossSum,pack done'])
    | i :: tail => match fuel with
      | 0 => .choice 0 Fin.elim0
      | fuel+1 => let s := stepFn i
                  .choice s.n fun d => let ans := s.branch d
                                       unrollAuxV2 ctx stepFn fuel (children i ans ++ tail) done' (productV2 ctx acc ans) (lossSum + stepLoss ctx i)

def unrollRankTreeV2 (ctx : Wd) (i : WorkItem) (stepFn : Wd → WalkerStep) :=
  unrollAuxV2 ctx stepFn (64^(num ctx 0)) [i.bits] [] (oneWord ctx) 0

end DetDLP.D4RankWalker


