-- Prove2me | Definitions.Def_DetDLP_D4WalkerTranscript
-- name    : DetDLP_D4WalkerTranscript
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:48:39.177357+00:00
-- url     : https://prove2.me/theorems/8d92e6f7-50bb-4c60-90e9-6aac63a0f56c
-- title:
--   Visited requests and message length in the D.4 rank walk
-- statement:
--   For one padded rank, record only the actual count and branch requests, with their suspended configurations and replies. The size parameter is the maximum framed message length, including the initial and final words.
-- source:
--   M14 padded-rank walker, oracle trace and resource contract.

import Definitions.Def_DetDLP_D4RankWalker
set_option autoImplicit false
namespace DetDLP.D4RankWalker
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
abbrev Call := Wd × Wd × Wd

def phaseState (tag : Wd) (ctx : Wd) (todo done_ : List Wd) (b u : ℕ) (acc : Wd) :=
  pack [tag,ctx,pack todo,pack done_,countWord b,countWord u,acc]
/-- Only the queries on this particular input rank are listed, in execution order. -/
def calls (ctx : Wd) (F : Wd → WalkerStep) : ℕ → List Wd → List Wd → ℕ → ℕ → Wd → List Call
  | fuel,todo,done_,b,u,acc =>
    let k := (todo.map (small ctx)).idxOf false
    let pending := todo.drop k; let done' := done_ ++ todo.take k
    match pending, fuel with
    | i :: tail, fuel+1 =>
      let s := F i; let w := digitWidth s.n; let d := u % 2^w
      let count : Call := (phaseState [true] ctx pending done' b u acc,ask ctx i 0,countWord s.n)
      if w ≤ b then if hd : d < s.n then
        let ans := s.branch ⟨d,hd⟩
        count :: (phaseState [false] ctx pending done' (b-w) (u/2^w) acc,ask ctx i (d+1),ans) ::
          calls ctx F fuel (children i ans ++ tail) done' (b-w) (u/2^w) (product ctx i acc ans)
      else [count] else [count]
    | _, _ => []

def tag (o : Option Wd) := o.elim [false] (fun w => true :: w)
def runCalls (ctx : Wd) (root : WorkItem) (F : Wd → WalkerStep) (b u : ℕ) :=
  calls ctx F (64^(num ctx 0)) [root.bits] [] b u (oneWord ctx)
def span (e : Call) := max (pair e.1 e.2.1).length (pair e.1 e.2.2).length
def maxLen (initial output : Wd) (cs : List Call) :=
  max (max (pair initial []).length output.length) ((cs.map span).foldr max 0)
end DetDLP.D4RankWalker


