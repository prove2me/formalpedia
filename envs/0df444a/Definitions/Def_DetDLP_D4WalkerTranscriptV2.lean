-- Prove2me | Definitions.Def_DetDLP_D4WalkerTranscriptV2
-- name    : DetDLP_D4WalkerTranscriptV2
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T10:09:18.888397+00:00
-- url     : https://prove2.me/theorems/3aaaba7a-2178-4698-8d6d-22a8deb31d4e
-- title:
--   Padded walker transcript and rank trace
-- statement:
--   A rank trace records, in depth-first visitation order, the node and its returned coefficient word for every active expansion. The transcript separately tracks the accumulated raw coefficient product and the sum of local losses, so a terminal successful word can be interpreted as one guard power of two multiplied by the product of all raw node weights.

import Definitions.Def_DetDLP_D4WalkerTranscript
import Definitions.Def_DetDLP_D4RankWalkerV2
set_option autoImplicit false
namespace DetDLP.D4RankWalker
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace


def phaseStateV2 (tag : Wd) (ctx : Wd) (todo done_ : List Wd) (b u : ℕ) (acc : Wd) (lossSum : ℕ) :=
  pack [tag,ctx,pack todo,pack done_,countWord b,countWord u,acc,countWord lossSum]
/-- Only the queries on this particular input rank are listed, in execution order. -/
def callsV2 (ctx : Wd) (F : Wd → WalkerStep) : ℕ → List Wd → List Wd → ℕ → ℕ → Wd → ℕ → List Call
  | fuel,todo,done_,b,u,acc,lossSum =>
    let k := (todo.map (small ctx)).idxOf false
    let pending := todo.drop k; let done' := done_ ++ todo.take k
    match pending, fuel with
    | i :: tail, fuel+1 =>
      let s := F i; let w := digitWidth s.n; let d := u % 2^w
      let count : Call := (phaseStateV2 [true] ctx pending done' b u acc lossSum,ask ctx i 0,countWord s.n)
      if w ≤ b then if hd : d < s.n then
        let ans := s.branch ⟨d,hd⟩
        count :: (phaseStateV2 [false] ctx pending done' (b-w) (u/2^w) acc lossSum,ask ctx i (d+1),ans) ::
          callsV2 ctx F fuel (children i ans ++ tail) done' (b-w) (u/2^w) (productV2 ctx acc ans) (lossSum + stepLoss ctx i)
      else [count] else [count]
    | _, _ => []

def runCallsV2 (ctx : Wd) (root : WorkItem) (F : Wd → WalkerStep) (b u : ℕ) :=
  callsV2 ctx F (64^(num ctx 0)) [root.bits] [] b u (oneWord ctx) 0

/-- Independent rank trace: neither weights, encodings of accumulated products, nor
losses enter the branch-selection recurrence. -/
def branchTrace (ctx : Wd) (F : Wd → WalkerStep) : ℕ → List Wd → List Wd → ℕ → ℕ → Option (List (Wd × Wd) × List Wd)
  | fuel,todo,done_,b,u =>
    let k := (todo.map (small ctx)).idxOf false
    let pending := todo.drop k; let done' := done_ ++ todo.take k
    match pending with
    | [] => if u = 0 then some ([],done') else none
    | i :: tail => match fuel with
      | 0 => none
      | fuel+1 => let s := F i; let w := Nat.clog 2 s.n; let d := u % 2^w
                  if w ≤ b then if hd : d < s.n then
                    let ans := s.branch ⟨d,hd⟩
                    (branchTrace ctx F fuel (children i ans ++ tail) done' (b-w) (u/2^w)).map
                      fun z => ((i,ans) :: z.1,z.2)
                  else none else none

open Polynomial ResidualScalarOracle
/-- Interpret raw row-major integer coefficients directly in the target ring. This also
handles a node answering at a different precision from the target modulus. -/
noncomputable def rawWeight (f : ℤ[X]) (l q : ℕ) (ans : Wd) : B f l q :=
  AdjoinRoot.mk _ (∑ j : Fin l, monomial j.val (AdjoinRoot.mk _
    (∑ i : Fin f.natDegree, monomial i.val (((ints (fld ans 1)).getD (j.val*f.natDegree+i.val) 0 : ℕ) : ZMod (2^q)))))

/-- Mathematical local loss, evaluated at the node's depth without a wire clamp. -/
def nodeLoss (S : ℕ) (i : Wd) := AppendixD4.loss (num (fld i 1) 1)
  (D3Stopped.shift S (num i 0)) (D3Stopped.width S (num i 0)) 0

end DetDLP.D4RankWalker


