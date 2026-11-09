-- Prove2me | Definitions.Def_Pr6453_InvoiceEvents
-- name    : Pr6453_InvoiceEvents
-- status  : Definition
-- author  : @gustasmickus
-- created : 2026-11-08T16:15:30.765524+00:00
-- url     : https://prove2.me/theorems/13ece0e8-5131-4183-a50a-1c8e486975b5
-- title:
--   PR #6453: the event-level invoice of the word
-- statement:
--   The event-level invoice of the PR #6453 word.
--
--   `assemble` walks the word's events and accumulates the two counters exactly as `pricing.py` does: a `LOCAL` event adds the whole local helper histogram to the targets and the whole local paid histogram to the paid calls; a `QUERY` event adds $104$ paid jobs at rank $1$; a whole idle job adds $208$ paid jobs at rank $8s$, where $s$ is the number of idle leaves; an individual idle job adds $104$ at rank $16$; a normalisation is free. After the fold, each diagonal term adds $104$ productive fields at rank $1+8\sigma$, where $\sigma$ is the index sum of the term.
--
--   `wordEvents` records the census of the PR #6453 word in the only two fields the invoice reads — $18$ native calls, $17$ binary queries, $14$ whole idle jobs of sizes $2,2,2,2,2,2,2,2,3,3,4,4,7,7$, $2$ individual idle jobs of size $2$, and $20$ normalisations — and `wordDiagonal` records the $34$ index sums $0,2,\dots,2,3,\dots,4,\dots,7,\dots,9$ of its diagonal terms, as listed in `physical.main_targets`. Both are data extracted from the certificate, not assumptions about it.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4: assemble in research/p104-third-anchor-clean-mixed-root/pricing.py; census and diagonal sums from RESULT.json (physical.main_targets, physical.whole_idle_jobs).

/-
PR #6453: the event-level invoice.

`assemble` folds over the word's events; `wordEvents` and `wordDiagonal` are the census of the
PR #6453 word (18 `LOCAL`, 17 `QUERY`, 14 `IDLE` of sizes 2,3,4,7, 2 `IDLE_ONE`, 20 `LAMBDA`,
and 34 diagonal terms of index sums 0,2,3,4,7,9), in the only two fields the invoice reads.
-/
import Definitions.Def_Pr6453_Invoice

set_option autoImplicit false

namespace Pr6453

/-- The five event tags of the word. -/
inductive Tag : Type
  | local
  | query
  | idle
  | idleOne
  | lambda
  deriving DecidableEq, Repr

/-- An event, recorded by the only two fields the invoice reads. -/
structure Ev where
  tag : Tag
  size : ℕ
  deriving DecidableEq, Repr

/-- The fold of `pricing.py → assemble` over the events, plus the diagonal contribution. -/
def assemble (evs : List Ev) (diag : List ℕ) (helpers paidLoc : List (ℕ × ℕ)) : (ℕ → ℕ) × (ℕ → ℕ) :=
  let step : (ℕ → ℕ) × (ℕ → ℕ) → Ev → (ℕ → ℕ) × (ℕ → ℕ) := fun acc e =>
    match e.tag with
    | .local => (fun r => acc.1 r + countIn helpers r, fun r => acc.2 r + countIn paidLoc r)
    | .query => (acc.1, fun r => acc.2 r + (if r = 1 then 104 else 0))
    | .idle => (acc.1, fun r => acc.2 r + (if r = 8 * e.size then 208 else 0))
    | .idleOne => (acc.1, fun r => acc.2 r + (if r = 8 * e.size then 104 else 0))
    | .lambda => acc
  let base := evs.foldl step (fun _ => 0, fun _ => 0)
  (fun r => base.1 r + (diag.map fun s => if 1 + 8 * s = r then 104 else 0).sum, base.2)

/-- The census of the PR #6453 word, in the order the tags occur (`LOCAL` calls, then the
binary queries, then the idle jobs, then the normalisations). -/
def wordEvents : List Ev :=
  List.replicate 18 ⟨.local, 0⟩
    ++ List.replicate 17 ⟨.query, 0⟩
    ++ List.replicate 8 ⟨.idle, 2⟩
    ++ List.replicate 2 ⟨.idle, 3⟩
    ++ List.replicate 2 ⟨.idle, 4⟩
    ++ List.replicate 2 ⟨.idle, 7⟩
    ++ List.replicate 2 ⟨.idleOne, 2⟩
    ++ List.replicate 20 ⟨.lambda, 0⟩

/-- The index sums of the diagonal terms (`1 + 8·sum` is the target rank). -/
def wordDiagonal : List ℕ :=
  [0] ++ List.replicate 18 2 ++ [18] ++ List.replicate 4 3 ++ List.replicate 4 4
    ++ List.replicate 4 7 ++ List.replicate 2 9

end Pr6453


