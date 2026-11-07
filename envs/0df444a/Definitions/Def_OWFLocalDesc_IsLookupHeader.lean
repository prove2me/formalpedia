-- Prove2me | Definitions.Def_OWFLocalDesc_IsLookupHeader
-- name    : OWFLocalDesc_IsLookupHeader
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:42.316185+00:00
-- url     : https://prove2.me/theorems/3bf1dc51-6c15-4983-bb09-275083dee33f
-- title:
--   A program for full-anchor lookup
-- statement:
--   **Full-anchor lookup** retains every point and uses the observed labels as tags. Its fixed program scans the anchor list sequentially, compares each stored point with the query, and returns the first matching tag, or $0$ if no point matches; it uses no sample-size or index input. Its running time on $U$ is polynomial in the lengths of the anchor list and the query.
--
--   A program $\sigma$ is a **lookup program** for the decoder $U$ if, on every anchor list made of tagged points of the query's length and on every tape,
--
--   1. whenever the run of $U$ on $\sigma$ halts, its output is the lookup answer, and
--   2. the run halts within a polynomial in the lengths of the anchor list and the query.
--
--   **Formalization Note** The paper fixes one such program; statements quantify over every program with properties 1 and 2. Property 2 is the polynomial running time stated on p.13; without it a slow but correct program would qualify. The helper `lookupAnswer` is the answer of the scan.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), §2.1, p.13

import Mathlib
import Definitions.Def_OWFLocalDesc_Decoder
set_option autoImplicit false

namespace OWFLocalDesc

/-- One scan step of full-anchor lookup with fuel: compare the next stored point with the query
`z`; on a match return its tag, otherwise move past the tag. -/
def lookupScan (z : List Bool) : ℕ → List Bool → Bool
  | 0, _ => false
  | fuel + 1, L =>
      if L.take z.length = z then L.getD z.length false
      else lookupScan z fuel (L.drop (z.length + 1))

/-- **The full-anchor lookup answer.** p.13: "Its fixed program scans the anchor list L_A
sequentially, compares each stored point with the query, and returns the first matching tag, or
zero if no point matches." -/
def lookupAnswer (L z : List Bool) : Bool := lookupScan z L.length L

/-- **A header for the full-anchor lookup program.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), §2.1, p.13:
"Its fixed program scans the anchor list L_A sequentially, compares each stored point with the query,
and returns the first matching tag, or zero if no point matches. The scan reaches the list's end
marker only when no stored point matches; it uses no sample-size or index input. Its running time
on U is polynomial in the lengths of the anchor list and the query; this bound covers the
comparisons, the read of the end marker and the simulation overhead."

`IsLookupHeader U σ` says that the program `σ` (empty payload), on every anchor list made of
tagged points of the query's length and every tape, (1) returns the lookup answer whenever it
halts, and (2) halts within a polynomial in the lengths of the anchor list and the query.

**Formalization Note.** The paper fixes one such program; the formalization quantifies over every
program with these two properties. Property (2) is the polynomial running time on `U` stated on
p.13; without it a slow but correct program would qualify. -/
def IsLookupHeader (U : Decoder) (σ : List Bool) : Prop :=
  (∀ (L w z : List Bool) (s : ℕ) (o : Option Bool), (z.length + 1) ∣ L.length →
      U.run σ L w z s = some o → o = some (lookupAnswer L z)) ∧
    ∃ c : ℕ, ∀ L w z : List Bool, (z.length + 1) ∣ L.length →
      ∃ s ≤ (L.length + z.length) ^ c + c, (U.run σ L w z s).isSome

end OWFLocalDesc


