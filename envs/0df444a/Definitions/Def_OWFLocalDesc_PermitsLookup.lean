-- Prove2me | Definitions.Def_OWFLocalDesc_PermitsLookup
-- name    : OWFLocalDesc_PermitsLookup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:32.292868+00:00
-- url     : https://prove2.me/theorems/2cccfe65-8734-4db9-8cf3-415d1a062a36
-- title:
--   A clock permits full-anchor lookup
-- statement:
--   A clock $t$ **permits full-anchor lookup** if, at every point length $n$, the lookup program halts within $t(n)$ steps on every list of $m(n)$ tagged $n$-bit points, every $n$-bit query and every public tape of length $t(n)$.
--
--   On a dataset in which every repeated point has the same label, the full-anchor certificate is then valid on every tape.
--
--   **Formalization Note** Point lengths are positive. The helper `fullAnchorList` is the anchor list $x_1y_1\cdots x_my_m$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), §2.1, p.13

import Mathlib
import Definitions.Def_OWFLocalDesc_Decoder
set_option autoImplicit false

namespace OWFLocalDesc

/-- The anchor list of the full-anchor certificate: every point followed by its tag,
`x_1 a_1 ⋯ x_m a_m` (p.13: "Full-anchor lookup retains A = [m] and uses the observed labels as
tags"). -/
def fullAnchorList {m n : ℕ} (x : Fin m → Fin n → Bool) (a : Fin m → Bool) : List Bool :=
  (List.ofFn fun i => List.ofFn (x i) ++ [a i]).flatten

/-- **A clock permits full-anchor lookup.** Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), §2.1, p.13: "A clock
permits full-anchor lookup if, at every point length, this program halts within the clock on every
list of m(n) tagged points and every query of that length."

**Formalization Note.** "This program" is the lookup header `σ` (see `IsLookupHeader`). It runs
on a public tape of the clock's length, as every hypothesis does; the tape is arbitrary. Point
lengths are positive (§2, p.11). -/
def PermitsLookup (U : Decoder) (σ : List Bool) (m t : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (x : Fin (m n) → Fin n → Bool) (a : Fin (m n) → Bool)
    (w : Fin (t n) → Bool) (z : Fin n → Bool),
      (U.run σ (fullAnchorList x a) (List.ofFn w) (List.ofFn z) (t n)).isSome

end OWFLocalDesc


