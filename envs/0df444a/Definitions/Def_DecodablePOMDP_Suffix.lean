-- Prove2me | Definitions.Def_DecodablePOMDP_Suffix
-- name    : DecodablePOMDP_Suffix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:24:42.060412+00:00
-- url     : https://prove2.me/theorems/559a5437-3748-4f5f-9f9a-0255027052c0
-- title:
--   Suffixes $u_h$ (Definition 4), $\mathcal U_h$ and the suffix update
-- statement:
--   The **suffix** of a history $h_h=(A_{1:h-1},\widetilde Z_{2:h})$ is the entire history if $h\le L$, and
--
--   $$u_h=(\widetilde Z_{h-L+1:h},\ A_{h-L+1:h-1})$$
--
--   otherwise; it contains at most $L$ actions and $L$ observations. $\mathcal U_h$ is the set of all suffixes of these lengths at stage $h$, reachable or not. After action $a$ and observation $z$ the suffix is updated by appending $(a,z)$ and keeping the window of stage $h+1$.
--
--   Suffixes are the finite part of the planner's state: by Lemma 4 they carry all the information the conditional beliefs need.
--
--   **Formalization Note** A suffix is stored as the list of pairs $(a_k,z_{k+1})$ of the window (newest first) together with its oldest observation $z_{h-L+1}$ when $h>L$.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Definition 4, p.9; p.10

import Mathlib
import Definitions.Def_DecodablePOMDP_Value

namespace DecodablePOMDP

/-- **Suffix** (Definition 4, p.9), stored as `(first, steps)`: `steps` is the list of
action–observation pairs `(a_k, z_{k+1})` of the window, newest first, and `first` is the oldest
observation of the window when it is not paired with an action of the window. -/
abbrev Suffix (A O S : Type) := Option (O × S) × List (A × (O × S))

/-- **The suffix of a history** (Definition 4, p.9). For the history `h_h` of `t = h − 1` steps
(newest first): the entire history if `h ≤ L` (`first = none`, all `h − 1` pairs); otherwise
`(Z̃_{h−L+1:h}, A_{h−L+1:h−1})`, i.e. `first = z_{h−L+1}` and the `L − 1` newest pairs
`(a_k, z_{k+1})`, `k = h−L+1, …, h−1`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Definition 4, p.9: "Define the recent-history
suffix, or simply suffix uh to be the entire history if h ≤ L, and (Z̃h−L+1:h, Ah−L+1:h−1)
otherwise. Thus, uh contains at most L actions and at most L observations."

**Formalization Note.** The case test `L ≤ t ∧ 0 < t` is `h > L` for `L ≥ 1` (the only case used). The window `(Z̃_{h−L+1:h}, A_{h−L+1:h−1})` is the same data as `first` plus
`steps`. -/
def suffixOf {A O S : Type} (L t : ℕ) (hist : Hist A (O × S) t) : Suffix A O S :=
  if hlt : L ≤ t ∧ 0 < t then (some (hist ⟨L - 1, by omega⟩).2, (List.ofFn hist).take (L - 1))
  else (none, List.ofFn hist)

/-- **Suffixes of stage `h`** `U_h` (Definition 4, p.9; p.10): `u` has the shape of a suffix at
stage `h`: `h − 1` pairs and no separate first observation if `h ≤ L`; `L − 1` pairs and a first
observation if `h > L`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), p.10: "For the planner, Uh contains all
suffixes of the lengths in Definition 4 … including those not reachable from µ1." -/
def IsSuffixAt {A O S : Type} (L h : ℕ) (u : Suffix A O S) : Prop :=
  (h ≤ L ∧ u.1 = none ∧ u.2.length = h - 1) ∨ (L < h ∧ u.1.isSome ∧ u.2.length = L - 1)

/-- **Updated suffix** `u⁺` (p.10): after action `a` at stage `h` and observation `z` at stage
`h + 1`, append `(a, z)` and, if `h + 1 > L`, keep only the window of Definition 4 at stage `h + 1`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), p.10: "Updating h and uh is straightforward:
h becomes h+1, and uh drops the earliest action/observation pair and replaces it with the most
recent one." -/
def suffixUpdate {A O S : Type} (L h : ℕ) (u : Suffix A O S) (a : A) (z : O × S) :
    Suffix A O S :=
  if h + 1 ≤ L then (none, (a, z) :: u.2)
  else ((((a, z) :: u.2)[L - 1]?).map Prod.snd, ((a, z) :: u.2).take (L - 1))

end DecodablePOMDP


