-- Prove2me | Definitions.Def_RestrictedDec_Supplement_interact
-- name    : RestrictedDec_Supplement_interact
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:24:46.264947+00:00
-- url     : https://prove2.me/theorems/74df368b-f60c-430f-af0a-8e08bc4fd2de
-- title:
--   Interaction of an adversary with a challenger; tuple and coin helpers
-- statement:
--   The primitive security experiments of Appendix A are interactions of a uniform PPT adversary with a challenger. The challenger keeps a state; on each move of the adversary it either replies (the reply is the adversary's next input) or ends the experiment with an output bit. The adversary is activated at most $p(\lambda)+1$ times, and running out of activations ends the experiment with output $0$.
--
--   The module also fixes the helpers used by every construction: the $i$-th field of a tuple code, the canonical parse of a string as a $k$-tuple (a string that is not the code of a $k$-tuple is **malformed**), a coin string read as a coin vector, and the split of a coin vector of length $a+b$ into its first $a$ and last $b$ coins.
--
--   **Formalization Note** The adversary is the published `RestrictedDec.Adversary`.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A, pp.29–34

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_RestrictedDec_Adversary
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- The `i`-th field (from `0`) of a `BeyondDS.tup` code, `[]` if absent. -/
def fld (o : Str) (i : ℕ) : Str := (BeyondDS.untup o).getD i []

/-- The **canonical parse** of a string as a `k`-tuple: `some [w₀, …, w_{k−1}]` exactly when the
string is `tup [w₀, …, w_{k−1}]`; every other string is **malformed** (`none`). -/
def parseTup (k : ℕ) (C : Str) : Option (List Str) :=
  if (BeyondDS.untup C).length = k ∧ BeyondDS.tup (BeyondDS.untup C) = C then
    some (BeyondDS.untup C) else none

/-- A coin string read as a coin vector of length `k` (missing bits read `0`). -/
def coinsOf (k : ℕ) (r : Str) : Fin k → Bool := fun i => r.getD i false

/-- The first `a` coins of a coin vector of length `a + b`. -/
def cL {a b : ℕ} (ρ : Fin (a + b) → Bool) : Fin a → Bool := fun i => ρ (Fin.castAdd b i)

/-- The last `b` coins of a coin vector of length `a + b`. -/
def cR {a b : ℕ} (ρ : Fin (a + b) → Bool) : Fin b → Bool := fun i => ρ (Fin.natAdd a i)

/-- The **interaction of a uniform PPT adversary with a challenger** in a primitive security
experiment. The challenger has a state `st : σ`; on each move of the adversary it either replies
(new state, reply string, which is the adversary's next input) or ends the experiment with an output
bit. The adversary is activated at most `fuel` times (`p(λ) + 1` in every experiment); running out
of activations ends the experiment with output `0`.
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), App. A, pp.29–34: the
experiments of Definitions 5, 7, 9, 10, 11, 12 and 13 are each an interaction of a PPT adversary
with a challenger.

**Formalization Note.** The adversary is the published `RestrictedDec.Adversary` (uniform reactive
machine, `p(λ)` fresh coins per activation). Its moves are `BeyondDS.tup` codes read with `fld`. -/
noncomputable def interact {σ : Type} (A : Adversary) (lam : ℕ)
    (ch : σ → Str → PMF ((σ × Str) ⊕ Bool)) : ℕ → σ → Str → Str → PMF Bool
  | 0, _, _, _ => PMF.pure false
  | fuel + 1, st, s, input =>
    (A.activate lam s input).bind fun r =>
      (ch st r.2).bind fun o =>
        match o with
        | .inl (st', reply) => interact A lam ch fuel st' r.1 reply
        | .inr b => PMF.pure b

end Supplement

end RestrictedDec


