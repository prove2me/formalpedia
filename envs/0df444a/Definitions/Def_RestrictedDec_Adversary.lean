-- Prove2me | Definitions.Def_RestrictedDec_Adversary
-- name    : RestrictedDec_Adversary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:52:01.981976+00:00
-- url     : https://prove2.me/theorems/912f2ba6-0c83-4ee7-8821-78e92020a0c3
-- title:
--   Uniform PPT adversaries as reactive machines
-- statement:
--   A **uniform probabilistic polynomial-time adversary** is given by a step function $f$ on bit strings, computed in polynomial time, and a polynomial $p$. At security parameter $\lambda$ it is activated at most $p(\lambda)+1$ times. Each activation reads $(1^\lambda,\text{state},\text{input},\text{coins})$ with $p(\lambda)$ fresh uniform coins and returns a new state and a move, both cut to $p(\lambda)$ bits. A move is
--
--   1. a functional decryption query $(F,c)$: a function description and a ciphertext,
--   2. the challenge pair $(m_0,m_1)$, or
--   3. the final guess $b'$.
--
--   The same machine is used for every $\lambda$ (no advice), so the model is uniform, as the paper's strictness convention requires ("a single PPT attack").
--
--   **Formalization Note** Moves are coded with `BeyondDS.tup` and a two-bit tag; every string decodes to some move.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 1, p.13; §2.3, p.15; p.28 (uniform separating witnesses: "insufficient for a uniform adversary")

import Mathlib
import Definitions.Def_BeyondDS_tup
open QAlgorithms.Complexity
open Polynomial
set_option autoImplicit false

namespace RestrictedDec

/-- A **uniform probabilistic polynomial-time adversary**, as a reactive machine: one step
function `f` (the same for every `λ`, no advice) and a polynomial `p`. On each activation it reads
`tup [1^λ, state, input, coins]` with `p(λ)` fresh uniform coins and outputs `tup [state′, move]`;
the kept state and the move are cut to `p(λ)` bits, and the adversary is activated at most
`p(λ) + 1` times (see `runGame`).
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Definition 1, p.13 ("every
probabilistic polynomial-time (PPT) adversary"); §2.3, p.15 ("a single PPT attack"); the
adversary chooses each query after seeing earlier answers (p.13).

**Formalization Note.** The model is uniform: there is no advice string. The bounds on coins,
state, output and number of activations make the adversary polynomial-time once `f` is. -/
structure Adversary where
  f : Str → Str
  p : ℕ[X]

/-- The adversary's step function is computed in polynomial time. -/
def Adversary.Valid (A : Adversary) : Prop := PolyTimeComputable A.f

/-- One activation: from state and input to new state and move, with fresh uniform coins. -/
noncomputable def Adversary.activate (A : Adversary) (lam : ℕ) (s input : Str) :
    PMF (Str × Str) :=
  (PMF.uniformOfFintype (Fin (A.p.eval lam) → Bool)).map fun c =>
    let out := BeyondDS.untup (A.f (BeyondDS.tup [encNat lam, s, input, List.ofFn c]))
    ((out.getD 0 []).take (A.p.eval lam), (out.getD 1 []).take (A.p.eval lam))

/-- A move of the adversary: a functional decryption query `(F, c)` (description `d`, ciphertext
`c`), the challenge pair `(m₀, m₁)`, or the final guess `b′`. -/
inductive Move
  | query (d c : Str)
  | challenge (m0 m1 : Str)
  | guess (b : Bool)

/-- The parser of moves: `tup [00, d, c]` is a query, `tup [01, m₀, m₁]` a challenge, and every
other string the guess given by the first bit of its second field (`0` if absent). -/
def decMove (o : Str) : Move :=
  let fs := BeyondDS.untup o
  match fs.getD 0 [] with
  | [false, false] => .query (fs.getD 1 []) (fs.getD 2 [])
  | [false, true] => .challenge (fs.getD 1 []) (fs.getD 2 [])
  | _ => .guess ((fs.getD 1 []).headD false)

end RestrictedDec


