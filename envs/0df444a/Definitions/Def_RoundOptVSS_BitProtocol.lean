-- Prove2me | Definitions.Def_RoundOptVSS_BitProtocol
-- name    : RoundOptVSS_BitProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:01:54.342209+00:00
-- url     : https://prove2.me/theorems/c1ef5433-7a43-4c2a-95c6-50c9c70b7726
-- title:
--   Uniform bit-level protocols and polynomial communication and computation
-- statement:
--   A **bit-level protocol** is given by six maps $\{0,1\}^*\to\{0,1\}^*$ (initial state, coin request, private message, broadcast, state update, output) together with a public message cap $\mathrm{cap}(n,t,\kappa,h,D)$. Each map reads one self-delimiting string beginning with the parameters $n,t,\kappa,h,D$, the party index and the round in unary, followed by its arguments (the state; the coins in binary; the recipient index for a private message; the received messages, entry by entry). Messages and states are bit strings and secrets are bit vectors $x\in\{0,1\}^h$; an output string decodes to $x$ if it is a $1$ followed by exactly $h$ bits and to $\bot$ otherwise. Every bit-level protocol defines a (3,1)-round protocol of the execution model.
--
--   The protocol has **communication and computation polynomial in $n,\kappa,h$** (`Efficient`) if there is one polynomial $p$, chosen before every parameter, such that every one of the six maps is computable in polynomial time (by a multi-stack Turing machine), and for all valid parameters the cap is at most $p(n+t+\kappa+h)$ and, in every execution against every adversary, every honest state, every honest message and every honest coin request has length at most $p(n+t+\kappa+h)$.
--
--   Since $t<n$, a bound polynomial in $n+t+\kappa+h$ is polynomial in $n,\kappa$ and $h$, the quantities of Theorem 1.1 and Theorem 8.1.
--
--   **Formalization Note** Bit strings, polynomial-time computability and the unary encoding of numbers are the published `QAlgorithms.Complexity.{Str, PolyTimeComputable, encNat}`.
-- source:
--   Liu-Zhang, Masserova, Round-Optimal Statistical Verifiable Secret Sharing with Polynomial Complexity, manuscript (2026; STOC 2027 submission, sha256 3a45d95d…), Theorem 1.1 (p.2) and Theorem 8.1 (pp.28–29): "communication and computation polynomial in n, κ and the input length h"; §8.4 (p.31)

import Mathlib
import Definitions.Def_RoundOptVSS_Model
import Definitions.Def_QAlgorithms_ClassicalStringComputability

open QAlgorithms.Complexity

namespace RoundOptVSS

/-!
# Bit-level protocols and "communication and computation polynomial in n, κ and h"

Liu-Zhang, Masserova, *Round-Optimal Statistical Verifiable Secret Sharing with Polynomial
Complexity*, manuscript (STOC 2027 submission, sha256 3a45d95d…), Theorem 1.1 (p.2) and
Theorem 8.1 (pp.28–29): "communication and computation polynomial in n, κ and the input length h".

**Formalization Note.**
* A bit-level protocol is six maps `Str → Str` (`Str = List Bool`, reused from
  `QAlgorithms.Complexity`) plus a public message cap. Messages and states are bit strings and
  secrets are bit vectors `Fin h → Bool`.
* Every map reads one self-delimiting string: the header `encNat n ++ encNat t ++ encNat κ ++
  encNat h ++ encNat dealer ++ encNat i ++ encNat round` (the parameters in unary), followed by
  the encoded arguments (`encStr`: each bit `b` as `true, b`, then `false`; lists of strings by
  `encList`; coin values and moduli in binary, `Nat.bits`; inboxes entry by entry with
  `encOpt`). One map (`privM`) also reads the recipient index `encNat j`.
* `Efficient` asks for one polynomial `p` and requires every map to be `PolyTimeComputable` and,
  on every execution in the support, every honest state, honest message, honest coin request and
  the cap to have length at most `p(n + t + κ + h)`. The polynomial is chosen before every
  parameter.
-/

/-- Self-delimiting encoding of a bit string: each bit `b` as `true, b`, then `false`. -/
def encStr (s : Str) : Str := s.flatMap (fun b => [true, b]) ++ [false]

/-- Decoding of `encStr`: the string and the rest of the input, or `none` if malformed. -/
def decStr : Str → Option (Str × Str)
  | true :: b :: rest => (decStr rest).map fun p => (b :: p.1, p.2)
  | false :: rest => some ([], rest)
  | _ => none

/-- Self-delimiting encoding of a list of bit strings. -/
def encList (l : List Str) : Str := l.flatMap (fun s => true :: encStr s) ++ [false]

/-- Decoding of `encList` (stops at the first malformed entry). -/
def decListAux : ℕ → Str → List Str
  | 0, _ => []
  | k + 1, true :: rest =>
      match decStr rest with
      | some p => p.1 :: decListAux k p.2
      | none => []
  | _ + 1, _ => []

/-- Decoding of `encList`. -/
def decList (w : Str) : List Str := decListAux w.length w

/-- A natural number in binary (least significant bit first). -/
def encBin (N : ℕ) : Str := N.bits

/-- Decoding of `encBin` (any bit string is read as a number). -/
def decBin (w : Str) : ℕ := w.foldr (fun b acc => 2 * acc + if b then 1 else 0) 0

/-- Encoding of an optional string. -/
def encOpt : Option Str → Str
  | none => [false]
  | some s => true :: encStr s

/-- Encoding of an inbox indexed by sender (its length `n` is in the header). -/
def encInbox {n : ℕ} (f : Fin n → Option Str) : Str := (List.ofFn f).flatMap encOpt

/-- Encoding of a secret `x ∈ {0,1}^h`. -/
def encSecret {h : ℕ} (x : Fin h → Bool) : Str := List.ofFn x

/-- Encoding of an optional input (the dealer's `some x`, the others' `none`). -/
def encInput {h : ℕ} (x : Option (Fin h → Bool)) : Str := encOpt (x.map encSecret)

/-- Decoding of an output string: `true` followed by exactly `h` bits is the secret, anything
else is ⊥. -/
def decOutput (h : ℕ) (w : Str) : Option (Fin h → Bool) :=
  match w with
  | true :: v => if hv : v.length = h then some (fun j => v.get (Fin.cast hv.symm j)) else none
  | _ => none

/-- The header: all parameters, the party index and the round, in unary. -/
def hdr (P : Params) (i : Fin P.n) (r : ℕ) : Str :=
  encNat P.n ++ encNat P.t ++ encNat P.κ ++ encNat P.h ++ encNat P.dealer ++ encNat i ++ encNat r

/-- A uniform bit-level protocol: the same six string maps for every parameter set. -/
structure BitProtocol where
  initM : Str → Str
  coinsM : Str → Str
  privM : Str → Str
  bcastM : Str → Str
  recvM : Str → Str
  outM : Str → Str
  cap : Params → ℕ

/-- The input string of the coin request of party `i` in round `r` from state `st`. -/
def coinsInput (P : Params) (i : Fin P.n) (r : Fin 4) (st : Str) : Str :=
  hdr P i r ++ encStr st

/-- The protocol (in the sense of `Protocol`) that a bit-level protocol defines. -/
def BitProtocol.toProtocol (B : BitProtocol) : Protocol Str Str Bool where
  init P i x := B.initM (hdr P i 0 ++ encInput x)
  coins P i r st := (decList (B.coinsM (coinsInput P i r st))).map decBin
  send P i r st c :=
    (fun j => B.privM (hdr P i r ++ encNat j ++ encStr st ++ encList (c.map encBin)),
     B.bcastM (hdr P i r ++ encStr st ++ encList (c.map encBin)))
  recv P i r st c pr bc :=
    B.recvM (hdr P i r ++ encStr st ++ encList (c.map encBin) ++ encInbox pr ++ encInbox bc)
  output P i st := decOutput P.h (B.outM (hdr P i 4 ++ encStr st))
  msgLen := List.length
  msgCap := B.cap

/-- Communication and computation polynomial in `n, κ, h`: one polynomial `p` (chosen before
every parameter) such that every map is polynomial-time computable and, for all valid parameters,
the cap and, on every execution in the support against every adversary, every honest state,
every honest message and every honest coin request have length at most `p(n + t + κ + h)`. -/
def Efficient (B : BitProtocol) : Prop :=
  ∃ p : Polynomial ℕ,
    PolyTimeComputable B.initM ∧ PolyTimeComputable B.coinsM ∧ PolyTimeComputable B.privM ∧
    PolyTimeComputable B.bcastM ∧ PolyTimeComputable B.recvM ∧ PolyTimeComputable B.outM ∧
    ∀ P : Params, P.Valid →
      B.cap P ≤ p.eval (P.n + P.t + P.κ + P.h) ∧
      ∀ (C : Finset (Fin P.n)), C.card ≤ P.t →
        ∀ (x : Fin P.h → Bool) (A : ShareAdv P Str Bool) (Bd : RecAdv A),
          ∀ o ∈ (exec B.toProtocol P C x A Bd).support, ∀ i, i ∉ C →
            (∀ r : Fin 5, ((o.stateAt r) i).length ≤ p.eval (P.n + P.t + P.κ + P.h)) ∧
            ∀ r : Fin 4,
              (B.coinsM (coinsInput P i r ((o.stateAt r.castSucc) i))).length ≤
                  p.eval (P.n + P.t + P.κ + P.h) ∧
              (∀ j, ((o.roundAt r).sent i j).length ≤ p.eval (P.n + P.t + P.κ + P.h)) ∧
              ((o.roundAt r).sentB i).length ≤ p.eval (P.n + P.t + P.κ + P.h)

end RoundOptVSS


