-- Prove2me | Definitions.Def_EarlyStoppingEIG_Exact_Messages
-- name    : EarlyStoppingEIG_Exact_Messages
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:55:34.609121+00:00
-- url     : https://prove2.me/theorems/8d9a2796-4f12-4f3a-99be-c18439cbe27e
-- title:
--   Public parameters, signed receipts and raw EIG trees
-- statement:
--   Let $n,t$ be natural numbers with $2t<n$, and let $s$ be the designated sender among $n$ named parties. The input alphabet is binary. A receipt is either an exact valid signed message or the absence marker $\bot$. Signed reports carry their author, round and a complete identity-indexed list of preceding-round receipts. A report containing $\bot$ is distinct from an absent report.
--
--   $$\Sigma_d=\{w: |w|=d,\ w_1=s,\ w\text{ has distinct identities}\},\qquad 1\le d\le t+1.$$
--
--   A local view stores direct receipts, own signatures and an optional actual halt round and bit. Raw tree values are read by traversing the nested signed reports. These values are separate from reconstructed entries and resolved bits. The sender’s input and the actual faulty set are absent from the public parameters.
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), §§2–3.2, pp.15–18; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Definitions.Def_EarlyStoppingEIG_Exact_Authentication

namespace EarlyStoppingEIG.Exact

/-- Public parameters only. In particular neither the actual fault count nor the
sender's private bit is part of these parameters. -/
structure Parameters where
  n : ℕ
  t : ℕ
  sender : Fin n
  majority : 2 * t < n

abbrev Party (P : Parameters) := Fin P.n
abbrev Message (P : Parameters) := AuthTerm (Party P)
abbrev Receipt (P : Parameters) := Option (Message P)

def encodeReceipt {P : Parameters} : Receipt P → Message P
  | none => .tuple []
  | some m => .tuple [m]

def decodeReceipt {P : Parameters} : Message P → Option (Receipt P)
  | .tuple [] => some none
  | .tuple [m] => some (some m)
  | _ => none

def bitPayload {P : Parameters} (b : Bool) : Message P := .atom (if b then 1 else 0)

def IsSenderBit (P : Parameters) (m : Message P) (b : Bool) : Prop :=
  ∃ q, m = .sig P.sender q (bitPayload b)

/-- Parse the exact signed report, including its author and round tag. A
successfully parsed report of a missing receipt differs from no report. -/
def reportList {P : Parameters} (j : Party P) (r : ℕ) : Message P →
    Option (List (Message P))
  | .sig k _ (.tuple [.atom u, .tuple xs]) =>
      if k = j ∧ u = r ∧ xs.length = P.n then some xs else none
  | _ => none

def reported {P : Parameters} (j : Party P) (r : ℕ) (m : Message P)
    (k : Party P) : Option (Receipt P) := do
  let xs ← reportList j r m
  let x ← xs[k.val]?
  decodeReceipt x

/-- Recursive syntactic validity. Only the sender has a round-one message;
later reports have exactly one receipt slot per identity. The signature's
provenance is enforced separately by the operational semantics. -/
def WellFormed (P : Parameters) : ℕ → Party P → Message P → Prop
  | 0, _, _ => False
  | 1, j, m => j = P.sender ∧ ∃ b, IsSenderBit P m b
  | r + 2, j, m =>
      (reportList j (r + 2) m).isSome ∧
      ∀ k, ∃ a, reported j (r + 2) m k = some a ∧
        ∀ x, a = some x → WellFormed P (r + 1) k x

def ReportsBit (P : Parameters) (j : Party P) (m : Message P) (b : Bool) : Prop :=
  WellFormed P 2 j m ∧
    ∃ v, reported j 2 m P.sender = some (some v) ∧ IsSenderBit P v b

def IsPath (P : Parameters) (w : List (Party P)) : Prop :=
  w.head? = some P.sender ∧ w.Nodup ∧ 1 ≤ w.length ∧ w.length ≤ P.t + 1

/-- A party's local history, including its own exact signed messages. A halt
stores the round and output bit; receipts are never overwritten after closing
their round. No other party's view or private input occurs here. -/
structure LocalView (P : Parameters) where
  receipt : ℕ → Party P → Receipt P
  own : ℕ → Receipt P
  halt : Option (ℕ × Bool)

def emptyView (P : Parameters) : LocalView P :=
  ⟨fun _ _ => none, fun _ => none, none⟩

def Seen (P : Parameters) (v : LocalView P) (h : ℕ) (m : Message P) : Prop :=
  ∃ r, 1 ≤ r ∧ r ≤ h ∧ ∃ j a, v.receipt r j = some a ∧ Occurs m a

/-- Read down nested receipt lists from the last reporting identity to the
sender. Failure at an intermediate report produces the missing marker. -/
def readPath (P : Parameters) : List (Party P) → Receipt P → Receipt P
  | [], a => a
  | j :: rest, a => do
      let m ← a
      let prev ← reported j (rest.length + 2) m (rest.headD P.sender)
      readPath P rest prev

/-- The raw EIG value, as distinct from a reconstructed round entry. -/
def rawValue (P : Parameters) (v : LocalView P) (w : List (Party P)) : Receipt P :=
  match w.reverse with
  | [] => none
  | [j] => v.receipt 1 j
  | j :: k :: rest => do
      let m ← v.receipt w.length j
      let a ← reported j w.length m k
      readPath P (k :: rest).dropLast a

end EarlyStoppingEIG.Exact


