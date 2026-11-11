-- Prove2me | Definitions.Def_EarlyStoppingEIG_Exact_Cover
-- name    : EarlyStoppingEIG_Exact_Cover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:56:16.173531+00:00
-- url     : https://prove2.me/theorems/82020e2c-e3bc-4b4b-a969-35705408c0b4
-- title:
--   Accumulated conflict pairs with loops and accepted covers
-- statement:
--   Each local conflict set accumulates the four source checks: a sending gap or missing required initial message; an observed signature differing from the direct receipt; a reported previous receipt differing from the direct receipt; and a party whose valid sending prefix stops at round two, with the corresponding sender-bit consistency checks. Comparisons retain exact signed receipts, including absence.
--
--   $$S\subseteq\mathcal P\setminus\{i\},\quad |S|\le r-2,\quad \forall\{j,k\}\in\mathrm{Conflicts}_i,\quad j\in S\ \lor\ k\in S.$$
--
--   A self-loop forces its identity into a cover. Covers need not be unique, minimum or faulty. Accumulation includes only invocations before the final round and no checks after the party halts. This is a local explanation test, not a fault-identification oracle.
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), §3.4, pp.21–22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Definitions.Def_EarlyStoppingEIG_Exact_Messages

namespace EarlyStoppingEIG.Exact

def SendingGap (P : Parameters) (v : LocalView P) (h : ℕ) (j : Party P) : Prop :=
  v.receipt 2 j = none ∨
  (j = P.sender ∧ v.receipt 1 j = none) ∨
  ∃ a b, 2 ≤ a ∧ a < b ∧ b ≤ h ∧ v.receipt a j = none ∧ (v.receipt b j).isSome

def ConflictingSignature (P : Parameters) (v : LocalView P) (h : ℕ)
    (j : Party P) : Prop :=
  ∃ u m, 1 ≤ u ∧ u ≤ h ∧ Seen P v h m ∧ WellFormed P u j m ∧ v.receipt u j ≠ some m

def ReceiptConflict (P : Parameters) (v : LocalView P) (h : ℕ)
    (j k : Party P) : Prop :=
  ∃ u m a, 2 ≤ u ∧ u ≤ h ∧ Seen P v h m ∧ WellFormed P u k m ∧
    reported k u m j = some a ∧ a ≠ v.receipt (u - 1) j

def StopsAfterTwo (P : Parameters) (v : LocalView P) (h : ℕ) (j : Party P) : Prop :=
  2 < h ∧ (v.receipt 2 j).isSome ∧ ∀ u, 3 ≤ u → u ≤ h → v.receipt u j = none

def RoundTwoConflict (P : Parameters) (v : LocalView P) (h : ℕ)
    (j k : Party P) : Prop :=
  StopsAfterTwo P v h j ∧
    ((j = k ∧ ¬ ∃ m b, v.receipt 2 j = some m ∧ ReportsBit P j m b) ∨
     ∃ m b senderMessage, v.receipt 2 j = some m ∧ IsSenderBit P senderMessage b ∧
       reported j 2 m P.sender = some (some senderMessage) ∧
       ¬ ∃ a, v.receipt 2 k = some a ∧
         reported k 2 a P.sender = some (some senderMessage))

/-- Undirected conflicts, including loops. Every test reads only this local
view; an edge does not certify which endpoint is faulty. -/
def newConflict (P : Parameters) (v : LocalView P) (h : ℕ) (j k : Party P) : Prop :=
  (j = k ∧ (SendingGap P v h j ∨ ConflictingSignature P v h j)) ∨
  ReceiptConflict P v h j k ∨ ReceiptConflict P v h k j ∨
  RoundTwoConflict P v h j k ∨ RoundTwoConflict P v h k j

/-- Accumulated history: old conflicts are retained even if a later receipt
would remove the evidence of a sending gap. -/
def conflict (P : Parameters) (v : LocalView P) (h : ℕ) (j k : Party P) : Prop :=
  ∃ q, 2 ≤ q ∧ q ≤ h ∧ q < P.t + 1 ∧
    (∀ R b, v.halt = some (R, b) → q ≤ R) ∧ newConflict P v q j k

def AcceptedCover (P : Parameters) (i : Party P) (v : LocalView P) (r : ℕ)
    (S : Finset (Party P)) : Prop :=
  i ∉ S ∧ S.card ≤ r - 2 ∧ ∀ j k, conflict P v r j k → j ∈ S ∨ k ∈ S

def coverAccepts (P : Parameters) (i : Party P) (v : LocalView P) (r : ℕ) : Prop :=
  ∃ S, AcceptedCover P i v r S

end EarlyStoppingEIG.Exact


