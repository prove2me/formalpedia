-- Prove2me | Definitions.Def_EarlyStoppingEIG_Exact_StatementContext
-- name    : EarlyStoppingEIG_Exact_StatementContext
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:58:35.885302+00:00
-- url     : https://prove2.me/theorems/268fea37-87ac-4f32-90c7-e3fecd7e5fb3
-- title:
--   Actual output snapshots, first termination context and broadcast clauses
-- statement:
--   An actual output snapshot records the horizon used by a nonsender’s actual output invocation: the stopping round at the final round, or one less at early stopping after round two. Reconstructed entries and resolved outputs are computed from that execution’s own local history. Entry functions also denote the same mathematical reconstruction if the output subroutine can short-circuit to zero.
--
--   $$3\le r<t+1,\quad p\text{ honest and first to halt in }r,\quad p\notin S,\quad |S|\le r-2,\quad S\text{ accepted at }p.$$
--
--   This is exactly the shared context of Lemmas 15–24. It imposes none of their conclusions, and permits honest parties in $S$. The broadcast predicates require honest-sender validity, a common output for every honest party, and actual termination. They refer to the corrected concrete protocol through its execution semantics.
-- source:
--   Giovanni Deligios, Fatima Elsheimy, Simon Holmgaard Kamp, Ivana Klasovitá, Charalampos Papamanthou, Chen-Da Liu-Zhang, Julian Loss, STOC 2027 submission #196 (October 2026), §4, pp.24–31, especially p.27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/196.pdf

import Definitions.Def_EarlyStoppingEIG_Exact_Execution

namespace EarlyStoppingEIG.Exact

/-- The actual invocation's horizon: early stopping uses r-1, final stopping
uses r. The sender does not invoke this subroutine. The corrected t=0 branch
also does not invoke it. -/
def OutputSnapshot (P : Parameters) (E : Execution P) (i : Party P) (h : ℕ) : Prop :=
  i ≠ P.sender ∧ ∃ r b, HaltsAt P E i r b ∧ 2 ≤ h ∧ h ≤ P.t + 1 ∧
    ((r = P.t + 1 ∧ 2 ≤ r ∧ h = r) ∨ (3 ≤ r ∧ r < P.t + 1 ∧ h = r - 1))

noncomputable def EntryAt (P : Parameters) (E : Execution P) (i : Party P)
    (h : ℕ) (w : List (Party P)) (u : ℕ) : Entry P :=
  reconstructed P i ((E.state h).views i) h w u

noncomputable def OutputAt (P : Parameters) (E : Execution P) (i : Party P) (h : ℕ) : Bool :=
  output P i ((E.state h).views i) h

def AllFaulty (P : Parameters) (E : Execution P) (w : List (Party P)) : Prop :=
  ∀ j ∈ w, j ∈ faulty P E

def NoEarlierHonestHalt (P : Parameters) (E : Execution P) (r : ℕ) : Prop :=
  ∀ i, Honest P E i → ∀ q b, q < r → ¬ HaltsAt P E i q b

/-- Exactly the shared context at the top of p.27. It does not assert any of
Lemmas 15–24, does not require S to be faulty, and does not identify the actual
fault count with any party's local estimate. The sending-through-r fact is a
consequence of this context and the transition rules, not an extra premise. -/
def FirstCover (P : Parameters) (E : Execution P) (p : Party P) (r : ℕ)
    (S : Finset (Party P)) : Prop :=
  3 ≤ r ∧ r < P.t + 1 ∧ Honest P E p ∧ (∃ b, HaltsAt P E p r b) ∧
    NoEarlierHonestHalt P E r ∧ AcceptedCover P p ((E.state r).views p) r S

def BroadcastValidity (P : Parameters) (E : Execution P) (b : Bool) : Prop :=
  Honest P E P.sender → ∀ i, Honest P E i → Outputs P E i b

def BroadcastAgreement (P : Parameters) (E : Execution P) : Prop :=
  ∃ b, ∀ i, Honest P E i → Outputs P E i b

def BroadcastTermination (P : Parameters) (E : Execution P) : Prop :=
  ∀ i, Honest P E i → ∃ r b, HaltsAt P E i r b

end EarlyStoppingEIG.Exact


