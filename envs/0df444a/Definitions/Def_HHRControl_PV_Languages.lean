-- Prove2me | Definitions.Def_HHRControl_PV_Languages
-- name    : HHRControl_PV_Languages
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:31.672977+00:00
-- url     : https://prove2.me/theorems/8841bf4c-215c-4d9d-b9a7-29ac3d4ea149
-- title:
--   Definition 3.1, pp. 4–8, 24, 27, 28 — instance codes, the control languages, (certifiably) vulnerable and resistant; Hitting Set, Restricted Hitting Set and X3C
-- statement:
--   This file states the complexity notions of Definition 3.1 for control by partition of voters, and the three source problems of the paper's reductions.
--
--   **Instance codes.** An instance of Control by Partition of Voters, the candidates $C=\{0,\dots,m-1\}$, a distinguished candidate $c$ and the ballots $P(0),\dots,P(n-1)$, is written as the list of numbers
--   $$m,\; n,\; c,\; \mathrm{code}(P(0)),\;\dots,\;\mathrm{code}(P(n-1)),$$
--   each number in binary over a four-letter alphabet. The ballots are listed one voter at a time, as the paper assumes (p. 4). The **language** of the constructive (destructive) problem is the set of codes of the instances whose answer is Yes.
--
--   **Definition 3.1.** A voting system is
--   1. **vulnerable** to a type of control if it is susceptible to it and the language is in P;
--   2. **certifiably-vulnerable** if it is susceptible and some polynomial-time computable function maps the code of every yes-instance to the code of a partition $(V_1,V_2)$ that achieves the control goal for that instance, and the code of every no-instance to a fixed token meaning "control is impossible" (for partition problems any partition that works is acceptable);
--   3. **resistant** if it is susceptible and the language is NP-complete.
--
--   **Hitting Set** (p. 24). Given $B=\{b_1,\dots,b_m\}$, a family $S=\{S_1,\dots,S_n\}$ of subsets of $B$ and a positive integer $k$: is there $B'\subseteq B$ with $\|B'\|\le k$ and $S_i\cap B'\neq\emptyset$ for each $i$? **Restricted Hitting Set** (p. 27) is the same question for the instances with
--   $$n(k+1)+1\le m-k .$$
--   **Exact Cover by Three-Sets** (X3C, p. 28). Given $B=\{b_1,\dots,b_m\}$ with $m=3q$, $q\ge1$, and a family $S$ of subsets of $B$ with $\|S_i\|=3$: is there a subfamily in which every element of $B$ occurs in exactly one set?
--
--   The vulnerability and resistance clauses of Theorem 3.6 are stated with these notions, and the hardness proofs reduce from these problems.
--
--   **Formalization Note** P, NP-completeness and polynomial-time computability are the published `CookPvsNP` notions on Cook's one-tape Turing machine; numbers are written with the published `encNats` over `BSym`. Writing $n$ explicitly makes the code determine the instance. A partition is coded as the number `1` followed by the membership vector of $V_1$; the "control impossible" token is the single number `0`. A Hitting Set or X3C instance is coded by its sizes followed by the incidence vectors of the sets. Restricted Hitting Set's condition is written $n(k+1)+1+k\le m$, which avoids natural-number subtraction and has the same solutions.
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, pp. 4–5 Definition 3.1 and footnotes 6–7; p. 4 (input coding); p. 8 Control by Partition of Voters; p. 24 Hitting Set; p. 27 Restricted Hitting Set; p. 28 Exact Cover by Three-Sets

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_HHRControl_PV_Elections

namespace HHRControl.PV

open CookPvsNP ProjSchedTW.Complexity

/-! # Instance codes, the control languages, vulnerability and resistance; Hitting Set and X3C

Hemaspaandra, Hemaspaandra & Rothe, *Anyone but Him*, arXiv:cs/0507027v5: Definition 3.1
(pp. 4–5), Control by Partition of Voters (p. 8), Hitting Set (p. 24), Restricted Hitting Set
(p. 27), Exact Cover by Three-Sets (p. 28).

Every instance is written over the alphabet `BSym` as a list of natural numbers in binary
(`encNats`); the ballots are listed one voter at a time (p. 4). -/

/-- The code of the control instance `(C, c, V)` with `C = Fin m`, `c`, and the ballots `P`: the
numbers `m`, `n`, `c`, then the code of every ballot, voter by voter. -/
def electionCode (E : VotingSystem) {m n : ℕ} (c : Fin m) (P : Fin n → E.Ballot m) :
    List BSym :=
  encNats ([m, n, (c : ℕ)] ++ (List.ofFn fun v : Fin n => E.code (P v)).flatten)

/-- The language of constructive control by partition of voters: the codes of the yes-instances. -/
def ccLang (rule : TieRule) (E : VotingSystem) : Lang BSym :=
  { w | ∃ (m n : ℕ) (c : Fin m) (P : Fin n → E.Ballot m), CCPV rule E P c ∧ w = electionCode E c P }

/-- The language of destructive control by partition of voters: the codes of the yes-instances. -/
def dcLang (rule : TieRule) (E : VotingSystem) : Lang BSym :=
  { w | ∃ (m n : ℕ) (c : Fin m) (P : Fin n → E.Ballot m), DCPV rule E P c ∧ w = electionCode E c P }

/-- The code of the partition `(V₁, V₁ᶜ)` of the voters `Fin n`: the number `1`, then the
membership vector of `V₁` (`1` for a voter in `V₁`, `0` for a voter in `V₂`). -/
def partitionCode {n : ℕ} (V₁ : Finset (Fin n)) : List BSym :=
  encNats (1 :: List.ofFn fun v : Fin n => if v ∈ V₁ then 1 else 0)

/-- The output "control is impossible": the single number `0`. -/
def impossibleCode : List BSym := encNats [0]

/-! ## Vulnerability, certifiable vulnerability and resistance (Definition 3.1) -/

/-- Vulnerable to constructive control by partition of voters: susceptible, and the language is in
P. -/
def VulnerableCC (rule : TieRule) (E : VotingSystem) : Prop :=
  SusceptibleCC rule E ∧ ccLang rule E ∈ CookPvsNP.P BSym

/-- Vulnerable to destructive control by partition of voters: susceptible, and the language is in
P. -/
def VulnerableDC (rule : TieRule) (E : VotingSystem) : Prop :=
  SusceptibleDC rule E ∧ dcLang rule E ∈ CookPvsNP.P BSym

/-- Certifiably vulnerable to constructive control by partition of voters: susceptible, and a
polynomial-time computable function maps the code of every yes-instance to the code of a partition
that makes `c` the unique winner, and the code of every no-instance to `impossibleCode`. -/
def CertVulnerableCC (rule : TieRule) (E : VotingSystem) : Prop :=
  SusceptibleCC rule E ∧
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ (m n : ℕ) (c : Fin m) (P : Fin n → E.Ballot m),
        (CCPV rule E P c →
          ∃ V₁ : Finset (Fin n), twoStage rule E P V₁ = {c} ∧
            f (electionCode E c P) = partitionCode V₁) ∧
        (¬ CCPV rule E P c → f (electionCode E c P) = impossibleCode)

/-- Certifiably vulnerable to destructive control by partition of voters: susceptible, and a
polynomial-time computable function maps the code of every yes-instance to the code of a partition
that makes `c` not the unique winner, and the code of every no-instance to `impossibleCode`. -/
def CertVulnerableDC (rule : TieRule) (E : VotingSystem) : Prop :=
  SusceptibleDC rule E ∧
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ (m n : ℕ) (c : Fin m) (P : Fin n → E.Ballot m),
        (DCPV rule E P c →
          ∃ V₁ : Finset (Fin n), twoStage rule E P V₁ ≠ {c} ∧
            f (electionCode E c P) = partitionCode V₁) ∧
        (¬ DCPV rule E P c → f (electionCode E c P) = impossibleCode)

/-- Resistant to constructive control by partition of voters: susceptible, and the language is
NP-complete. -/
def ResistantCC (rule : TieRule) (E : VotingSystem) : Prop :=
  SusceptibleCC rule E ∧ NPComplete (ccLang rule E)

/-- Resistant to destructive control by partition of voters: susceptible, and the language is
NP-complete. -/
def ResistantDC (rule : TieRule) (E : VotingSystem) : Prop :=
  SusceptibleDC rule E ∧ NPComplete (dcLang rule E)

/-! ## Hitting Set (p. 24) and Restricted Hitting Set (p. 27) -/

/-- `B'` is a hitting set of the family `S`: it meets every `S i`. -/
def IsHittingSet {m n : ℕ} (S : Fin n → Finset (Fin m)) (B' : Finset (Fin m)) : Prop :=
  ∀ i, (S i ∩ B').Nonempty

/-- The code of a Hitting Set instance `(B, S, k)` with `B = Fin m` and `S : Fin n → Finset (Fin m)`:
the numbers `m`, `n`, `k`, then the incidence vector of each `S i`. -/
def hsCode (m n k : ℕ) (S : Fin n → Finset (Fin m)) : List BSym :=
  encNats ([m, n, k] ++
    (List.ofFn fun i : Fin n => List.ofFn fun j : Fin m => if j ∈ S i then 1 else 0).flatten)

/-- Hitting Set: the codes of the instances with a positive integer `k` such that `S` has a hitting
set of size at most `k`. -/
def hittingSetLang : Lang BSym :=
  { w | ∃ (m n k : ℕ) (S : Fin n → Finset (Fin m)), 1 ≤ k ∧
      (∃ B' : Finset (Fin m), B'.card ≤ k ∧ IsHittingSet S B') ∧ w = hsCode m n k S }

/-- Restricted Hitting Set: as Hitting Set, for the instances with `n(k + 1) + 1 ≤ m − k`
(written `n(k + 1) + 1 + k ≤ m`). -/
def restrictedHSLang : Lang BSym :=
  { w | ∃ (m n k : ℕ) (S : Fin n → Finset (Fin m)), 1 ≤ k ∧ n * (k + 1) + 1 + k ≤ m ∧
      (∃ B' : Finset (Fin m), B'.card ≤ k ∧ IsHittingSet S B') ∧ w = hsCode m n k S }

/-! ## Exact Cover by Three-Sets (p. 28) -/

/-- The code of an X3C instance with `B = Fin (3q)` and `S : Fin n → Finset (Fin (3q))`: the numbers
`3q`, `n`, then the incidence vector of each `S i`. -/
def x3cCode (q n : ℕ) (S : Fin n → Finset (Fin (3 * q))) : List BSym :=
  encNats ([3 * q, n] ++
    (List.ofFn fun i : Fin n => List.ofFn fun j : Fin (3 * q) => if j ∈ S i then 1 else 0).flatten)

/-- Exact Cover by Three-Sets: the codes of the instances with `m = 3q`, `q ≥ 1`, every `S i` of
size three, for which some subfamily covers every element of `B` exactly once. -/
def x3cLang : Lang BSym :=
  { w | ∃ (q n : ℕ) (S : Fin n → Finset (Fin (3 * q))), 1 ≤ q ∧ (∀ i, (S i).card = 3) ∧
      (∃ T : Finset (Fin n), ∀ b, (T.filter fun i => b ∈ S i).card = 1) ∧ w = x3cCode q n S }

end HHRControl.PV


