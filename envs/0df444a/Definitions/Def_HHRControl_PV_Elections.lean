-- Prove2me | Definitions.Def_HHRControl_PV_Elections
-- name    : HHRControl_PV_Elections
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:55.546516+00:00
-- url     : https://prove2.me/theorems/8477972b-8af8-43b6-92c6-1978202c376f
-- title:
--   §2, §3, pp. 3–8 — plurality, Condorcet and approval winner sets on a candidate subset, TE/TP nominees, the two-stage partition-of-voters election, and susceptibility
-- statement:
--   This file sets up the elections of §2 and the control problem *Control by Partition of Voters* of §3 of Hemaspaandra, Hemaspaandra and Rothe.
--
--   **Elections.** An election has the candidates $C=\{0,\dots,m-1\}$ and the voters $V=\{0,\dots,n-1\}$; voter $v$ casts the ballot $P(v)$ (so $V$ is a multiset of ballots, listed one voter at a time). For plurality and Condorcet voting a ballot is a strict linear order on $C$, given by the position $r(x)$ of each candidate ($r(x)<r(y)$ means $x$ is preferred to $y$). For approval voting a ballot is the set of approved candidates (its 0-1 vector). Ballots are always over all of $C$; the election $(D,U)$ with candidates $D\subseteq C$ and voters $U\subseteq V$ uses the preferences induced on $D$ (footnote 5).
--
--   **Winner sets.** For the election $(D,U)$:
--   1. *plurality*: the score of $x\in D$ is the number of voters in $U$ who rank $x$ first among $D$; the winners are the $x\in D$ of maximum score;
--   2. *Condorcet*: $x\in D$ wins iff for every $y\in D$, $y\neq x$,
--   $$\#\{v\in U : x \succ_v y\} > \#\{v\in U : y \succ_v x\},$$
--   i.e. $x$ beats $y$ by a strict majority in their pairwise election;
--   3. *approval*: the winners are the $x\in D$ approved by a maximum number of voters of $U$.
--
--   With $D=\emptyset$ there is no winner; there may also be no Condorcet winner.
--
--   **Tie-handling and the two-stage election.** A subcommittee $U$ holds the subelection $(C,U)$. In model **TP** (Ties-Promote) it nominates all its winners; in model **TE** (Ties-Eliminate) it nominates its winner if there is exactly one and nobody otherwise. For a partition of $V$ into $V_1$ and $V_2=V\setminus V_1$ (either may be empty), the nominees of $V_1$ and of $V_2$ run against each other in the final election with voter set $V$:
--   $$\mathrm{twoStage}(V_1)=W\bigl(N(V_1)\cup N(V_2),\,V\bigr).$$
--   *Constructive control* asks whether some partition makes the distinguished candidate $c$ the unique winner ($\mathrm{twoStage}(V_1)=\{c\}$); *destructive control* asks whether some partition makes $c$ not the unique winner ($\neq\{c\}$; an empty winner set counts).
--
--   **Susceptibility** (Definition 3.1). A voting system is susceptible to constructive control if in some election a candidate who is not the unique winner of $(C,V)$ can be made the unique winner, and susceptible to destructive control if in some election the unique winner of $(C,V)$ can be made not the unique winner; otherwise it is immune.
--
--   These are the objects of Theorem 3.6 and of every lemma used in its proof.
--
--   **Formalization Note** A voting system is a structure `VotingSystem` bundling the ballot type `Ballot m`, the winner-set function `winners m n P D U` and a ballot code `code` (used by the instance codes in `HHRControl.PV.Languages`): a ranking is coded as its candidates from most to least preferred, an approval ballot as its 0-1 vector. A ranking is `Equiv.Perm (Fin m)` read as the position map. The partition is `V₁ : Finset (Fin n)` and its complement.
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, pp. 3–4 §2 and footnote 5 (voting systems, TE/TP); pp. 4–5 Definition 3.1 (immune, susceptible); p. 8 Control by Partition of Voters

import Mathlib

namespace HHRControl.PV

/-! # Elections, winner sets on a candidate subset, and control by partition of voters

Hemaspaandra, Hemaspaandra & Rothe, *Anyone but Him*, arXiv:cs/0507027v5, §2 (pp. 3–4), §3
(Definition 3.1, pp. 4–5; Control by Partition of Voters, p. 8).

Conventions:
* An election has the candidates `Fin m` and the voters `Fin n`; a profile is `P : Fin n → β m`,
  one ballot per voter (the multiset `V` written as a list of ballots).
* A ranking ballot `r : Ranking m` gives every candidate its position: `r x < r y` means that the
  voter prefers `x` to `y` (position `0` is the most preferred candidate).
* An approval ballot is the `Finset` of the candidates the voter approves of ("Yes").
* Ballots are always over all of `Fin m`; the winner set of the election with candidate set `D`
  and voter set `U` uses the preferences induced on `D` (footnote 5, p. 3).
-/

/-- A strict ranking of the candidates `Fin m`: `r x` is the position of candidate `x`, `0` being
the most preferred position. -/
abbrev Ranking (m : ℕ) : Type := Equiv.Perm (Fin m)

/-- An approval ballot over the candidates `Fin m`: the set of candidates the voter approves of. -/
abbrev Approval (m : ℕ) : Type := Finset (Fin m)

/-- A voting system with ballots `Ballot m` over `m` candidates. `winners m n P D U` is the set of
winners of the election whose candidates are `D`, whose voters are `U`, and in which voter `v`
casts the ballot `P v` (read through the preferences it induces on `D`). `code` writes a ballot as a
list of natural numbers, for the instance codes of the control problems. -/
structure VotingSystem where
  /-- The ballots over `m` candidates. -/
  Ballot : ℕ → Type
  /-- The winner set of the election `(D, U)` under the profile `P`. -/
  winners : ∀ (m n : ℕ), (Fin n → Ballot m) → Finset (Fin m) → Finset (Fin n) → Finset (Fin m)
  /-- The code of a ballot, as a list of natural numbers. -/
  code : ∀ {m : ℕ}, Ballot m → List ℕ

/-! ## Plurality, Condorcet and approval voting (§2, p. 3) -/

/-- The plurality score of `x` in the election `(D, U)`: the number of voters in `U` who rank `x`
first among the candidates in `D`. -/
def pluralityScore {m n : ℕ} (P : Fin n → Ranking m) (D : Finset (Fin m)) (U : Finset (Fin n))
    (x : Fin m) : ℕ :=
  (U.filter fun v => ∀ y ∈ D, y ≠ x → P v x < P v y).card

/-- The number of voters in `U` who prefer `x` to `y`. -/
def prefCount {m n : ℕ} (P : Fin n → Ranking m) (U : Finset (Fin n)) (x y : Fin m) : ℕ :=
  (U.filter fun v => P v x < P v y).card

/-- The approval score of `x` among the voters `U`: the number of voters in `U` approving of `x`. -/
def approvalScore {m n : ℕ} (P : Fin n → Approval m) (U : Finset (Fin n)) (x : Fin m) : ℕ :=
  (U.filter fun v => x ∈ P v).card

/-- The ballot code of a ranking: the candidates from the most to the least preferred. -/
def rankingCode {m : ℕ} (r : Ranking m) : List ℕ :=
  List.ofFn fun i : Fin m => ((r.symm i : Fin m) : ℕ)

/-- The ballot code of an approval ballot: its 0-1 vector (`1` for "Yes"), candidate by candidate. -/
def approvalCode {m : ℕ} (A : Approval m) : List ℕ :=
  List.ofFn fun x : Fin m => if x ∈ A then 1 else 0

/-- Plurality voting: every candidate of `D` with a maximum number of voters in `U` ranking it
first among `D` wins. -/
def plurality : VotingSystem where
  Ballot := Ranking
  winners := fun _ _ P D U =>
    D.filter fun x => ∀ y ∈ D, pluralityScore P D U y ≤ pluralityScore P D U x
  code := rankingCode

/-- Condorcet voting: `x ∈ D` wins iff for every other `y ∈ D`, strictly more voters of `U` prefer
`x` to `y` than `y` to `x` (a strict majority in the pairwise election, ballots being strict). -/
def condorcet : VotingSystem where
  Ballot := Ranking
  winners := fun _ _ P D U =>
    D.filter fun x => ∀ y ∈ D, y ≠ x → prefCount P U y x < prefCount P U x y
  code := rankingCode

/-- Approval voting: every candidate of `D` with a maximum number of approvals among the voters `U`
wins. -/
def approval : VotingSystem where
  Ballot := Approval
  winners := fun _ _ P D U =>
    D.filter fun x => ∀ y ∈ D, approvalScore P U y ≤ approvalScore P U x
  code := approvalCode

/-! ## Control by partition of voters (p. 8) -/

/-- The two tie-handling models for subelections (p. 3): Ties-Eliminate and Ties-Promote. -/
inductive TieRule where
  | TE
  | TP
  deriving DecidableEq

/-- The nominees of the subcommittee `U` (the subelection `(C, U)` with all candidates `C`):
under TP every winner of the subelection; under TE its winner if it is the only one, and nobody if
two or more candidates tie for winning (or if there is no winner). -/
def nominees (rule : TieRule) (E : VotingSystem) {m n : ℕ} (P : Fin n → E.Ballot m)
    (U : Finset (Fin n)) : Finset (Fin m) :=
  match rule with
  | .TP => E.winners m n P Finset.univ U
  | .TE => if (E.winners m n P Finset.univ U).card = 1 then E.winners m n P Finset.univ U else ∅

/-- The winner set of the hierarchical two-stage election for the partition of the voters into
`V₁` and its complement `V₂ = V₁ᶜ`: the nominees of `(C, V₁)` and of `(C, V₂)` run against each other
with the whole voter set `V`. Either part may be empty. -/
def twoStage (rule : TieRule) (E : VotingSystem) {m n : ℕ} (P : Fin n → E.Ballot m)
    (V₁ : Finset (Fin n)) : Finset (Fin m) :=
  E.winners m n P (nominees rule E P V₁ ∪ nominees rule E P V₁ᶜ) Finset.univ

/-- Constructive control by partition of voters (p. 8): some partition of `V` makes `c` the unique
winner of the two-stage election. -/
def CCPV (rule : TieRule) (E : VotingSystem) {m n : ℕ} (P : Fin n → E.Ballot m) (c : Fin m) :
    Prop :=
  ∃ V₁ : Finset (Fin n), twoStage rule E P V₁ = {c}

/-- Destructive control by partition of voters (p. 8): some partition of `V` makes `c` not the
unique winner of the two-stage election. -/
def DCPV (rule : TieRule) (E : VotingSystem) {m n : ℕ} (P : Fin n → E.Ballot m) (c : Fin m) :
    Prop :=
  ∃ V₁ : Finset (Fin n), twoStage rule E P V₁ ≠ {c}

/-! ## Susceptibility (Definition 3.1, pp. 4–5) -/

/-- `E` is susceptible to constructive control by partition of voters (model `rule`): in some
election a candidate who is not the unique winner of `(C, V)` can be made the unique winner. -/
def SusceptibleCC (rule : TieRule) (E : VotingSystem) : Prop :=
  ∃ (m n : ℕ) (P : Fin n → E.Ballot m) (c : Fin m),
    E.winners m n P Finset.univ Finset.univ ≠ {c} ∧ CCPV rule E P c

/-- `E` is susceptible to destructive control by partition of voters (model `rule`): in some
election the unique winner `c` of `(C, V)` can be made not the unique winner. -/
def SusceptibleDC (rule : TieRule) (E : VotingSystem) : Prop :=
  ∃ (m n : ℕ) (P : Fin n → E.Ballot m) (c : Fin m),
    E.winners m n P Finset.univ Finset.univ = {c} ∧ DCPV rule E P c

end HHRControl.PV


