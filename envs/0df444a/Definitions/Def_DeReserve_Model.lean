-- Prove2me | Definitions.Def_DeReserve_Model
-- name    : DeReserve_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:10.68637+00:00
-- url     : https://prove2.me/theorems/a2520815-6961-41a5-b7d5-2582a2b53fdd
-- title:
--   India reserves with OBC de-reservation: categories, priorities, $C^{IN}_s$, $C^{BT}_s$, assignments, DA-BT and the axioms of Theorem 4
-- statement:
--   This module sets up the model of Aygün–Turhan for admissions to technical colleges in India with OBC de-reservation.
--
--   **Primitives.** There are a finite set $I$ of individuals and a finite set $S$ of institutions. The position categories are $\mathcal C=\{o,SC,ST,OBC\}$, where $o$ is the open category, and the reserve categories are $\mathcal R=\{SC,ST,OBC\}$. Each individual reports a membership $t_i\in\mathcal R\cup\{GC\}$. Institution $s$ has a capacity vector $q_s=(q^o_s,q^{SC}_s,q^{ST}_s,q^{OBC}_s)\in\mathbb N^4$ and $\bar q_s=q^o_s+q^{SC}_s+q^{ST}_s+q^{OBC}_s$ positions. Its priority $\succ_s$ is a strict linear order on $I\cup\{\emptyset\}$; $i$ is acceptable at $s$ when $i\succ_s\emptyset$. Each individual has a strict preference $P_i$ on $S\cup\{\emptyset\}$, with weak version $R_i$.
--
--   **India Reserves rule $C^{IN}_s(A,q)$.** For a set $A$ of applicants and a capacity vector $q$: the open category takes the $q^o$ highest-priority acceptable members of $A$; from the rest $A'$, each reserve category $r$ takes the $q^r$ highest-priority acceptable members of $A'$ with $t_i=r$. Each chosen applicant carries the label of the category she is chosen under.
--
--   **Backward Transfers rule $C^{BT}_s(A)$.** Start with $q^1_s=q_s$. At iteration $n$ run $C^{IN}_s(A,q^n_s)$ and let $\tau_n$ be the number of vacant OBC positions. If $\tau_n=0$ stop; otherwise move $\tau_n$ positions from OBC to the open category to get $q^{n+1}_s$. With $N$ the last iteration, $C^{BT}_s(A,q_s)=C^{IN}_s(A,q^N_s)$, labels included.
--
--   **Assignments.** An assignment $\eta$ gives each individual either nothing or an institution–category pair $(s,c)$, with $c=o$ for a GC individual and $c\in\{o,t_i\}$ otherwise, such that $|\eta(s)|\le\bar q_s$, $|\{j:(j,r)\in\eta(s)\}|\le q^r_s$ for $r\in\mathcal R$, and every seated individual is acceptable at her institution. The number of open positions is not capped by $q^o_s$. The induced matching is $\mu(\eta)$. A mechanism maps every preference profile and every membership profile to an assignment.
--
--   **DA-BT.** Applicant-proposing deferred acceptance under the rules $C^{BT}_s$: in each step every individual rejected in the previous step (everyone in step 1) applies to her best acceptable institution that has not rejected her; each institution holds $C^{BT}_s$ of the applicants it held plus its new applicants, with labels, and rejects the rest. The algorithm stops at the first step without a rejection.
--
--   **Axioms of Theorem 4.**
--   1. *Individual rationality:* $\mu_i(\eta)\,R_i\,\emptyset$.
--   2. *Meritocracy:* if $s\,P_i\,\mu(i)$, everyone holding an open position at $s$, or a position of $i$'s reserve category, has priority over $i$.
--   3. *Non-wastefulness:* if $s\,P_i\,\mu(i)$ and $i\succ_s\emptyset$, then $i$'s reserve positions at $s$ are full and $|\{j:(j,o)\text{ or }(j,OBC)\in\eta(s)\}|=q^o_s+q^{OBC}_s$.
--   4. *Open-first:* (1) $|\{j:(j,o)\text{ or }(j,OBC)\in\eta(s)\}|=\min(|\eta(s)|,q^o_s+q^{OBC}_s)$; (2) every open holder has priority over every reserve holder; (3a) an individual with fewer than $q^o_s+q^{OBC}_s-|\{j:(j,OBC)\in\eta(s)\}|$ higher-priority individuals in $\mu_s(\eta)$ holds an open position; (3) for every open holder $i$ with $t_i=r\in\mathcal R$, moving $i$ to an $r$ position either exceeds $q^r_s$ or violates (1), (2) or (3a).
--   5. *Incentive-compatibility:* no individual gains from reporting another preference together with a membership in $\{t_i,GC\}$.
--
--   The module also defines stability with respect to the $C^{BT}_s$, strategy-proofness in preferences for a fixed membership profile, compliance with the spirit of affirmative action (Definition 1), and Afacan's improvement relation.
--
--   **Formalization Note** Priorities and preferences are rank bijections $\mathrm{Option}\,I\simeq\mathrm{Fin}(|I|+1)$ and $\mathrm{Option}\,S\simeq\mathrm{Fin}(|S|+1)$, rank $0$ best, with `none` for $\emptyset$; a membership is `Option Res`, `none` being GC. $C^{IN}_s$, $C^{BT}_s$ and DA-BT return labels (`I → Option Cat`, `I → Option (S × Cat)`). $C^{BT}_s$ searches its last iteration among $q^{OBC}_s+1$ iterations and DA-BT runs $|I|\cdot|S|+1$ steps; neither bound is reached before termination. Five deviations from the printed text are built in and declared on every theorem that uses them: assignments seat only acceptable individuals (correction C2), non-wastefulness concerns pairs with $i\succ_s\emptyset$ (reading R1), open-first has the added (3a) and the corrected (3) (correction C1), membership deviations are $\tilde t_i\in\{t_i,GC\}$ (reading R2), and DA proposals go only to institutions the individual finds acceptable (reading R0).
-- source:
--   Aygün–Turhan, How to De-reserve Reserves: Admissions to Technical Colleges in India, arXiv:2103.05899v5, §2 Framework pp.6–10 (categories, memberships, capacities, priorities, preferences, C^IN p.8–9, matching/assignment p.9–10, mechanism and incentive-compatibility p.10), Definition 1 pp.11–12, §4 Backward Transfers Choice Rule pp.18–19, §4.1 DA-BT pp.20–21, §4.2 axioms pp.22–24, stability p.37 and Lemma 2 p.42, improvement (Afacan 2017, Def. 8) p.36

import Mathlib

namespace DeReserve

/-!
# How to De-reserve Reserves: the model

Aygün–Turhan, *How to De-reserve Reserves: Admissions to Technical Colleges in India*,
arXiv:2103.05899v5 (22 May 2022): §2 Framework (pp.6–10), Definition 1 (pp.11–12), §4 the
backward transfers choice rule and DA-BT (pp.18–21), §4.2 the axioms (pp.22–24), and the
proof-only notions of the Appendix (stability, p.37 and Lemma 2 p.42; strategy-proofness;
the improvement relation, p.36).

This module bundles the tightly coupled objects of the paper: categories, memberships,
capacities, priorities, preferences, the India Reserves rule `C^IN_s`, the backward transfers
rule `C^BT_s`, assignments, the DA-BT mechanism and the five axioms of Theorem 4.

**Formalization Note.**
* Individuals `I` and institutions `S` are arbitrary finite types (either may be empty).
* `∅` (remaining unmatched / leaving a position empty) is `none`.
* A priority `≻_s` (a strict linear order on `I ∪ {∅}`, p.7) is a rank bijection
  `Option I ≃ Fin (|I| + 1)`, rank `0` being the highest priority: `i ≻_s j` is
  `pri s (some i) < pri s (some j)`, and `i` is acceptable at `s` iff `i ≻_s ∅`. Every strict
  linear order on `I ∪ {∅}` is such a bijection and conversely, so no instance is lost or added.
  Acceptable sets are arbitrary.
* A preference `P_i` (a strict linear order on `S ∪ {∅}`, p.7) is a rank bijection
  `Option S ≃ Fin (|S| + 1)`, rank `0` most preferred: `x P_i y` is `P i x < P i y` and
  `x R_i y` is `P i x ≤ P i y`.
* A membership is `Option Res`, `none` being `GC` (general category).
* A capacity vector is a function `Cat → ℕ`; `q s` is `(q^o_s, q^SC_s, q^ST_s, q^OBC_s)` and the
  number of positions is `q̄_s = q^o_s + q^SC_s + q^ST_s + q^OBC_s` (p.6).
* `C^IN_s` and `C^BT_s` return a *labelled* choice `I → Option Cat` (`none` = not chosen);
  the chosen set is the set of labelled applicants.
* An assignment is `η : I → Option (S × Cat)`; `η(s)` is the finset of pairs `(i, c)` with
  `η i = some (s, c)`.
-/

/-! ## Primitives (§2, pp.6–7) -/

/-- The position categories `C = {o, SC, ST, OBC}` (p.6); `o` is the open category. -/
inductive Cat
  | o
  | SC
  | ST
  | OBC
  deriving DecidableEq, Repr

instance : Fintype Cat := ⟨{.o, .SC, .ST, .OBC}, fun x => by cases x <;> decide⟩

/-- The reserve categories `R = {SC, ST, OBC}` (p.6). -/
inductive Res
  | SC
  | ST
  | OBC
  deriving DecidableEq, Repr

instance : Fintype Res := ⟨{.SC, .ST, .OBC}, fun x => by cases x <;> decide⟩

/-- A reserve category viewed as a position category. -/
def Res.toCat : Res → Cat
  | .SC => .SC
  | .ST => .ST
  | .OBC => .OBC

/-- A (reported) category membership `t_i ∈ R ∪ {GC}` (p.6): `some r` is membership of the
reserve category `r`, `none` is `GC`. -/
abbrev CatMembership := Option Res

/-- A vector of positions over categories, `(q^o, q^SC, q^ST, q^OBC)` (p.6). -/
abbrev Cap := Cat → ℕ

/-- The number of positions `q̄_s = q^o_s + q^SC_s + q^ST_s + q^OBC_s` of a capacity vector
(p.6: `q^o_s = q_s − q^SC_s − q^ST_s − q^OBC_s`). -/
def Cap.total (q : Cap) : ℕ := q .o + q .SC + q .ST + q .OBC

/-- A strict priority `≻_s` over `I ∪ {∅}` (p.7), as a rank bijection; smaller rank is higher
priority, `none` is `∅`. -/
abbrev Priority (I : Type*) [Fintype I] := Option I ≃ Fin (Fintype.card I + 1)

/-- A strict preference `P_i` over `S ∪ {∅}` (p.7), as a rank bijection; smaller rank is more
preferred, `none` is `∅`. -/
abbrev Pref (S : Type*) [Fintype S] := Option S ≃ Fin (Fintype.card S + 1)

variable {I S : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]

/-- `i ≻_s j`: applicant `i` has higher priority than `j` (p.7). -/
def Priority.higher (p : Priority I) (i j : I) : Prop := p (some i) < p (some j)

instance (p : Priority I) (i j : I) : Decidable (p.higher i j) := by
  unfold Priority.higher; infer_instance

/-- `i ≻_s ∅`: applicant `i` is acceptable (p.7). -/
def Priority.Acceptable (p : Priority I) (i : I) : Prop := p (some i) < p none

instance (p : Priority I) (i : I) : Decidable (p.Acceptable i) := by
  unfold Priority.Acceptable; infer_instance

/-- The `k` highest-priority members of `X` under `≻_s` (all of `X` if `|X| ≤ k`): the members
`i` of `X` with fewer than `k` members of `X` ranked above them. -/
def topK (p : Priority I) (X : Finset I) (k : ℕ) : Finset I :=
  X.filter fun i => (X.filter fun j => p.higher j i).card < k

/-! ## The India Reserves choice rule `C^IN_s` (pp.8–9) -/

/-- `C^o_s(A, k)` (pp.8, 32): the open-category stage alone, i.e. the `k` highest-priority
*acceptable* members of `A` ("individuals are selected following `≻_s` up to the capacity"). -/
def openChoice (p : Priority I) (A : Finset I) (k : ℕ) : Finset I :=
  topK p (A.filter p.Acceptable) k

/-- `C^r_s(A', q^r)` (p.8, Stage 2): the `k` highest-priority acceptable members of `A'` with
membership `r`, i.e. selection following the category merit order `≻^r_s` of p.7. -/
def resChoice (p : Priority I) (T : I → CatMembership) (A' : Finset I) (r : Res) (k : ℕ) :
    Finset I :=
  topK p ((A'.filter p.Acceptable).filter fun i => T i = some r) k

/-- **The India Reserves choice rule `C^IN_s(A, q)` with labels** (pp.8–9). Stage 1: the open
category takes `C^o_s(A, q^o)`. Stage 2: from `A' = A \ C^o_s(A, q^o)`, each reserve category
`r` takes `C^r_s(A', q^r)`. The value at `i` is the category under which `i` is chosen, or
`none` if `i` is not chosen. The capacity vector `q` is arbitrary (C^BT calls it with updated
vectors). -/
def cin (p : Priority I) (T : I → CatMembership) (A : Finset I) (q : Cap) : I → Option Cat :=
  fun i =>
    if i ∈ openChoice p A (q .o) then some .o
    else
      match T i with
      | none => none
      | some r =>
        if i ∈ resChoice p T (A \ openChoice p A (q .o)) r (q r.toCat) then some r.toCat
        else none

/-- The number of applicants labelled `c` by a labelled choice. -/
def labelCount (ch : I → Option Cat) (c : Cat) : ℕ :=
  (Finset.univ.filter fun i => ch i = some c).card

/-! ## The backward transfers choice rule `C^BT_s` (pp.18–19) -/

/-- `τ`: the number of vacant OBC positions after running `C^IN_s(A, q)` (p.18). -/
def vacantOBC (p : Priority I) (T : I → CatMembership) (A : Finset I) (q : Cap) : ℕ :=
  q .OBC - labelCount (cin p T A q) .OBC

/-- One backward transfer (p.18): move the `τ` vacant OBC positions to the open category.
When `τ = 0` the vector is unchanged. -/
def transfer (p : Priority I) (T : I → CatMembership) (A : Finset I) (q : Cap) : Cap :=
  fun c =>
    match c with
    | .o => q .o + vacantOBC p T A q
    | .OBC => q .OBC - vacantOBC p T A q
    | c => q c

/-- `q^n_s` (p.18), indexed from `1` as in the paper: `q^1_s = q_s` and
`q^{n+1}_s` is obtained from `q^n_s` by one backward transfer. (The value at index `0` is set
to `q_s` as well and is never used.) Once `τ_n = 0` the sequence is constant. -/
def iterCaps (p : Priority I) (T : I → CatMembership) (q : Cap) (A : Finset I) : ℕ → Cap
  | 0 => q
  | 1 => q
  | n + 2 => transfer p T A (iterCaps p T q A (n + 1))

/-- Search for the last iteration from iteration `n` on, with `fuel` further iterations. -/
def lastIterAux (p : Priority I) (T : I → CatMembership) (q : Cap) (A : Finset I) :
    ℕ → ℕ → ℕ
  | 0, n => n
  | fuel + 1, n =>
    if vacantOBC p T A (iterCaps p T q A n) = 0 then n
    else lastIterAux p T q A fuel (n + 1)

/-- `N`, the last iteration of `C^BT_s(A, q_s)` (pp.18–19, 32): the first iteration `n ≥ 1`
with `τ_n = 0`. Each non-final iteration lowers `q^OBC` by `τ_n ≥ 1`, and `τ_n = 0` once
`q^{OBC,n} = 0`, so `N ≤ q^OBC_s + 1`; the search uses that many iterations as fuel. -/
def lastIter (p : Priority I) (T : I → CatMembership) (q : Cap) (A : Finset I) : ℕ :=
  lastIterAux p T q A (q .OBC) 1

/-- **The backward transfers choice rule `C^BT_s(A, q_s)` with labels** (pp.18–19):
`C^BT_s(A, q_s) = C^IN_s(A, q^N_s)` with `N` the last iteration. -/
def cbt (p : Priority I) (T : I → CatMembership) (q : Cap) (A : Finset I) : I → Option Cat :=
  cin p T A (iterCaps p T q A (lastIter p T q A))

/-- The set of applicants chosen by `C^BT_s(A, q_s)`. -/
def chosenBT (p : Priority I) (T : I → CatMembership) (q : Cap) (A : Finset I) : Finset I :=
  Finset.univ.filter fun i => cbt p T q A i ≠ none

/-! ## Assignments and matchings (pp.9–10) -/

/-- An assignment `η : I → Option (S × Cat)` (p.9): `η i = some (s, c)` means that `i` holds a
category-`c` position at `s`, `none` that `i` is unmatched. -/
abbrev Assignment (I S : Type*) := I → Option (S × Cat)

/-- `η(s)`: the set of individual–category pairs of institution `s` (p.9). -/
def atInst (η : Assignment I S) (s : S) : Finset (I × Cat) :=
  Finset.univ.filter fun x => η x.1 = some (s, x.2)

/-- `μ_i(η)`: the institution `i` is matched with, `none` if unmatched (p.10). -/
def muI (η : Assignment I S) (i : I) : Option S := (η i).map Prod.fst

/-- `μ_s(η)`: the set of individuals matched with `s` (p.10). -/
def muS (η : Assignment I S) (s : S) : Finset I :=
  Finset.univ.filter fun i => muI η i = some s

/-- `|{j | (j, c) ∈ H}|` for a set `H` of individual–category pairs. -/
def catCount (H : Finset (I × Cat)) (c : Cat) : ℕ :=
  ((H.filter fun x => x.2 = c).image Prod.fst).card

/-- `|{j | (j, o) ∈ H or (j, OBC) ∈ H}|` for a set `H` of individual–category pairs. -/
def openOBCCount (H : Finset (I × Cat)) : ℕ :=
  ((H.filter fun x => x.2 = .o ∨ x.2 = .OBC).image Prod.fst).card

/-- A label `c` is one the membership `t` is eligible for (p.9, item 1): `o` always, and `r`
when `t = r ∈ R`. -/
def Eligible (t : CatMembership) (c : Cat) : Prop :=
  c = .o ∨ ∃ r, t = some r ∧ c = r.toCat

/-- **Feasible assignment** (p.9, items 1–2, with correction C2). Given capacities `q`,
priorities `pri` and the (reported) membership profile `T`:
1. a GC individual holds only open positions, a member of `r ∈ R` only open or `r` positions;
2. `|η(s)| ≤ q̄_s` and `|{j | (j, r) ∈ η(s)}| ≤ q^r_s` for every `r ∈ R`;
3. (C2) an individual holds a position at `s` only if she is acceptable at `s` (`i ≻_s ∅`).
Item 3 of p.9 (`η(i) = (s, c)` iff `(i, c) ∈ η(s)`) holds by construction. The number of open
positions at `s` is *not* capped by `q^o_s`. -/
def IsAssignment (q : S → Cap) (pri : S → Priority I) (T : I → CatMembership)
    (η : Assignment I S) : Prop :=
  (∀ i s c, η i = some (s, c) → Eligible (T i) c) ∧
  (∀ s, (atInst η s).card ≤ (q s).total) ∧
  (∀ s (r : Res), catCount (atInst η s) r.toCat ≤ q s r.toCat) ∧
  (∀ i s c, η i = some (s, c) → (pri s).Acceptable i)

instance (t : CatMembership) (c : Cat) : Decidable (Eligible t c) := by
  unfold Eligible; infer_instance

instance (q : S → Cap) (pri : S → Priority I) (T : I → CatMembership) (η : Assignment I S) :
    Decidable (IsAssignment q pri T η) := by
  unfold IsAssignment; infer_instance

/-- A mechanism (p.10): a map from reported preference profiles and reported membership
profiles to assignments, on the full domain `P × T`. Feasibility of the output is stated
separately (`IsAssignment`). -/
abbrev Mechanism (I S : Type*) [Fintype S] := (I → Pref S) → (I → CatMembership) → Assignment I S

/-! ## DA-BT (pp.20–21) -/

/-- The best institution for `P_i` among those not in `excl` that are acceptable to `i`
(`s P_i ∅`); `none` if there is none. Computed as the institution of least rank among the
options that are `∅` or outside `excl`. -/
def bestAcceptable (P : Pref S) (excl : Finset S) : Option S :=
  match (Finset.univ.filter fun k : Fin (Fintype.card S + 1) =>
      ∀ s, P.symm k = some s → s ∉ excl).min with
  | ⊤ => none
  | (k : Fin (Fintype.card S + 1)) => P.symm k

/-- The state of the DA-BT procedure after a step: the tentative assignment (who is held where,
with the label given by `C^BT_s`), the institutions that have rejected each individual so far,
and the individuals rejected in that step (the proposers of the next step). -/
structure DAState (I S : Type*) where
  /-- Tentative assignment at the end of the step. -/
  held : Assignment I S
  /-- `rejected i`: the institutions that have rejected `i` so far. -/
  rejected : I → Finset S
  /-- The individuals rejected in the step (the proposers of the next step). -/
  rejLast : Finset I

/-- The state before step 1: nobody is held, nobody has been rejected, and every individual
proposes in step 1. -/
def DAState.init : DAState I S :=
  ⟨fun _ => none, fun _ => ∅, Finset.univ⟩

/-- **One step of DA-BT** (pp.20–21). If the previous step had no rejection, the algorithm has
terminated and the state is unchanged. Otherwise each individual rejected in the previous step
(every individual in step 1) applies to her best institution that has not rejected her and
that is acceptable to her (if any). `A^n_s` is the set held by `s` at the end of the previous
step together with the new proposers of `s`; `s` tentatively holds `C^BT_s(A^n_s, q_s)` (with
its labels) and rejects the rest of `A^n_s`, including previously held individuals. -/
def daStep (q : S → Cap) (pri : S → Priority I) (P : I → Pref S) (T : I → CatMembership)
    (st : DAState I S) : DAState I S :=
  if st.rejLast = ∅ then st
  else
    -- the institution each individual is at in step `n`: held there, or newly applying there
    let cand : I → Option S := fun i =>
      match muI st.held i with
      | some s => some s
      | none => if i ∈ st.rejLast then bestAcceptable (P i) (st.rejected i) else none
    let apps : S → Finset I := fun s => Finset.univ.filter fun i => cand i = some s
    { held := fun i =>
        match cand i with
        | some s => (cbt (pri s) T (q s) (apps s) i).map fun c => (s, c)
        | none => none
      rejected := fun i =>
        match cand i with
        | some s => if cbt (pri s) T (q s) (apps s) i = none then insert s (st.rejected i)
                    else st.rejected i
        | none => st.rejected i
      rejLast := Finset.univ.filter fun i =>
        ∃ s, cand i = some s ∧ cbt (pri s) T (q s) (apps s) i = none }

/-- **The DA-BT mechanism** (pp.20–21): run `daStep` from the initial state. A rejection
permanently adds a pair `(i, s)` to the rejection record, so at most `|I|·|S|` steps contain
a rejection and the algorithm has terminated after `|I|·|S| + 1` steps; the outcome is the
tentative assignment at that point, each individual carrying the category label given by
`C^BT_s` at the final step. -/
def daBT (q : S → Cap) (pri : S → Priority I) : Mechanism I S :=
  fun P T =>
    ((daStep q pri P T)^[Fintype.card I * Fintype.card S + 1] DAState.init).held

/-! ## The axioms (pp.10, 22–23) -/

/-- **Individual rationality** of an assignment (p.22): `μ_i(η) R_i ∅` for every `i`. -/
def IndividuallyRational (P : I → Pref S) (η : Assignment I S) : Prop :=
  ∀ i, P i (muI η i) ≤ P i none

/-- **Meritocracy** of an assignment (p.22): for every `(i, s)` with `s P_i μ(i)`, every `j`
with `(j, o) ∈ η(s)`, or with `(j, t(i)) ∈ η(s)` where `t(i) ∈ R`, satisfies `j ≻_s i`. -/
def Meritocratic (pri : S → Priority I) (P : I → Pref S) (T : I → CatMembership)
    (η : Assignment I S) : Prop :=
  ∀ i s, P i (some s) < P i (muI η i) →
    ∀ j, ((j, Cat.o) ∈ atInst η s ∨ ∃ r, T i = some r ∧ (j, r.toCat) ∈ atInst η s) →
      (pri s).higher j i

/-- **Non-wastefulness** of an assignment (p.22, reading R1): for every `(i, s)` with
`s P_i μ(i)` and `i ≻_s ∅` (the positions `i` is eligible for at `s`), if `t(i) ∈ R` then
`|{j | (j, t(i)) ∈ η(s)}| = q^{t(i)}_s`, and `|{j | (j, o) ∈ η(s) or (j, OBC) ∈ η(s)}| =
q^o_s + q^OBC_s`. -/
def NonWasteful (q : S → Cap) (pri : S → Priority I) (P : I → Pref S) (T : I → CatMembership)
    (η : Assignment I S) : Prop :=
  ∀ i s, P i (some s) < P i (muI η i) → (pri s).Acceptable i →
    (∀ r, T i = some r → catCount (atInst η s) r.toCat = q s r.toCat) ∧
    openOBCCount (atInst η s) = q s .o + q s .OBC

/-- Open-first condition (1) for a set `H` of pairs at `s` (p.23):
`|{j | (j, o) ∈ H or (j, OBC) ∈ H}| = min(|H|, q^o_s + q^OBC_s)`. -/
def OF1 (qs : Cap) (H : Finset (I × Cat)) : Prop :=
  openOBCCount H = min H.card (qs .o + qs .OBC)

/-- Open-first condition (2) for a set `H` of pairs at `s` (p.23): `(i, o) ∈ H` and
`(j, r) ∈ H` with `r ∈ R` imply `i ≻_s j`. -/
def OF2 (ps : Priority I) (H : Finset (I × Cat)) : Prop :=
  ∀ i j (r : Res), (i, Cat.o) ∈ H → (j, r.toCat) ∈ H → ps.higher i j

/-- Open-first condition (3a) for a set `H` of pairs at `s` (correction C1, the extended
over-and-above principle of p.23): every `(i, c) ∈ H` such that fewer than
`q^o_s + q^OBC_s − |{j | (j, OBC) ∈ H}|` individuals of `H` rank above `i` has `c = o`. -/
def OF3a (qs : Cap) (ps : Priority I) (H : Finset (I × Cat)) : Prop :=
  ∀ x ∈ H, ((H.image Prod.fst).filter fun j => ps.higher j x.1).card <
      qs .o + qs .OBC - catCount H .OBC → x.2 = .o

/-- `η'(s) = (η(s) \ {(i, o)}) ∪ {(i, r)}` (p.23, open-first (3)): the pair `(i, o)` is
replaced by `(i, r)`. -/
def moveToRes (H : Finset (I × Cat)) (i : I) (r : Res) : Finset (I × Cat) :=
  insert (i, r.toCat) (H.erase (i, Cat.o))

/-- **Open-first** at institution `s` (p.23, corrected C1): (1), (2), (3a) hold for `η(s)`, and
(3) for every `i` with `(i, o) ∈ η(s)` and `t(i) = r ∈ R`, the set
`η'(s) = (η(s) \ {(i, o)}) ∪ {(i, r)}` either exceeds the capacity `q^r_s` or violates (1),
(2) or (3a). -/
def OpenFirstAt (q : S → Cap) (pri : S → Priority I) (T : I → CatMembership)
    (η : Assignment I S) (s : S) : Prop :=
  OF1 (q s) (atInst η s) ∧ OF2 (pri s) (atInst η s) ∧ OF3a (q s) (pri s) (atInst η s) ∧
  ∀ i (r : Res), (i, Cat.o) ∈ atInst η s → T i = some r →
    q s r.toCat < catCount (moveToRes (atInst η s) i r) r.toCat ∨
      ¬ OF1 (q s) (moveToRes (atInst η s) i r) ∨ ¬ OF2 (pri s) (moveToRes (atInst η s) i r) ∨
      ¬ OF3a (q s) (pri s) (moveToRes (atInst η s) i r)

/-- **Open-first** of an assignment (p.23, corrected C1): it holds at every institution. -/
def OpenFirst (q : S → Cap) (pri : S → Priority I) (T : I → CatMembership)
    (η : Assignment I S) : Prop :=
  ∀ s, OpenFirstAt q pri T η s

instance (qs : Cap) (H : Finset (I × Cat)) : Decidable (OF1 qs H) := by
  unfold OF1; infer_instance

instance (ps : Priority I) (H : Finset (I × Cat)) : Decidable (OF2 ps H) := by
  unfold OF2; infer_instance

instance (qs : Cap) (ps : Priority I) (H : Finset (I × Cat)) : Decidable (OF3a qs ps H) := by
  unfold OF3a; infer_instance

instance (q : S → Cap) (pri : S → Priority I) (T : I → CatMembership) (η : Assignment I S)
    (s : S) : Decidable (OpenFirstAt q pri T η s) := by
  unfold OpenFirstAt; infer_instance

instance (q : S → Cap) (pri : S → Priority I) (T : I → CatMembership) (η : Assignment I S) :
    Decidable (OpenFirst q pri T η) := by
  unfold OpenFirst; infer_instance

instance (P : I → Pref S) (η : Assignment I S) : Decidable (IndividuallyRational P η) := by
  unfold IndividuallyRational; infer_instance

instance (pri : S → Priority I) (P : I → Pref S) (T : I → CatMembership) (η : Assignment I S) :
    Decidable (Meritocratic pri P T η) := by
  unfold Meritocratic; infer_instance

instance (q : S → Cap) (pri : S → Priority I) (P : I → Pref S) (T : I → CatMembership)
    (η : Assignment I S) : Decidable (NonWasteful q pri P T η) := by
  unfold NonWasteful; infer_instance

/-- A mechanism is individually rational if every outcome is (p.22). -/
def Mechanism.IR (φ : Mechanism I S) : Prop :=
  ∀ P T, IndividuallyRational P (φ P T)

/-- A mechanism complies with meritocracy if every outcome does (p.22). -/
def Mechanism.Meritocratic (pri : S → Priority I) (φ : Mechanism I S) : Prop :=
  ∀ P T, DeReserve.Meritocratic pri P T (φ P T)

/-- A mechanism is non-wasteful if every outcome is (p.23). -/
def Mechanism.NonWasteful (q : S → Cap) (pri : S → Priority I) (φ : Mechanism I S) : Prop :=
  ∀ P T, DeReserve.NonWasteful q pri P T (φ P T)

/-- A mechanism satisfies open-first if every outcome does (p.24). -/
def Mechanism.OpenFirst (q : S → Cap) (pri : S → Priority I) (φ : Mechanism I S) : Prop :=
  ∀ P T, DeReserve.OpenFirst q pri T (φ P T)

/-- **Incentive-compatibility** (p.10, reading R2): for every `(P, T)`, every `i`, every
reported preference `P̃_i` and every reported membership `t̃_i ∈ {t_i, GC}`, it is not the case
that `μ_i(φ((P̃_i, P_{-i}), (t̃_i, T_{-i}))) P_i μ_i(φ(P, T))`. The preference and membership
reports may be changed at once. -/
def Mechanism.IncentiveCompatible (φ : Mechanism I S) : Prop :=
  ∀ (P : I → Pref S) (T : I → CatMembership) (i : I) (P' : Pref S) (t' : CatMembership),
    (t' = T i ∨ t' = none) →
    ¬ P i (muI (φ (Function.update P i P') (Function.update T i t')) i) < P i (muI (φ P T) i)

/-! ## Proof-only notions (Appendix) -/

/-- **Stability with respect to the BT choice rules** (p.37; Lemma 2, p.42) of the matching
`μ : I → Option S` at preferences `P` and reported memberships `T`:
(1) `μ_i R_i ∅` for all `i`; (2) `C^BT_s(μ_s, q_s) = μ_s` for all `s`; (3) there is no `(i, s)`
with `s P_i μ_i` and `i ∈ C^BT_s(μ_s ∪ {i}, q_s)`. -/
def StableBT (q : S → Cap) (pri : S → Priority I) (P : I → Pref S) (T : I → CatMembership)
    (μ : I → Option S) : Prop :=
  (∀ i, P i (μ i) ≤ P i none) ∧
  (∀ s, chosenBT (pri s) T (q s) (Finset.univ.filter fun i => μ i = some s) =
      Finset.univ.filter fun i => μ i = some s) ∧
  ¬ ∃ i s, P i (some s) < P i (μ i) ∧
      i ∈ chosenBT (pri s) T (q s) (insert i (Finset.univ.filter fun j => μ j = some s))

instance (q : S → Cap) (pri : S → Priority I) (P : I → Pref S) (T : I → CatMembership)
    (μ : I → Option S) : Decidable (StableBT q pri P T μ) := by
  unfold StableBT; infer_instance

/-- **Strategy-proofness in preferences** for every fixed membership profile (pp.36, 44): no
`i` gains by reporting `P̃_i` instead of `P_i` while `T` is unchanged. -/
def Mechanism.StrategyProof (φ : Mechanism I S) : Prop :=
  ∀ (P : I → Pref S) (T : I → CatMembership) (i : I) (P' : Pref S),
    ¬ P i (muI (φ (Function.update P i P') T) i) < P i (muI (φ P T) i)

/-- **Complies with the spirit of affirmative action** (Definition 1, pp.11–12), for a choice
rule depending on the reported membership profile: for every `A`, `T` and every member `i` of
a reserve category `r` (`t_i = r`), if `i ∉ C(A)` when `i` reports `r`, then `i ∉ C(A)` when
`i` reports `GC`. -/
def CompliesSpiritAA (C : (I → CatMembership) → Finset I → Finset I) : Prop :=
  ∀ (A : Finset I) (T : I → CatMembership) (i : I) (r : Res), T i = some r →
    i ∉ C T A → i ∉ C (Function.update T i none) A

/-- **Improvement** (Afacan 2017, Definition 8, as adapted on p.36): `C'` is an improvement over
`C` for `i` if for every `A`, (i) `i ∈ C(A)` implies `i ∈ C'(A)`, and (ii) `i ∉ C(A) ∪ C'(A)`
implies `C(A) = C'(A)`. -/
def IsImprovement (C' C : Finset I → Finset I) (i : I) : Prop :=
  ∀ A, (i ∈ C A → i ∈ C' A) ∧ (i ∉ C A ∪ C' A → C A = C' A)

end DeReserve


