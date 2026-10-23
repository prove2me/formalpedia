-- Prove2me | Definitions.Def_AffirmativeChoice_Reserve_Model
-- name    : AffirmativeChoice_Reserve_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:14.121223+00:00
-- url     : https://prove2.me/theorems/961f8998-8bed-4685-a07e-588400cf586d
-- title:
--   §2–§4, pp. 5–10 and Appendix A, p. 19 — choice problems, affirmative action axioms, MPI, MTC, reserve functions, reserve representation, Condition B
-- statement:
--   This file sets up the model of Doğan and Yıldız, *Choice with Affirmative Action*, for a school of capacity $q$.
--
--   **Problems.** Let $\mathcal S$ be a nonempty finite set of students. A *problem* $(S,\tau,\succ)$ consists of a set $S\subseteq\mathcal S$ of applicants, a type function $\tau$ ($\tau(s)=1$: minority, $\tau(s)=0$: majority) and a strict priority ordering $\succ$ on $S$. We write $S^m$ and $S^M$ for the minority and majority students of $S$. The *rank* of $s$ is $\mathrm{rank}(s,\succ)=|\{s'\in S: s'\succ s\}|+1$, and $r_k(\succ)$ is the student of rank $k$. The *restriction* of a problem to $S'\subseteq S$ keeps the types and the priority ordering of the students in $S'$.
--
--   **Tiers.** The *top tier* $T(S,\tau,\succ)$ is the set of students of rank at most $q$ (all of $S$ if $|S|\le q$); the *bottom tier* is $B=S\setminus T$. We write $T^m=S^m\cap T$, $T^M=S^M\cap T$, and $B^m=S^m\cap B$. Two problems have *coinciding top tiers* if their top tiers are the same set with the same relative priority ordering.
--
--   **Choice rules.** A *choice rule* $C$ maps each problem to a set $C(S,\tau,\succ)\subseteq S$ of at most $q$ students, nonempty when $S$ is nonempty. $C^m$ denotes the chosen minority students and $C^A=C^m\cap B$ the minority students *chosen via affirmative action*.
--
--   **Changes of a problem.** $\tau'$ is obtained from $\tau$ by *changing the type* of $s\in S$ if $\tau'(s)\neq\tau(s)$ and $\tau'(s')=\tau(s')$ for every other $s'\in S$. A priority ordering $\succ'$ is an *improvement* over $\succ$ for $s$ if $s\succ s'$ implies $s\succ' s'$ for each $s'$, there is some $s'\neq s$ with $s'\succ s$ and $s\succ' s'$, and $\succ$ and $\succ'$ agree on pairs of students other than $s$.
--
--   **Axioms.**
--   1. *Capacity-filling*: $|C(S,\tau,\succ)|=\min\{|S|,q\}$.
--   2. *Neutrality*: if $|S|=|S'|$ and $\tau(r_k(\succ))=\tau'(r_k(\succ'))$ for every $k\in\{1,\dots,|S|\}$, then $r_k(\succ)\in C(S,\tau,\succ)$ if and only if $r_k(\succ')\in C(S',\tau',\succ')$ for every $k$.
--   3. *Priority-compatibility*: if $s$ is chosen, $s'$ is not, and $s'\succ s$, then $s$ is a minority and $s'$ a majority student.
--   4. An *affirmative action rule* satisfies 1–3.
--   5. *Substitutability*: a chosen student remains chosen in every restriction to a set $S'\subseteq S$ containing it.
--   6. *MPI* (monotonicity in priority improvements): if $s\in C^m(S,\tau,\succ)$ and $\succ'$ is an improvement over $\succ$ for $s$, then $C^m(S,\tau,\succ)\subseteq C^m(S,\tau,\succ')$.
--   7. *MTC* (monotonicity in type changes): if $s\in C^m(S,\tau,\succ)$ and $\tau'$ is obtained by changing the type of $s$, then $C^m(S,\tau,\succ)\setminus\{s\}\subseteq C^m(S,\tau',\succ)$.
--
--   **Reserves.** A *reserve function* $R$ assigns to each problem a natural number $R(S,\tau,\succ)\le|T^M(S,\tau,\succ)|$ such that $R(S,\tau,\succ)=R(S',\tau',\succ')$ whenever, for each $k\in\{1,\dots,q\}$, the $k$-th ranked students of the two problems have the same type (a missing $k$-th student counts as its own type). $C$ admits a *reserve representation* via $R$ if, for every problem, $C(S,\tau,\succ)$ consists of all top-tier minority students, the $\min\{R,|B^m|\}$ highest-priority bottom-tier minority students, and the highest-priority majority students until all $q$ seats are filled or no majority student is left:
--
--   $$C(S,\tau,\succ)=T^m\ \cup\ \{\text{top } R \text{ of } B^m\}\ \cup\ \{\text{top } q-|T^m|-\min\{R,|B^m|\} \text{ of } S^M\}.$$
--
--   **Condition B.** For each problem $(S,\tau,\succ)$:
--   - B1: if $\tau'$ is obtained from $\tau$ by changing the type of a top-tier minority student, then $R(S,\tau',\succ)\in\{R(S,\tau,\succ),R(S,\tau,\succ)+1\}$;
--   - B2: if $\succ'$ is obtained from $\succ$ by improving the priority rank of a top-tier minority student, then $R(S,\tau,\succ')\in\{R(S,\tau,\succ),R(S,\tau,\succ)+1\}$;
--   - B3: if $\succ$ is obtained from $\succ'$ by improving the priority rank of a top-tier majority student $M$, then (i) $R(S,\tau,\succ')\in\{R(S,\tau,\succ),R(S,\tau,\succ)+1\}$, and (ii) $R(S,\tau,\succ')=R(S,\tau,\succ)$ if fewer than $R(S,\tau,\succ)$ top-tier majority students have lower priority than $M$ at $\succ$.
--
--   $C$ has a *bounded reserve representation* if it admits a reserve representation via a reserve function satisfying B1–B3.
--
--   **The reserve function of the proof.** For a choice rule $C$, $R_C(S,\tau,\succ)$ is the largest value of $|C^A(S',\tau',\succ')|$ over all problems $(S',\tau',\succ')$ whose students of ranks $1,\dots,q$ have the same types as those of $(S,\tau,\succ)$.
--
--   These are the objects of Theorem 1 of the paper and of its proof in Appendix A.1.
--
--   **Formalization Note.** A problem stores $\tau$ and the priority as functions on all of $\mathcal S$ (`τ : 𝒮 → Bool` with `true` = minority; `pri : 𝒮 → ℕ`, smaller = higher priority, injective on $S$); only their values on $S$ enter any axiom or the representation. The paper's "nonempty subset" is required only for nonempty $S$ (impossible otherwise). On p. 6 the printed "Given $S\in\mathcal S$" and "$\tau(s)=\tau'(s)$" are read as $S\subseteq\mathcal S$ and $\tau(s')=\tau'(s')$. In B2 the improved minority student is top-tier before the improvement; in B3 the majority student $M$ is top-tier at $\succ'$, before the improvement (improving a top-tier student never changes the top-tier set). B3 (ii) follows footnote 15. The type of the $k$-th student is an `Option Bool`, `none` when $k>|S|$. The proof's reserve function is a supremum (`sSup` on ℕ) of a set that contains $|C^A(S,\tau,\succ)|$ and is bounded by $q$; it equals the paper's $R(\rho)$ (computed at a problem with $|S^m|=q$) whenever that problem exists.
-- source:
--   Doğan & Yıldız, Choice with Affirmative Action, SSRN 3626941 (version of October 17, 2021), pp. 5–10 and 19–20, §2–§4, Condition B (footnote 15), Appendix A, proof of Theorem 1

import Mathlib

namespace AffirmativeChoice.Reserve

/-- §2, p. 5: a (choice) problem `(S, τ, ≻)`. `S` is a set of students, `τ s = true` means that
`s` is a minority student (type 1) and `τ s = false` a majority student (type 0), and the strict
priority ordering is `s ≻ s' ↔ pri s < pri s'` (smaller number = higher priority), which is
complete, transitive and antisymmetric on `S` because `pri` is injective on `S`.
Only the values of `τ` and `pri` on `S` are part of the problem. -/
structure Problem (𝒮 : Type*) where
  S : Finset 𝒮
  τ : 𝒮 → Bool
  pri : 𝒮 → ℕ
  inj : Set.InjOn pri ↑S

variable {𝒮 : Type*} [DecidableEq 𝒮]

/-- §2, p. 6: the restriction `(S', τ|_{S'}, ≻|_{S'})` of a problem to `S' ⊆ S`. -/
def Problem.restrict (P : Problem 𝒮) (S' : Finset 𝒮) (h : S' ⊆ P.S) : Problem 𝒮 :=
  ⟨S', P.τ, P.pri, P.inj.mono (by exact_mod_cast h)⟩

/-- The problem `(S, τ', ≻)`: same students and priorities, type function `τ'`. -/
def Problem.withType (P : Problem 𝒮) (τ' : 𝒮 → Bool) : Problem 𝒮 :=
  ⟨P.S, τ', P.pri, P.inj⟩

/-- The problem `(S, τ, ≻')`: same students and types, priority ordering given by `pri'`. -/
def Problem.withPri (P : Problem 𝒮) (pri' : 𝒮 → ℕ) (h : Set.InjOn pri' ↑P.S) : Problem 𝒮 :=
  ⟨P.S, P.τ, pri', h⟩

/-- §2, p. 6: `rank(s, ≻) = |{s' ∈ S : s' ≻ s}| + 1` (1-based). -/
def rank (P : Problem 𝒮) (s : 𝒮) : ℕ :=
  (P.S.filter (fun s' => P.pri s' < P.pri s)).card + 1

/-- §2, p. 5: `S^m`, the minority students of `S`. -/
def minor (P : Problem 𝒮) : Finset 𝒮 := P.S.filter (fun s => P.τ s = true)

/-- §2, p. 5: `S^M`, the majority students of `S`. -/
def major (P : Problem 𝒮) : Finset 𝒮 := P.S.filter (fun s => P.τ s = false)

/-- §4, p. 9 and Appendix A, p. 19: the top tier `T(S, τ, ≻)`, the students of rank at most `q`
(all of `S` when `|S| ≤ q`). -/
def top (q : ℕ) (P : Problem 𝒮) : Finset 𝒮 := P.S.filter (fun s => rank P s ≤ q)

/-- Appendix A, p. 19: the bottom tier `B(S, τ, ≻) = S \ T(S, τ, ≻)`. -/
def bottom (q : ℕ) (P : Problem 𝒮) : Finset 𝒮 := P.S \ top q P

/-- Appendix A, p. 19: `T^m = S^m ∩ T`, the top-tier minority students. -/
def topMin (q : ℕ) (P : Problem 𝒮) : Finset 𝒮 := (top q P).filter (fun s => P.τ s = true)

/-- Appendix A, p. 19: `T^M = S^M ∩ T`, the top-tier majority students. -/
def topMaj (q : ℕ) (P : Problem 𝒮) : Finset 𝒮 := (top q P).filter (fun s => P.τ s = false)

/-- The bottom-tier minority students `S^m ∩ B`. -/
def botMin (q : ℕ) (P : Problem 𝒮) : Finset 𝒮 := (bottom q P).filter (fun s => P.τ s = true)

/-- The type of the `k`-th ranked student `r_k(≻)` (§2, p. 6): `some true` (minority),
`some false` (majority), or `none` when no student of `S` has rank `k`. -/
def typeAt (P : Problem 𝒮) (k : ℕ) : Option Bool :=
  if ∃ s ∈ P.S, rank P s = k ∧ P.τ s = true then some true
  else if ∃ s ∈ P.S, rank P s = k then some false
  else none

/-- Appendix A, p. 19: the top tiers of two problems coincide if they are the same set of students
with the same relative priority ordering. -/
def TopCoincide (q : ℕ) (P P' : Problem 𝒮) : Prop :=
  top q P = top q P' ∧
    ∀ s ∈ top q P, ∀ s' ∈ top q P, (P.pri s < P.pri s' ↔ P'.pri s < P'.pri s')

/-- §2, p. 6: a choice rule for a school of capacity `q` maps each problem to a subset of `S` of
size at most `q`, nonempty whenever `S` is nonempty. -/
structure ChoiceRule (𝒮 : Type*) (q : ℕ) where
  C : Problem 𝒮 → Finset 𝒮
  subset : ∀ P, C P ⊆ P.S
  card_le : ∀ P, (C P).card ≤ q
  nonempty : ∀ P, P.S.Nonempty → (C P).Nonempty

variable {q : ℕ}

/-- §2, p. 6: `C^m(S, τ, ≻)`, the chosen minority students. -/
def Cm (C : ChoiceRule 𝒮 q) (P : Problem 𝒮) : Finset 𝒮 := (C.C P).filter (fun s => P.τ s = true)

/-- Appendix A, p. 19: `C^A(S, τ, ≻) = C^m(S, τ, ≻) ∩ B(S, τ, ≻)`, the minority students chosen
via affirmative action. -/
def CA (C : ChoiceRule 𝒮 q) (P : Problem 𝒮) : Finset 𝒮 := Cm C P ∩ bottom q P

/-- §2, p. 6: `τ'` is obtained from `τ` by changing the type of `s ∈ S`
(`τ'(s) ≠ τ(s)` and `τ'(s') = τ(s')` for `s' ∈ S \ {s}`). -/
def TypeChange (P : Problem 𝒮) (s : 𝒮) (τ' : 𝒮 → Bool) : Prop :=
  s ∈ P.S ∧ τ' s ≠ P.τ s ∧ ∀ s' ∈ P.S, s' ≠ s → τ' s' = P.τ s'

/-- §2, p. 6: the priority ordering given by `pri'` (a strict ordering on `S`) is an improvement
over that of `P` for `s ∈ S`. -/
structure Improvement (P : Problem 𝒮) (s : 𝒮) (pri' : 𝒮 → ℕ) : Prop where
  mem : s ∈ P.S
  inj : Set.InjOn pri' ↑P.S
  weak : ∀ s' ∈ P.S, P.pri s < P.pri s' → pri' s < pri' s'
  strict : ∃ s' ∈ P.S, s' ≠ s ∧ P.pri s' < P.pri s ∧ pri' s < pri' s'
  others : ∀ s' ∈ P.S, ∀ s'' ∈ P.S, s' ≠ s → s'' ≠ s →
    (P.pri s' < P.pri s'' ↔ pri' s' < pri' s'')

/-- §3.1, p. 7: capacity-filling, `|C(S, τ, ≻)| = min{|S|, q}`. -/
def CapacityFilling (C : ChoiceRule 𝒮 q) : Prop :=
  ∀ P, (C.C P).card = min P.S.card q

/-- §3.1, p. 7: neutrality. If `|S| = |S'|` and the `k`-th ranked students have the same type for
each `k ∈ {1, …, |S|}`, then `r_k(≻) ∈ C(S, τ, ≻) ↔ r_k(≻') ∈ C(S', τ', ≻')` for each `k`. -/
def Neutral (C : ChoiceRule 𝒮 q) : Prop :=
  ∀ P P' : Problem 𝒮, P.S.card = P'.S.card →
    (∀ k, 1 ≤ k → k ≤ P.S.card → typeAt P k = typeAt P' k) →
    ∀ s ∈ P.S, ∀ s' ∈ P'.S, rank P s = rank P' s' → (s ∈ C.C P ↔ s' ∈ C.C P')

/-- §3.1, p. 7: priority-compatibility. If `s` is chosen, `s'` is not, and `s' ≻ s`, then `s` is a
minority student and `s'` a majority student. -/
def PriorityCompatible (C : ChoiceRule 𝒮 q) : Prop :=
  ∀ P : Problem 𝒮, ∀ s ∈ C.C P, ∀ s' ∈ P.S, s' ∉ C.C P → P.pri s' < P.pri s →
    P.τ s = true ∧ P.τ s' = false

/-- §3.1, p. 7: an affirmative action rule satisfies capacity-filling, neutrality and
priority-compatibility. -/
def IsAffirmativeActionRule (C : ChoiceRule 𝒮 q) : Prop :=
  CapacityFilling C ∧ Neutral C ∧ PriorityCompatible C

/-- §3.1, p. 7: substitutability. A chosen student stays chosen at every restriction
`(S', τ|_{S'}, ≻|_{S'})` with `s ∈ S' ⊆ S`. -/
def Substitutable (C : ChoiceRule 𝒮 q) : Prop :=
  ∀ P : Problem 𝒮, ∀ s ∈ C.C P, ∀ S' (h : S' ⊆ P.S), s ∈ S' → s ∈ C.C (P.restrict S' h)

/-- §3.2, p. 8: monotonicity in priority improvements. For each chosen minority student `s` and
each improvement `≻'` over `≻` for `s`, `C^m(S, τ, ≻) ⊆ C^m(S, τ, ≻')`. -/
def MPI (C : ChoiceRule 𝒮 q) : Prop :=
  ∀ P : Problem 𝒮, ∀ s ∈ Cm C P, ∀ pri' (h : Improvement P s pri'),
    Cm C P ⊆ Cm C (P.withPri pri' h.inj)

/-- §3.2, p. 8: monotonicity in type changes. For each chosen minority student `s` and each `τ'`
obtained from `τ` by changing the type of `s`, `C^m(S, τ, ≻) \ {s} ⊆ C^m(S, τ', ≻)`. -/
def MTC (C : ChoiceRule 𝒮 q) : Prop :=
  ∀ P : Problem 𝒮, ∀ s ∈ Cm C P, ∀ τ', TypeChange P s τ' →
    Cm C P \ {s} ⊆ Cm C (P.withType τ')

/-- §4, p. 9: a reserve function assigns to each problem a natural number at most the number of
top-tier majority students, depending only on the types of the students of ranks `1, …, q`. -/
def IsReserveFunction (q : ℕ) (R : Problem 𝒮 → ℕ) : Prop :=
  (∀ P, R P ≤ (topMaj q P).card) ∧
    ∀ P P' : Problem 𝒮, (∀ k, 1 ≤ k → k ≤ q → typeAt P k = typeAt P' k) → R P = R P'

/-- §4, p. 9: the reserve procedure with reserve number `r`: all top-tier minority students, the
`r` highest-priority bottom-tier minority students (all of them if fewer), and then the
highest-priority majority students until the `q` seats are filled or no majority student is
left. -/
def reserveChoice (q : ℕ) (P : Problem 𝒮) (r : ℕ) : Finset 𝒮 :=
  topMin q P
    ∪ (botMin q P).filter
        (fun b => ((botMin q P).filter (fun b' => P.pri b' < P.pri b)).card < r)
    ∪ (major P).filter
        (fun s => ((major P).filter (fun s' => P.pri s' < P.pri s)).card <
          q - (topMin q P).card - min r (botMin q P).card)

/-- §4, p. 9: `C` admits a reserve representation via `R`. -/
def IsReserveRep (C : ChoiceRule 𝒮 q) (R : Problem 𝒮 → ℕ) : Prop :=
  ∀ P, C.C P = reserveChoice q P (R P)

/-- Condition B1, p. 10: changing the type of a top-tier minority student keeps `R` or raises it
by one. -/
def CondB1 (q : ℕ) (R : Problem 𝒮 → ℕ) : Prop :=
  ∀ P : Problem 𝒮, ∀ s ∈ topMin q P, ∀ τ', TypeChange P s τ' →
    R (P.withType τ') = R P ∨ R (P.withType τ') = R P + 1

/-- Condition B2, p. 10: improving the priority rank of a top-tier minority student keeps `R` or
raises it by one. -/
def CondB2 (q : ℕ) (R : Problem 𝒮 → ℕ) : Prop :=
  ∀ P : Problem 𝒮, ∀ s ∈ topMin q P, ∀ pri' (h : Improvement P s pri'),
    R (P.withPri pri' h.inj) = R P ∨ R (P.withPri pri' h.inj) = R P + 1

/-- Condition B3 (i), p. 10: if `≻` is obtained from `≻'` by improving the priority rank of a
top-tier majority student `M` (top-tier at `≻'`), then `R(≻') = R(≻)` or `R(≻') = R(≻) + 1`. -/
def CondB3i (q : ℕ) (R : Problem 𝒮 → ℕ) : Prop :=
  ∀ P' : Problem 𝒮, ∀ M ∈ topMaj q P', ∀ pri (h : Improvement P' M pri),
    R P' = R (P'.withPri pri h.inj) ∨ R P' = R (P'.withPri pri h.inj) + 1

/-- Condition B3 (ii), p. 10 with footnote 15: in the situation of B3, `R(≻') = R(≻)` if the
number of top-tier majority students with lower priority than `M` at `≻` is less than `R(≻)`. -/
def CondB3ii (q : ℕ) (R : Problem 𝒮 → ℕ) : Prop :=
  ∀ P' : Problem 𝒮, ∀ M ∈ topMaj q P', ∀ pri (h : Improvement P' M pri),
    ((topMaj q (P'.withPri pri h.inj)).filter (fun M' => pri M < pri M')).card <
        R (P'.withPri pri h.inj) →
      R P' = R (P'.withPri pri h.inj)

/-- Condition B, p. 10: B1, B2, B3 (i) and B3 (ii). -/
def ConditionB (q : ℕ) (R : Problem 𝒮 → ℕ) : Prop :=
  CondB1 q R ∧ CondB2 q R ∧ CondB3i q R ∧ CondB3ii q R

/-- §4, p. 9: `C` has a bounded reserve representation. -/
def HasBoundedReserveRep (C : ChoiceRule 𝒮 q) : Prop :=
  ∃ R : Problem 𝒮 → ℕ, IsReserveFunction q R ∧ ConditionB q R ∧ IsReserveRep C R

/-- Proof of Theorem 1, p. 20: the reserve function of the proof, as the largest number of students
chosen via affirmative action over all problems whose students of ranks `1, …, q` have the same
types as in `P`. -/
noncomputable def canonicalReserve (C : ChoiceRule 𝒮 q) (P : Problem 𝒮) : ℕ :=
  sSup {n | ∃ P' : Problem 𝒮, (∀ k, 1 ≤ k → k ≤ q → typeAt P' k = typeAt P k) ∧
    n = (CA C P').card}

end AffirmativeChoice.Reserve


