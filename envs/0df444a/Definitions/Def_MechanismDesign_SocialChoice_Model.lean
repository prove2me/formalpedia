-- Prove2me | Definitions.Def_MechanismDesign_SocialChoice_Model
-- name    : MechanismDesign_SocialChoice_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T03:32:28.857973+00:00
-- url     : https://prove2.me/theorems/8c8f3706-9a55-4c9c-9f47-924b589a495f
-- title:
--   Nontransferrable utility: linear-order preferences, direct mechanisms, DSIC, dictatorship, monotonicity, set-monotonicity, unanimity
-- statement:
--   This bundle fixes the vocabulary of §8.2 of Börgers' *An Introduction to the Theory of Mechanism Design*.
--
--   A finite set $I$ of agents (the book's $I=\{1,\dots,N\}$) must choose one alternative from a finite set $A$. Each agent $i$ holds a preference relation $R_i$ over $A$, read "$a\,R_i\,b$: $a$ is weakly preferred to $b$". Every $R_i$ is a **linear order**: it is complete ($a\,R_i\,b$ or $b\,R_i\,a$), transitive, and the only indifference is among identical alternatives ($a\,R_i\,b$ and $b\,R_i\,a$ imply $a=b$). The strict part is $a\,P_i\,b$ iff $a\,R_i\,b$ and not $b\,R_i\,a$. Write $\mathcal R$ for the set of all linear orders over $A$ and $R=(R_1,\dots,R_N)\in\mathcal R^N$ for a preference profile.
--
--   1. **Direct mechanism** (Definition 8.1): a function $f:\mathcal R^N\to A$.
--   2. **Dominant strategy incentive compatibility** (Definition 8.2): for every agent $i$, every profile $R$ and every $R_i'\in\mathcal R$,
--   $$f(R_i,R_{-i})\;R_i\;f(R_i',R_{-i}).$$
--   3. **Dictatorial** (Definition 8.3): there is an agent $i$ such that $f(R)\,R_i\,a$ for every profile $R$ and every $a\in A$.
--   4. **Monotone** (Definition 8.4, Maskin monotonicity): if $f(R)=a$ and, for every agent $i$, $a\,R_i'\,b$ holds for every $b$ with $a\,R_i\,b$, then $f(R')=a$.
--   5. **Set-monotone** (Definition 8.5): if $f(R)\in B\subseteq A$ and, for every agent $i$, $a\,R_i'\,a' \Leftrightarrow a\,R_i\,a'$ for all $a,a'\in A$ with at least one of $a,a'$ outside $B$, then $f(R')\in B$.
--   6. **Respects unanimity** (Definition 8.6): if $a\,R_i\,b$ for all $i\in I$ and $b\in A$, then $f(R)=a$.
--
--   These notions are the hypotheses and conclusions of Propositions 8.1–8.5, which lead from strategy-proofness through monotonicity to dictatorship.
--
--   **Formalization Note** A linear order is the structure `LinPref A` with the relation `rel` (the book's $R_i$) and its three axioms; completeness includes reflexivity. A profile is a function `ι → LinPref A` from a finite agent type `ι`. The deviation profile $(R_i',R_{-i})$ is `Function.update R i R'_i`. "The range of $f$ is $A$" is `Function.Surjective f` in the theorems.
-- source:
--   Börgers, An Introduction to the Theory of Mechanism Design, Oxford University Press 2015, DOI 10.1093/acprof:oso/9780199734023.001.0001, pp.142–145, §8.2.1–8.2.2, Definitions 8.1–8.6

import Mathlib

/-!
# Direct mechanisms with nontransferrable utility (Börgers, Ch. 8, §8.2.1–8.2.2, pp.142–145)

A finite set of agents `ι` (the book's `I = {1, …, N}`) chooses one alternative from a finite
set `A`. Each agent's preference `R_i` is a **linear order** on `A`: complete, transitive, and
"the only indifference is among identical alternatives" (p.142). A direct mechanism is a
function `f : R^N → A` (Definition 8.1). This file fixes the vocabulary of Definitions 8.1–8.6.
-/

namespace MechanismDesign.SocialChoice

/-- A **linear order** preference on the set of alternatives `A` (Börgers, p.142): a relation
`rel`, where `rel a b` reads "`a` is weakly preferred to `b`" (the book's `a R_i b`), that is
complete (`a R b` or `b R a` for all `a, b`; in particular reflexive), transitive, and in which
the only indifference is among identical alternatives (`a R b` and `b R a` imply `a = b`).
The book's set `R` of all linear orders over `A` is the type `LinPref A`. -/
structure LinPref (A : Type*) where
  /-- `rel a b`: `a` is weakly preferred to `b`. -/
  rel : A → A → Prop
  /-- Completeness. -/
  total : ∀ a b : A, rel a b ∨ rel b a
  /-- Transitivity. -/
  trans : ∀ a b c : A, rel a b → rel b c → rel a c
  /-- The only indifference is among identical alternatives. -/
  antisymm : ∀ a b : A, rel a b → rel b a → a = b

/-- The strict order `P_i` derived from `R_i` (p.142): `a P_i b` iff `a R_i b` and not `b R_i a`,
read "`a` is strictly preferred to `b`". -/
def LinPref.strict {A : Type*} (R : LinPref A) (a b : A) : Prop :=
  R.rel a b ∧ ¬ R.rel b a

/-- **Definition 8.1** (p.142): a direct mechanism is a function `f : R^N → A` from preference
profiles (one linear order per agent) to alternatives. -/
abbrev DirectMechanism (ι A : Type*) : Type _ := (ι → LinPref A) → A

variable {ι A : Type*}

/-- **Definition 8.2** (p.143): `f` is dominant strategy incentive-compatible if for every agent
`i` and all preference relations `R_i, R'_i`, and every profile `R_{-i}` of the others,
`f(R_i, R_{-i}) R_i f(R'_i, R_{-i})`. The profile `(R'_i, R_{-i})` is `Function.update R i R'_i`. -/
def IsDSIC [DecidableEq ι] (f : DirectMechanism ι A) : Prop :=
  ∀ (i : ι) (R : ι → LinPref A) (Ri' : LinPref A),
    (R i).rel (f R) (f (Function.update R i Ri'))

/-- **Definition 8.3** (p.143): `f` is dictatorial if there is some individual `i` such that for
all profiles `R`, `f(R) R_i a` for all `a ∈ A`. -/
def IsDictatorial (f : DirectMechanism ι A) : Prop :=
  ∃ i : ι, ∀ (R : ι → LinPref A) (a : A), (R i).rel (f R) a

/-- **Definition 8.4** (p.144, Maskin monotonicity): `f` is monotone if whenever `f(R) = a` and,
for every agent `i`, `a R'_i b` for all `b ∈ A` such that `a R_i b`, then `f(R') = a`. -/
def IsMonotone (f : DirectMechanism ι A) : Prop :=
  ∀ (R R' : ι → LinPref A) (a : A), f R = a →
    (∀ (i : ι) (b : A), (R i).rel a b → (R' i).rel a b) → f R' = a

/-- **Definition 8.5** (p.145): `f` is set-monotone if whenever `f(R) ∈ B` for some `B ⊆ A` and,
for every agent `i`, `R'_i` differs from `R_i` only regarding the ranking of elements of `B`
(`a R'_i a' ⇔ a R_i a'` for all `a, a'` such that at least one of `a, a'` is not in `B`), then
`f(R') ∈ B`. -/
def IsSetMonotone (f : DirectMechanism ι A) : Prop :=
  ∀ (R R' : ι → LinPref A) (B : Set A), f R ∈ B →
    (∀ (i : ι) (a a' : A), (a ∉ B ∨ a' ∉ B) → ((R' i).rel a a' ↔ (R i).rel a a')) →
    f R' ∈ B

/-- **Definition 8.6** (p.145): `f` respects unanimity if whenever an alternative `a` is at the
top of every individual's preference relation (`a R_i b` for all `i ∈ I` and `b ∈ A`), then
`f(R) = a`. -/
def RespectsUnanimity (f : DirectMechanism ι A) : Prop :=
  ∀ (R : ι → LinPref A) (a : A), (∀ (i : ι) (b : A), (R i).rel a b) → f R = a

end MechanismDesign.SocialChoice


