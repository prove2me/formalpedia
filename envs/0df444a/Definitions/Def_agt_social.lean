-- Prove2me | Definitions.Def_agt_social
-- name    : agt_social
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-13T03:10:18.738686+00:00
-- url     : https://prove2.me/theorems/6e27c068-52bd-44e2-9fca-2c4d944dc168
-- title:
--   Preferences, social welfare and social choice functions
-- statement:
--   This bundle fixes the social-choice vocabulary of §9.2 of *Algorithmic Game Theory* (Nisan, "Introduction to Mechanism Design (for Computer Scientists)"). There is a set $A$ of alternatives and a set $\iota$ of voters; a **preference** is a strict total order on $A$, written as a relation $r(a,b)$ meaning "$a$ is strictly preferred to $b$" (the book's $b \prec a$).
--
--   1. **`IsPrefProfile`** — a profile assigns a strict total order to every voter (the book's $L^n$).
--   2. **`IsSWF`** — a social welfare function in the proper sense: on every preference profile the aggregate relation is again a strict total order (Definition 9.1).
--   3. **`SWFUnanimity`** — on the profile where all voters hold the identical preference $r$, the social preference is $r$ (Definition 9.2).
--   4. **`SWFDictator`** — voter $i$ is a dictator in $F$: on every profile the social preference coincides with $i$'s (Definition 9.2).
--   5. **`SWFIIA`** — independence of irrelevant alternatives: if two profiles agree on how every voter compares $a$ with $b$, the social comparisons of $a$ with $b$ agree (Definition 9.2).
--   6. **`IncentiveCompatible`** — no voter can, by misreporting their preference, move the outcome of the social choice function to one they strictly prefer under their true preference (Definition 9.4).
--   7. **`SCFMonotone`** — if the outcome changes from $a$ to $a' \ne a$ when voter $i$ alone changes their vote, then $i$ ranked $a$ above $a'$ before and $a'$ above $a$ after (Definition 9.5).
--   8. **`SCFDictator`** — voter $i$ is a dictator in $f$: whenever $a$ is $i$'s unique top alternative, $f$ elects $a$ (Definition 9.7).
--   9. **`SCFOnto`** — every alternative is elected on some preference profile (the hypothesis of Theorem 9.8).
--
--   *A note on conventions.* Aggregators are total functions on all relation-valued profiles, but every property quantifies only over genuine preference profiles, so behavior on invalid inputs is irrelevant to every statement — no junk input can carry content. The relation orientation is the reverse of the book's $\prec$; each docstring restates it.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Ch. 9, Section 9.2, Definitions 9.1-9.7, pp. 211-214

import Mathlib.Order.RelClasses
import Mathlib.Data.Fintype.Card

/-!
The social-choice vocabulary of Chapter 9 (Nisan, "Introduction to Mechanism
Design (for Computer Scientists)") of Nisan–Roughgarden–Tardos–Vazirani
(eds.), *Algorithmic Game Theory* (2007), §9.2.

There is a set `A` of alternatives (candidates) and a set `ι` of voters.
Each voter holds a **preference**: a strict total order on `A`.  Throughout
this development a preference is a relation `r : A → A → Prop` together with
the property `IsStrictTotalOrder A r`, and `r a b` reads "`a` is strictly
preferred to (ranked above) `b`" — the book writes `b ≺ a` for the same
statement.  A **social welfare function** aggregates a profile of
preferences into one social preference; a **social choice function**
aggregates it into a single chosen alternative (Definition 9.1).

Aggregators are total functions on all relation-valued profiles; every
property below quantifies only over genuine preference profiles, so the
behavior of an aggregator on invalid inputs is irrelevant to every statement.
-/

namespace AGT

variable {A ι : Type*}

/-- A **preference profile**: every voter's relation is a strict total order
on the alternatives (Definition 9.1; `L^n` in the book). -/
def IsPrefProfile (P : ι → A → A → Prop) : Prop :=
  ∀ i, IsStrictTotalOrder A (P i)

/-- A **social welfare function** in the proper sense: on every preference
profile the social relation is again a strict total order (Definition 9.1). -/
def IsSWF (F : (ι → A → A → Prop) → A → A → Prop) : Prop :=
  ∀ P : ι → A → A → Prop, IsPrefProfile P → IsStrictTotalOrder A (F P)

/-- **Unanimity** (Definition 9.2): on the profile where all voters hold the
identical preference `r`, the social preference is `r`. -/
def SWFUnanimity (F : (ι → A → A → Prop) → A → A → Prop) : Prop :=
  ∀ r : A → A → Prop, IsStrictTotalOrder A r →
    ∀ a b, F (fun _ => r) a b ↔ r a b

/-- Voter `i` is a **dictator** in the social welfare function `F`
(Definition 9.2): on every preference profile the social preference is
`i`'s. -/
def SWFDictator (F : (ι → A → A → Prop) → A → A → Prop) (i : ι) : Prop :=
  ∀ P : ι → A → A → Prop, IsPrefProfile P → ∀ a b, F P a b ↔ P i a b

/-- **Independence of irrelevant alternatives** (Definition 9.2): the social
preference between `a` and `b` depends only on the voters' preferences
between `a` and `b`. -/
def SWFIIA (F : (ι → A → A → Prop) → A → A → Prop) : Prop :=
  ∀ P Q : ι → A → A → Prop, IsPrefProfile P → IsPrefProfile Q →
    ∀ a b, (∀ i, P i a b ↔ Q i a b) → (F P a b ↔ F Q a b)

variable [DecidableEq ι]

/-- **Incentive compatibility** (Definition 9.4): no voter can, by
misreporting their preference, move the outcome to one they strictly prefer
(under their true preference) over the truthful outcome. -/
def IncentiveCompatible (f : (ι → A → A → Prop) → A) : Prop :=
  ∀ P : ι → A → A → Prop, IsPrefProfile P →
    ∀ i (r' : A → A → Prop), IsStrictTotalOrder A r' →
      ¬ P i (f (Function.update P i r')) (f P)

/-- **Monotonicity** (Definition 9.5): if the outcome changes from `a` to
`a' ≠ a` when voter `i` alone changes their vote from `P i` to `r'`, then
`i` ranks `a` above `a'` in the old vote and `a'` above `a` in the new
one. -/
def SCFMonotone (f : (ι → A → A → Prop) → A) : Prop :=
  ∀ P : ι → A → A → Prop, IsPrefProfile P →
    ∀ i (r' : A → A → Prop), IsStrictTotalOrder A r' →
      f P ≠ f (Function.update P i r') →
        P i (f P) (f (Function.update P i r')) ∧
          r' (f (Function.update P i r')) (f P)

/-- Voter `i` is a **dictator** in the social choice function `f`
(Definition 9.7): whenever `a` is `i`'s unique top alternative, `f`
chooses `a`. -/
def SCFDictator (f : (ι → A → A → Prop) → A) (i : ι) : Prop :=
  ∀ P : ι → A → A → Prop, IsPrefProfile P →
    ∀ a, (∀ b, b ≠ a → P i a b) → f P = a

/-- `f` is **onto**: every alternative is chosen on some preference profile
(the hypothesis of Theorem 9.8). -/
def SCFOnto (f : (ι → A → A → Prop) → A) : Prop :=
  ∀ a : A, ∃ P : ι → A → A → Prop, IsPrefProfile P ∧ f P = a

end AGT


