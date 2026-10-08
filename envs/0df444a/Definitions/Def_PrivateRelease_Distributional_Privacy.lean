-- Prove2me | Definitions.Def_PrivateRelease_Distributional_Privacy
-- name    : PrivateRelease_Distributional_Privacy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T16:06:47.060411+00:00
-- url     : https://prove2.me/theorems/b9076839-c920-495e-922f-e3b1d414ad88
-- title:
--   Set-database neighbours, ε-differential privacy and (ε, β)-distributional privacy (Definitions 2.1, 7.1, 7.2)
-- statement:
--   Let $X$ be a data universe and $R$ a measurable space of outputs. In §7 of the paper a **database** of size $n$ is a set $D\subseteq X$ with $|D|=n$ (it is drawn without replacement), and a **mechanism** assigns to every such database $D$ the law $A(D)$ of its random output, a measure on $R$.
--
--   1. **Neighbouring databases** (Definition 2.1, read for sets). Two databases $D,D'$ of size $n$ are *neighbours* if $D'$ arises from $D$ by replacing one element: $|D|=|D'|=n$ and $|D\setminus D'|=1$.
--   2. **$\varepsilon$-differential privacy** (Definition 2.1). The mechanism is $\varepsilon$-differentially private on databases of size $n$ if for all neighbours $D,D'$ and all measurable events $E\subseteq R$,
--   $$\Pr[A(D)\in E]\le e^{\varepsilon}\,\Pr[A(D')\in E].$$
--   3. **Good pairs.** A pair $(D_1,D_2)$ is *good* if $\Pr[A(D_1)\in E]\le e^{\varepsilon}\Pr[A(D_2)\in E]$ holds for **all** measurable events $E$ simultaneously, and *bad* otherwise.
--   4. **$S$-neighbours** (Definition 7.1). For a finite set $S\subseteq X$ with $|S|\ge n$, two $S$-neighbours $D_1,D_2$ are drawn independently, each uniformly at random among the $\binom{|S|}{n}$ subsets of $S$ of size $n$ (that is, by drawing $n$ elements of $S$ without replacement).
--   5. **$(\varepsilon,\beta)$-distributional privacy** (Definition 7.2). The mechanism is $(\varepsilon,\beta)$-distributionally private on databases of size $n$ if for every finite $S\subseteq X$ with $|S|\ge n$, the $S$-neighbours $(D_1,D_2)$ form a good pair with probability at least $1-\beta$. Counting ordered pairs, this says
--   $$\#\{(D_1,D_2): D_1,D_2\subseteq S,\ |D_1|=|D_2|=n,\ (D_1,D_2)\text{ bad}\}\ \le\ \beta\binom{|S|}{n}^{2}.$$
--
--   Distributional privacy asks that the output reveal no more about the sample than is inherent in the population $S$ it was drawn from; differential privacy asks that it hide any single element. Theorem 7.3 relates the two.
--
--   **Formalization Note.** Databases are `Finset X` and a mechanism is `A : Finset X → Measure R`; only its values on $n$-element sets matter. The paper's neighbour relation "$|D\Delta D'|\le1$" holds for equal-size sets only when $D=D'$; the intended *replace one element* reading is used. Events range over measurable sets (all sets when $R$ carries the σ-algebra $\top$). The paper leaves "drawn at random" from an infinite $S$ undefined, so only finite $S$ are quantified; the two draws are taken independently, which is what the proof of Theorem 7.3 uses. The bad event is "some event $E$ violates the inequality", the negation of the paper's "for all events $E$"; the guarantee is not per event. No probability-measure hypothesis is built in, and $\beta$ is an arbitrary real number (for $\beta\ge1$ the condition is vacuous).
-- source:
--   Blum, Ligett, Roth, A Learning Theory Approach to Non-Interactive Database Privacy, arXiv:1109.2229v1 (2011), p. 5, Definition 2.1; p. 19, Definitions 7.1 and 7.2

import Mathlib

namespace PrivateRelease.Distributional

open MeasureTheory

/-- Neighbouring set-databases (Definition 2.1, p. 5, read for the set-databases of §7, p. 19):
two databases `D, D′ ⊆ X` of size `n` are neighbours when `D′` arises from `D` by replacing a single
element, i.e. both have `n` elements and exactly one element of `D` is missing from `D′`. -/
def SetNeighbors {X : Type} [DecidableEq X] (n : ℕ) (D D' : Finset X) : Prop :=
  D.card = n ∧ D'.card = n ∧ (D \ D').card = 1

/-- ε-differential privacy (Definition 2.1, p. 5) for a mechanism on set-databases of size `n`:
`Pr[A(D) ∈ E] ≤ exp(ε) · Pr[A(D′) ∈ E]` for all neighbouring `D, D′` and all measurable events
`E ⊆ R`. The law of the output of the mechanism on input `D` is the measure `A D`. -/
def IsDPSet {X R : Type} [DecidableEq X] [MeasurableSpace R] (A : Finset X → Measure R) (n : ℕ) (ε : ℝ) : Prop :=
  ∀ D D' : Finset X, SetNeighbors n D D' → ∀ E : Set R, MeasurableSet E →
    A D E ≤ ENNReal.ofReal (Real.exp ε) * A D' E

/-- The guarantee of Definition 7.2 (p. 19) for one pair of databases: for all measurable events
`E ⊆ R`, `Pr[A(D₁) ∈ E] ≤ e^ε · Pr[A(D₂) ∈ E]`. -/
def GoodPair {X R : Type} [MeasurableSpace R] (A : Finset X → Measure R) (ε : ℝ)
    (D₁ D₂ : Finset X) : Prop :=
  ∀ E : Set R, MeasurableSet E → A D₁ E ≤ ENNReal.ofReal (Real.exp ε) * A D₂ E

open Classical in
/-- The number of ordered pairs `(D₁, D₂)` of `n`-element subsets of the finite set `S` that are
*bad*, i.e. for which the guarantee `GoodPair A ε D₁ D₂` fails. -/
noncomputable def badPairCount {X R : Type} [MeasurableSpace R] (A : Finset X → Measure R)
    (n : ℕ) (ε : ℝ) (S : Finset X) : ℕ :=
  ((S.powersetCard n ×ˢ S.powersetCard n).filter fun p => ¬ GoodPair A ε p.1 p.2).card

/-- (ε, β)-distributional privacy (Definitions 7.1 and 7.2, p. 19). For every finite `S ⊆ X` with
`|S| ≥ n`, draw two `S`-neighbours `D₁, D₂` independently and uniformly among the `n`-element
subsets of `S` (drawing `n` elements of `S` without replacement); then with probability at least
`1 − β` the pair satisfies `Pr[A(D₁) ∈ E] ≤ e^ε Pr[A(D₂) ∈ E]` for all measurable events `E`.
As a count: at most `β · C(|S|, n)²` of the `C(|S|, n)²` ordered pairs are bad. -/
def IsDistPrivate {X R : Type} [MeasurableSpace R] (A : Finset X → Measure R) (n : ℕ)
    (ε β : ℝ) : Prop :=
  ∀ S : Finset X, n ≤ S.card →
    (badPairCount A n ε S : ℝ) ≤ β * ((S.card.choose n : ℕ) : ℝ) ^ 2

end PrivateRelease.Distributional


