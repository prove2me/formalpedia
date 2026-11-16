-- Prove2me | Definitions.Def_WitnessIsolation_AffineCollapse_Supplement_bounds
-- name    : WitnessIsolation_AffineCollapse_Supplement_bounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:50:37.281304+00:00
-- url     : https://prove2.me/theorems/74d3af78-ca0b-4206-9cec-5d5142674bb0
-- title:
--   Real-valued circuit bounds for SAT and NP languages; recurrence thresholds
-- statement:
--   Write $S(s,v)$ for the published `satComplexity s v`: the least gate count of a circuit deciding satisfiability of well-formed descriptions of length at most $s$ with at most $v$ variables, valued in $\mathbb N\cup\{\infty\}$.
--
--   1. $\mathrm{SatBound}(s,v,b)$ for $b\in\mathbb R$ says $S(s,v)$ is a finite number $N$ with $N\le b$. Thus "$S(s,v)\le b$" never silently converts $\infty$ to a real number.
--   2. $\mathrm{LanguageBound}(L,b)$ says that for every sufficiently large input length $m$ there is a circuit $C$ with $m$ inputs and one output, in the published circuit model, of size at most $b(m)$ that accepts exactly the words of $L$ of length $m$.
--   3. Given natural numbers $A,B$, a function $p$, a real $\zeta$ and a natural number $N$, $N$ is a **recurrence threshold** if for every $v\ge N$, every $2\le t\le v$ with $p(tv)\ge (2+\zeta)/(t+1)$, and every $s\ge v$,
--   $$S(s,v)\le (s+2)^A\bigl(1+S((s+2)^B,t)\bigr).$$
--   4. $A,B$ are **recurrence exponents** for a pruning family $I$ if $A\ge1$, $B\ge2$, and every witness-length guarantee $p$ of $I$ and every $\zeta>0$ admit a recurrence threshold. This is the conclusion of Corollary 6.1, packaged as a predicate.
--   5. $\mathrm{PolynomialCap}(c,d,s,v)$ says $s\le c\,(v+2)^d$. Quantifying over all $c>0$ and $d$ expresses "$s\le\mathrm{poly}(v)$" for every fixed polynomial.
--
--   These predicates state the asymptotic conclusions of Theorems 1.3 and 1.5 and Lemma 7.1 without an abstract cost interface: every bound refers to actual circuits.
-- source:
--   Sebastian ben daniel, STOC 2027 submission #346 (October 2026), p. 7, PDF p. 8 (definition of S(s,v), §2); p. 12, PDF p. 13 (Corollary 6.1, (6.1)–(6.2)); pp. 2–3, PDF pp. 3–4 (bounds of Theorems 1.3 and 1.5)

import Definitions.Def_WitnessIsolation_AffineCollapse_model

set_option autoImplicit false
noncomputable section

namespace WitnessIsolation.AffineCollapse.Supplement

/-- `S(s,v) ≤ b`, stated through finite attainment of the published `satComplexity`
(an `ℕ∞` minimum), never by coercing an infinite value to a real number. -/
def SatBound (s v : ℕ) (b : ℝ) : Prop :=
  ∃ N : ℕ, satComplexity s v = (N : ℕ∞) ∧ (N : ℝ) ≤ b

/-- A language has actual published-model circuits `Circuit m 1` of size at most `b m`
at every sufficiently large input length `m`. -/
def LanguageBound (L : Set (List Bool)) (b : ℕ → ℝ) : Prop :=
  ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∃ C : Circuit m 1,
    (C.size : ℝ) ≤ b m ∧ ∀ x : Bits m, C.accepts x ↔ List.ofFn x ∈ L

/-- `N` is a threshold of Corollary 6.1 (printed p. 12 / PDF p. 13) for exponents `A,B`,
guarantee `p` and slack `ζ`: recurrence (6.2) holds for every `v ≥ N`, `2 ≤ t ≤ v`
with (6.1), and every `s ≥ v`. -/
def IsRecurrenceThreshold (A B : ℕ) (p : ℕ → ℝ) (ζ : ℝ) (N : ℕ) : Prop :=
  ∀ v : ℕ, N ≤ v → ∀ t : ℕ, 2 ≤ t → t ≤ v → (2+ζ)/((t:ℝ)+1) ≤ p (t*v) →
    ∀ s : ℕ, v ≤ s →
      satComplexity s v ≤ ((s+2)^A : ℕ) * (1 + satComplexity ((s+2)^B) t)

/-- `A,B` are recurrence exponents of Corollary 6.1 for the pruner `I`:
`A ≥ 1`, `B ≥ 2`, and every guarantee of `I` and every `ζ > 0` admit a threshold. -/
def RecurrenceExponents (I : PruningFamily) (A B : ℕ) : Prop :=
  1 ≤ A ∧ 2 ≤ B ∧ ∀ p : ℕ → ℝ, HasGuarantee I p →
    ∀ ζ : ℝ, 0 < ζ → ∃ N : ℕ, IsRecurrenceThreshold A B p ζ N

/-- The description cap `s ≤ c·(v+2)^d`; quantifying over all `c > 0` and `d` expresses
`s ≤ poly(v)` for every fixed polynomial. -/
def PolynomialCap (c : ℝ) (d : ℕ) (s v : ℕ) : Prop :=
  (s:ℝ) ≤ c * ((v:ℝ)+2)^d

end WitnessIsolation.AffineCollapse.Supplement


