-- Prove2me | Definitions.Def_TurnstileRank_TightBounds_Info
-- name    : TurnstileRank_TightBounds_Info
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:06:25.607789+00:00
-- url     : https://prove2.me/theorems/b0056668-df01-4c63-87ec-8bb128c96b19
-- title:
--   Discrete probability, conditional mutual information in bits, and expected conditional variance
-- statement:
--   All random variables of the paper are discrete (§3.2 defines entropy and mutual information by sums over values; logarithms are base two). A probability space is a discrete law $P$ (a `PMF`) on a sample type $\Omega$, and a random variable is a function on $\Omega$.
--
--   * $\mathrm{prob}(P,E)=P[E]$ for any event $E\subseteq\Omega$.
--   * For a finite-valued $A$, the conditional law given an event $E$ is $a\mapsto P[A=a,E]/P[E]$, and the relative entropy of two laws $p,q$ of $A$ is $D_{KL}(p\,\|\,q)=\sum_a p(a)\log_2\frac{p(a)}{q(a)}$ with $0\log 0=0$ and value $+\infty$ when $p(a)>0=q(a)$ for some $a$; `klBits` takes values in $[0,\infty]$.
--   * Conditional mutual information in bits, for a finite-valued $A$ and arbitrary $B$, $C$:
--   $$I(A;B\mid C)=\sum_{(b,c)}P[B=b,C=c]\;D_{KL}\big(P_{A\mid B=b,C=c}\,\big\|\,P_{A\mid C=c}\big),$$
--   valued in $[0,\infty]$. For finite-valued $A$ this equals $H(A\mid C)-H(A\mid B,C)$ of §3.2 (and Fact 3.5 when $C$ is constant). Unconditional information takes $C$ constant.
--   * The conditional mean $E[Z\mid C]$ is the random variable whose value at $\omega$ is the mean of $Z$ over $\{C=C(\omega)\}$, and Definition 4.9's expected conditional variance is the number $\mathrm{Var}(Z\mid C)=E[(Z-E[Z\mid C])^2]$. Both are infinite sums over $\Omega$; every $Z$ used in this mission is bounded.
--   * The binary entropy $h_2(\delta)=-\delta\log_2\delta-(1-\delta)\log_2(1-\delta)$ (Fact 3.4).
--   * `indepProd p q` is the law of a pair of independent variables with laws $p$ and $q$.
-- source:
--   Hu, Jiang, Liu, Yu (2026), Tight Bounds for Rank Estimation in Turnstile Streams, held STOC 2027 submission, SHA-256 4be4260012249f6a39249d22651326b8b78a13b1a792ae41b80f8363cd5567b6, §3.2, printed p. 12 (PDF 13), and Definition 4.9, printed p. 16 (PDF 17)

import Mathlib

/-!
# Discrete probability and information in bits

Hu, Jiang, Liu, Yu (2026), *Tight Bounds for Rank Estimation in Turnstile Streams*, held STOC 2027
submission (SHA-256 4be42600…), §3.2, printed p. 12 (PDF 13): "All logarithms are base two, so all
quantities below are in bits", entropy, conditional entropy, `I(A ; B | C) := H(A | C) − H(A | B, C)`,
relative entropy, Fact 3.5 `I(A ; B) = Σ_b P[B = b] D_KL(P_b ‖ P)`, and the binary entropy `h₂`
(Fact 3.4); §4.2.2, Definition 4.9, printed p. 16 (PDF 17): the expected conditional variance
`Var(Z | C) := E[Var(Z | C)] = E[(Z − E[Z | C])²]`.

**Formalization Note.**
* Every random variable of the paper is discrete (§3.2 defines its quantities by sums over values),
  so a probability space is a `PMF` on a sample type `Ω` and a random variable is a function on `Ω`.
  The sample type may be uncountable (a group `G`); a `PMF` always has countable support.
* `prob P E` is the probability of an arbitrary event (no measurability is needed for a `PMF`).
* `condMI P A B C` is `I(A ; B | C)` in bits for a *finite-valued* `A`, written in the form of
  Fact 3.5 conditioned on `C`: `Σ_{b,c} P[B = b, C = c] · D_KL(P_{A | b, c} ‖ P_{A | c})`. For a
  finite-valued `A` this equals `H(A | C) − H(A | B, C)`, and it needs no finiteness of `B` or `C`.
  Relative entropy is `∞` when the first law charges a zero of the second; otherwise it is
  the nonnegative finite KL sum, embedded with `ENNReal.ofReal`. Thus `condMI` uses nonnegative
  extended sums and has no real-tsum summability junk. Unconditional
  information is `condMI P A B (fun _ => ())`.
* `condExp P Z C` is the random variable `E[Z | C]`, and `condVar P Z C` is the number
  `E[(Z − E[Z | C])²]` of Definition 4.9. Both are infinite sums; they are the paper's quantities
  for a bounded `Z`, which is the case for every `Z` this mission uses (a sum of at most `d` signs,
  or a conditional mean of one).
-/

noncomputable section

open scoped Classical

namespace TurnstileRank.TightBounds

variable {Ω α β γ : Type*}

/-- The probability `P[E]` of an event `E` under the discrete law `P`. -/
def prob (P : PMF Ω) (E : Set Ω) : ℝ := (P.toOuterMeasure E).toReal

/-- The conditional law of `A` given the event `E`: `a ↦ P[A = a, E] / P[E]` (it is `0` when
`P[E] = 0`; such events carry no weight in `condMI`). -/
def condLaw (P : PMF Ω) (A : Ω → α) (E : Set Ω) (a : α) : ℝ :=
  prob P ({ω | A ω = a} ∩ E) / prob P E

/-- Relative entropy `D_KL(p ‖ q) = Σ_a p(a) log₂ (p(a) / q(a))` in bits of two laws on a finite
set, with `0 log 0 = 0` and value `∞` if `p(a) > 0 = q(a)` for some `a`.
The arguments are probability mass functions in the source domain. -/
def klBits [Fintype α] (p q : α → ℝ) : ENNReal :=
  if ∃ a, 0 < p a ∧ q a = 0 then ⊤
  else ENNReal.ofReal (∑ a, if p a = 0 then 0 else p a * Real.logb 2 (p a / q a))

/-- Conditional mutual information `I(A ; B | C)` in bits, for a finite-valued `A`:
`Σ_{(b, c)} P[B = b, C = c] · D_KL(P_{A | B = b, C = c} ‖ P_{A | C = c})`. -/
def condMI [Fintype α] (P : PMF Ω) (A : Ω → α) (B : Ω → β) (C : Ω → γ) : ENNReal :=
  ∑' bc : β × γ,
    ENNReal.ofReal (prob P {ω | B ω = bc.1 ∧ C ω = bc.2}) *
      klBits (condLaw P A {ω | B ω = bc.1 ∧ C ω = bc.2}) (condLaw P A {ω | C ω = bc.2})

/-- The conditional mean `E[Z | C]`, as a random variable: on `ω` it is the mean of `Z` over the
event `{C = C ω}`. -/
def condExp (P : PMF Ω) (Z : Ω → ℝ) (C : Ω → γ) : Ω → ℝ := fun ω =>
  (∑' ω', (P ω').toReal * Z ω' * (if C ω' = C ω then 1 else 0)) / prob P {ω' | C ω' = C ω}

/-- Definition 4.9: the expected conditional variance `Var(Z | C) := E[(Z − E[Z | C])²]`, a number. -/
def condVar (P : PMF Ω) (Z : Ω → ℝ) (C : Ω → γ) : ℝ :=
  ∑' ω, (P ω).toReal * (Z ω - condExp P Z C ω) ^ 2

/-- The binary entropy `h₂(δ) = −δ log₂ δ − (1 − δ) log₂ (1 − δ)` (Fact 3.4). -/
def h2 (δ : ℝ) : ℝ := -δ * Real.logb 2 δ - (1 - δ) * Real.logb 2 (1 - δ)

/-- The law of two independent random variables with laws `p` and `q`. -/
def indepProd (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind fun a => q.map fun b => (a, b)

end TurnstileRank.TightBounds


