-- Prove2me | Definitions.Def_GoldieRenewal_Implicit_CramerConditions
-- name    : GoldieRenewal_Implicit_CramerConditions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:07:58.295059+00:00
-- url     : https://prove2.me/theorems/115a8cca-0c42-4e84-9615-fcffd51fa08c
-- title:
--   Lemma 2.2 hypotheses (2.3)–(2.5), arithmetic laws (p. 127), m = E|M|^κ log|M| (2.7) and E log|M| ∈ [−∞, ∞)
-- statement:
--   This file fixes the conditions on the multiplier $M$ under which Goldie's implicit renewal theorem holds, together with the constants they produce.
--
--   **Arithmetic laws** (p. 127). A probability law $\mu$ on $\mathbb R$ is *arithmetic* if it is centred lattice: it is concentrated on $\{n\lambda : n\in\mathbb Z\}$ for some $\lambda>0$. Otherwise it is *nonarithmetic*.
--
--   **Cramér-type conditions** (Lemma 2.2, p. 129). Let $M$ be a real random variable with law $\nu$ and let $\kappa>0$. The conditions are
--   $$
--   \text{(2.3)}\ \ E|M|^\kappa = 1,\qquad \text{(2.4)}\ \ E|M|^\kappa\log^+|M|<\infty,
--   $$
--   and (2.5): the conditional law of $\log|M|$, given $M\neq 0$, is nonarithmetic.
--
--   **The constant $m$** (2.7): $m := E|M|^\kappa\log|M|$, with the convention $0^a\log 0 := 0$ for $a\ge 0$ (p. 127).
--
--   **The mean of $\log|M|$** (2.6). With $\log 0 = -\infty$, $E\log|M| := E\log^+|M| - E\log^-|M| \in [-\infty,\infty)$ whenever $E\log^+|M|<\infty$.
--
--   These objects are the hypotheses and constants of Lemma 2.2 and Theorem 2.3; Lemma 2.2 shows $E\log|M|<0$ and $m\in(0,\infty)$.
--
--   **Formalization Note** The law $\nu$ is required to have total mass one. The moments in (2.3), (2.4), $E\log^+|M|$ and $E\log^-|M|$ are lower Lebesgue integrals in $[0,\infty]$, so they carry no junk value. In (2.5) the law $\nu$ is conditioned on $\{x\neq 0\}$ before $x\mapsto\log|x|$ is applied, so Lean's $\log 0 = 0$ never enters; $\log^-|0|$ is set to $+\infty$ explicitly. $m$ is a Bochner integral, the paper's value once Lemma 2.2 gives integrability. $E\log|M|$ is computed in the extended reals and is only used together with $E\log^+|M|<\infty$. The conventions are the same as those of the sibling Kesten mission (`GoldieRenewal.Kesten`).
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 127 (§1, arithmetic laws, 0^a log 0 := 0), p. 129, Lemma 2.2, (2.3)–(2.7), p. 142 (Y := log|M| ∈ [−∞, ∞))

import Mathlib

namespace GoldieRenewal.Implicit

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- **Arithmetic law** (Goldie 1991, §1, p. 127): a law `μ` on `ℝ` is *arithmetic* (centred
lattice) when it is concentrated on `{n λ : n ∈ ℤ}` for some `λ > 0`, i.e. the complement of that
lattice is `μ`-null. A law is *nonarithmetic* when it is not arithmetic.

**Formalization Note** "Concentrated on" is encoded as "the complement has measure zero", which for
a probability law is the same as "the lattice has measure one". The zero measure is arithmetic
under this definition, so a nonarithmetic law is never the zero measure. -/
def IsArithmetic (μ : Measure ℝ) : Prop :=
  ∃ l : ℝ, 0 < l ∧ μ (Set.range (fun n : ℤ => (n : ℝ) * l))ᶜ = 0

/-- **The conditions of Lemma 2.2** (Goldie 1991, p. 129, (2.3)–(2.5)), stated for the law `ν` of
the random variable `M` and an exponent `κ > 0`:

* `ν` is a probability law (because it is the law of `M`);
* (2.3) `E|M|^κ = 1`;
* (2.4) `E|M|^κ log⁺|M| < ∞`;
* (2.5) the conditional law of `log|M|` given `M ≠ 0` is nonarithmetic.

**Formalization Note** The expectations of the nonnegative quantities `|M|^κ` and
`|M|^κ log⁺|M|` are lower Lebesgue integrals in `[0, ∞]`, so (2.3) and (2.4) carry no junk value.
`|0|^κ = 0` for `κ > 0`, and the integrand of (2.4) is `0` at `M = 0`, matching the paper's
convention `0^a log 0 := 0`. In (2.5) the conditional law is `ν` conditioned on `{x ≠ 0}`
(Mathlib's `ProbabilityTheory.cond`), pushed forward by `x ↦ log|x|`; only points `x ≠ 0` carry
mass, so Lean's `Real.log 0 = 0` never enters. `0 < κ` is a field of the structure. The same
conventions are used by the sibling mission on Kesten's theorem (`GoldieRenewal.Kesten`).
The probability-law field prevents a rescaled, nonprobability measure from satisfying the moment
equation while violating the conclusion of Lemma 2.2. -/
structure CramerConditions (κ : ℝ) (ν : Measure ℝ) : Prop where
  probability : ν Set.univ = 1
  pos : 0 < κ
  moment_eq_one : ∫⁻ x, ENNReal.ofReal (|x| ^ κ) ∂ν = 1
  moment_log_finite : ∫⁻ x, ENNReal.ofReal (|x| ^ κ * max (Real.log |x|) 0) ∂ν < ∞
  nonarithmetic : ¬ IsArithmetic ((ν[|{x : ℝ | x ≠ 0}]).map (fun x => Real.log |x|))

/-- **The constant `m`** of (2.7) (Goldie 1991, p. 129): `m := E|M|^κ log|M|` for `M` with law `ν`.

**Formalization Note** This is a Bochner integral. Under `CramerConditions κ ν`, Lemma 2.2 of the
paper proves `m ∈ (0, ∞)` (the integrand is integrable), so the value is the paper's `m`, not a
junk `0`. The integrand is `0` at `x = 0`, as in the paper's convention `0^a log 0 := 0`. -/
noncomputable def cramerMean (κ : ℝ) (ν : Measure ℝ) : ℝ :=
  ∫ x, |x| ^ κ * Real.log |x| ∂ν

/-- **`E log⁺|M|`** for `M` with law `ν`, as an element of `[0, ∞]`. -/
noncomputable def logPlusMoment (ν : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (max (Real.log |x|) 0) ∂ν

/-- **`E log⁻|M|`** for `M` with law `ν`, as an element of `[0, ∞]`, with the paper's convention
`log 0 = −∞` (so `log⁻|0| = +∞`, p. 142: "`Y := log|M| ∈ [−∞, ∞)`").

**Formalization Note** The integrand is `∞` at `x = 0` on purpose: Lean's `Real.log 0 = 0` would
otherwise make an atom of `M` at `0` contribute nothing. -/
noncomputable def logMinusMoment (ν : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (if x = 0 then ∞ else ENNReal.ofReal (max (-Real.log |x|) 0)) ∂ν

/-- **`E log|M|` in `[−∞, ∞]`** (Goldie 1991, (2.6), p. 129): `E log⁺|M| − E log⁻|M|` computed in
`EReal`, for `M` with law `ν`.

**Formalization Note** `EReal` subtraction gives `⊤ − ⊤ = ⊥`; the value is therefore the paper's
`E log|M|` only when `E log⁺|M| < ∞`, which is why every statement using it also asserts or assumes
`logPlusMoment ν < ∞`. When `E log⁺|M| < ∞` the value lies in `[−∞, ∞)` and equals `−∞` exactly when
`E log⁻|M| = ∞` (in particular when `P(M = 0) > 0`). -/
noncomputable def logAbsMean (ν : Measure ℝ) : EReal :=
  (logPlusMoment ν : EReal) - (logMinusMoment ν : EReal)

end GoldieRenewal.Implicit


