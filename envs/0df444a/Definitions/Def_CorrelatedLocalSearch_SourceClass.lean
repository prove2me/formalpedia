-- Prove2me | Definitions.Def_CorrelatedLocalSearch_SourceClass
-- name    : CorrelatedLocalSearch_SourceClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:40.125824+00:00
-- url     : https://prove2.me/theorems/c95e53d7-08c9-4c0d-962f-df212dd92b89
-- title:
--   Tapes, cylinders, the reference mass $P[w]=k^{-|w|}$ and the source class $\mathcal Q_{s,D}$
-- statement:
--   A **tape** is a sequence $\omega=(\omega_0,\omega_1,\dots)\in[k]^{\mathbb N}$ of symbols from the alphabet $[k]=\{0,\dots,k-1\}$, and a **word** is a finite sequence $w\in[k]^*$. The prefix of length $t$ of $\omega$ is $\omega\!\restriction\!t=(\omega_0,\dots,\omega_{t-1})$, and the **cylinder** $[w]$ is the set of tapes with prefix $w$. Under the reference law $P$ the symbols are independent and uniform on $[k]$, so
--   $$
--   P[w]=k^{-|w|}.
--   $$
--   For real $s$ and $D$, the **source class** is
--   $$
--   \mathcal Q_{s,D}=\{\nu \text{ a probability measure on } [k]^{\mathbb N} : \nu[w]\le D\,P[w]^s \text{ for every word } w\},
--   $$
--   one constant $D$ for prefixes of all lengths, including the empty word. The paper uses it for $0<s\le 1$ and $D\ge 1$.
--
--   This is the class of correlated random sources against which every robustness statement of the mission is proved: the source is a single law on whole tapes, not a sequence of conditional laws.
--
--   **Formalization Note** Tapes are functions $\mathbb N\to\mathrm{Fin}\,k$ with the product σ-algebra; positions are 0-based. $P[w]$ is the closed formula $(1/k)^{|w|}$ (the sanity file checks it is the cylinder mass of the uniform product measure, and that this measure lies in $\mathcal Q_{s,D}$ for $s\le1\le D$). The bound $\nu[w]\le DP[w]^s$ is stated in $[0,\infty]$ via `ENNReal.ofReal`.
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), §2 'Tapes and sources', eq. (1), p.5 (PDF p.7)

import Mathlib

set_option autoImplicit false

namespace CorrelatedLocalSearch

open MeasureTheory

/-- The prefix `ω↾t = (ω 0, …, ω (t−1))` of length `t` of a tape `ω : ℕ → Fin k`
(Xu, *Local Search with Correlated Randomness*, arXiv:2607.17469 (sha256 17e00d69…), §2
"Tapes and sources", p.5).

**Formalization Note** Tape positions are 0-based: `ω 0` is the first symbol read. -/
def tapePrefix {k : ℕ} (ω : ℕ → Fin k) (t : ℕ) : List (Fin k) :=
  List.ofFn (fun i : Fin t => ω i)

/-- The cylinder `[w]` of a word `w`: the set of tapes with prefix `w`
(Xu, arXiv:2607.17469 (sha256 17e00d69…), §2, p.5). -/
def cyl {k : ℕ} (w : List (Fin k)) : Set (ℕ → Fin k) :=
  {ω | tapePrefix ω w.length = w}

/-- The reference mass `P[w] = k^{−|w|}` of a word `w` under the uniform product law
`P = π^ℕ`, `π` uniform on `[k]` (Xu, arXiv:2607.17469 (sha256 17e00d69…), §2, p.5:
`P[w] = ∏ᵢ π(wᵢ)`; §4, p.9: the next source symbol "is uniform on `[k]` under the reference
law `P`").

**Formalization Note** `P[w]` is written as the closed formula `(1/k)^{|w|}` rather than as
the cylinder mass of the product measure; the two agree (checked in the sanity file). -/
noncomputable def refMass (k : ℕ) (w : List (Fin k)) : ℝ :=
  ((k : ℝ)⁻¹) ^ w.length

/-- The source class `Q_{s,D}` of (1) (Xu, arXiv:2607.17469 (sha256 17e00d69…), §2, eq. (1),
p.5): the probability laws `ν` on whole tapes `[k]^ℕ` such that `ν[w] ≤ D · P[w]^s` for every
word `w`, one constant `D` for prefixes of all lengths.

**Formalization Note** Tapes carry the product σ-algebra (`MeasurableSpace.pi`, each `Fin k`
discrete). The alphabet is `[k] = Fin k` with the uniform reference law, the only case
Theorem 4.1 uses. Membership requires `IsProbabilityMeasure ν` ("ν ranges over probability
laws on whole tapes"). The bound is imposed on every word, including the empty one. The class
is defined for all real `s, D`; the paper uses it for `0 < s ≤ 1`, `D ≥ 1`, and every
statement restricts to that range. -/
def SourceClass (k : ℕ) (s D : ℝ) : Set (Measure (ℕ → Fin k)) :=
  {ν | IsProbabilityMeasure ν ∧
    ∀ w : List (Fin k), ν (cyl w) ≤ ENNReal.ofReal (D * refMass k w ^ s)}

end CorrelatedLocalSearch


