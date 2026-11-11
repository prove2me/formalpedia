-- Prove2me | Definitions.Def_QTolTest1673_Unified_Tester
-- name    : QTolTest1673_Unified_Tester
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:06.964594+00:00
-- url     : https://prove2.me/theorems/320d6fb5-c7f3-4350-92a5-d86663b44e2b
-- title:
--   Nonadaptive quantum testers and tolerant testing with error at most $\delta$
-- statement:
--   Quantum algorithms access $f:\mathbb F_2^n\to\{\pm1\}$ through the standard value oracle $O_f|x,b\rangle=|x,b\oplus(1-f(x))/2\rangle$; auxiliary registers, entanglement and intermediate measurements are allowed, and each application of $O_f$ is one query.
--
--   1. A **nonadaptive tester** with $m$ rounds runs the same fixed $T$-query circuit $A$ (input-independent unitaries interleaved with $O_f$, with an auxiliary workspace) $m$ times, measuring its whole register after each run. No outcome is used to choose a later query. After the last round it outputs $D(z_1,\dots,z_m)\in\{\text{Accept},\text{Reject}\}$ for an arbitrary classical decision rule $D$ of the outcomes. Its number of oracle queries is $mT$.
--   2. An algorithm $\mathcal A$ is a **tolerant tester** for a class $\mathcal C$ with thresholds $\varepsilon_1,\varepsilon_2$ and **error probability at most $\delta$** if for every $f$:
--   $$\operatorname{dist}(f,\mathcal C)\le\varepsilon_1\ \Longrightarrow\ \Pr[\mathcal A\text{ accepts }f]\ge1-\delta,\qquad \operatorname{dist}(f,\mathcal C)\ge\varepsilon_2\ \Longrightarrow\ \Pr[\mathcal A\text{ rejects }f]\ge1-\delta.$$
--   Inputs with distance strictly between the thresholds are unconstrained.
--
--   These definitions express the conclusion of the unified upper bound: a nonadaptive tester whose query count is bounded in terms of $k$, $\delta$ and the Fourier-mass gap.
--
--   **Formalization Note** Algorithms are the published `QAlgorithms.AdaptiveQueryAlg`, whose rounds run frozen query algorithms against the XOR oracle of the bit function $b_f=(1-f)/2$; this is exactly $O_f$. Acceptance probabilities are the published Born-rule `outProb`, with output `true` for Accept. The nonadaptive run is built recursively: each round records its outcome and the next round is the same circuit whatever the outcome. The query count is read off with the published `worstCaseQueries`, the largest number of oracle calls on any branch.
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), source.pdf SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, §2.1 (p. 13), §2.2 (p. 14), Algorithm 1 (p. 20), proof of Theorem 1.1 (pp. 20–21)

import Definitions.Def_FourierDimTesting102_Quantum_Algorithm

/-!
# Nonadaptive quantum testers and tolerant testing with error `δ`

Zekun Ye, Jialin Zhang, *Quantum Tolerant Testing of Fourier Dimensionality and Juntas*,
STOC 2027 submission #1673 (October 2026), §2.1 (p. 13), §2.2 (p. 14), Algorithm 1 and the
proof of Theorem 1.1 (pp. 20–21).

Quantum algorithms are the published adaptive query algorithms
`QAlgorithms.AdaptiveQueryAlg (V n) Bool`: each round runs a frozen `QueryAlg` (input-independent
unitaries, auxiliary workspace) against the XOR oracle `|x, b⟩ ↦ |x, b ⊕ b_f(x)⟩`, which is the
source's standard value oracle `O_f|x,b⟩ = |x, b ⊕ (1 − f(x))/2⟩` for `f = (-1)^{b_f}`, measures
the whole register, and continues. Output `true` is Accept, `false` is Reject.
-/

namespace QTolTest1673.Unified

open QAlgorithms FourierDimTesting102.Quantum

/-- The `r` remaining rounds of a nonadaptive run: every round runs the same frozen algorithm `A`,
ignores the outcomes recorded so far (`acc`, most recent first) and only records its own; after
the last round the decision rule `D` is applied to the outcomes in chronological order. -/
noncomputable def nonadaptiveLoop {n w T : ℕ} (A : QueryAlg (V n) Bool (Fin w) T)
    (D : List ((V n × Bool) × Fin w) → Bool) :
    ℕ → List ((V n × Bool) × Fin w) → AdaptiveQueryAlg (V n) Bool
  | 0, acc => .halt (D acc.reverse)
  | r + 1, acc => .round T w A fun z => nonadaptiveLoop A D r (z :: acc)

/-- p. 21: a nonadaptive tester. Its `m` query circuits are fixed in advance (`m` independent
runs of the frozen `T`-query algorithm `A`), no earlier outcome is used to choose a later query,
and the answer is an arbitrary classical function `D` of the `m` measurement outcomes (p. 6: the
postprocessing need not be efficient). Its query count is `m · T`. -/
noncomputable def nonadaptiveTester {n w T : ℕ} (m : ℕ) (A : QueryAlg (V n) Bool (Fin w) T)
    (D : List ((V n × Bool) × Fin w) → Bool) : AdaptiveQueryAlg (V n) Bool :=
  nonadaptiveLoop A D m []

/-- §2.1 (p. 13) and §2.2 (p. 14): `𝒜` is a tolerant tester for the class `S` with thresholds
`ε₁, ε₂` and error probability at most `δ`: every `ε₁`-close input (`dist(f, S) ≤ ε₁`, YES) is
accepted with probability at least `1 − δ`, and every `ε₂`-far input (`dist(f, S) ≥ ε₂`, NO) is
rejected with probability at least `1 − δ`. Inputs strictly between the thresholds are
unconstrained. -/
def IsTolerantTester {n : ℕ} (𝒜 : AdaptiveQueryAlg (V n) Bool) (S : Set (BoolFn n))
    (ε₁ ε₂ δ : ℝ) : Prop :=
  ∀ f : BoolFn n,
    (distToSet f S ≤ ε₁ → 1 - δ ≤ 𝒜.outProb f true) ∧
      (ε₂ ≤ distToSet f S → 1 - δ ≤ 𝒜.outProb f false)

/-! ### Sanity checks -/

example {n w T : ℕ} (A : QueryAlg (V n) Bool (Fin w) T)
    (D : List ((V n × Bool) × Fin w) → Bool) :
    nonadaptiveTester 0 A D = .halt (D []) := rfl

example {n w T : ℕ} (A : QueryAlg (V n) Bool (Fin w) T)
    (D : List ((V n × Bool) × Fin w) → Bool) :
    worstCaseQueries (nonadaptiveTester 1 A D) = T := by
  simp [nonadaptiveTester, nonadaptiveLoop, worstCaseQueries]

end QTolTest1673.Unified


