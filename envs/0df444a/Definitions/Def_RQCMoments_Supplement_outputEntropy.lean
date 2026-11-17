-- Prove2me | Definitions.Def_RQCMoments_Supplement_outputEntropy
-- name    : RQCMoments_Supplement_outputEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:48:26.697495+00:00
-- url     : https://prove2.me/theorems/906740d9-4a1c-4f3c-aa6a-70ea6881ee72
-- title:
--   Output Shannon entropy $S(U)$, the Kolmogorov distances $\eta$ and $\delta$ (Definition 7.3)
-- statement:
--   Fix an input $y\in\{0,1\}^n$ and let $P_x(U)=|\langle x|U|y\rangle|^2$ be the probability of outcome $x$ given $U\in U(2^n)$. The **Shannon entropy of the output distribution** is
--
--   $$S(U)=-\sum_{x\in\{0,1\}^n}P_x(U)\log_2 P_x(U),\qquad 0\log 0=0 .$$
--
--   For two distributions $\mu$ (a design) and $\nu$ (Haar) on $U(2^n)$, $\eta$ is the largest Kolmogorov distance between the laws of a single $P_x$,
--
--   $$\eta=\max_{x}\ \sup_{z\in\mathbb R}\big|\Pr_{\mu}[P_x\le z]-\Pr_{\nu}[P_x\le z]\big| ,$$
--
--   and (Definition 7.3) $\delta$ is the supremum, over $x,x'$ (not necessarily distinct) and $s,t\ge0$ not both zero, of the Kolmogorov distance between the laws of $sP_x+tP_{x'}$ under $\mu$ and under $\nu$.
--
--   Theorems 7.2, 7.6 and 7.8 bound the mean, the standard deviation and the concentration of $S$ under a design through $\eta$ and $\delta$.
--
--   **Formalization Note** Logarithms are base two (p.13): $S=\sum_x\mathrm{negMulLog}(P_x)/\ln2$. The suprema are real suprema; for probability measures every term lies in $[0,1]$. Index combinations violating $s,t\ge0$, $(s,t)\neq(0,0)$ contribute the empty supremum $0$, which does not change the supremum of these nonnegative terms.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), §1, p.4 (PDF p.6); Theorem 7.2 and its proof, p.63 (PDF p.65); Definition 7.3, p.64 (PDF p.66)

import Mathlib
import Definitions.Def_RQCMoments_entry

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- The Shannon entropy (in bits) of the output distribution of `U` on input `y`:
`S(U) = −∑_{x ∈ {0,1}^n} P_x(U) log₂ P_x(U)`, with `P_x(U) = |⟨x|U|y⟩|²` and `0 log 0 = 0`
(Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), §1, p.4, PDF p.6; proof of Theorem 7.2, p.63, PDF p.65; logarithms base two, p.13).

**Formalization Note** `Real.negMulLog t = −t ln t` (with value `0` at `t = 0`), divided by `ln 2`
to get base two. Basis states `{0,1}^n` are `Fin (2^n)`; `P_x` is the published `RQCMoments.entry`. -/
noncomputable def outputEntropy {n : ℕ} (y : Fin (2 ^ n)) (U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : ℝ :=
  ∑ x : Fin (2 ^ n), Real.negMulLog (entry x y U) / Real.log 2

/-- `η(k, ε)` of Theorem 7.2: the maximum over outputs `x` of the Kolmogorov distance between the law
of `P_x` under `μ` and under `ν` (the Haar measure in the theorems)
(Hung, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 7.2, p.63, PDF p.65; Kolmogorov distance (2), p.2).

**Formalization Note** The Kolmogorov distance is `sup_z |μ(P_x ≤ z) − ν(P_x ≤ z)|`, written as a real
supremum; for probability measures every term lies in `[0,1]`, so the supremum is a genuine one. -/
noncomputable def entropyEta {n : ℕ} (y : Fin (2 ^ n))
    (μ ν : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)) : ℝ :=
  ⨆ x : Fin (2 ^ n), ⨆ z : ℝ,
    |(μ {U | entry x y U ≤ z}).toReal - (ν {U | entry x y U ≤ z}).toReal|

/-- **Definition 7.3** (`δ(k, ε)`)
(Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Definition 7.3, p.64, PDF p.66).
The supremum, over `x, x' ∈ {0,1}^n` (not necessarily distinct) and `s, t ≥ 0` not both zero, of the
Kolmogorov distance between the law of `s P_x + t P_{x'}` for `U ∼ μ` and for `U ∼ ν` (the Haar
measure in the theorems).

**Formalization Note** Real suprema; index combinations violating `s, t ≥ 0`, `(s, t) ≠ (0, 0)`
contribute the empty supremum `0`, which does not change the supremum of these nonnegative terms.
For probability measures every term lies in `[0,1]`. -/
noncomputable def entropyDelta {n : ℕ} (y : Fin (2 ^ n))
    (μ ν : Measure (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ)) : ℝ :=
  ⨆ x : Fin (2 ^ n), ⨆ x' : Fin (2 ^ n), ⨆ s : ℝ, ⨆ t : ℝ,
    ⨆ (_ : 0 ≤ s ∧ 0 ≤ t ∧ (s ≠ 0 ∨ t ≠ 0)), ⨆ z : ℝ,
      |(μ {U | s * entry x y U + t * entry x' y U ≤ z}).toReal -
        (ν {U | s * entry x y U + t * entry x' y U ≤ z}).toReal|

end Supplement

end RQCMoments


