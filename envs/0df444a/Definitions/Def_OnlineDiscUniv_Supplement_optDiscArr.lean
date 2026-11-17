-- Prove2me | Definitions.Def_OnlineDiscUniv_Supplement_optDiscArr
-- name    : OnlineDiscUniv_Supplement_optDiscArr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:28:46.320243+00:00
-- url     : https://prove2.me/theorems/8d89fbc1-3381-4242-8e41-a8427eb66648
-- title:
--   Expected discrepancy, failure and success probabilities, and their optima for independent-entry arrays
-- statement:
--   Fix an array of entry laws $\nu=(\nu_{k,i})$ and let the input have the array law $\bigotimes_{k,i}\nu_{k,i}$. For a randomized online algorithm with seed $U\sim\rho$ independent of the input, and $D_{M,N}=\|N^{-1/2}\sum_k\varepsilon_k\xi_k\|_\infty$, define, with all probabilities and expectations taken jointly over the seed and the input,
--   $$
--   \mathbb E D_{M,N},\qquad \mathbb P(D_{M,N}>\kappa),\qquad \mathbb E(D_{M,N}-\kappa)_+,\qquad \mathbb P(D_{M,N}\le\kappa),
--   $$
--   and the optimal values
--   $$
--   \inf_{\varepsilon\text{ online}}\mathbb E D_{M,N},\qquad \sup_{\varepsilon\text{ online}}\mathbb P(D_{M,N}\le\kappa).
--   $$
--
--   These are the quantities of Theorem 6.1. When all entry laws equal one law $\mu$ they coincide with the published i.i.d. versions.
--
--   **Formalization Note** All values lie in $[0,\infty]$; expectations are lower integrals. The infimum and supremum range over every seed space with a σ-algebra, every seed probability law and every jointly measurable causal online algorithm (the published `OnlineDiscUniv.OnlineAlg`), exactly as in the published `OnlineDiscUniv.optDisc`.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), §6.2, Theorem 6.1, p.25 (PDF p.26); §2.1, p.5 (PDF p.6); Theorem 1.1, pp.1–2 (PDF pp.2–3)

import Mathlib
import Definitions.Def_OnlineDiscUniv_OnlineAlg
import Definitions.Def_OnlineDiscUniv_Supplement_arrayLaw

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace OnlineDiscUniv.Supplement

variable {S : Type*} [MeasurableSpace S] {M N : ℕ}

/-- The expected discrepancy `E D_{M,N}` of an online algorithm with seed law `ρ` on an input
array with independent entries of laws `ν k i` (Jo–Lee, arXiv:2610.00103, artifact sha256
cb190f12…, §6.2, Theorem 6.1, printed p.25, PDF p.26; §2.1, p.5, PDF p.6). The seed is
independent of the input, so the joint law is `ρ ⊗ arrayLaw ν`.

**Formalization Note** A lower integral in `ℝ≥0∞` (never the junk `0` of a non-integrable
Bochner integral), exactly as the published `OnlineDiscUniv.expDisc`, with `arrayLaw ν` in place
of `inputLaw μ M N`. -/
noncomputable def expDiscArr (ν : Fin N → Fin M → Measure ℝ) (ρ : Measure S)
    (A : OnlineAlg S M N) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (disc A p.1 p.2) ∂(ρ.prod (arrayLaw ν))

/-- The failure probability `P(D_{M,N} > κ)` on an input array with independent entries of laws
`ν k i` (Jo–Lee, arXiv:2610.00103, Theorem 6.1, p.25, PDF p.26; (1.1), p.2, PDF p.3), including
the seed. -/
noncomputable def failProbArr (ν : Fin N → Fin M → Measure ℝ) (ρ : Measure S)
    (A : OnlineAlg S M N) (κ : ℝ) : ℝ≥0∞ :=
  (ρ.prod (arrayLaw ν)) {p | κ < disc A p.1 p.2}

/-- The expected excess `E(D_{M,N} − κ)_+` on an input array with independent entries of laws
`ν k i` (Jo–Lee, arXiv:2610.00103, Theorem 6.1, p.25, PDF p.26; (1.1), p.2, PDF p.3), a lower
integral in `ℝ≥0∞` (`ofReal` of a negative number is `0`, the positive part). -/
noncomputable def expExcessArr (ν : Fin N → Fin M → Measure ℝ) (ρ : Measure S)
    (A : OnlineAlg S M N) (κ : ℝ) : ℝ≥0∞ :=
  ∫⁻ p, ENNReal.ofReal (disc A p.1 p.2 - κ) ∂(ρ.prod (arrayLaw ν))

/-- The success probability `P(D_{M,N} ≤ κ)` on an input array with independent entries of laws
`ν k i` (Jo–Lee, arXiv:2610.00103, Theorem 6.1, p.25, PDF p.26), including the seed. -/
noncomputable def succProbArr (ν : Fin N → Fin M → Measure ℝ) (ρ : Measure S)
    (A : OnlineAlg S M N) (κ : ℝ) : ℝ≥0∞ :=
  (ρ.prod (arrayLaw ν)) {p | disc A p.1 p.2 ≤ κ}

/-- The optimal expected online discrepancy `inf_{ε online} E D_{M,N}` on an input array with
independent entries of laws `ν k i` (Jo–Lee, arXiv:2610.00103, Theorem 6.1, p.25, PDF p.26).

**Formalization Note** As the published `OnlineDiscUniv.optDisc`: the infimum ranges over every
seed space `S : Type` with a σ-algebra, every probability law `ρ` of the seed, and every (jointly
measurable, causal) online algorithm with seed space `S`; deterministic algorithms are included
(a one-point seed space). -/
noncomputable def optDiscArr (ν : Fin N → Fin M → Measure ℝ) : ℝ≥0∞ :=
  ⨅ (S : Type) (_ : MeasurableSpace S) (ρ : Measure S) (_ : IsProbabilityMeasure ρ)
    (A : OnlineAlg S M N), expDiscArr ν ρ A

/-- The supremal success probability `sup_{ε online} P(D_{M,N} ≤ κ)` on an input array with
independent entries of laws `ν k i` (Jo–Lee, arXiv:2610.00103, Theorem 6.1, p.25, PDF p.26),
over the same class of randomized online algorithms as `optDiscArr`. -/
noncomputable def optSuccArr (ν : Fin N → Fin M → Measure ℝ) (κ : ℝ) : ℝ≥0∞ :=
  ⨆ (S : Type) (_ : MeasurableSpace S) (ρ : Measure S) (_ : IsProbabilityMeasure ρ)
    (A : OnlineAlg S M N), succProbArr ν ρ A κ

end OnlineDiscUniv.Supplement


