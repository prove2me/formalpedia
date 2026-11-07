-- Prove2me | Definitions.Def_RobustQSC_phaseLaw
-- name    : RobustQSC_phaseLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:52:13.706301+00:00
-- url     : https://prove2.me/theorems/63a00f6a-1141-4f81-9241-869e430da5e8
-- title:
--   The uniform law on $F_\mu=\{f:\mu_f=\mu\}$
-- statement:
--   For $\mu$ on $\{0,1\}^n$, a draw $f\sim F_\mu$ is
--
--   $$
--   f(x)=\sqrt{\mu(x)}\,\omega_x,\qquad(\omega_x)_x\ \text{i.i.d. Steinhaus}.
--   $$
--
--   This is the uniform law on $F_\mu=\{f:\mu_f=\mu\}$. It is the conditional randomness that remains once the measure of $f$ has been fixed, and the fixed-$q$ concentration of §5 is proved under it.
--
--   **Formalization Note** Defined for every $\mu$; it is the uniform law on $F_\mu$ when $\mu\ge0$, which holds on the support of $\mathrm{Dirichlet}(\vec1)$.
-- source:
--   Coladangelo, Li, Slote, Robust quantum state certification and uncertainty principles for total influence, arXiv:2607.27184 (sha256 09d2692e…), §2.5.3, p.15; glossary, p.79; proof of Lemma 2, p.24

import Definitions.Def_RobustQSC_steinhaus
import Definitions.Def_QAlgorithms_Defs_Basic

namespace RobustQSC

open MeasureTheory QAlgorithms

/-- `f ∼ F_μ`: the uniform law on `F_μ = {f : μ_f = μ}`, i.e. `f(x) = √μ(x) · ω_x` with
`(ω_x)_x` i.i.d. Steinhaus.

Source: Coladangelo, Li, Slote, *Robust quantum state certification and uncertainty principles
for total influence*, arXiv:2607.27184 (sha256 09d2692e…), §2.5.3, p.15 ("define F_µ = {f : µ_f =
µ} … using the randomness in f ∼_unif F_µ"), glossary, p.79; Lemma 2's proof, p.24
(`ĝ(s) = N^{-1/2} Σ_x √µ(x) ω_x q(x) (−1)^{⟨x,s⟩}`).

**Formalization Note.** Defined for every `μ : {0,1}ⁿ → ℝ`; it is the uniform law on `F_μ` when
`μ ≥ 0` (the support of `Dirichlet(1⃗)`). -/
noncomputable def phaseLaw {n : ℕ} (μ : Qubits n → ℝ) : Measure (EuclideanSpace ℂ (Qubits n)) :=
  (Measure.pi fun _ : Qubits n => steinhaus).map fun ω =>
    WithLp.toLp 2 fun x => ((Real.sqrt (μ x) : ℝ) : ℂ) * ω x

/-! ### Sanity tests -/

instance {n : ℕ} (μ : Qubits n → ℝ) : IsProbabilityMeasure (phaseLaw μ) := by
  unfold phaseLaw
  refine Measure.isProbabilityMeasure_map ?_
  exact ((WithLp.measurable_toLp 2 _).comp (by fun_prop)).aemeasurable

end RobustQSC


