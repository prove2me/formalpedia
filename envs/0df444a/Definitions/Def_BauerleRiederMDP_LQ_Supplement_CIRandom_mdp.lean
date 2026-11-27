-- Prove2me | Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_mdp
-- name    : BauerleRiederMDP_LQ_Supplement_CIRandom_mdp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T23:05:54.89563+00:00
-- url     : https://prove2.me/theorems/8e87bd67-b3c7-432c-b2dd-63e34d71cbf7
-- title:
--   The stationary infinite-horizon Markov Decision Model of §9.1
-- statement:
--   **The stationary infinite-horizon Markov Decision Model of §9.1** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §9.1, pp.268–269, PDF 278–279, following §7.6.1): $E = [0, \infty )$ (wealth), $A = \mathbb R _+ \times  \mathbb R ^d$ (consumption $c$, amounts $a$ in the risky assets), `D(x) = {(c, a) | 0 ≤ c ≤ x, x − c + a · R_1 ≥ 0 ℙ-a.s.}`, $T(x, c, a, z) = x - c + a \cdot  z$, $Q^Z(\cdot |x, c, a)$ = the law of $R_1$, $r(x, c, a) = U_c(c) + \beta (1 - p) \mathbb E [U_p(T(x, c, a, R_1))]$ and discount factor $\tilde{\beta} = \beta p$.
--
--   **Formalization Note.** The model is the published `MDPFinance.Contracting` model with $E = \mathbb R \ge 0$ and $A = \mathbb R  \times  \mathbb R ^d$. The next state is $T(x, c, a, z)$ truncated at $0$ (`Real.toNNReal`); for $(c, a) \in  D(x)$ the truncation is inactive almost surely, so it changes no transition law on $D$. The expectation in $r$ is a Bochner integral of $U_p \circ  T^+$, which is integrable for every $(x, c, a)$ ($U_p$ is concave and increasing, hence of at most linear growth, and $\mathbb E \|R_1\| < \infty $), so it is the book's expectation. The consumption enters the reward as $U_c(c^+)$, which is $U_c(c)$ on $D$ ($c \ge  0$); $U_c$ is only given on $[0, \infty )$.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §9.1, pp.268–269, PDF 278–279, following §7.6.1

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **The stationary infinite-horizon Markov Decision Model of §9.1** (Bäuerle & Rieder, *Markov
Decision Processes with Applications to Finance* (2011), §9.1, pp.268–269, PDF 278–279, following
§7.6.1): `E = [0, ∞)` (wealth), `A = ℝ_+ × ℝ^d` (consumption `c`, amounts `a` in the risky assets),
`D(x) = {(c, a) | 0 ≤ c ≤ x, x − c + a · R_1 ≥ 0 ℙ-a.s.}`, `T(x, c, a, z) = x − c + a · z`,
`Q^Z(·|x, c, a)` = the law of `R_1`, `r(x, c, a) = U_c(c) + β(1 − p) 𝔼[U_p(T(x, c, a, R_1))]` and
discount factor `β̃ = βp`.

**Formalization Note.** The model is the published `MDPFinance.Contracting` model with
`E = ℝ≥0` and `A = ℝ × ℝ^d`. The next state is `T(x, c, a, z)` truncated at `0`
(`Real.toNNReal`); for `(c, a) ∈ D(x)` the truncation is inactive almost surely, so it changes no
transition law on `D`. The expectation in `r` is a Bochner integral of `U_p ∘ T⁺`, which is
integrable for every `(x, c, a)` (`U_p` is concave and increasing, hence of at most linear growth,
and `𝔼‖R_1‖ < ∞`), so it is the book's expectation. The consumption enters the reward as `U_c(c⁺)`, which is `U_c(c)` on
`D` (`c ≥ 0`); `U_c` is only given on `[0, ∞)`. -/
noncomputable def CIRandom.mdp {d : ℕ} (C : CIRandom d) :
    MDPFinance.Contracting.MarkovDecisionModel ℝ≥0 (ℝ × (Fin d → ℝ)) where
  D := {p | 0 ≤ p.2.1 ∧ p.2.1 ≤ p.1 ∧
    C.μR {z | (p.1 : ℝ) - p.2.1 + ∑ k, p.2.2 k * z k < 0} = 0}
  hD_meas := by
    have hS : MeasurableSet {q : (ℝ≥0 × (ℝ × (Fin d → ℝ))) × (Fin d → ℝ) |
        (q.1.1 : ℝ) - q.1.2.1 + ∑ k, q.1.2.2 k * q.2 k < 0} :=
      measurableSet_lt (by fun_prop) measurable_const
    have hm : Measurable fun p : ℝ≥0 × (ℝ × (Fin d → ℝ)) =>
        C.μR (Prod.mk p ⁻¹' {q : (ℝ≥0 × (ℝ × (Fin d → ℝ))) × (Fin d → ℝ) |
          (q.1.1 : ℝ) - q.1.2.1 + ∑ k, q.1.2.2 k * q.2 k < 0}) :=
      measurable_measure_prodMk_left hS
    have h1 : Measurable fun p : ℝ≥0 × (ℝ × (Fin d → ℝ)) => p.2.1 := measurable_fst.comp measurable_snd
    have h2 : Measurable fun p : ℝ≥0 × (ℝ × (Fin d → ℝ)) => (p.1 : ℝ) :=
      measurable_coe_nnreal_real.comp measurable_fst
    refine (measurableSet_le measurable_const h1).inter ((measurableSet_le h1 h2).inter ?_)
    exact hm (measurableSet_singleton 0)
  hD_graph := ⟨fun _ => (0, 0), measurable_const, fun x => by
    refine ⟨le_rfl, by simp, ?_⟩
    have : {z : Fin d → ℝ | (x : ℝ) - 0 + ∑ k, (0 : Fin d → ℝ) k * z k < 0} = ∅ := by
      ext z; simp
    simp only [this]; simp⟩
  Q := (Kernel.id ×ₖ Kernel.const _ C.μR).map
    (fun q : (ℝ≥0 × (ℝ × (Fin d → ℝ))) × (Fin d → ℝ) =>
      Real.toNNReal ((q.1.1 : ℝ) - q.1.2.1 + ∑ k, q.1.2.2 k * q.2 k))
  isMarkovQ := Kernel.IsMarkovKernel.map _ (by fun_prop)
  r := fun p => C.Uc (Real.toNNReal p.2.1) + C.β * (1 - C.p) *
    ∫ z, C.Up (Real.toNNReal ((p.1 : ℝ) - p.2.1 + ∑ k, p.2.2 k * z k)) ∂C.μR
  hr_meas := by
    have hUp : Measurable fun y : ℝ => C.Up (Real.toNNReal y) :=
      (C.Up_util.2.2.comp_continuous (by fun_prop) (fun y => by simp)).measurable
    have hUc : Measurable fun y : ℝ => C.Uc (Real.toNNReal y) :=
      (C.Uc_util.2.2.comp_continuous (by fun_prop) (fun y => by simp)).measurable
    have hF : Measurable fun q : (ℝ≥0 × (ℝ × (Fin d → ℝ))) × (Fin d → ℝ) =>
        C.Up (Real.toNNReal ((q.1.1 : ℝ) - q.1.2.1 + ∑ k, q.1.2.2 k * q.2 k)) :=
      hUp.comp (by fun_prop)
    have hI := (hF.stronglyMeasurable.integral_prod_right' (ν := C.μR)).measurable
    exact (hUc.comp (measurable_fst.comp measurable_snd)).add (measurable_const.mul hI)
  β := C.β * C.p
  hβ0 := mul_pos C.β_mem.1 C.p_mem.1
  hβ1 := by
    exact mul_le_one₀ C.β_mem.2 C.p_mem.1.le C.p_mem.2.le

end BauerleRiederMDP.LQ.Supplement


