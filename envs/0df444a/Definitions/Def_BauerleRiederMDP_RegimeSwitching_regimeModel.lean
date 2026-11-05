-- Prove2me | Definitions.Def_BauerleRiederMDP_RegimeSwitching_regimeModel
-- name    : BauerleRiederMDP_RegimeSwitching_regimeModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:11.161415+00:00
-- url     : https://prove2.me/theorems/7a737bf3-0f75-47bf-b67f-cb2ec9a8df71
-- title:
--   Markov Decision Model of the consumption-investment problem with regime switching (4.19)
-- statement:
--   The **consumption-investment problem with regime switching** (4.19) is the stationary Markov Decision Model with
--
--   1. states $(x,j)\in[0,\infty)\times E_Y$ (wealth, environment) and actions $(c,a)\in\mathbb R_+\times\mathbb R^d$;
--   2. $D(x,j)=\{(c,a): 0\le c\le x,\ (1+i)(x-c+a\cdot R(j))\ge0\ \mathbb P\text{-a.s.}\}$;
--   3. disturbances $(z,k)$ (relative risk, new environment) with law $Q^Z(B\times\{k\}\mid(x,j),(c,a))=Q_j(B)p_{jk}$;
--   4. transition $T((x,j),(c,a),(z,k))=\big((1+i)(x-c+a\cdot z),k\big)$;
--   5. reward $\beta^nU_c(c)$ at time $n$, with discount factor $\beta\in(0,1]$.
--
--   **Formalization Note** The wealth is a nonnegative real and $T$ truncates it at $0$; for admissible actions the wealth is nonnegative $Q_j$-a.s., so the truncation changes no law. $E_Y$ carries the discrete $\sigma$-algebra.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.4, p.102 (PDF p.116)

import Mathlib
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_DisturbanceMDM
import Definitions.Def_BauerleRiederMDP_RegimeSwitching_RegimeMarket_transition
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BauerleRiederMDP.RegimeSwitching

/-- The stationary Markov Decision Model of the **consumption-investment problem with regime
switching** (4.19) (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance* (2011), §4.4, p.102, PDF p.116): `E = [0, ∞) × E_Y` (wealth, environment
state), `A = ℝ_+ × ℝ^d` (consumption `c`, amounts `a` in the risky assets),
`D(x, j) = {(c, a) ∈ A | 0 ≤ c ≤ x and (1 + i)(x − c + a · R(j)) ≥ 0 ℙ-a.s.}`,
`Z = [−1, ∞)^d × E_Y` (relative risk, new environment state),
`T((x, j), (c, a), (z, k)) = ((1 + i)(x − c + a · z), k)`,
`Q^Z(B × {k} | (x, j), (c, a)) = Q_j(B) p_{jk}`, `r((x, j), (c, a)) = U_c(c)` with discount factor
`β`. As a non-stationary model (Remark 2.1.2 c), p.14) the reward at time `n` is
`r_n = β^n r`; the terminal reward `β^N g` with `g(x, j) = U_p(x)` is passed to
`valueFunction` (see `J`).

**Formalization Note.** The state space is `ℝ≥0 × E_Y` and `T` truncates the wealth with
`Real.toNNReal`; for `(c, a) ∈ D(x, j)` the wealth is `≥ 0` for `Q_j`-a.e. `z`, so the
truncation changes no law. The disturbance space is all of `ℝ^d × E_Y`. `E_Y` carries the
discrete σ-algebra. -/
noncomputable def regimeModel {EY : Type*} [Fintype EY] [MeasurableSpace EY]
    [DiscreteMeasurableSpace EY] {d : ℕ} (M : RegimeMarket EY d) (i β : ℝ) (Uc : ℝ → ℝ) :
    DisturbanceMDM (ℝ≥0 × EY) (ℝ × (Fin d → ℝ)) ((Fin d → ℝ) × EY) where
  D _ s := {ca | 0 ≤ ca.1 ∧ ca.1 ≤ s.1 ∧
    ∀ᵐ z ∂(M.Q s.2 : Measure (Fin d → ℝ)), 0 ≤ (1 + i) * (s.1 - ca.1 + ∑ k, ca.2 k * z k)}
  T _ sa zk := (Real.toNNReal ((1 + i) * (sa.1.1 - sa.2.1 + ∑ k, sa.2.2 k * zk.1 k)), zk.2)
  measurable_T n := by
    refine Measurable.prodMk ?_ (measurable_snd.comp measurable_snd)
    apply Measurable.real_toNNReal
    fun_prop
  QZ _ := (Kernel.ofFunOfCountable (fun j : EY =>
      ((M.Q j : Measure (Fin d → ℝ)).prod (M.transition j : Measure EY)))).comap
    (fun sa : (ℝ≥0 × EY) × (ℝ × (Fin d → ℝ)) => sa.1.2) (by fun_prop)
  isMarkovKernel_QZ _ := by
    refine ⟨fun sa => ?_⟩
    change IsProbabilityMeasure (((M.Q sa.1.2 : Measure (Fin d → ℝ)).prod
      (M.transition sa.1.2 : Measure EY)))
    infer_instance
  r n sa := β ^ n * Uc sa.2.1

end BauerleRiederMDP.RegimeSwitching


