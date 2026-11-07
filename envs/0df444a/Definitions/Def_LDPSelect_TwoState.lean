-- Prove2me | Definitions.Def_LDPSelect_TwoState
-- name    : LDPSelect_TwoState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:55:29.541193+00:00
-- url     : https://prove2.me/theorems/b47e79c7-9c85-4e97-ac75-0d3432253323
-- title:
--   The two-state instances: $\delta,\ell,h$, $\Delta(a)$, $Y$, deterministic tails and the gap $\gamma$
-- statement:
--   Fix $a>1$ and $\mu>0$, and put
--
--   $$\delta=\frac{(a-1)\mu}{2(a+2)},\qquad \ell=\mu-\delta,\qquad h=\mu+\delta,$$
--
--   $$\Delta(a)=\frac{(a-1)^2\mu}{12(a+1)(a+2)}\ (1<a\le3),\qquad \Delta(a)=\frac{(a-1)\mu}{6(a+1)(a+2)}\ (a\ge3).$$
--
--   $Y$ is uniform on $\{0,\mu,2\mu\}$. In the two-state instances the first arrival $u$ is uniform on $\{0,2\gamma\}$, the second $v$ has value $Y$, and all later arrivals carry deterministic values $\tau_i$. For a state $A$ after the first two arrivals, the deterministic continuation is the largest $\sum_{i\in S}\tau_i$ over sets $S$ of later arrivals with $A\cup S\in\mathcal F$. Then
--
--   1. $t_0$ and $t_1$ are the thresholds faced by $v$ when $u$ was rejected and accepted (rejection minus acceptance continuation);
--   2. $\beta_0,\beta_1$ are the continuations after accepting $v$;
--   3. $\gamma=(\beta_0+F_a(Y,t_0))-(\beta_1+F_a(Y,t_1))$ is the continuation after rejecting $u$ minus that after accepting it.
--
--   **Formalization Note** $u$ and $v$ are positions $0$ and $1$. The two formulas for $\Delta(a)$ agree at $a=3$.
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), Proposition 12, p.6 (pdf p.7); Lemma 16, p.9 (pdf p.10); A.5, p.18 (pdf p.19); A.6, p.19 (pdf p.20)

import Mathlib
import Definitions.Def_LDPSelect_Family
import Definitions.Def_LDPSelect_Fa

open MeasureTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-!
# The two-state instances

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), Proposition 12, p.6; Lemma 16, p.9; A.5, p.18; A.6, p.19.

**Formalization Note.** The paper's first arrival `u` is position `0`, the second arrival `v` is position
`1`, and positions `≥ 2` have deterministic values `τ`. The parameter `μ` is real and every use has
`0 < μ`; `toNNReal` converts a positive value. `tailCont` is the deterministic continuation; a `Finset.sup`
over the empty set gives `0`, which happens only for `A ∉ F`, and every use has `A ∈ F`.
-/

/-- `δ = (a − 1) μ / (2 (a + 2))`. -/
noncomputable def deltaParam (a μ : ℝ) : ℝ := (a - 1) * μ / (2 * (a + 2))

/-- `ℓ = μ − δ`. -/
noncomputable def ell (a μ : ℝ) : ℝ := μ - deltaParam a μ

/-- `h = μ + δ`. -/
noncomputable def high (a μ : ℝ) : ℝ := μ + deltaParam a μ

/-- `∆(a)` of Proposition 12, p.6: `(a−1)²μ/(12(a+1)(a+2))` for `a ≤ 3`, `(a−1)μ/(6(a+1)(a+2))` for
`a ≥ 3`; the two agree at `a = 3`. -/
noncomputable def gapDelta (a μ : ℝ) : ℝ :=
  if a ≤ 3 then (a - 1) ^ 2 * μ / (12 * (a + 1) * (a + 2))
  else (a - 1) * μ / (6 * (a + 1) * (a + 2))

/-- `Y`, uniform on `{0, μ, 2μ}`. -/
noncomputable def Y (μ : ℝ) : Measure ℝ≥0 :=
  (3⁻¹ : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac μ.toNNReal + Measure.dirac (2 * μ).toNNReal)

/-- The uniform law on `{0, 2γ}`. -/
noncomputable def uniform2 (γ : ℝ) : Measure ℝ≥0 :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac (2 * γ).toNNReal)

open Classical in
/-- The deterministic continuation from state `A` after the first two arrivals: the largest
`∑_S τ` over `S` among positions `≥ 2` with `A ∪ S ∈ F`. -/
noncomputable def tailCont {m : ℕ} (F : Family (m + 2)) (τ : Fin (m + 2) → ℝ≥0)
    (A : Finset (Fin (m + 2))) : ℝ :=
  (((Finset.univ.filter fun S : Finset (Fin (m + 2)) =>
      (∀ i ∈ S, 2 ≤ i.val) ∧ A ∪ S ∈ F).sup fun S => ∑ i ∈ S, τ i : ℝ≥0) : ℝ)

/-- `t_0`: the threshold of the second arrival when the first was rejected. -/
noncomputable def t0 {m : ℕ} (F : Family (m + 2)) (τ : Fin (m + 2) → ℝ≥0) : ℝ :=
  tailCont F τ ∅ - tailCont F τ {1}

/-- `t_1`: the threshold of the second arrival when the first was accepted. -/
noncomputable def t1 {m : ℕ} (F : Family (m + 2)) (τ : Fin (m + 2) → ℝ≥0) : ℝ :=
  tailCont F τ {0} - tailCont F τ {0, 1}

/-- `γ = (β_0 + F_a(Y, t_0)) − (β_1 + F_a(Y, t_1))` (A.6, p.19), with `β_0, β_1` the continuations
after accepting the second arrival: rejection minus acceptance at the first arrival. -/
noncomputable def gammaOf {m : ℕ} (a μ : ℝ) (F : Family (m + 2)) (τ : Fin (m + 2) → ℝ≥0) : ℝ :=
  (tailCont F τ {1} + Fa a (Y μ) (t0 F τ)) - (tailCont F τ {0, 1} + Fa a (Y μ) (t1 F τ))

/-- The prior of Lemma 16: position `0` uniform on `{0, 2γ}`, position `1` is `Y`, later positions
deterministic. -/
noncomputable def twoStatePrior {m : ℕ} (γ μ : ℝ) (τ : Fin (m + 2) → ℝ≥0) :
    Fin (m + 2) → Measure ℝ≥0 := fun i =>
  if i.val = 0 then uniform2 γ else if i.val = 1 then Y μ else Measure.dirac (τ i)

end LDPSelect


