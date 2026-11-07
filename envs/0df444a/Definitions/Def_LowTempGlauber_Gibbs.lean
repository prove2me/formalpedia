-- Prove2me | Definitions.Def_LowTempGlauber_Gibbs
-- name    : LowTempGlauber_Gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:02.45604+00:00
-- url     : https://prove2.me/theorems/3cee3f32-ddca-4087-ab3b-5e6165d9b16b
-- title:
--   The Gibbs family $\mu_t\propto w\,e^{tH}$, $Z_t$, and upper-$\delta$-tailed estimators
-- statement:
--   Let $\Omega$ be a finite set with a weight $w:\Omega\to\mathbb R_{>0}$ and a Hamiltonian $H:\Omega\to[-H_{\max},H_{\max}]$. For $t\in\mathbb R$,
--   $$Z_t=\sum_{x\in\Omega}w(x)e^{tH(x)},\qquad \mu_t(x)=\frac{w(x)e^{tH(x)}}{Z_t}.$$
--
--   **Definition 13.** For $\delta\in(0,1/4)$, a nonnegative random variable $W$ is an **upper-$\delta$-tailed estimator** for a quantity $Z$ if $\mathbb E[W]=Z$,
--   $$\Pr\bigl[\tfrac12Z\le W\le2Z\bigr]\ge1-\delta\qquad\text{and}\qquad\mathbb E\bigl[W\,\mathbf 1\{W>4Z\}\bigr]\le\delta Z.$$
--
--   Such estimators are weaker than relative-error estimators: they only need a constant-factor estimate with a controlled upper tail, which is what the paper's phase selector (Lemma 14) requires.
--
--   **Formalization Note** A random variable is represented by its law $W$, a probability measure on $\mathbb R$ carried by $[0,\infty)$ and integrable. The range $\delta\in(0,1/4)$ is part of the definition. Positivity of $w$ and the bound on $H$ are hypotheses of the statements.
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), §3.3, p.15 (setup and Definition 13)

import Mathlib

namespace LowTempGlauber

/-!
# The Gibbs family `μ_t ∝ w e^{tH}` and upper-δ-tailed estimators

A. Galanis, D. Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission manuscript dated 3 November 2026 (held version, sha256 c41a38ff…7533d), §3.3, p.15
(the generic setup and Definition 13).

On a finite space `Ω` with a weight `w : Ω → ℝ_{>0}` and a Hamiltonian `H : Ω → [−H_max, H_max]`,
`Z_t = Σ_x w(x) e^{tH(x)}` and `μ_t(x) = w(x) e^{tH(x)}/Z_t`.

**Formalization Note.**
* Positivity of `w` and the bound `|H| ≤ H_max` are hypotheses of the statements, not part of `Zt`.
* A nonnegative random variable `W` is represented by its law, a measure on `ℝ`. `IsUpperTailed δ Z W`
  is Definition 13: `δ ∈ (0, 1/4)` (the definition's standing range), `W` is a probability law
  carried by `[0, ∞)`, integrable, with `E[W] = Z`, `Pr[Z/2 ≤ W ≤ 2Z] ≥ 1 − δ` and
  `E[W 1{W > 4Z}] ≤ δ Z`.
-/

open MeasureTheory

variable {Ω : Type*} [Fintype Ω]

/-- The partition function `Z_t = Σ_x w(x) e^{tH(x)}`, p.15. -/
noncomputable def Zt (w H : Ω → ℝ) (t : ℝ) : ℝ :=
  ∑ x, w x * Real.exp (t * H x)

/-- The Gibbs law `μ_t(x) = w(x) e^{tH(x)}/Z_t`, p.15. -/
noncomputable def muT (w H : Ω → ℝ) (t : ℝ) (x : Ω) : ℝ :=
  w x * Real.exp (t * H x) / Zt w H t

/-- Definition 13, p.15: the law `W` of a nonnegative random variable is an upper-`δ`-tailed estimator
for `Z` (for `δ ∈ (0, 1/4)`): `E[W] = Z`, `Pr[Z/2 ≤ W ≤ 2Z] ≥ 1 − δ` and `E[W 1{W > 4Z}] ≤ δ Z`. -/
def IsUpperTailed (δ Z : ℝ) (W : Measure ℝ) : Prop :=
  0 < δ ∧ δ < 1 / 4 ∧ IsProbabilityMeasure W ∧ W (Set.Iio 0) = 0 ∧
    Integrable (fun x : ℝ => x) W ∧ ∫ x, x ∂W = Z ∧
    1 - δ ≤ (W (Set.Icc (Z / 2) (2 * Z))).toReal ∧
    ∫ x in Set.Ioi (4 * Z), x ∂W ≤ δ * Z

end LowTempGlauber


