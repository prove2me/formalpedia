-- Prove2me | Definitions.Def_LowTempGlauber_ChainLayer
-- name    : LowTempGlauber_ChainLayer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:25:55.669758+00:00
-- url     : https://prove2.me/theorems/d3e7fa4e-b325-4958-bbcd-1151542a43e8
-- title:
--   Variance, Dirichlet form, $(A,b)$ weak Poincaré inequalities and $\chi^2$ for finite chains
-- statement:
--   Let $P$ be a Markov chain on a finite state space $\Omega$, presented as a matrix acting on row vectors, and let $\pi$ be its stationary distribution. For $f:\Omega\to\mathbb R$ the paper (§2.1) uses
--
--   1. the **variance** $\operatorname{Var}_\pi(f)=\tfrac12\sum_{x,y\in\Omega}\pi(x)\pi(y)\,(f(x)-f(y))^2$;
--   2. the **Dirichlet form** $\mathcal E_P(f,f)=\tfrac12\sum_{x,y\in\Omega}\pi(x)P(x,y)\,(f(x)-f(y))^2$;
--   3. the **oscillation** $f_{\max}-f_{\min}$;
--   4. the **$(A,b)$ weak Poincaré inequality**: $P$ satisfies it if
--   $$\operatorname{Var}_\pi(f)\le A\,\mathcal E_P(f,f)+b\,(f_{\max}-f_{\min})^2\qquad\text{for all }f:\Omega\to\mathbb R;$$
--   5. the **chi-square divergence** $\chi^2(\nu\|\pi)=\sum_x\pi(x)\bigl(\nu(x)/\pi(x)-1\bigr)^2$.
--
--   A weak Poincaré inequality is an ordinary Poincaré inequality up to an additive error controlled by the oscillation; it is the functional inequality that the paper derives from the structure of disagreements and that drives every mixing bound of the mission.
--
--   Nonnegative spectrum of $P$ (Lemma 4) is the published predicate `SKWeakPoincare.HasNonnegSpectrum`: $\sum_x\pi(x)f(x)(Pf)(x)\ge0$ for all $f$; for a chain reversible with respect to $\pi>0$, $P$ is self-adjoint in $\ell^2(\pi)$, so this is exactly "every eigenvalue of $P$ is nonnegative".
--
--   **Formalization Note** With real division, $\chi^2$ is the paper's value only when $\nu(x)=0$ wherever $\pi(x)=0$; statements using it assume this. The standing range $A,b>0$ of the weak Poincaré inequality is a hypothesis of each statement.
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), §2.1, p.8, and Lemma 4, p.8

import Mathlib

namespace LowTempGlauber

/-!
# Variance, Dirichlet form, oscillation, weak Poincaré inequalities, χ²

A. Galanis, D. Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission manuscript dated 3 November 2026 (held version, sha256 c41a38ff…7533d), §2.1, p.8, and
Lemma 4, p.8.

A chain on a finite state space `Ω` is a matrix `P : Matrix Ω Ω ℝ` acting on row vectors (as in the
published `MarkovMixing` layer); `π : Ω → ℝ` is its stationary distribution.

**Formalization Note.**
* `variance` and `dirichlet` are the page's two double sums, with the factor `1/2`.
* `osc f = f_max − f_min`, written with `⨆`/`⨅`; on a finite nonempty `Ω` these are a maximum and a
  minimum (every statement using `osc` has a nonempty state space).
* `IsWeakPoincare P π A b` is the page's inequality for every `f : Ω → ℝ`; the page's standing range
  `A, b > 0` is a hypothesis of each statement that uses it.
* Nonnegative spectrum (Lemma 4) is not defined here: the statements use the published
  `SKWeakPoincare.HasNonnegSpectrum π P` (`⟨f, P f⟩_π ≥ 0` for every `f`).
* `chiSq ν π = Σ π(x)(ν(x)/π(x) − 1)²`, Lemma 4's display. Real division by `0` gives `0`, so it is the
  page's `χ²` only when `ν(x) = 0` wherever `π(x) = 0`; statements using it assume that.
-/

variable {Ω : Type*} [Fintype Ω]

/-- `Var_π(f) = ½ Σ_{x,y} π(x) π(y) (f(x) − f(y))²`, p.8. -/
noncomputable def variance (π : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, π x * π y * (f x - f y) ^ 2

/-- The Dirichlet form `E_P(f, f) = ½ Σ_{x,y} π(x) P(x, y) (f(x) − f(y))²`, p.8. -/
noncomputable def dirichlet (P : Matrix Ω Ω ℝ) (π : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  (1 / 2) * ∑ x, ∑ y, π x * P x y * (f x - f y) ^ 2

/-- `f_max − f_min`, p.8. -/
noncomputable def osc (f : Ω → ℝ) : ℝ :=
  (⨆ x, f x) - (⨅ x, f x)

/-- `P` satisfies an `(A, b)` weak-Poincaré inequality, p.8:
`Var_π(f) ≤ A · E_P(f, f) + b (f_max − f_min)²` for all `f : Ω → ℝ`. -/
def IsWeakPoincare (P : Matrix Ω Ω ℝ) (π : Ω → ℝ) (A b : ℝ) : Prop :=
  ∀ f : Ω → ℝ, variance π f ≤ A * dirichlet P π f + b * osc f ^ 2

/-- `χ²(ν ‖ π) = Σ_x π(x) (ν(x)/π(x) − 1)²`, Lemma 4, p.8. -/
noncomputable def chiSq (ν π : Ω → ℝ) : ℝ :=
  ∑ x, π x * (ν x / π x - 1) ^ 2

end LowTempGlauber


