-- Prove2me | Definitions.Def_JencovaRenyi_interpNorm
-- name    : JencovaRenyi_interpNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:29.118982+00:00
-- url     : https://prove2.me/theorems/4ebda211-9e67-4115-a500-9986f319ca4f
-- title:
--   Complex interpolation: admissible functions on the strip and the norm $\|x\|_\theta$ of $C_\theta(X_0, X_1)$
-- statement:
--   Let $X_1$ be a normed complex space and $X_0\subseteq X_1$ a subspace with norm $\|\cdot\|_0$, encoded by a gauge $n_0 : X_1\to[0,\infty]$ with $X_0 = \{n_0 < \infty\}$. Let $S = \{z\in\mathbb C : 0\le \operatorname{Re} z\le 1\}$. A function $f : S\to X_1$ is **admissible**, $f\in\mathcal F(X_0,X_1)$, if
--
--   1. $f$ is bounded, continuous on $S$ and analytic in the interior of $S$;
--   2. for $t\in\mathbb R$, $f(it)\in X_0$, and $t\mapsto f(it)\in X_0$ is continuous and bounded for $\|\cdot\|_0$.
--
--   Its norm is $|||f|||_{\mathcal F} = \max\{\sup_t \|f(it)\|_0,\ \sup_t\|f(1+it)\|_1\}$, and for $0<\theta<1$
--   $$
--   \|x\|_\theta = \inf\{|||f|||_{\mathcal F} : f\in\mathcal F,\ f(\theta) = x\},
--   $$
--   the norm of $C_\theta(X_0,X_1) = \{f(\theta) : f\in\mathcal F\}$.
--
--   This is the construction by which the paper defines $L_p(\mathcal M,\varphi) = C_{1/p}(L_\infty(\mathcal M,\varphi), L_1(\mathcal M))$.
--
--   **Formalization Note** $f$ is a function on all of $\mathbb C$, only its values on $S$ matter. The value $\|x\|_\theta = \infty$ means $x\notin C_\theta(X_0,X_1)$. As printed, there is no decay condition at infinity.
-- source:
--   Jenčová, Rényi relative entropies and noncommutative $L_p$-spaces, arXiv:1609.08462v4, Appendix B, p.22, conditions (a), (b) and (B.9)

import Mathlib

open scoped ENNReal
open Complex

namespace JencovaRenyi

/-- The closed strip `S = {z ∈ ℂ : 0 ≤ Re z ≤ 1}` of Appendix B (Jenčová, arXiv:1609.08462v4,
p.22). -/
def strip : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}

/-- The admissible functions `𝓕(X₀, X₁)` of the complex interpolation method (Jenčová,
arXiv:1609.08462v4, Appendix B, p.22). `X₁` is a normed complex space and `X₀ ⊆ X₁` is given by
its gauge `n₀ : X₁ → [0, ∞]`, with `X₀ = {n₀ < ∞}` and `‖·‖₀ = n₀` there. A function
`f : S → X₁` is admissible when

* (a) `f` is bounded, continuous on `S` and analytic in the interior of `S`;
* (b) for `t ∈ ℝ`, `f(it) ∈ X₀`, and `t ↦ f(it) ∈ X₀` is continuous and bounded (for `‖·‖₀`).

**Formalization Note.** `f` is a function on all of `ℂ`; only its values on `S` matter. There is
no decay condition at infinity, as printed. -/
def IsAdmissible {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] (n₀ : X → ℝ≥0∞)
    (f : ℂ → X) : Prop :=
  (∃ C : ℝ, ∀ z ∈ strip, ‖f z‖ ≤ C) ∧ ContinuousOn f strip ∧
    DifferentiableOn ℂ f {z : ℂ | 0 < z.re ∧ z.re < 1} ∧
    (∀ t : ℝ, n₀ (f ((t : ℂ) * I)) < ⊤) ∧
    (∀ t : ℝ, Filter.Tendsto (fun s : ℝ => n₀ (f ((s : ℂ) * I) - f ((t : ℂ) * I)))
      (nhds t) (nhds 0)) ∧
    (⨆ t : ℝ, n₀ (f ((t : ℂ) * I))) < ⊤

/-- The norm `|||f|||_𝓕 = max {sup_t ‖f(it)‖₀, sup_t ‖f(1+it)‖₁}` (Jenčová, arXiv:1609.08462v4,
Appendix B, p.22). -/
noncomputable def admissibleNorm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (n₀ : X → ℝ≥0∞) (f : ℂ → X) : ℝ≥0∞ :=
  max (⨆ t : ℝ, n₀ (f ((t : ℂ) * I))) (⨆ t : ℝ, (‖f (1 + (t : ℂ) * I)‖₊ : ℝ≥0∞))

/-- The complex interpolation norm (B.9) of Jenčová, arXiv:1609.08462v4, Appendix B, p.22:
`‖x‖_θ = inf {|||f|||_𝓕 : f(θ) = x, f ∈ 𝓕}` on `C_θ(X₀, X₁) = {f(θ) : f ∈ 𝓕}`.

**Formalization Note.** The value is in `[0, ∞]`; it is `⊤` exactly when `x ∉ C_θ(X₀, X₁)` (no
admissible `f` with `f(θ) = x`), so `C_θ(X₀, X₁) = {‖·‖_θ < ⊤}`. The paper uses `0 < θ < 1`. -/
noncomputable def interpNorm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (n₀ : X → ℝ≥0∞) (θ : ℝ) (x : X) : ℝ≥0∞ :=
  ⨅ (f : ℂ → X) (_ : IsAdmissible n₀ f) (_ : f (θ : ℂ) = x), admissibleNorm n₀ f

end JencovaRenyi


