-- Prove2me | Definitions.Def_SinkhornHall_Analysis
-- name    : SinkhornHall_Analysis
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:18.942638+00:00
-- url     : https://prove2.me/theorems/dbe928b2-6adc-43b0-840a-e500c111fc55
-- title:
--   KL divergence of nonnegative vectors, the capacity $\kappa(x,y)$ and the geometric-program objective
-- statement:
--   Three analytic objects of the paper.
--
--   1. **KL divergence of nonnegative vectors.** For nonnegative $p,q\in\mathbb R^I$,
--   $$D(p\|q)=\sum_i p_i\log\frac{p_i}{q_i},$$
--   with the conventions $0\log\frac0x=0$ for $x\ge0$ and $x\log\frac x0=\infty$ for $x>0$. The sums of $p$ and $q$ may differ, so $D(p\|q)$ can be negative.
--   2. **Capacity.** For a nonnegative matrix $A$, positive marginals $r,c$ with $R=\sum_i r_i$, $C=\sum_j c_j$, and positive $x,y$,
--   $$\kappa(x,y)=\frac{\sum_{i,j}A_{ij}x_iy_j}{\prod_i x_i^{r_i/R}\,\prod_j y_j^{c_j/C}}.$$
--   This is the objective of the geometric program (2.2), whose alternating minimization is the Sinkhorn algorithm.
--   3. **Unconstrained geometric program.** For positive reals $q_k$ and vectors $\omega_k\in\mathbb R^d$,
--   $$f(\xi)=\log\sum_k q_k e^{\omega_k^\top\xi}\qquad(\xi\in\mathbb R^d).$$
--
--   **Formalization Note** $D$ takes values in the extended reals `EReal` so that $\infty$ is representable; it is $\top$ exactly when some $q_i=0<p_i$. No mass-correction term is added (Mathlib's `InformationTheory.klDiv` adds one). Powers in $\kappa$ are real powers (`Real.rpow`) of positive numbers; $\log$ is the natural logarithm.
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, §1 Notation p.4 (D(p∥q)); §2.1 (2.2) p.6 (κ); §2.1 (2.5) p.7 (f)

import Mathlib

open Finset

namespace SinkhornHall

/-!
Analytic objects of Hayashi–Hirai–Sakabe, *Finding Hall blockers by matrix scaling*,
arXiv:2204.07425v2: the KL divergence of nonnegative vectors (§1 Notation, p.4), the capacity
`κ(x, y)` of (2.2) (§2.1, p.6) and the unconstrained geometric-program objective (2.5) (p.7).
-/

open Classical in
/-- **KL divergence of nonnegative vectors.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §1 Notation, p.4: "For two nonnegative vectors p, q ∈ ℝⁿ,
let D(p∥q) denote the KL-divergence between p and q: D(p∥q) := Σᵢ pᵢ log pᵢ/qᵢ, where
0 log 0/x := 0 for x ≥ 0 and x log x/0 := ∞ for x > 0. In this paper, we allow p, q to have
different sum p([n]) ≠ q([n]); so D(p∥q) can be negative for such a case."

`klDiv p q` is `⊤` if some `qᵢ = 0 < pᵢ`, and otherwise the real number `Σᵢ pᵢ log(pᵢ/qᵢ)`.

**Formalization Note.** Valued in `EReal` so that the paper's `∞` is representable. In the finite
case every term with `pᵢ = 0` is `0 · log(…) = 0`, matching `0 log 0/x := 0`; `Real.log` is the
natural logarithm. No mass-correction term is added (unlike Mathlib's
`InformationTheory.klDiv`), so `D` can be negative when the sums differ, as the paper says. The
definition is meant for nonnegative vectors; every statement using it assumes nonnegativity. -/
noncomputable def klDiv {ι : Type*} [Fintype ι] (p q : ι → ℝ) : EReal :=
  if ∃ i, q i = 0 ∧ 0 < p i then ⊤
  else ((∑ i, p i * Real.log (p i / q i) : ℝ) : EReal)

/-- **The capacity `κ(x, y)`** of the geometric program (2.2).
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2.1, (2.2), p.6:
"κ(x, y) := Σ_{i,j} A_ij x_i y_j / (∏_i x_i^{r_i/R} ∏_j y_j^{c_j/C})  s.t. x_i, y_j > 0", where
`R := r([n])` and `C := c([m])` (p.5).

**Formalization Note.** The powers `x_i^{r_i/R}` are `Real.rpow`; they are meant for positive
`x`, `y` (every statement assumes this), where `Real.rpow` is the usual power. `R` and `C` are
written out as `Σ r` and `Σ c`. §2.1 assumes `R = C`; that is a hypothesis of the statements, not
part of the definition. -/
noncomputable def kappa {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (r : ι → ℝ)
    (c : κ → ℝ) (x : ι → ℝ) (y : κ → ℝ) : ℝ :=
  (∑ i, ∑ j, A i j * x i * y j) /
    ((∏ i, x i ^ (r i / ∑ i', r i')) * ∏ j, y j ^ (c j / ∑ j', c j'))

/-- **Objective of an unconstrained geometric program** (2.5).
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §2.1, (2.5), p.7: "Given positive reals q_k > 0 and
vectors ω_k ∈ ℝᵈ (k = 1, 2, …, m ≥ 2), minimize function f : ℝᵈ → ℝ defined by
f(ξ) := log Σ_{k=1}^m q_k e^{ω_kᵀ ξ}".

**Formalization Note.** The terms are indexed by a finite type `K`; `ω_kᵀ ξ` is `ω k ⬝ᵥ ξ` on
`Fin d → ℝ`; `log` is `Real.log` (natural). Positivity of `q` is a hypothesis of the statements. -/
noncomputable def gpObjective {K : Type*} [Fintype K] {d : ℕ} (q : K → ℝ) (ω : K → Fin d → ℝ)
    (ξ : Fin d → ℝ) : ℝ :=
  Real.log (∑ k, q k * Real.exp (ω k ⬝ᵥ ξ))

end SinkhornHall


