-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_trivialRockafellian
-- name    : RockafellianRelax_Supplement_trivialRockafellian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:11:28.495062+00:00
-- url     : https://prove2.me/theorems/80242245-9d08-4341-a003-1b076ef23812
-- title:
--   The trivial Rockafellian, which gives (4.2) and (4.9)
-- statement:
--   For $\varphi : \mathbb R^n \to \overline{\mathbb R}$, the **trivial Rockafellian** $f : \mathbb R^m \times \mathbb R^n \to \overline{\mathbb R}$ is
--
--   $$
--   f(u,x) = \begin{cases}\varphi(x), & u = 0,\\ +\infty, & u \ne 0.\end{cases}
--   $$
--
--   For $\varphi = f_0 + \sum_i p_i f_i$ it is the Rockafellian (4.2), $f_0(x) + \sum_i (p_i+u_i) f_i(x) + \iota_{\{0\}^s}(u)$. For $\varphi = f_0 + \sum_i p_i g(\xi_i,\cdot)$ and the perturbation $(u,v)$ it is the Rockafellian (4.9).
--
--   It is the epi-limit in Theorems 4.4 and 4.5.
--
--   **Formalization Note** The paper's indicator sums equal $+\infty$ off $u = 0$ because $\infty - \infty = \infty$ there. The definition is written by cases, as `EReal` has $-\infty + \infty = -\infty$.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §3.1, p.7 (trivial design); display (4.2), p.10; display (4.9), p.16

import Mathlib

namespace RockafellianRelax.Supplement

open Classical in
/-- **The trivial Rockafellian**, used for (4.2) and (4.9).
Royset, Chen & Eckstrand, arXiv:2204.04762v4, §3.1, p.7: "A trivial design (but still useful as seen in the next section) is to let
f(u, x) = ∞ for u ≠ 0 and f(0, x) = φ(x)".

**Formalization Note.** (4.2), p.10, `f₀(x) + ∑ (pᵢ + uᵢ) fᵢ(x) + ι_{{0}^s}(u)`, is this function
for the objective `φ` of (2.1), and (4.9), p.16, is this function for the objective of (4.8), with
the perturbation `(u, v) ∈ ℝ^{s+sm}`: off `u = 0` the indicator makes the paper's sum `+∞` because
`∞ − ∞ = ∞` (footnote 1, p.4). It is defined by cases since `⊥ + ⊤ = ⊥` in `EReal`. -/
noncomputable def trivialRockafellian {m n : ℕ} (φ : (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) × (Fin n → ℝ) → EReal :=
  fun z => if z.1 = 0 then φ z.2 else ⊤

end RockafellianRelax.Supplement


