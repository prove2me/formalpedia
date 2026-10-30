-- Prove2me | Definitions.Def_PorteusGenSS_IsPFOrder
-- name    : PorteusGenSS_IsPFOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:08:21.90801+00:00
-- url     : https://prove2.me/theorems/635b9283-d758-4261-83d1-9dafd072a827
-- title:
--   Pólya frequency function of order $n$ ($PF_n$)
-- statement:
--   A measurable function $\varphi:\mathbb R\to\mathbb R$ is a **Pólya frequency function of order $n$** ($\varphi$ is $PF_n$) if
--
--   1. $0<\int_{-\infty}^{\infty}\varphi(x)\,dx<\infty$ (with $\varphi$ Lebesgue integrable), and
--   2. for every $1\le k\le n$ and all $x_1<\dots<x_k$, $t_1<\dots<t_k$,
--   $$
--   \det\big[\varphi(x_i-t_j)\big]_{i,j=1}^{k}\ \ge 0 .
--   $$
--
--   The case $k=1$ forces $\varphi\ge 0$. These total-positivity conditions underlie the smoothing and shape-preserving properties of convolution with $\varphi$.
--
--   **Formalization Note** Measurability is the paper's standing convention for all functions (§X); it is carried by `Integrable φ` (a.e. strong measurability, i.e. Lebesgue measurability), not by a Borel `Measurable φ`.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 5, p. 421

import Mathlib

open MeasureTheory

namespace PorteusGenSS

/-- **Pólya frequency function of order n (Definition 5).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 5, p. 421: "A function φ is a Pólya frequency function of order n (φ is PFₙ)
if (a) 0 < ∫_{−∞}^∞ φ(x) dx < ∞ (b) det[φ(xᵢ − tⱼ)]_{1,k} ≥ 0 if 1 ≤ k ≤ n,
x₁ < x₂ < ⋯ < x_k, and t₁ < t₂ < ⋯ < t_k."

`IsPFOrder n φ` says: `φ` is Lebesgue integrable on ℝ with `0 < ∫ φ`, and for every
`1 ≤ k ≤ n` and all strictly increasing `x₁ < ⋯ < x_k`, `t₁ < ⋯ < t_k`, the `k × k` determinant
`det [φ(xᵢ − tⱼ)]` is nonnegative.

**Formalization Note.** Measurability is the paper's standing convention (§X, p. 425: "All
functions appearing in this paper are assumed to be real valued (Lebesgue) measurable"); it is
carried by `Integrable φ`, which includes a.e. strong measurability, i.e. Lebesgue measurability.
No Borel `Measurable φ` is required (that would exclude Lebesgue-measurable non-Borel φ).
"∫φ < ∞" is `Integrable φ` (for `n ≥ 1` the case `k = 1` gives `φ ≥ 0`, so a finite integral is
an absolutely convergent one). The determinant is Mathlib's `Matrix.det` of the matrix
`(i, j) ↦ φ(xᵢ − tⱼ)` indexed by `Fin k`. -/
def IsPFOrder (n : ℕ) (φ : ℝ → ℝ) : Prop :=
  Integrable φ ∧ 0 < ∫ x, φ x ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ n → ∀ x t : Fin k → ℝ, StrictMono x → StrictMono t →
      0 ≤ (Matrix.of fun i j => φ (x i - t j)).det

end PorteusGenSS


