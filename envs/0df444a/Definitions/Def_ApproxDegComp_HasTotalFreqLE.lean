-- Prove2me | Definitions.Def_ApproxDegComp_HasTotalFreqLE
-- name    : ApproxDegComp_HasTotalFreqLE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:30:45.561236+00:00
-- url     : https://prove2.me/theorems/cc357987-45dc-4298-8eda-41c9e6b267f8
-- title:
--   Trigonometric polynomial of total frequency at most $D$
-- statement:
--   A function $R:\mathbb R^n\to\mathbb C$ is a **trigonometric polynomial of total frequency at most $D$** if it can be written as a finite sum
--
--   $$R(\theta)=\sum_{a\in\mathbb Z^n,\ \|a\|_1\le D}c_a\,e^{i\langle a,\theta\rangle},\qquad \|a\|_1=\sum_i|a_i|,$$
--
--   with complex coefficients $c_a$. A real-valued $R$ is treated as a complex-valued one.
--
--   Total frequency is the trigonometric analogue of total degree; it is what the polynomial construction of the proof of Theorem 23 transfers from the degree of an approximant of $f\circ g$.
--
--   **Formalization Note** The coefficients form a finitely supported function on $\mathbb Z^n$; the bound is on the $\ell_1$ norm of every frequency in the support.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Definition 21, p.15 (complex coefficients as in Definition 18, p.13)

import Mathlib

namespace ApproxDegComp

/-- **Trigonometric polynomial of total frequency at most D** (Definition 21, p.15).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Definition 21, p.15: "A multivariate trigonometric polynomial R has total frequency at most
D if it can be written as R(θ) = Σ_{‖a‖₁≤D} c_a e^{i⟨a,θ⟩} where a ∈ ℤⁿ and ‖a‖₁ = Σᵢ |aᵢ|."

`HasTotalFreqLE R D` says that `R : ℝⁿ → ℂ` is a finite sum of exponentials `c_a e^{i⟨a,θ⟩}`
with integer frequency vectors `a` of `ℓ₁` norm at most `D`.

**Formalization Note** The coefficients are a finitely supported `c : (Fin n → ℤ) →₀ ℂ` (complex,
as Definition 18 allows); the bound is on the `ℓ₁` norm `Σᵢ |aᵢ|` of each frequency in the
support. A real-valued `R` is written `fun θ => (R θ : ℂ)`. -/
def HasTotalFreqLE {n : ℕ} (R : (Fin n → ℝ) → ℂ) (D : ℕ) : Prop :=
  ∃ c : (Fin n → ℤ) →₀ ℂ, (∀ a ∈ c.support, ∑ i, |a i| ≤ (D : ℤ)) ∧
    ∀ θ : Fin n → ℝ, R θ = ∑ a ∈ c.support,
      c a * Complex.exp (Complex.I * ((∑ i, (a i : ℝ) * θ i : ℝ) : ℂ))

end ApproxDegComp


