-- Prove2me | Definitions.Def_LCAntiConc_IsInducedBy
-- name    : LCAntiConc_IsInducedBy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:48:18.733201+00:00
-- url     : https://prove2.me/theorems/345f9866-39d8-4477-8a27-1f732a4fdcd8
-- title:
--   Partition induced by sums of squares
-- statement:
--   Let $\tilde{\mathbb E}$ be a degree-$D$ pseudo-expectation on the sphere and $s$ even. Let $(r_j)_{j\in J}$ be a finite family of sums of squares, each of degree at most $s$, whose sum equals $1$ modulo the sphere constraint: $\sum_j r_j-1=(\|v\|_2^2-1)h$. The **partition induced by $(r_j)$** consists of the indices $j$ with $\tilde{\mathbb E}r_j>0$, the weights $p_j=\tilde{\mathbb E}r_j$, and the reweighted pseudo-expectations
--
--   $$\tilde{\mathbb E}_j f=\frac{\tilde{\mathbb E}(r_jf)}{\tilde{\mathbb E}r_j}.\tag{3.3}$$
--
--   A partition $\{(p_i,\tilde{\mathbb E}_i)\}_{i\in I}$ is **induced by** $(r_j)$ if it is this partition, with its indices enumerated by an injection $I\to J$ onto $\{j:\tilde{\mathbb E}r_j>0\}$.
--
--   **Formalization Note** "Sum of squares of degree at most $s$" is a finite sum of squares each of degree at most $s$. The multiple $(\|v\|_2^2-1)h$ is required to have degree at most $s$; this is automatic, because $\|v\|_2^2$ is the top-degree part of $\|v\|_2^2-1$. Formula (3.3) is required on polynomials of degree at most $D-s$, the domain of the reweighted pseudo-expectations.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), "Partitions induced by sums of squares", (3.3), p.16 (PDF p.18)

import Mathlib
import Definitions.Def_LCAntiConc_sphereConstraint

namespace LCAntiConc

/-- A partition `{(pᵢ, Ẽᵢ)}_{i ∈ ι}` of a degree-`D` pseudo-expectation `Ẽ` is induced by a finite
family `(r_j)_{j ∈ ι'}` of sums of squares, each of degree at most `s`, whose sum equals `1`
modulo the sphere constraint: the partition consists of the indices `j` with `Ẽ r_j > 0`
(enumerated by an injection `e : ι → ι'`), with weights `pᵢ = Ẽ r_{e i}` and the reweighted
pseudo-expectations `Ẽᵢ f = Ẽ(r_{e i} f) / Ẽ r_{e i}` (3.3).

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), "Partitions induced by sums of squares",
(3.3), p.16 (PDF p.18).

**Formalization Note** "Sum of squares of degree at most `s`" is a finite sum of squares each of
degree at most `s`. "Sum equals `1` modulo the sphere constraint" is
`∑ⱼ r_j - 1 = (‖v‖₂² - 1) h` with `(‖v‖₂² - 1) h` of degree at most `s`; the degree bound is
automatic, because `‖v‖₂²` is the top form of `‖v‖₂² - 1`. The formula for `Ẽᵢ` is required on
polynomials of degree at most `D - s`, the domain of a degree-`(D - s)` pseudo-expectation. -/
def IsInducedBy {n : ℕ} (D s : ℕ) (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) {ι ι' : Type*}
    [Fintype ι] [Fintype ι'] (p : ι → ℝ) (Li : ι → MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ)
    (r : ι' → MvPolynomial (Fin n) ℝ) (e : ι → ι') : Prop :=
  (∀ j, ∃ (m : ℕ) (g : Fin m → MvPolynomial (Fin n) ℝ),
      r j = ∑ l, g l ^ 2 ∧ ∀ l, (g l ^ 2).totalDegree ≤ s) ∧
    (∃ h : MvPolynomial (Fin n) ℝ, ∑ j, r j - 1 = sphereConstraint n * h ∧
      (sphereConstraint n * h).totalDegree ≤ s) ∧
    Function.Injective e ∧ Set.range e = {j | 0 < L (r j)} ∧
    (∀ i, p i = L (r (e i))) ∧
    ∀ i, ∀ f : MvPolynomial (Fin n) ℝ, f.totalDegree ≤ D - s →
      Li i f = L (r (e i) * f) / L (r (e i))

end LCAntiConc


