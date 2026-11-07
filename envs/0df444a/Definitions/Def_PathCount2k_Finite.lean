-- Prove2me | Definitions.Def_PathCount2k_Finite
-- name    : PathCount2k_Finite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:45:16.03573+00:00
-- url     : https://prove2.me/theorems/494f5c2b-93fb-4c76-9e75-4c954be27344
-- title:
--   Defs. 2.15–2.16 — the five-point law $\xi$ and the finite estimator $Z_0$, $Y_0$
-- statement:
--   The **finite scalar distribution** $\xi$ takes the values $-2,-1,0,1,2$ with probabilities $\tfrac1{12},\tfrac16,\tfrac12,\tfrac16,\tfrac1{12}$. In one finite trial, for an integer $D\ge1$, every coordinate of $g_v\in\mathbb Z^k$ and every entry of $H_{i,v}\in\mathbb Z^{D\times D}$ is an independent copy of $\xi$, and
--   $$
--   Z_0=\sum_{P\in\mathcal P_k}\Delta_P\,b_0^\top H_{1,v_1}\cdots H_{k,v_k}b_0,\qquad Y_0=\frac{Z_0^2}{k!\,D^{k-1}}.
--   $$
--
--   $\xi$ matches the Gaussian moments up to order four, which lets the algorithm use finitely many random bits.
--
--   **Formalization Note** $\xi$ is a sum of point masses on $\mathbb R$; the integer samples live in the same real sample space as the Gaussian ones. $Z_0$ is defined over any commutative ring ($\mathbb Z$ for the dynamic program, $\mathbb R$ for the moments).
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), Definition 2.15, p.12; Definition 2.16, p.13

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_PathCount2k_Exterior
import Definitions.Def_PathCount2k_Gaussian

open MeasureTheory ProbabilityTheory

namespace PathCount2k

/-- **The finite scalar distribution `ξ`**, Definition 2.15, p.12:
`Pr(ξ = −2) = 1/12`, `Pr(ξ = −1) = 1/6`, `Pr(ξ = 0) = 1/2`, `Pr(ξ = 1) = 1/6`, `Pr(ξ = 2) = 1/12`,
as a probability measure on `ℝ` (a sum of point masses). -/
noncomputable def xiLaw : Measure ℝ :=
  (1 / 12 : NNReal) • Measure.dirac (-2) + (1 / 6 : NNReal) • Measure.dirac (-1) +
    (1 / 2 : NNReal) • Measure.dirac 0 + (1 / 6 : NNReal) • Measure.dirac 1 +
    (1 / 12 : NNReal) • Measure.dirac 2

/-- **The law of one finite trial**, Definition 2.16, p.13: vertex vectors `g_v ∈ ℤ^k` and matrices
`H_{i,v} ∈ ℤ^{D×D}` whose coordinates and entries are "mutually independent copies of `ξ`".

**Formalization Note.** The samples are integers; they are placed in the same real sample space
`VecSample n k × MatSample n k D` as the Gaussian trial, and `xiLaw` is supported on
`{−2, −1, 0, 1, 2}`. -/
noncomputable def finiteLaw (n k D : ℕ) : Measure (VecSample n k × MatSample n k D) :=
  (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin k => xiLaw).prod
    (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin D =>
      Measure.pi fun _ : Fin D => xiLaw)

/-- **The finite sum `Z₀`**, Definition 2.16, p.13:
`Z₀ = ∑_{P ∈ P_k} Δ_P b₀ᵀ H_{1,v₁} ⋯ H_{k,v_k} b₀`, where `P = (v₁, …, v_k)` and `Δ_P` is the
determinant of the sampled vertex vectors in path order. Defined over any commutative ring:
`ℤ` for the dynamic program (Lemma 2.16), `ℝ` for the moments (Lemma 2.14). -/
def Z0 {R : Type*} [CommRing R] (n : ℕ) (E : Finset (Fin n × Fin n)) (k D : ℕ)
    (g : Fin n → Fin k → R) (H : Fin k → Fin n → Fin D → Fin D → R) : R :=
  ∑ P ∈ paths n E k, Delta g P * pathEntry H P

/-- **The finite estimator** `Y₀ = Z₀² / (k! D^{k−1})`, Definition 2.16, p.13: "The output of one
trial is `Y₀`". -/
noncomputable def Y0 (n : ℕ) (E : Finset (Fin n × Fin n)) (k D : ℕ)
    (ω : VecSample n k × MatSample n k D) : ℝ :=
  Z0 n E k D ω.1 ω.2 ^ 2 / ((Nat.factorial k : ℝ) * (D : ℝ) ^ (k - 1))

end PathCount2k


