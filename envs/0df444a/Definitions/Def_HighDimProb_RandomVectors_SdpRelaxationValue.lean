-- Prove2me | Definitions.Def_HighDimProb_RandomVectors_SdpRelaxationValue
-- name    : HighDimProb_RandomVectors_SdpRelaxationValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T06:40:49.806115+00:00
-- url     : https://prove2.me/theorems/6b0302a9-6b50-498e-84c2-438ec85f2cc4
-- title:
--   SDP(A) — the semidefinite relaxation (3.21)
-- statement:
--   This definition is $\mathrm{SDP}(A)$, the maximum value of the semidefinite relaxation
--   (3.21) of the integer optimization problem (3.20), which Theorem 3.5.6 shows approximates
--   $\mathrm{INT}(A)$ (the companion definition `IntegerCutValue`) to within a constant factor.
--
--   For an $n \times n$ real matrix $A = (A_{ij})$,
--
--   $$
--   \mathrm{SDP}(A) \;:=\; \sup\Bigl\{ \sum_{i,j=1}^n A_{ij}\, \langle X_i, X_j\rangle \;:\;
--   X_1,\dots,X_n \in \mathbb R^n,\ \|X_i\|_2 = 1 \text{ for } i = 1,\dots,n \Bigr\},
--   $$
--
--   the higher-dimensional relaxation of (3.20) that replaces each sign $x_i \in \{-1,1\}$ by a
--   unit vector $X_i \in \mathbb R^n$. As the book notes (Exercise 3.5.5), this optimization is
--   equivalent to a semidefinite program over the Gram matrix $X = (\langle X_i, X_j\rangle)$,
--   which is why it is computationally tractable in a way (3.20) is not.
--
--   **Formalization Note** The value is defined as `sSup` of the set of attainable objective
--   values rather than a claimed maximum: the feasible set (a product of unit spheres) is
--   compact, so a maximum is in fact attained, but the definition itself asserts only that the
--   value is the supremum, and commits to nothing about attainment. The set is always nonempty
--   (any unit vectors are feasible) and bounded above by $\sum_{i,j} |A_{ij}|$ (since
--   $|\langle X_i, X_j \rangle| \le 1$ by Cauchy-Schwarz), so `sSup` here is never the vacuous
--   or unbounded-above junk value.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Eq. (3.21), p. 65 (PDF p. 73)

import Mathlib

namespace HighDimProb.RandomVectors

/-- `SDP(A)`, the maximum of the semidefinite relaxation (3.21). Vershynin,
*High-Dimensional Probability* (2018), p. 65, Eq. (3.21):

`maximize ∑ᵢⱼ Aᵢⱼ ⟨Xᵢ, Xⱼ⟩ : ‖Xᵢ‖₂ = 1 for i = 1, …, n`,

taken over unit vectors `X₁, …, Xₙ ∈ ℝⁿ`. The value is the supremum of the (nonempty, bounded
above by `∑ᵢⱼ |Aᵢⱼ|` since `|⟨Xᵢ, Xⱼ⟩| ≤ 1`) set of attainable objective values, rather than a
claimed maximum, so the definition itself commits to nothing about whether the supremum is
attained. -/
noncomputable def sdpRelaxationValue {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {v : ℝ | ∃ X : Fin n → EuclideanSpace ℝ (Fin n), (∀ i, ‖X i‖ = 1) ∧
    v = ∑ i, ∑ j, A i j * inner ℝ (X i) (X j)}

end HighDimProb.RandomVectors


