-- Prove2me | Definitions.Def_LogRegretOCO_ONS_IsGenProj
-- name    : LogRegretOCO_ONS_IsGenProj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:59:04.540989+00:00
-- url     : https://prove2.me/theorems/c737d76d-8f54-4d92-ae88-f30ccce23538
-- title:
--   Generalized projection $z = \Pi_{\mathcal P}^A(y)$ (minimizer predicate)
-- statement:
--   Let $A$ be a real $n \times n$ matrix, $\mathcal P \subseteq \mathbb R^n$ and $y, z \in \mathbb R^n$. The point $z$ is a **generalized projection of $y$ onto $\mathcal P$ in the norm induced by $A$** if
--   $$
--   z \in \mathcal P \quad\text{and}\quad (y - z)^\top A (y - z) \le (y - w)^\top A (y - w) \ \text{ for all } w \in \mathcal P,
--   $$
--   that is, $z \in \operatorname{argmin}_{x \in \mathcal P} (y - x)^\top A (y - x)$. For $A = I_n$ this is the Euclidean projection. Online Newton Step projects in the norm of the matrix $A_t$.
--
--   **Formalization Note** The projection is a predicate, not a function, so no default value is produced when the minimizer does not exist. When $\mathcal P$ is non-empty, closed and bounded and $A$ is positive definite (the case of Online Newton Step), exactly one such $z$ exists, so a statement for every such $z$ is a statement about $\Pi_{\mathcal P}^A(y)$.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Machine Learning 69 (2007) 169–192, doi:10.1007/s10994-007-5016-8, Fig. 2, p. 176 (PDF p. 8); §4, definition of generalized projections, p. 188 (PDF p. 20)

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_qform

namespace LogRegretOCO.ONS

/-- **Generalized projection `z = Π_P^A(y)` (minimizer predicate).**
Hazan, Agarwal, Kale, *Logarithmic regret algorithms for online convex optimization*,
Machine Learning 69 (2007) 169–192, Fig. 2, p. 176: "Π_P^{A_{t−1}}(y) = argmin_{x∈P} (y − x)ᵀA_{t−1}(y − x)", and §4,
p. 188: "Π_P^A[y] ≜ min_{x∈P} (x − y)ᵀA(x − y)".

`IsGenProj A P y z` says that `z ∈ P` and `z` minimizes `x ↦ (y − x)ᵀA(y − x)` over `P`.

**Formalization Note.** The projection is a predicate, not a function, so no junk value is
produced when the minimizer does not exist. For `P` non-empty, closed and bounded and `A`
positive definite (the case of ONS) the minimizer exists and is unique, so a statement about
every `z` with `IsGenProj A P y z` is a statement about `Π_P^A(y)`. No existence or
uniqueness is asserted here. -/
def IsGenProj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P : Set (EuclideanSpace ℝ (Fin n)))
    (y z : EuclideanSpace ℝ (Fin n)) : Prop :=
  z ∈ P ∧ ∀ w ∈ P, qform A (y - z) ≤ qform A (y - w)

end LogRegretOCO.ONS


