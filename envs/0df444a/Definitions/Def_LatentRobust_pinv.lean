-- Prove2me | Definitions.Def_LatentRobust_pinv
-- name    : LatentRobust_pinv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:18:35.775158+00:00
-- url     : https://prove2.me/theorems/3549ec55-bc6a-400b-8ce0-a0722bf906a1
-- title:
--   The Moore–Penrose inverse $A^\dagger$ of a real matrix
-- statement:
--   For a real $m\times n$ matrix $A$, the **Moore–Penrose inverse** $A^\dagger$ is the unique $n\times m$ matrix $X$ with
--   $$
--   AXA=A,\qquad XAX=X,\qquad (AX)^\top=AX,\qquad (XA)^\top=XA .
--   $$
--   Such a matrix exists for every $A$ and is unique.
--
--   The mission uses $\Sigma^\dagger$ for $\Sigma=WW^\top$, which is singular whenever the weight matrix $W\in\mathbb R^{d\times k}$ has $k<d$; $\Sigma^\dagger$ appears in the Bayes-optimal classifier of the Gaussian mixture model and in its boundary-risk bounds.
--
--   **Formalization Note** Mathlib has no matrix pseudo-inverse. The module defines the predicate "satisfies the four Penrose conditions" and takes $A^\dagger$ to be a matrix satisfying it, chosen by `Classical.epsilon`; by existence and uniqueness this is the Moore–Penrose inverse, not a junk value.
-- source:
--   Javanmard, Mehrabi, Adversarial robustness for latent models: Revisiting the robust-standard accuracies tradeoff, arXiv:2110.11950v2, §1.1 Notation, p.4 ("W† stand for the Moore–Penrose inverse")

import Mathlib

namespace LatentRobust

/-- `X` satisfies the four Penrose conditions for `A`: `AXA = A`, `XAX = X`, `(AX)ᵀ = AX`,
`(XA)ᵀ = XA`. Exactly one real matrix satisfies them (the Moore–Penrose inverse). -/
def IsMoorePenrose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (X : Matrix (Fin n) (Fin m) ℝ) :
    Prop :=
  A * X * A = A ∧ X * A * X = X ∧ (A * X).transpose = A * X ∧ (X * A).transpose = X * A

/-- The Moore–Penrose inverse `A†` of a real matrix (Javanmard, Mehrabi, arXiv:2110.11950v2,
§1.1 Notation, p.4: "`W†` stand for the Moore–Penrose inverse").

**Formalization Note** Mathlib has no matrix pseudo-inverse, so `A†` is chosen by
`Classical.epsilon` among the matrices satisfying the four Penrose conditions
(`IsMoorePenrose`). Such a matrix exists and is unique for every real matrix, so this is the
paper's `A†` and not a junk value. Mathlib's `Matrix.inv` (which is `0` on singular matrices)
is not used: `Σ = WWᵀ` is singular whenever `k < d`. -/
noncomputable def pinv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  Classical.epsilon (IsMoorePenrose A)

end LatentRobust


