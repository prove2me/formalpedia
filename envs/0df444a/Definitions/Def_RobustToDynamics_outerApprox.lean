-- Prove2me | Definitions.Def_RobustToDynamics_outerApprox
-- name    : RobustToDynamics_outerApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:21.802558+00:00
-- url     : https://prove2.me/theorems/a8033384-c96f-4317-96c5-23630fc00784
-- title:
--   The outer approximation $\mathcal S_r=\bigcap_{k=0}^{r}\{x : AG^kx\le b\}$
-- statement:
--   For an integer $r\ge0$,
--   $$
--   \mathcal S_r=\bigcap_{k=0}^{r}\{x\in\mathbb R^n : AG^kx\le b\}.
--   $$
--   So $\mathcal S_0=P$ and $\mathcal S\subseteq\cdots\subseteq\mathcal S_{r+1}\subseteq\mathcal S_r\subseteq\cdots\subseteq\mathcal S_0$. Each $\mathcal S_r$ is a polyhedron; Theorem 2.7 asserts that $\mathcal S=\mathcal S_r$ for a computable $r$.
--
--   **Formalization Note** $r\in\mathbb N$ and $k$ ranges over $0,\dots,r$ inclusive.
-- source:
--   Ahmadi & Günlük, Robust-to-Dynamics Optimization, arXiv:1805.03682v2, §2.1, (2.6), p.8

import Mathlib

open Matrix

namespace RobustToDynamics

/-- **The outer approximation `S_r`.**
Ahmadi & Günlük, *Robust-to-Dynamics Optimization*, arXiv:1805.03682v2, §2.1, (2.6), p.8:
"For an integer r ≥ 0, let Sr := ⋂_{k=0}^{r} {x ∈ Rn| AGk x ≤ b}."

`outerApprox A b G r` is the set of `x` with `A Gᵏ x ≤ b` for `k = 0, 1, …, r`; so `S_0 = P` and
`S ⊆ S_{r+1} ⊆ S_r`.

**Formalization Note.** `ℝⁿ` is `Fin n → ℝ`; `r : ℕ` and `k` ranges over `0, …, r` inclusive. -/
def outerApprox {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ k : ℕ, k ≤ r → (A * G ^ k) *ᵥ x ≤ b}

end RobustToDynamics


