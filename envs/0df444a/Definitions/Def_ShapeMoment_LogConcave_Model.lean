-- Prove2me | Definitions.Def_ShapeMoment_LogConcave_Model
-- name    : ShapeMoment_LogConcave_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:52.840729+00:00
-- url     : https://prove2.me/theorems/b92b5381-950a-4205-b50a-aca2a0f655d1
-- title:
--   Feasible regions of (DMP-LC) and (DMP-LC′)
-- statement:
--   The feasible region of (DMP-LC) is the union over integer supports $[k,\ell]\subseteq[1,n]$ of vectors satisfying
--
--   $$\sum_{j=1}^n j^ix_j=q_i\ (0\le i\le m),\quad x_{j-1}x_{j+1}\le x_j^2\ (k<j<\ell),\quad x_j>0\ (k\le j\le\ell),\quad x_j=0\ (j\notin[k,\ell]).$$
--
--   The primed region uses the same moments, $x_j\ge0$, and $x_{j-u}^v x_{j+v}^u\le x_j^{u+v}$ for $1<j<n$, $1\le u\le j-1$, $1\le v\le n-j$.
--
--   These are the two paper-defined feasible sets. **Formalization Note** A `Fin n` index represents the paper index one greater than its value; the extension `ext` handles one-based arithmetic.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 6, (2b)–(2e), (3b)–(3d)

import Definitions.Def_ShapeMoment_LogConcave_DiscreteMoment

namespace ShapeMoment.LogConcave

/-- Feasible vectors of (DMP-LC), the union over all consecutive positive supports. -/
def feasLC (n m : ℕ) (q : ℕ → ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ k ℓ : ℕ, 1 ≤ k ∧ k ≤ ℓ ∧ ℓ ≤ n ∧
    (∀ i ≤ m, moment x i = q i) ∧
    (∀ j, k < j → j < ℓ → ext x (j - 1) * ext x (j + 1) ≤ ext x j ^ 2) ∧
    (∀ j, k ≤ j → j ≤ ℓ → 0 < ext x j) ∧
    (∀ j : Fin n, ¬ (k ≤ j.val + 1 ∧ j.val + 1 ≤ ℓ) → x j = 0)}

/-- Feasible vectors of the support-free formulation (DMP-LC′). -/
def feasLCPrime (n m : ℕ) (q : ℕ → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i ≤ m, moment x i = q i) ∧
    (∀ j u v : ℕ, 1 < j → j < n → 1 ≤ u → u ≤ j - 1 →
      1 ≤ v → v ≤ n - j →
      ext x (j - u) ^ v * ext x (j + v) ^ u ≤ ext x j ^ (u + v)) ∧
    (∀ j, 0 ≤ x j)}

end ShapeMoment.LogConcave


