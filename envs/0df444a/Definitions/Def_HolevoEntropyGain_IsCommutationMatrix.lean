-- Prove2me | Definitions.Def_HolevoEntropyGain_IsCommutationMatrix
-- name    : HolevoEntropyGain_IsCommutationMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:16:13.312083+00:00
-- url     : https://prove2.me/theorems/542607e3-5d3e-4049-8d28-886d8a61bc55
-- title:
--   Commutation matrix $\Delta$ of a coordinate symplectic space
-- statement:
--   Let $s \ge 0$ and $Z = \mathbb R^{2s}$. A **commutation matrix** is a real $2s\times 2s$ matrix $\Delta$ that is skew-symmetric and nondegenerate:
--
--   $$
--   \Delta^\top = -\Delta, \qquad \det \Delta \neq 0 .
--   $$
--
--   The pair $(Z,\Delta)$ is the coordinate symplectic space of a system of $s$ Bosonic modes; $\Delta_{jk}$ is the commutator of the canonical variables $R_j, R_k$ up to the factor $i$. No canonical form is imposed: the canonical matrix (22) of the paper is one instance.
--
--   **Formalization Note** $Z$ is `Fin (2 * s) → ℝ`.
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, p.4 ("coordinate symplectic space (dim Z = 2s) with the nondegenerate skew-symmetric commutation matrix Δ")

import Mathlib

namespace HolevoEntropyGain

/-- The commutation matrix `Δ` of a coordinate symplectic space `(Z, Δ)` with `dim Z = 2s`: a real,
skew-symmetric, nondegenerate `2s × 2s` matrix (Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, p.4, PDF p.4).

**Formalization Note** `Z` is `Fin (2 * s) → ℝ`. No canonical form is imposed; (22) is one instance. -/
def IsCommutationMatrix {s : ℕ} (Δ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ) : Prop :=
  Δ.transpose = -Δ ∧ Δ.det ≠ 0

end HolevoEntropyGain


