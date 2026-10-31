-- Prove2me | Definitions.Def_QKPSDP_symOf
-- name    : QKPSDP_symOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:48.73093+00:00
-- url     : https://prove2.me/theorems/cd8ef433-418b-47ad-b48a-4fcb02b7ba5e
-- title:
--   Upper-triangular coordinates of $\mathbb S^n$
-- statement:
--   A vector $u = (u_{ij})_{i\le j} \in \mathbb R^{n(n+1)/2}$ determines the symmetric matrix $C = \operatorname{symOf}(u)$ with
--
--   $$
--   C_{ij} = u_{\min(i,j),\,\max(i,j)} .
--   $$
--
--   This linear bijection $\mathbb R^{n(n+1)/2} \to \mathbb S^n$ is the coordinate system in which "for a generic $C \in \mathbb S^n$" is read: a property holds for generic $C$ if it holds for $\operatorname{symOf}(u)$ for Lebesgue-almost every $u$ (the proof of Lemma 4.10(i) shows the exceptional $C$ form "a set of measure zero", with $\dim(\mathbb S^n) = n(n+1)/2$).
-- source:
--   Tang & Toh, A feasible method for solving an SDP relaxation of the quadratic knapsack problem, arXiv:2303.06599v1, Lemma 4.10(i), p.16, and its proof, p.17

import Mathlib

namespace QKPSDP

/-- Tang & Toh, arXiv:2303.06599v1, Lemma 4.10(i), p.16, and its proof, p.17 ("`C ∈ Sⁿ` is
contained in a set of measure zero"; `dim(Sⁿ) = n(n+1)/2`): the coordinates in which "generic
`C ∈ Sⁿ`" is measured. A vector `u` of upper-triangular entries `u_{ij}` (`i ≤ j`) determines the
symmetric matrix `symOf u` with `(symOf u)_{ij} = u_{min(i,j), max(i,j)}`.

**Formalization Note** `u ↦ symOf u` is a linear bijection from `ℝ^{n(n+1)/2}` (indexed by the
pairs `i ≤ j`) onto `Sⁿ`. "For a generic `C ∈ Sⁿ`, P(C)" is encoded as
`∀ᵐ u ∂volume, P (symOf u)`, i.e. `P` holds outside a Lebesgue-null subset of `Sⁿ` in these
coordinates. Lebesgue measure on the `n²` entries of `Matrix (Fin n) (Fin n) ℝ` would be the wrong
space: `Sⁿ` is null there. -/
def symOf {n : ℕ} (u : {p : Fin n × Fin n // p.1 ≤ p.2} → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => u ⟨(min i j, max i j), min_le_max⟩

end QKPSDP


