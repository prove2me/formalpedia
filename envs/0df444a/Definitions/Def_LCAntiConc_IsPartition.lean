-- Prove2me | Definitions.Def_LCAntiConc_IsPartition
-- name    : LCAntiConc_IsPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:49:28.038997+00:00
-- url     : https://prove2.me/theorems/07d16b83-5177-4cc5-8db1-cf5cd25c6875
-- title:
--   Definition 3.5 — degree-$s$ partition of a pseudo-expectation
-- statement:
--   Let $s\le D$ be even and let $\tilde{\mathbb E}$ be a degree-$D$ pseudo-expectation satisfying $\{\|v\|^2=1\}$. A **degree-$s$ partition** of $\tilde{\mathbb E}$ is a finite collection $\mathcal C=\{(p_i,\tilde{\mathbb E}_i)\}$ of probabilities $p_i>0$ with $\sum_ip_i=1$ and degree-$(D-s)$ pseudo-expectations $\tilde{\mathbb E}_i$ satisfying $\{\|v\|^2=1\}$ such that
--
--   $$\mathop{\mathbb E}_{\mathcal C}\tilde{\mathbb E}_i f=\sum_i p_i\,\tilde{\mathbb E}_i f=\tilde{\mathbb E}f\qquad\text{for every polynomial }f\text{ with }\deg f\le D-s.\tag{3.2}$$
--
--   Partitions are the pseudo-expectation analogue of conditioning a distribution on a finite partition of the sample space; the conditioning lemmas of the paper produce partitions in which the pieces have small pseudo-variance.
--
--   **Formalization Note** The collection is indexed by a finite type.
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Definition 3.5, (3.2), p.16 (PDF p.18)

import Mathlib
import Definitions.Def_LCAntiConc_IsPseudoExp

namespace LCAntiConc

/-- **Definition 3.5** (partition): for even `s ≤ D` and a degree-`D` pseudo-expectation `Ẽ`, a
degree-`s` partition of `Ẽ` is a finite collection `{(pᵢ, Ẽᵢ)}` of probabilities `pᵢ > 0` with
`∑ᵢ pᵢ = 1` and degree-`(D - s)` pseudo-expectations `Ẽᵢ` satisfying `{‖v‖² = 1}` such that
`𝔼_𝒞 Ẽᵢ f = Ẽ f` for every polynomial `f` with `deg f ≤ D - s` (3.2).

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Definition 3.5, p.16 (PDF p.18).

**Formalization Note** The finite collection is indexed by a `Fintype` `ι`; `𝔼_𝒞 Ẽᵢ f` is
`∑ᵢ pᵢ Ẽᵢ f`. The subtraction `D - s` is taken together with `s ≤ D`. -/
def IsPartition {n : ℕ} (D s : ℕ) (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (Li : ι → MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) : Prop :=
  Even s ∧ s ≤ D ∧ IsPseudoExp D L ∧ (∀ i, 0 < p i) ∧ ∑ i, p i = 1 ∧
    (∀ i, IsPseudoExp (D - s) (Li i)) ∧
    ∀ f : MvPolynomial (Fin n) ℝ, f.totalDegree ≤ D - s → ∑ i, p i * Li i f = L f

end LCAntiConc


