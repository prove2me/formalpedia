-- Prove2me | Definitions.Def_LinExchangeSP_ZPlus_Setting
-- name    : LinExchangeSP_ZPlus_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:00.690371+00:00
-- url     : https://prove2.me/theorems/7e07a76e-1511-4917-8a6e-41c5bbe82c1b
-- title:
--   Definition 6.3, §6.2, Theorem 6.4, §7 — Z₊-matrices, M₂ matrices, the polyhedron P_M, its scaling, ℓ, B and λ
-- statement:
--   This module fixes the objects of Theorem 6.4 of Garg and Végh. Throughout, $k, t, m \ge 0$ are integers, matrices are rational, and vectors $x$ live in $\mathbb{R}^t$.
--
--   1. **$Z_+$-matrices** (Definition 6.3, p. 15). A matrix $M \in \mathbb{Q}^{k\times t}$ is a *$Z_+$-matrix*, written $M \in \mathcal{Z}_+(k,t)$, if all its off-diagonal entries are nonpositive and all its column sums are nonnegative:
--   $$M_{ij} \le 0 \ \ (i \ne j), \qquad \sum_{i=1}^k M_{ij} \ge 0 \ \ (j \in [t]).$$
--   For a non-square matrix the diagonal entries are the $M_{ii}$ with $1 \le i \le \min\{k,t\}$.
--
--   2. **Monotone two-variable-per-inequality matrices** (§6.2, p. 14). $\mathcal{M}_2(m,t)$ is the set of $m\times t$ rational matrices with at most one positive and at most one negative entry in every row. A system $Ax \le b$ with $A \in \mathcal{M}_2(m,t)$ is an *M2VPI system*.
--
--   3. **Polyhedra.** For a rational system $A \in \mathbb{Q}^{m\times t}$, $b \in \mathbb{Q}^m$,
--   $$P(A,b) = \{x \in \mathbb{R}^t : Ax \le b,\ x \ge 0\};$$
--   for a $Z_+$-matrix $M$ this is the polyhedron $P_M$ of Theorem 6.4.
--
--   4. **Scaling** (p. 15). $\alpha P = \{\alpha x : x \in P\}$ for a set $P \subseteq \mathbb{R}^t$ and $\alpha > 0$.
--
--   5. **The number of nonzero entries** $\ell$ of $M$.
--
--   6. **The constant** $B = \sum_{j=1}^k b_j \big/ \min_{i\in[k]} b_i$ of Theorem 6.4, defined for $k \ge 1$.
--
--   7. **The vector $\lambda$** (§7, p. 16): $\lambda_i = \sum_{j \ne i} \gamma_j$ for $\gamma \in \mathbb{Q}^t$.
--
--   These are the vocabulary of Theorem 6.4 and of Lemma 7.1.
--
--   **Formalization Note** Indices are 0-based (`Fin k`, `Fin t`); a diagonal entry is one whose row and column indices agree as natural numbers, which is exactly $1 \le i \le \min\{k,t\}$ after the shift. The row value $A_r x = \sum_j A_{rj} x_j$ is computed in $\mathbb{R}$ with the rational entries cast. $B$ takes a proof of $k \ge 1$, because the minimum over $[k]$ is only defined for nonempty $[k]$.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 14 (§6.2, M₂(m, n)), p. 15 (Definition 6.3, Theorem 6.4, notation αP), p. 16 (§7, λ)

import Mathlib

namespace LinExchangeSP.ZPlus

open Matrix

/-- Definition 6.3 (p. 15): `M ∈ Z₊(k, t)`. All off-diagonal entries are nonpositive and all column
sums are nonnegative. Diagonal entries are those `z_ii` with `1 ≤ i ≤ min{k, t}`, i.e. those whose row
and column indices agree as natural numbers (0-based here). -/
def IsZPlus {k t : ℕ} (M : Matrix (Fin k) (Fin t) ℚ) : Prop :=
  (∀ (i : Fin k) (j : Fin t), (i : ℕ) ≠ (j : ℕ) → M i j ≤ 0) ∧ ∀ j, 0 ≤ ∑ i, M i j

/-- `A ∈ M₂(m, t)` (§6.2, p. 14): a rational matrix with at most one positive and at most one
negative entry in every row. -/
def IsM2 {m t : ℕ} (A : Matrix (Fin m) (Fin t) ℚ) : Prop :=
  ∀ r, (∀ j j', 0 < A r j → 0 < A r j' → j = j') ∧ (∀ j j', A r j < 0 → A r j' < 0 → j = j')

/-- The value `A_r x = ∑ⱼ A_rj xⱼ` of the `r`-th row of a rational matrix at a real vector `x`. -/
noncomputable def rowVal {m t : ℕ} (A : Matrix (Fin m) (Fin t) ℚ) (x : Fin t → ℝ) (r : Fin m) : ℝ :=
  ∑ j, (A r j : ℝ) * x j

/-- The polyhedron `{x ∈ ℝᵗ : Ax ≤ b, x ≥ 0}` of a rational system `Ax ≤ b`. -/
def polyhedron {m t : ℕ} (A : Matrix (Fin m) (Fin t) ℚ) (b : Fin m → ℚ) : Set (Fin t → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ ∀ r, rowVal A x r ≤ (b r : ℝ)}

/-- `αP = {αx : x ∈ P}` (p. 15). -/
def scale {t : ℕ} (α : ℝ) (P : Set (Fin t → ℝ)) : Set (Fin t → ℝ) :=
  (fun x => α • x) '' P

/-- `ℓ`, the number of nonzero entries of `M`. -/
def nnz {k t : ℕ} (M : Matrix (Fin k) (Fin t) ℚ) : ℕ :=
  (Finset.univ.filter (fun e : Fin k × Fin t => M e.1 e.2 ≠ 0)).card

/-- `B = (∑ⱼ bⱼ) / minᵢ bᵢ` (Theorem 6.4, p. 15; §7, p. 16), defined for `k ≥ 1`. -/
noncomputable def Bconst {k : ℕ} (b : Fin k → ℚ) (hk : 0 < k) : ℝ :=
  (∑ j, (b j : ℝ)) / (Finset.univ.inf' ⟨⟨0, hk⟩, Finset.mem_univ _⟩ (fun i => (b i : ℝ)))

/-- `λᵢ := ∑_{j ≠ i} γⱼ` (§7, p. 16). -/
def lam {t : ℕ} (γ : Fin t → ℚ) (i : Fin t) : ℚ :=
  ∑ j ∈ Finset.univ.erase i, γ j

end LinExchangeSP.ZPlus


