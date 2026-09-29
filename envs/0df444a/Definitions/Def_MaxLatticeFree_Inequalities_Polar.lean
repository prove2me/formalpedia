-- Prove2me | Definitions.Def_MaxLatticeFree_Inequalities_Polar
-- name    : MaxLatticeFree_Inequalities_Polar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:56:46.630818+00:00
-- url     : https://prove2.me/theorems/31ff29ba-2be5-49b5-95b1-281e1b2adfc5
-- title:
--   The polar $K^*$, the set $\hat K$, the function $\rho_K$ and $\psi_B$
-- statement:
--   Let $W\subseteq\mathbb R^q$ be a linear subspace and $K\subseteq\mathbb R^q$ (in use, a closed convex subset of $W$ with the origin in its interior relative to $W$). Products $ry$ are standard inner products.
--
--   1. The **polar** of $K$ in $W$ is $K^*=\{y\in W\mid ry\le1 \text{ for all } r\in K\}$.
--   2. $\hat K=\{y\in K^*\mid \exists x\in K \text{ such that } xy=1\}$.
--   3. For $r\in W$,
--   $$\rho_K(r)=\sup_{y\in\hat K} ry .$$
--   4. For $f\in\mathbb R^q$ and $B\subseteq\mathbb R^q$, $\psi_B:W\to\mathbb R$ is $\psi_B=\rho_{B-f}$, where $B-f=\{x-f\mid x\in B\}$.
--
--   For a maximal lattice-free convex set $B$ with $f$ in its interior, $\psi_B$ is the coefficient function of the inequality $\sum_{r\in W}\psi_B(r)s_r\ge1$ of Theorem 3, and by Theorem 28 $\rho_K$ is the smallest sublinear function whose $1$-sublevel set is $K$.
--
--   **Formalization Note** The paper defines $\psi_B(r)=\max_{i}a_ir$ (eq. (4)) from a description $B=\{x\in f+W\mid a_i(x-f)\le1,\ i=1,\dots,t\}$. That value depends on the description when some row is not tight (see Remark 29), so $\psi_B$ is defined intrinsically as $\rho_{B-f}$; by Remark 29 it equals $\max_i a_ir$ for every description whose rows are tight. $\rho_K$ is a real supremum: when $0$ is in the interior of $K$ relative to $W$, $K^*$ is bounded, so the supremum is finite; $\hat K=\emptyset$ happens only for $K=W$, where the convention $\sup\emptyset=0$ gives the correct value $\rho_W=0$.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 18, eqs. (9), (10); p. 4, eq. (4)

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel

open scoped RealInnerProductSpace

namespace MaxLatticeFree.Inequalities

variable {q : ℕ}

/-- The polar of `K` inside `W` (arXiv:1701.06543v1, p. 18): `K* = {y ∈ W | r y ≤ 1 ∀ r ∈ K}`,
`r y` the standard inner product. -/
noncomputable def polarW (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (K : Set (EuclideanSpace ℝ (Fin q))) :
    Set (EuclideanSpace ℝ (Fin q)) :=
  {y | y ∈ W ∧ ∀ r ∈ K, ⟪r, y⟫ ≤ 1}

/-- `K̂ = {y ∈ K* | ∃ x ∈ K, x y = 1}` (arXiv:1701.06543v1, p. 18, eq. (9)). -/
noncomputable def Khat (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (K : Set (EuclideanSpace ℝ (Fin q))) :
    Set (EuclideanSpace ℝ (Fin q)) :=
  {y | y ∈ polarW W K ∧ ∃ x ∈ K, ⟪x, y⟫ = 1}

/-- `ρ_K(r) = sup_{y ∈ K̂} r y` for `r ∈ W` (arXiv:1701.06543v1, p. 18, eq. (10)). Real `sSup`:
for `K` with `0` in its interior relative to `W`, `K̂ ⊆ K*` is bounded; `K̂ = ∅` only for `K = W`,
where `sSup ∅ = 0` is the paper's `ρ_W = 0`. -/
noncomputable def rhoK (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (K : Set (EuclideanSpace ℝ (Fin q))) : W → ℝ :=
  fun r => sSup ((fun y => ⟪(r : EuclideanSpace ℝ (Fin q)), y⟫) '' Khat W K)

/-- `ψ_B := ρ_{B - f}` (arXiv:1701.06543v1, p. 4, eq. (4), in the representation-free form of
p. 18, eq. (10); equal to `max_i a_i r` for every description `B = {x ∈ f + W | a_i (x - f) ≤ 1}`
with tight rows, by Remark 29). -/
noncomputable def psiB (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (B : Set (EuclideanSpace ℝ (Fin q))) : W → ℝ :=
  rhoK W ((fun x => x - f) '' B)

end MaxLatticeFree.Inequalities


