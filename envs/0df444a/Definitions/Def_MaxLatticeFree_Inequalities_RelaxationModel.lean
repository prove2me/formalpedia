-- Prove2me | Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
-- name    : MaxLatticeFree_Inequalities_RelaxationModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:32:33.846446+00:00
-- url     : https://prove2.me/theorems/773d9c0c-bb37-4f13-b8ff-55352794d89c
-- title:
--   The semi-infinite relaxation $R_f(W)$, the affine hull $V$ and the space $\mathcal V$
-- statement:
--   Fix $q\ge 0$, a point $f\in\mathbb R^q$ and a linear subspace $W\subseteq\mathbb R^q$. This file sets up the model of Section 1 of Basu, Conforti, Cornuéjols and Zambelli.
--
--   1. The **integral points** $\mathbb Z^q$ are the vectors of $\mathbb R^q$ all of whose coordinates are integers.
--   2. The affine space $f+W=\{x\in\mathbb R^q \mid x-f\in W\}$.
--   3. $V$ is the **affine hull of the integral points of $f+W$**, $V=\operatorname{aff}\big((f+W)\cap\mathbb Z^q\big)$.
--   4. For sets $A,S\subseteq\mathbb R^q$, the **interior of $S$ relative to $A$** is $\operatorname{int}_A(S)=\{x\in S \mid B_\varepsilon(x)\cap A\subseteq S \text{ for some } \varepsilon>0\}$, where $B_\varepsilon(x)$ is the open Euclidean ball. For $S\subseteq A$ it is the interior of $S$ in the topology induced on $A$ by $\mathbb R^q$.
--   5. $\mathcal W$ is the space of real functions $s=(s_r)_{r\in W}$ on $W$ with finite support. For $s\in\mathcal W$ write $\sum_{r\in W} r s_r\in\mathbb R^q$, and for a function $\psi:W\to\mathbb R$ write
--   $$\Psi(s)=\sum_{r\in W}\psi(r)s_r .$$
--   6. The relaxation
--   $$R_f(W)=\Big\{s\in\mathcal W \ \Big|\ f+\sum_{r\in W} r s_r\in\mathbb Z^q,\ \ s_r\ge 0 \text{ for all } r\in W\Big\}.$$
--   7. $\mathcal V=\{s\in\mathcal W \mid f+\sum_{r\in W} r s_r\in V\}$, an affine subspace of $\mathcal W$ containing $R_f(W)$.
--
--   $R_f(W)$ is Gomory's corner relaxation with the integrality of the nonbasic variables dropped and one variable for every direction $r\in W$; its valid linear inequalities are the object of Theorem 3.
--
--   **Formalization Note** $\mathbb R^q$ is `EuclideanSpace ℝ (Fin q)`, $W$ a `Submodule`, and $\mathcal W$ is `W →₀ ℝ` (finitely supported functions). The page says "finite support, i.e. the set $\{r\in W\mid s_r>0\}$ has finite cardinality"; read literally this allows infinitely many negative entries, for which $\sum_r r s_r$ is undefined, so the usual meaning is taken. Every set in which it matters also requires $s\ge 0$.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 4, eq. (2); p. 5 (definition of V and 𝒱); p. 8 (interior relative to an affine space); p. 15, eq. (8)

import Mathlib

namespace MaxLatticeFree.Inequalities

/-- The integral points `ℤ^q` of `ℝ^q = EuclideanSpace ℝ (Fin q)`: every coordinate is an integer. -/
noncomputable def integralPoints (q : ℕ) : Set (EuclideanSpace ℝ (Fin q)) :=
  {x | ∀ i, ∃ z : ℤ, x.ofLp i = (z : ℝ)}

/-- The affine space `f + W = {x ∈ ℝ^q | x - f ∈ W}` (arXiv:1701.06543v1, p. 4). -/
noncomputable def affSpace {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) :
    Set (EuclideanSpace ℝ (Fin q)) :=
  {x | x - f ∈ W}

/-- `V`, the affine hull of `(f + W) ∩ ℤ^q` (arXiv:1701.06543v1, p. 4). -/
noncomputable def affHullInt {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) :
    AffineSubspace ℝ (EuclideanSpace ℝ (Fin q)) :=
  affineSpan ℝ (affSpace f W ∩ integralPoints q)

/-- Interior of `S` relative to a set `A` (arXiv:1701.06543v1, p. 8): the points `x ∈ S` such that
`B_ε(x) ∩ A ⊆ S` for some `ε > 0`, `B_ε(x)` the open Euclidean ball. For `S ⊆ A` this is the
interior of `S` in the topology induced on `A` by `ℝ^q`. -/
noncomputable def intRel {q : ℕ} (A S : Set (EuclideanSpace ℝ (Fin q))) : Set (EuclideanSpace ℝ (Fin q)) :=
  {x | x ∈ S ∧ ∃ ε : ℝ, 0 < ε ∧ Metric.ball x ε ∩ A ⊆ S}

/-- For a finitely supported `s ∈ 𝒲` (`s : W →₀ ℝ`), the vector `∑_{r ∈ W} r s_r ∈ ℝ^q`. -/
noncomputable def combo {q : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (s : W →₀ ℝ) :
    EuclideanSpace ℝ (Fin q) :=
  s.sum (fun r c => c • (r : EuclideanSpace ℝ (Fin q)))

/-- The linear function `Ψ(s) = ∑_{r ∈ W} ψ(r) s_r` on `𝒲` defined by `ψ : W → ℝ`
(arXiv:1701.06543v1, p. 15, eq. (8)). -/
noncomputable def linVal {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (ψ : W → ℝ)
    (s : W →₀ ℝ) : ℝ :=
  s.sum (fun r c => ψ r * c)

/-- `R_f(W)` (arXiv:1701.06543v1, p. 4, (2)): the finitely supported `s ∈ 𝒲` with
`f + ∑_{r ∈ W} r s_r ∈ ℤ^q` and `s_r ≥ 0` for all `r ∈ W`. -/
noncomputable def Rf {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) :
    Set (W →₀ ℝ) :=
  {s | f + combo W s ∈ integralPoints q ∧ ∀ r, 0 ≤ s r}

/-- `𝒱 = {s ∈ 𝒲 | f + ∑_{r ∈ W} r s_r ∈ V}` (arXiv:1701.06543v1, p. 5). -/
noncomputable def calV {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) :
    Set (W →₀ ℝ) :=
  {s | f + combo W s ∈ affHullInt f W}

end MaxLatticeFree.Inequalities


