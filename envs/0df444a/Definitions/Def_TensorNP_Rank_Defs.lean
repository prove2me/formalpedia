-- Prove2me | Definitions.Def_TensorNP_Rank_Defs
-- name    : TensorNP_Rank_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:14.36282+00:00
-- url     : https://prove2.me/theorems/d09d2421-01f4-4074-b99d-2d713fe190c5
-- title:
--   (6), p. 0:10 and p. 0:11 — outer product and the rank of a 3-tensor over a field
-- statement:
--   Let $E$ be a field and $l, m, n \in \mathbb N$. A **3-tensor** over $E$ is an array $\mathcal A = [\![a_{ijk}]\!] \in E^{l\times m\times n}$.
--
--   1. The **outer product** of $\mathbf x \in E^l$, $\mathbf y \in E^m$, $\mathbf z \in E^n$ is the tensor $\mathbf x\otimes\mathbf y\otimes\mathbf z$ with entries $a_{ijk} = x_i y_j z_k$.
--   2. The **rank of $\mathcal A$ over $E$** is
--   $$
--   \operatorname{rank}_E(\mathcal A) = \min\Big\{ r \in \mathbb N : \mathcal A = \sum_{s=1}^{r} \lambda_s\, \mathbf x_s\otimes\mathbf y_s\otimes\mathbf z_s \ \text{ for some } \lambda_s\in E,\ \mathbf x_s\in E^l,\ \mathbf y_s\in E^m,\ \mathbf z_s\in E^n \Big\}.
--   $$
--
--   The set over which the minimum is taken is never empty: $r = lmn$ works, using one term per entry. For a subfield $F \subseteq E$ and a tensor $\mathcal A \in F^{l\times m\times n}$, the rank of $\mathcal A$ over $E$ is obtained by regarding the entries of $\mathcal A$ as elements of $E$; so $\operatorname{rank}_{\mathbb Q}(\mathcal A)$ allows only rational $\lambda_s, \mathbf x_s, \mathbf y_s, \mathbf z_s$, while $\operatorname{rank}_{\mathbb R}(\mathcal A)$ allows real ones.
--
--   This is the notion of tensor rank (Hitchcock) used throughout the paper; the point of the mission is that it depends on the field.
--
--   **Formalization Note** Tensors are functions `Fin l → Fin m → Fin n → E`, so indices are 0-based: the paper's $a_{ijk}$ is `A (i-1) (j-1) (k-1)`. The paper calls a *nonzero* outer product rank-1; the definition allows zero summands (and arbitrary $\lambda_s$), which gives the same minimum, since zero summands can be dropped and $\lambda_s$ absorbed. The minimum is Lean's `sInf` on `ℕ`, which is a true minimum because the set is nonempty. The rank over an extension field is `rankOver E` applied to the entrywise cast of the tensor.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:10, §1.7, (6); p. 0:11, rank of A over E

import Mathlib

namespace TensorNP.Rank

/-- The outer product `x ⊗ y ⊗ z` of `x ∈ F^l`, `y ∈ F^m`, `z ∈ F^n` (Hillar–Lim §1.7, p. 0:10):
the `l × m × n` array with entries `a_{ijk} = x_i y_j z_k`. Indices are 0-based: the paper's
`a_{ijk}` is `outer x y z (i-1) (j-1) (k-1)`. -/
def outer {F : Type*} [Mul F] {l m n : ℕ} (x : Fin l → F) (y : Fin m → F) (z : Fin n → F) :
    Fin l → Fin m → Fin n → F :=
  fun i j k => x i * y j * z k

/-- The rank of a 3-tensor `A ∈ E^{l×m×n}` over the field `E`, display (6) of Hillar–Lim
(p. 0:10): the least `r` such that `A = ∑_{s=1}^r λ_s x_s ⊗ y_s ⊗ z_s` with `λ_s ∈ E`,
`x_s ∈ E^l`, `y_s ∈ E^m`, `z_s ∈ E^n`. The set of such `r` is never empty (`r = l·m·n` works,
using the standard basis), so `sInf` is a genuine minimum. Zero summands are allowed, which does
not change the minimum (drop them), so this agrees with the paper's "minimal number of rank-1
(nonzero) summands". For a subfield `F ⊆ E` and `A ∈ F^{l×m×n}`, the paper's `rank_E(A)` (p. 0:11)
is `rankOver E` applied to `A` with its entries cast into `E`. -/
noncomputable def rankOver (E : Type*) [Field E] {l m n : ℕ} (A : Fin l → Fin m → Fin n → E) : ℕ :=
  sInf {r : ℕ | ∃ (lam : Fin r → E) (x : Fin r → Fin l → E) (y : Fin r → Fin m → E)
    (z : Fin r → Fin n → E), A = ∑ s, lam s • outer (x s) (y s) (z s)}

end TensorNP.Rank


