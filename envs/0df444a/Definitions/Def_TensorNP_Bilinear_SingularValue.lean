-- Prove2me | Definitions.Def_TensorNP_Bilinear_SingularValue
-- name    : TensorNP_Bilinear_SingularValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:09:20.906812+00:00
-- url     : https://prove2.me/theorems/1cca998a-c9d7-4ecc-81ed-814c8bb24f91
-- title:
--   Definition 6.1 — $\ell^2$- and $\ell^3$-singular values of a 3-tensor
-- statement:
--   Fix a field $F$ ($\mathbb R$ or $\mathbb C$ in the paper) and a tensor $\mathcal A = [\![a_{ijk}]\!] \in F^{l\times m\times n}$. A number $\sigma \in F$ is an **$\ell^2$-singular value** of $\mathcal A$ if there are nonzero $\mathbf u \in F^l$, $\mathbf v \in F^m$, $\mathbf w \in F^n$ (the $\ell^2$-singular vectors) with
--   $$
--   \sum_{j,k} a_{ijk} v_j w_k = \sigma u_i,\qquad \sum_{i,k} a_{ijk} u_i w_k = \sigma v_j,\qquad \sum_{i,j} a_{ijk} u_i v_j = \sigma w_k \tag{20}
--   $$
--   for all $i, j, k$. It is an **$\ell^3$-singular value** if the same holds with right-hand sides $\sigma u_i^2$, $\sigma v_j^2$, $\sigma w_k^2$ (equations (21)).
--
--   The file also defines the languages of codes of rational tensors for which $\sigma = 0$ is an $\ell^2$-singular value over $F$, and for which it is an $\ell^3$-singular value over $F$, with the tensor code of the definition `TensorNP.Bilinear.Encoding`.
--
--   At $\sigma = 0$ both systems are the system (9) of tensor bilinear feasibility; Theorem 6.2 rests on that.
--
--   **Formalization Note** Over $\mathbb C$ the equations are taken literally as printed, without complex conjugates. The vectors are not normalized: (20) and (21) are as printed, and only $\sigma = 0$ is used in this mission, where the equations are scale-free.
-- source:
--   Hillar & Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), Art. 45 (final version, arXiv:0911.1393v5), p. 0:21, Definition 6.1, (20), (21)

import Mathlib
import Definitions.Def_TensorNP_Bilinear_Encoding

namespace TensorNP.Bilinear

open CookPvsNP ProjSchedTW.Complexity

/-! # ℓ²- and ℓ³-singular values of a 3-tensor (Hillar–Lim, Definition 6.1, p. 0:21) -/

/-- `σ` is an **ℓ²-singular value** of `A` over `F` (equations (20)): there are nonzero
`u ∈ F^I`, `v ∈ F^J`, `w ∈ F^K` with `Σ_{j,k} a_{ijk} v_j w_k = σ u_i`,
`Σ_{i,k} a_{ijk} u_i w_k = σ v_j`, `Σ_{i,j} a_{ijk} u_i v_j = σ w_k` for all `i, j, k`. -/
def IsL2SingularValue {I J K F : Type*} [Fintype I] [Fintype J] [Fintype K] [CommRing F]
    (A : I → J → K → F) (σ : F) : Prop :=
  ∃ (u : I → F) (v : J → F) (w : K → F), u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
    (∀ i, ∑ j, ∑ k, A i j k * v j * w k = σ * u i) ∧
    (∀ j, ∑ i, ∑ k, A i j k * u i * w k = σ * v j) ∧
    (∀ k, ∑ i, ∑ j, A i j k * u i * v j = σ * w k)

/-- `σ` is an **ℓ³-singular value** of `A` over `F` (equations (21)): as (20), with the
right-hand sides `σ u_i²`, `σ v_j²`, `σ w_k²`. -/
def IsL3SingularValue {I J K F : Type*} [Fintype I] [Fintype J] [Fintype K] [CommRing F]
    (A : I → J → K → F) (σ : F) : Prop :=
  ∃ (u : I → F) (v : J → F) (w : K → F), u ≠ 0 ∧ v ≠ 0 ∧ w ≠ 0 ∧
    (∀ i, ∑ j, ∑ k, A i j k * v j * w k = σ * u i ^ 2) ∧
    (∀ j, ∑ i, ∑ k, A i j k * u i * w k = σ * v j ^ 2) ∧
    (∀ k, ∑ i, ∑ j, A i j k * u i * v j = σ * w k ^ 2)

/-- The codes of the rational tensors for which `σ = 0` is an ℓ²-singular value over `F`. -/
def zeroL2SingLang (F : Type*) [Field F] : Lang BSym :=
  { w | ∃ (l m n : ℕ) (A : Fin l → Fin m → Fin n → ℚ),
      IsL2SingularValue (fun i j k => (A i j k : F)) 0 ∧ w = tensorCode A }

/-- The codes of the rational tensors for which `σ = 0` is an ℓ³-singular value over `F`. -/
def zeroL3SingLang (F : Type*) [Field F] : Lang BSym :=
  { w | ∃ (l m n : ℕ) (A : Fin l → Fin m → Fin n → ℚ),
      IsL3SingularValue (fun i j k => (A i j k : F)) 0 ∧ w = tensorCode A }

end TensorNP.Bilinear


