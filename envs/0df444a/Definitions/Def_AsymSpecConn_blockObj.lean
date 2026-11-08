-- Prove2me | Definitions.Def_AsymSpecConn_blockObj
-- name    : AsymSpecConn_blockObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:07.691692+00:00
-- url     : https://prove2.me/theorems/ed4c50ff-3b20-49a7-8e70-d4d286e16f8b
-- title:
--   The block tensors $a_{j_1,\dots,j_k}$ of a decomposition of the legs
-- statement:
--   Let $Y$ be a $k$-tensor and, for every leg $i$, let the leg space be an internal direct sum $\bigoplus_j U^{(i)}_j$. Let $p^{(i)}_j$ be the projection onto $U^{(i)}_j$ along the other summands. For a choice $J=(j_1,\dots,j_k)$, the **block tensor** is
--   $$a_J=(p^{(1)}_{j_1}\otimes\dots\otimes p^{(k)}_{j_k})Y,$$
--   viewed as a $k$-tensor in $U^{(1)}_{j_1}\otimes\dots\otimes U^{(k)}_{j_k}$.
--
--   **Formalization Note** The source's $a_J$ lies in the original tensor product. It is the image of the tensor here under the inclusions $U^{(i)}_{j_i}\subseteq V_i$, and the two are equivalent because inclusion and projection restrict each to the other, so they have the same class and vanish together. The module also names the projection (`internalProj`).
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Lemma 3.4, pp.22–23

import Mathlib
import Definitions.Def_mme_tensor

set_option autoImplicit false

open PiTensorProduct
open scoped TensorProduct

namespace AsymSpecConn

universe u

/-- The projection `p_j : W → U_j` onto the summand `U_j` along the other summands of an internal
direct sum decomposition `W = ⊕_j U_j` (Lemma 3.4, p.22 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)). -/
noncomputable def internalProj {K : Type u} [Field K] {W : Type*} [AddCommGroup W] [Module K W]
    {ι : Type*} [DecidableEq ι] (U : ι → Submodule K W) (h : DirectSum.IsInternal U) (j : ι) :
    W →ₗ[K] U j :=
  (DirectSum.component K ι (fun j => U j) j).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap U) h).symm.toLinearMap

/-- **The block tensors `a_{j₁,…,j_k} = (p^{(1)}_{j₁} ⊗ ⋯ ⊗ p^{(k)}_{j_k}) t`** of Lemma 3.4
(p.22 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)), viewed in `U^{(1)}_{j₁} ⊗ ⋯ ⊗ U^{(k)}_{j_k}`. Given a `k`-tensor `Y` and, for
every leg `i`, an internal direct sum decomposition `Y.V i = ⊕_j U i j`, `blockObj Y U hU J` is
the `k`-tensor with legs `U i (J i)` obtained by applying the projection onto `U i (J i)` (along
the other summands) on every leg `i`.

**Formalization Note** The paper's `a_J` lives in `Y.V 1 ⊗ ⋯ ⊗ Y.V k`; it is the image of
`(blockObj Y U hU J).t` under the inclusions `U i (J i) ⊆ Y.V i`, and the two are equivalent
tensors (inclusion and projection restrict each to the other). -/
noncomputable def blockObj {K : Type u} [Field K] {k : ℕ} (Y : MME.TensorObj K k)
    {ι : Fin k → Type*} [∀ i, DecidableEq (ι i)] (U : ∀ i, ι i → Submodule K (Y.V i))
    (hU : ∀ i, DirectSum.IsInternal (U i)) (J : ∀ i, ι i) : MME.TensorObj K k where
  V i := ↥(U i (J i))
  t := PiTensorProduct.map (fun i => internalProj (U i) (hU i) (J i)) Y.t

end AsymSpecConn


