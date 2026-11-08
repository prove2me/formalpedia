-- Prove2me | Definitions.Def_AsymSpecConn_permRep
-- name    : AsymSpecConn_permRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:01.865299+00:00
-- url     : https://prove2.me/theorems/84ee076d-f7cf-4e49-b35a-1933877aea9e
-- title:
--   The action of $\mathfrak S_n$ on $V^{\otimes n}$ by permuting the factors
-- statement:
--   For a vector space $V$ and $n\in\mathbb N$, the symmetric group $\mathfrak S_n$ acts on $V^{\otimes n}$ by permuting the tensor factors: $\sigma\cdot(v_1\otimes\dots\otimes v_n)=v_{\sigma^{-1}(1)}\otimes\dots\otimes v_{\sigma^{-1}(n)}$. This is the representation decomposed in the polynomial count of irreducible summands.
--
--   **Formalization Note** The carrier is the indexed tensor power over $\mathrm{Fin}\,n$, and the action is Mathlib's `PiTensorProduct.reindex`.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Lemma 3.3 and Lemma 3.4, p.22

import Mathlib

set_option autoImplicit false

open PiTensorProduct
open scoped TensorProduct

namespace AsymSpecConn

universe u

/-- **The action of `𝔖_n` on `V^{⊗n}` by permuting the factors** (Lemmas 3.3, 3.4, p.22 of
Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): `σ · (v₁ ⊗ ⋯ ⊗ v_n) = v_{σ⁻¹(1)} ⊗ ⋯ ⊗ v_{σ⁻¹(n)}`, a representation of
`Equiv.Perm (Fin n)` on `⨂[K] _ : Fin n, V` (Mathlib's `PiTensorProduct.reindex`). -/
noncomputable def permRep (K : Type u) [Field K] (V : Type*) [AddCommGroup V] [Module K V]
    (n : ℕ) : Representation K (Equiv.Perm (Fin n)) (⨂[K] _ : Fin n, V) where
  toFun σ := (PiTensorProduct.reindex K (fun _ : Fin n => V) σ).toLinearMap
  map_one' := by
    apply PiTensorProduct.ext; apply MultilinearMap.ext; intro x
    simp; rfl
  map_mul' σ τ := by
    apply PiTensorProduct.ext; apply MultilinearMap.ext; intro x
    simp [PiTensorProduct.reindex_tprod]; rfl

end AsymSpecConn


