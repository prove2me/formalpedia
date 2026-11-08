-- Prove2me | Definitions.Def_AsymSpecConn_kronPowPi
-- name    : AsymSpecConn_kronPowPi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:04.016088+00:00
-- url     : https://prove2.me/theorems/f7557eb9-22e9-4d2a-b03d-bb00d3a60c19
-- title:
--   The Kronecker power $t^{\otimes n}$ with legs $V_i^{\otimes n}$
-- statement:
--   For a $k$-tensor $t\in V_1\otimes\dots\otimes V_k$, the **Kronecker power** $t^{\otimes n}$ is the $k$-tensor in $V_1^{\otimes n}\otimes\dots\otimes V_k^{\otimes n}$ obtained from the $n$-fold tensor product of $t$ with itself by grouping the factors of each leg. If $t=\sum_\alpha c_\alpha\,b_{1,\alpha_1}\otimes\dots\otimes b_{k,\alpha_k}$ in bases $(b_{i,x})$ of the $V_i$, then
--   $$t^{\otimes n}=\sum_{\alpha^1,\dots,\alpha^n}\Bigl(\prod_{m=1}^n c_{\alpha^m}\Bigr)\bigotimes_{i=1}^k\bigl(b_{i,\alpha^1_i}\otimes\dots\otimes b_{i,\alpha^n_i}\bigr).$$
--
--   **Formalization Note** Each leg is the indexed tensor power over $\mathrm{Fin}\,n$, so $\mathfrak S_n$ acts on it by permuting the factors; this is why the iterated `MME.TensorObj.kronPow` is not used. The Lean term is the coordinate formula above in Mathlib's chosen bases, and the resulting tensor does not depend on the bases.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Lemma 3.4, p.22

import Mathlib
import Definitions.Def_mme_tensor

set_option autoImplicit false

open PiTensorProduct
open scoped TensorProduct

namespace AsymSpecConn

universe u

/-- **The Kronecker power `t^{⊗n}` with legs `V_i^{⊗n}`** (Lemma 3.4, p.22 of
Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)). For a `k`-tensor `t ∈ V₁ ⊗ ⋯ ⊗ V_k`, `t^{⊗n}` is the `k`-tensor in
`V₁^{⊗n} ⊗ ⋯ ⊗ V_k^{⊗n}` obtained from the `n`-fold tensor product of `t` with itself by
regrouping the factors. In coordinates: choose a basis `(b_{i,x})_x` of every `V_i` and write
`t = Σ_α c_α b_{1,α₁} ⊗ ⋯ ⊗ b_{k,α_k}`; then
`t^{⊗n} = Σ_{α¹, …, αⁿ} (c_{α¹} ⋯ c_{αⁿ}) ⨂_i (b_{i,α¹_i} ⊗ ⋯ ⊗ b_{i,αⁿ_i})`.

**Formalization Note** Each leg is `⨂[K] _ : Fin n, X.V i`, so that `𝔖_n` acts on it by
permuting the factors (`permRep`). The coordinate formula uses Mathlib's chosen bases
(`Module.Free.chooseBasis`); the resulting tensor does not depend on the bases. -/
noncomputable def kronPowPi {K : Type u} [Field K] {k : ℕ} (X : MME.TensorObj K k) (n : ℕ) :
    MME.TensorObj K k where
  V i := ⨂[K] _ : Fin n, X.V i
  t :=
    let b := fun i => Module.Free.chooseBasis K (X.V i)
    let c := (Basis.piTensorProduct b).repr X.t
    ∑ α : Fin n → (∀ i, Module.Free.ChooseBasisIndex K (X.V i)),
      (∏ m, c (α m)) • ⨂ₜ[K] i, ⨂ₜ[K] m, b i (α m i)

end AsymSpecConn


