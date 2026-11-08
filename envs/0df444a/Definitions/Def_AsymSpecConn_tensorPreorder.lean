-- Prove2me | Definitions.Def_AsymSpecConn_tensorPreorder
-- name    : AsymSpecConn_tensorPreorder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:58.078678+00:00
-- url     : https://prove2.me/theorems/aac5cf9e-1e2e-4632-b18c-ae3fac526b98
-- title:
--   Restriction preorder on $\mathcal S_F$ and the asymptotic spectrum of $k$-tensors
-- statement:
--   On the semiring $\mathcal S_F$ of $k$-tensors over a field $F$ up to equivalence, with direct sum and Kronecker product, the **restriction preorder** is: $s\le t$ if a representative of $s$ equals $(A_1\otimes\dots\otimes A_k)$ applied to a representative of $t$, for linear maps $A_i$. The **asymptotic spectrum of complex $k$-tensors** $\Delta=\Delta_{\mathbb C}$ is the spectrum of $\mathcal S_{\mathbb C}$ with this preorder.
--
--   **Formalization Note** $\mathcal S_F$ is the published `MME.TensorQ F k`, and the preorder is the one underlying the published `MME.TensorQ.tensorStrassen`, whose `le` is restriction on representatives. Only the preorder is used here; the further fields of `MME.StrassenPreorder` are proved facts there, not assumptions here. $k\ge2$ is the standing assumption of §3.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), §3, p.21

import Mathlib
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_AsymSpecConn_Spectrum

set_option autoImplicit false

open scoped NNReal

namespace AsymSpecConn

universe u

/-- **The restriction preorder on `S_F`** (§3, p.21 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): on the
semiring `MME.TensorQ F k` of `k`-tensors over `F` up to equivalence, `s ≤ t` iff (a
representative of) `s` is a restriction `(A₁ ⊗ ⋯ ⊗ A_k) t` of (a representative of) `t`.

**Formalization Note** This is the preorder underlying the published `MME.TensorQ.tensorStrassen`
(its `le` is `MME.TensorObj.Restrict` on representatives). Only the preorder is used; the
further fields of `MME.StrassenPreorder` are proved facts there, not assumptions here.
`k ≥ 2` is the standing assumption of §3 ("Fix k ≥ 2"). -/
noncomputable abbrev tensorPreorder (F : Type u) [Field F] {k : ℕ} (hk : 2 ≤ k) :
    Preorder (MME.TensorQ F k) :=
  (MME.TensorQ.tensorStrassen F k hk).toPreorder

/-- **The asymptotic spectrum `Δ = Δ_ℂ` of complex `k`-tensors** (§3, p.21 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)):
the spectrum (`Spectrum`) of the semiring `S_ℂ = MME.TensorQ ℂ k` with the restriction preorder.
The space `Δ` is the subtype `↥(tensorSpectrum hk)` with the topology of pointwise
convergence. -/
abbrev tensorSpectrum {k : ℕ} (hk : 2 ≤ k) : Set (MME.TensorQ ℂ k → ℝ≥0) :=
  Spectrum (MME.TensorQ ℂ k) (tensorPreorder ℂ hk)

end AsymSpecConn


