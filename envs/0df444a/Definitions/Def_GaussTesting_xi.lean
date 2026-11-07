-- Prove2me | Definitions.Def_GaussTesting_xi
-- name    : GaussTesting_xi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:22.933279+00:00
-- url     : https://prove2.me/theorems/f89bafa7-cc5d-4ea8-9e08-f9de8a51c84c
-- title:
--   The symmetrized test operator $\Xi=\Pi_{\mathrm{sym}}\Pi_{\mathrm{test}}\Pi_{\mathrm{sym}}$
-- statement:
--   Let $\Pi_{\mathrm{test}}=\Pi_K$ be a projector on $\mathcal H^{\otimes k}$ and $m=k+l$ with $l\ge1$. The symmetrized operator of Definition 3.1 is
--
--   $$
--   \Xi=\Pi^{(1,\dots,m)}_{\mathrm{sym}}\;\Pi^{(1,\dots,k)}_{\mathrm{test}}\;\Pi^{(1,\dots,m)}_{\mathrm{sym}}\qquad(3.3)
--   $$
--
--   on $\mathcal H^{\otimes m}$, where $\Pi^{(1,\dots,k)}_{\mathrm{test}}$ acts on the original $k$ copies. It is the analytical device behind every soundness bound in the paper: its spectral gap controls the gradient of the rejection probability.
--
--   **Formalization Note** `xi K l` takes the number $l=m-k$ of added registers.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), Definition 3.1, eq. (3.3), p.21

import Definitions.Def_GaussTesting_symSub
import Definitions.Def_GaussTesting_proj
import Definitions.Def_GaussTesting_amplSub

namespace GaussTesting

/-- The symmetrized test operator of Definition 3.1, (3.3), on `m = k + l` registers:
`Ξ = Π^{(1,…,m)}_sym Π^{(1,…,k)}_test Π^{(1,…,m)}_sym`, with `Π_test = Π_K`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), Definition 3.1, eq. (3.3), p.21.

**Formalization Note.** `l = m − k` is the number of added registers (`m > k` is `1 ≤ l`); `Ξ` acts on
`ℓ²(Fin (k + l) → ι) = ℋ^{⊗m}`. -/
noncomputable def xi {ι : Type*} {k : ℕ} (K : ClosedSubmodule ℂ (Ell2 (Fin k → ι))) (l : ℕ) :
    Ell2 (Fin (k + l) → ι) →L[ℂ] Ell2 (Fin (k + l) → ι) :=
  proj (symSub ι (k + l)) ∘L proj (amplSub K l) ∘L proj (symSub ι (k + l))

end GaussTesting


