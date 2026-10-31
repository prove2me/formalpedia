-- Prove2me | Definitions.Def_ObliviousRSP_modifiedBobState
-- name    : ObliviousRSP_modifiedBobState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:42.467179+00:00
-- url     : https://prove2.me/theorems/c7ad46e4-9db0-49d3-8186-7f00ed62a2f7
-- title:
--   Bob's state in the modified protocol, eq. (6)
-- statement:
--   In the modified protocol (Fig. 3) Alice measures the single specimen $\varphi$ (register 1) together with her half of $|\Phi_{d'}\rangle$ (register 2). When the outcome has POVM element $M_m$ (an operator on registers 1, 2), Bob's half (register 3) is left in the unnormalized state
--   $$
--   \mathbf b = \operatorname{Tr}_{12}\!\big[(\varphi_1\otimes|\Phi_{d'}\rangle\langle\Phi_{d'}|_{23})(M_{m,12}\otimes I_3)\big].
--   $$
--
--   This is the quantity the paper compares with $p_m\rho_{\varphi m}$ to show that the modified protocol looks the same to Bob.
--
--   **Formalization Note** $\varphi\otimes|\Phi_{d'}\rangle\langle\Phi_{d'}|$ is indexed by $\iota\times(\sigma\times\sigma)$ and regrouped as $(\iota\times\sigma)\times\sigma$ along the inverse of `Equiv.prodAssoc`, so registers 1, 2 form the traced left factor (`WildeQIT.partialTraceLeft`). The definition takes any operator $M_m$ and any matrix $\varphi$.
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, eq. (6), p.4

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_ObliviousRSP_maxEnt

open scoped Kronecker

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, eq. (6), p.4: in the modified protocol (Fig. 3) Alice measures the single specimen
`φ` (register 1) together with her half of `|Φ_{d′}⟩` (register 2); when the outcome has
POVM element `M_m`, Bob's half (register 3) is left in the unnormalized state
**b** `= Tr_12[(φ_1 ⊗ |Φ_{d′}⟩⟨Φ_{d′}|_23)(M_m12 ⊗ I_3)]`.

**Formalization Note.** `φ ⊗ₖ maxEnt σ` is indexed by `ι × (σ × σ)` and is reindexed to
`(ι × σ) × σ` along `(Equiv.prodAssoc ι σ σ).symm`, so registers 1, 2 form the left factor
and register 3 the right factor; `Tr_12` is `WildeQIT.partialTraceLeft` over `ι × σ`. -/
noncomputable def modifiedBobState {ι σ : Type} [Fintype ι] [Fintype σ] [DecidableEq σ]
    (Mm : Matrix (ι × σ) (ι × σ) ℂ) (φ : Matrix ι ι ℂ) : Matrix σ σ ℂ :=
  WildeQIT.partialTraceLeft
    (Matrix.reindex (Equiv.prodAssoc ι σ σ).symm (Equiv.prodAssoc ι σ σ).symm (φ ⊗ₖ maxEnt σ) *
      (Mm ⊗ₖ (1 : Matrix σ σ ℂ)))

end ObliviousRSP


