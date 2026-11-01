-- Prove2me | Definitions.Def_WildeQIT_EntManip_relEntEntanglement
-- name    : WildeQIT_EntManip_relEntEntanglement
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:11.777187+00:00
-- url     : https://prove2.me/theorems/83ad6bec-7adb-439e-899f-81187b895da3
-- title:
--   Relative entropy of entanglement $E_R(A;B)_\rho=\min_{\sigma\in\mathrm{SEP}} D(\rho\|\sigma)$
-- statement:
--   Let $\rho_{AB}\in\mathcal D(\mathcal H_A\otimes\mathcal H_B)$. The **relative entropy of entanglement** of $\rho_{AB}$ is the relative-entropy distance from $\rho_{AB}$ to the closest separable state:
--
--   $$
--   E_R(A;B)_\rho \equiv \min_{\sigma_{AB}\in\mathrm{SEP}(A:B)} D(\rho_{AB}\|\sigma_{AB}).
--   $$
--
--   It is an LOCC monotone (Theorem 19.2.1), and it is the quantity through which the converse of the entanglement manipulation theorem is proved.
--
--   **Formalization Note** $\mathrm{SEP}(A:B)$ is the published `WildeQIT.IsSeparable` (finite convex combinations of pure product states; every separable state has this form). The minimum is written as an infimum in the extended reals; in finite dimensions it is attained, so it equals the book's minimum.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 19.2.1, (19.22), p. 538

import Mathlib
import Definitions.Def_WildeQIT_IsSeparable
import Definitions.Def_WildeQIT_QMemory_qRelEntropy

namespace WildeQIT.EntManip

/-- **Relative entropy of entanglement** (Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, Definition 19.2.1, p. 538): for `ρ_AB ∈ D(H_A ⊗ H_B)`,
`E_R(A;B)_ρ ≡ min_{σ_AB ∈ SEP(A:B)} D(ρ_AB‖σ_AB)` (19.22).

**Formalization Note** `SEP(A:B)` is the published `WildeQIT.IsSeparable` (finite convex
combinations of pure product states, Definition 4.3.2; every separable state, mixed local factors
included, has this form). The minimum is written as an infimum in `EReal`; in finite dimensions
the infimum is attained, so it is the book's minimum. Relative entropy in bits. -/
noncomputable def relEntEntanglement {a b : Type} [Fintype a] [DecidableEq a] [Fintype b]
    [DecidableEq b] (ρ : Matrix (a × b) (a × b) ℂ) : EReal :=
  ⨅ σ : {σ : Matrix (a × b) (a × b) ℂ // WildeQIT.IsSeparable σ}, WildeQIT.QMemory.qRelEntropy ρ σ.1

end WildeQIT.EntManip


