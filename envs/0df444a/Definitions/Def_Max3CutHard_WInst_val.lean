-- Prove2me | Definitions.Def_Max3CutHard_WInst_val
-- name    : Max3CutHard_WInst_val
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:17.904888+00:00
-- url     : https://prove2.me/theorems/fd3a93c3-129f-46ec-bd78-31aeed2858c3
-- title:
--   The value $\mathrm{val}(\Phi)=\max_\sigma\mathrm{val}_\Phi(\sigma)$
-- statement:
--   For an instance $\Phi$ on finite variable sets $U$ and $W$,
--
--   $$\mathrm{val}(\Phi)=\max_{\sigma:U\cup W\to\mathbb Z_3}\mathrm{val}_\Phi(\sigma).$$
--
--   Håstad's theorem is a gap statement about this value.
--
--   **Formalization Note** A maximum over the finite nonempty set of pairs $(U\to\mathbb Z_3)\times(W\to\mathbb Z_3)$ (`Finset.sup'`), not a real supremum.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Section 2, Håstad's equations, p.4

import Mathlib
import Definitions.Def_Max3CutHard_WInst_valAt

namespace Max3CutHard

/-- **`val(Φ) = max_σ val_Φ(σ)`.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Section 2, Håstad's equations, p.4:
"`val(Φ) = max_σ val_Φ(σ)`".

**Formalization Note.** A maximum over the finite nonempty set of assignments
`(U → ℤ₃) × (W → ℤ₃)` (`Finset.sup'`), for finite `U`, `W`. -/
noncomputable def WInst.val {U W : Type} [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (Φ : WInst U W) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun σ : (U → ZMod 3) × (W → ZMod 3) => Φ.valAt σ.1 σ.2

end Max3CutHard


