-- Prove2me | Definitions.Def_FourierRankQLB_padObj
-- name    : FourierRankQLB_padObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:13.568772+00:00
-- url     : https://prove2.me/theorems/f1e00b38-94d7-45a2-972c-ed35d235fc25
-- title:
--   The padded objective $\overline v=(v,0_{\ell_n})$
-- statement:
--   For $v\in\mathbb R^{d_n}$, the vector $\overline v=(v,0_{\ell_n})\in\mathbb R^n$, which puts $v$ on the hidden block and $0$ on the padded coordinate.
--
--   The objectives of Theorem 5.1 have this form.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, §5.1, p.31

import Mathlib
import Definitions.Def_FourierRankQLB_Ambient
import Definitions.Def_FourierRankQLB_dn

namespace FourierRankQLB

/-- The padded objective `v̄ = (v, 0_{ℓ_n})` of a vector `v ∈ ℝ^{d_n}`.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, §5.1, p. 31.

**Formalization Note.** The vector `v` occupies the first `dn n` coordinates, as `Abar` does. -/
noncomputable def padObj {n : ℕ} (v : Fin (dn n) → ℝ) : Ambient n :=
  WithLp.toLp 2 fun i => if h : i.1 < dn n then v ⟨i.1, h⟩ else 0

end FourierRankQLB


