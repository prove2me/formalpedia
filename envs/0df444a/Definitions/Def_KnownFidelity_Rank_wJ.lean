-- Prove2me | Definitions.Def_KnownFidelity_Rank_wJ
-- name    : KnownFidelity_Rank_wJ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:48.170483+00:00
-- url     : https://prove2.me/theorems/daf65934-7d07-4ac2-a438-c885fcc416ba
-- title:
--   The weight $w(\tau)=\mathrm{tr}(L\tau L^*)$ of §4.1
-- statement:
--   For a state $\tau$ on $\mathbb C^j$ (identified with the span of $J$),
--
--   $$w(\tau)=\mathrm{tr}\big(L\tau L^*\big),$$
--
--   with $L=\sqrt\ell\,\sigma_J^{-1/2}$. Since $L^*L\preceq I$, $0\le w(\tau)\le 1$.
--
--   **Formalization Note** The trace is taken as a real number.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §4.1 (unnumbered), p. 8 (PDF p. 10)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_Lmat

open scoped Matrix

namespace KnownFidelity.Rank

/-- **The weight `w(τ) = tr(L τ L*)` of §4.1.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §4.1 (unnumbered), printed p. 8 (PDF p. 10): "set L = √ℓ σ_J^{−1/2},
w(τ) = tr(LτL*)."

**Formalization Note.** The trace is taken as a real number (its real part; it is real for
Hermitian `τ`); `L` is `Lmat lam J ℓ`. -/
noncomputable def wJ {d j : ℕ} (lam : Fin d → ℝ) (J : Fin j ↪ Fin d) (ℓ : ℝ)
    (τ : Matrix (Fin j) (Fin j) ℂ) : ℝ :=
  (Lmat lam J ℓ * τ * (Lmat lam J ℓ)ᴴ).trace.re

end KnownFidelity.Rank


