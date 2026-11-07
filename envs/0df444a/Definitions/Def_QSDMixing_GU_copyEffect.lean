-- Prove2me | Definitions.Def_QSDMixing_GU_copyEffect
-- name    : QSDMixing_GU_copyEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:51:54.930389+00:00
-- url     : https://prove2.me/theorems/a194fbf2-b477-44c2-aff9-613fea0823b6
-- title:
--   $\mathrm{tr}(E\rho^{\otimes k})$ for a state presented as a mixture
-- statement:
--   For a state $\rho=\sum_a w_a|v_a\rangle\langle v_a|$ and a bounded operator $E$ on $\ell^2(\mathrm{Fin}\,k\to\iota)$, this is
--
--   $$
--   \mathrm{tr}(E\rho^{\otimes k})=\sum_{a:\mathrm{Fin}\,k\to\mathbb N}\Big(\prod_j w_{a(j)}\Big)\,\mathrm{Re}\,\langle v_{a(1)}\otimes\dots\otimes v_{a(k)},\,E\,(v_{a(1)}\otimes\dots\otimes v_{a(k)})\rangle.
--   $$
--
--   It is the probability of the outcome of effect $E$ on $k$ i.i.d. copies of $\rho$.
--
--   **Formalization Note** The series converges absolutely for bounded $E$, since the product weights sum to $1$. For positive $E$ the inner products are real.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (4), p.4; eq. (34), p.12

import Mathlib
import Definitions.Def_GaussTesting_Ell2
import Definitions.Def_QSDMixing_GU_tensorVec
import Definitions.Def_QSDMixing_GU_MixedState

set_option autoImplicit false
open GaussTesting (Ell2)

namespace QSDMixing.GU

/-- `tr(E ρ^{⊗k})` for `ρ = Σ_a w_a |v_a⟩⟨v_a|`, an operator `E` on `ℓ²(Fin k → ι)`:
`Σ_{a : Fin k → ℕ} (∏_j w_{a j}) · Re ⟨v_{a 1} ⊗ … ⊗ v_{a k}, E (v_{a 1} ⊗ … ⊗ v_{a k})⟩`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (4), p.4, and eq. (34), p.12.

**Formalization Note.** The series converges absolutely for every bounded `E`, because the product
weights sum to `1` and `|⟨x, E x⟩| ≤ ‖E‖` on unit vectors, so the junk value of `∑'` never occurs. For
positive `E` the inner product is real, and `Re` only serves to land in `ℝ`. -/
noncomputable def copyEffect {ι : Type} (ρ : MixedState ι) (k : ℕ)
    (E : Ell2 (Fin k → ι) →L[ℂ] Ell2 (Fin k → ι)) : ℝ :=
  ∑' a : Fin k → ℕ, (∏ j, ρ.w (a j)) *
    (inner ℂ (tensorVec fun j => ρ.v (a j)) (E (tensorVec fun j => ρ.v (a j)))).re

end QSDMixing.GU


