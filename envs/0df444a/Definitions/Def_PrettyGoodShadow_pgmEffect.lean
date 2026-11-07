-- Prove2me | Definitions.Def_PrettyGoodShadow_pgmEffect
-- name    : PrettyGoodShadow_pgmEffect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:23:46.780209+00:00
-- url     : https://prove2.me/theorems/c00edd44-d951-428f-b675-b9fd87e7381c
-- title:
--   The integral pretty good measurement $M_y=D_S(p_y\rho_y^{\otimes n})$ and its outcome law
-- statement:
--   The integral pretty good measurement associated with the ensemble $\{p_y,\rho_y^{\otimes n}\}_{y\in\mathcal L}$ has the operators
--
--   $$
--   M_y=D_S\big(p_y\rho_y^{\otimes n}\big),\qquad S=S(p,n).
--   $$
--
--   On $n$ copies of $\rho_x$ its outcome $\hat x$ has the law $\Pr[\hat x=y]=\operatorname{tr}(M_y\rho_x^{\otimes n})$.
--
--   **Formalization Note** The operators sum to the projector onto $\operatorname{supp}(S)$, not to the identity. The source completes them arbitrarily on the orthogonal complement, which no $\rho_x^{\otimes n}$ with $p_x>0$ sees. For $p_x=0$ the total mass of the law may be below $1$; such labels only ever carry weight $0$.
-- source:
--   Grewal, Pelecanos, Spilecki, Tang, Wright, Pretty good shadow tomography, arXiv:2610.06781 (sha256 bd055b7d…), Definition 3.1, p.16; Algorithm 1, p.18

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_PrettyGoodShadow_obs
import Definitions.Def_DimFreeShadow_recoveryEffect
import Definitions.Def_PrettyGoodShadow_divS

namespace PrettyGoodShadow

open DimFreeShadow (ensembleState)

open ShadowTomography.UpperBound (tensorPow)

/-- **The integral pretty good measurement** associated with the ensemble `{p_y, ρ_y^{⊗n}}_{y ∈ L}`
(arXiv:2610.06781, sha256 bd055b7d…, Definition 3.1, p.16): `M_y := D_S(p_y ρ_y^{⊗n})` with `S = S(p, n)`.

**Formalization Note** These operators sum to the projector onto `supp(S)`, not to the identity. The page
completes them "arbitrarily" off `supp(S)`, which no `ρ_x^{⊗n}` with `p_x > 0` sees, so the completion enters
only in the milestone `copy_accounting`. -/
noncomputable def pgmEffect {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] (p : L → ℝ)
    (ρ : L → Matrix d d ℂ) (n : ℕ) (y : L) : Matrix (Fin n → d) (Fin n → d) ℂ :=
  divS (ensembleState p ρ n) ((p y : ℂ) • tensorPow (ρ y) n)

/-- **Outcome law of the integral PGM** on `n` copies of `ρ_x` (arXiv:2610.06781, sha256 bd055b7d…,
Algorithm 1, step 2, p.18): `Pr[x̂ = y] = tr(M_y ρ_x^{⊗n})`.

**Formalization Note** For `p_x > 0` this is a probability vector in `y`. For `p_x = 0` its total mass
`tr(Π ρ_x^{⊗n})` may be below `1`; such labels only ever appear with weight `0`. -/
noncomputable def pgmLaw {L d : Type} [Fintype L] [Fintype d] [DecidableEq d] (p : L → ℝ)
    (ρ : L → Matrix d d ℂ) (n : ℕ) (x y : L) : ℝ :=
  obs (pgmEffect p ρ n y) (tensorPow (ρ x) n)

end PrettyGoodShadow


