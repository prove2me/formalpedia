-- Prove2me | Definitions.Def_SelectiveDPT_IsNegAdvWitness
-- name    : SelectiveDPT_IsNegAdvWitness
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:48.632405+00:00
-- url     : https://prove2.me/theorems/6fb140ad-563f-476b-ab63-d467abfe3cc7
-- title:
--   Witness $\Gamma^\pm$ to the normalized negative-weights adversary method
-- statement:
--   Let $f : D \to Y$ and let $\mu$ be a distribution on $D$ with purification $|\mathcal D\rangle$. A $|D| \times |D|$ complex matrix $\Gamma^\pm$ is a **witness to Proposition 2.5** for computing $f$ under $\mu$ if
--
--   1. $\Gamma^\pm$ is Hermitian;
--   2. $\Gamma^\pm_{x,x'} = 0$ whenever $f(x) = f(x')$;
--   3. $\|\Gamma^\pm\| = 1$ (spectral norm);
--   4. $\Gamma^\pm |\mathcal D\rangle = |\mathcal D\rangle$.
--
--   These are the conditions of the normalized negative-weights adversary method of Høyer, Lee and Špalek as stated in Proposition 2.5; entries may be complex.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Proposition 2.5, p.13

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_SelectiveDPT_IsDistOn

open Matrix

namespace SelectiveDPT

open QAlgorithms

/-- `Γ±` is a witness to the normalized negative-weights adversary method for computing `f` under
the distribution `μ` on `D` (arXiv:2609.26678, Proposition 2.5, p.13): a `|D| × |D|` Hermitian
matrix with `Γ±_{x,x'} = 0` whenever `f(x) = f(x')`, `‖Γ±‖ = 1` (spectral norm), and
`Γ± |D⟩ = |D⟩` for the purification `|D⟩ = Σ_x √(D(x)) |x⟩`.

**Formalization Note.** Entries may be complex; no realness or symmetry beyond Hermiticity is
required, as in the paper. -/
def IsNegAdvWitness {α Y : Type*} [DecidableEq α] (μ : α → ℝ) (D : Finset α) (f : α → Y)
    (Γ : Matrix D D ℂ) : Prop :=
  Γ.IsHermitian ∧ (∀ x x' : D, f x.1 = f x'.1 → Γ x x' = 0) ∧ specNorm Γ = 1 ∧
    Γ *ᵥ sqrtDist μ D = sqrtDist μ D

end SelectiveDPT


