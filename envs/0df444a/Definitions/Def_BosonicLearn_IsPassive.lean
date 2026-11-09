-- Prove2me | Definitions.Def_BosonicLearn_IsPassive
-- name    : BosonicLearn_IsPassive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:20:31.317631+00:00
-- url     : https://prove2.me/theorems/4af7d42f-166d-47e2-bcf3-8a60a19e294c
-- title:
--   Passive (gauge-invariant) Gaussian states
-- statement:
--   A density operator $\rho$ on the $n$-mode Fock space is a **passive Gaussian state** if it is a Gaussian state and it is block diagonal in the total photon number sectors:
--
--   $$\langle u|\rho|v\rangle=0\qquad\text{whenever } |u|\ne|v|,\qquad |u|=\textstyle\sum_i u_i ,$$
--
--   for occupation vectors $u,v\in\mathbb N^n$. Passive states are the hard instances of the lower bounds (Theorems 5 and 9) and are parametrized by fugacity matrices (Lemma 2).
--
--   **Formalization Note** Zero mean is a consequence of block diagonality and is not stated separately.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 5

import Mathlib
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace BosonicLearn

/-- **Passive Gaussian states.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5: "A subclass of Gaussian states of particular interest is called *passive* Gaussian
states (or, *gauge-invariant* Gaussian states), which are Gaussian states whose density operators are
block diagonal in the total photon number sectors."

`IsPassive ρ` says `ρ` is a Gaussian state (for some mean and covariance) and its Fock matrix elements
`⟨u|ρ|v⟩` vanish whenever the total photon numbers `|u| = ∑ᵢ uᵢ` and `|v|` differ.

**Formalization Note.** The paper notes that passive states are zero-mean; that is a consequence of the
definition, not an extra clause. -/
def IsPassive {n : ℕ} (ρ : State (Occupation (Fin n))) : Prop :=
  (∃ (μ : Fin n ⊕ Fin n → ℝ) (S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ),
      IsGaussianState ρ μ S) ∧
    ∀ u v : Occupation (Fin n), ∑ i, u i ≠ ∑ i, v i → ρ.coefficients u v = 0

end BosonicLearn


