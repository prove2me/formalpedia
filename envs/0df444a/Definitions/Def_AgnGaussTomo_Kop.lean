-- Prove2me | Definitions.Def_AgnGaussTomo_Kop
-- name    : AgnGaussTomo_Kop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:38.424229+00:00
-- url     : https://prove2.me/theorems/bbdf012e-9816-4435-b755-a92199ecf373
-- title:
--   The operator $K_\theta=\sum_i b_i\hat a_i^\dagger+\tfrac12\sum_{ij}A_{ij}\hat a_i^\dagger\hat a_j^\dagger$
-- statement:
--   For $\theta=(b,A)\in\mathcal P_n$ define
--
--   $$
--   K_\theta=L_b+Q_A,\qquad L_b=\sum_i b_i\hat a_i^\dagger,\qquad Q_A=\tfrac12\sum_{i,j}A_{ij}\hat a_i^\dagger\hat a_j^\dagger ,
--   $$
--
--   so that $|\Phi(\theta)\rangle=e^{K_\theta}|0\rangle$. On Fock coefficients the creation operator acts by $(\hat a_i^\dagger\varphi)(m)=\sqrt{m_i}\,\varphi(m-e_i)$ for $m_i\ge1$ and $0$ otherwise. $K_\theta$ raises the photon number by one or two, and its norm on low-photon subspaces drives the derivative bounds of the refinement analysis.
--
--   **Formalization Note** `create i` is $\hat a_i^\dagger$ on coefficient families; `Kop θ` is defined for every $\theta$ (no condition on $A$).
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Fact 2.4, Eq. (5), printed p. 11 (PDF p. 14); creation operators, §2.2, p. 8 (PDF p. 11)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47
import Definitions.Def_AgnGaussTomo_Pspace

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- The creation operator `â_i†` on Fock coefficient families (§2.2, printed p. 8:
`â_i† |m⟩ = √(m_i + 1) |m + e_i⟩`): `(â_i† φ)(m) = √(m_i) φ(m − e_i)` if `m_i ≥ 1`, else `0`. -/
noncomputable def create {n : ℕ} (i : Fin n) (φ : Occupation (Fin n) → ℂ) :
    Occupation (Fin n) → ℂ :=
  fun m => if 1 ≤ m i then (Real.sqrt (m i : ℝ) : ℂ) * φ (Function.update m i (m i - 1)) else 0

/-- **The operator `K_θ = L_b + Q_A = Σᵢ bᵢ âᵢ† + ½ Σᵢⱼ Aᵢⱼ âᵢ† âⱼ†`.** Arulandu, Chen, Chen, Li, Ma,
*Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), Fact 2.4,
Eq. (5), printed p. 11 (PDF p. 14): "We also define K_θ ≡ L_b + Q_A for θ = (b, A)", with
`L_b = Σᵢ bᵢ âᵢ†`, `Q_A = ½ Σᵢⱼ Aᵢⱼ âᵢ†âⱼ†`.

`Kop θ φ` applies `K_θ` to a Fock coefficient family `φ`.

**Formalization Note.** `(b, A) = (Pspace.b θ, Pspace.A θ)`; `K_θ` is defined for every `θ` (no
`‖A‖_op < 1` needed). It is applied to arbitrary coefficient families; on the finitely supported
families of `F_{≤m}` (Lemma 3.10) all sums are finite. -/
noncomputable def Kop {n : ℕ} (θ : Pspace n) (φ : Occupation (Fin n) → ℂ) :
    Occupation (Fin n) → ℂ :=
  fun m => ∑ i, Pspace.b θ i * create i φ m +
    (1 / 2 : ℂ) * ∑ i, ∑ j, Pspace.A θ i j * create i (create j φ) m

end AgnGaussTomo


