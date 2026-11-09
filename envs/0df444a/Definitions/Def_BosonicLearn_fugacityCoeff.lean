-- Prove2me | Definitions.Def_BosonicLearn_fugacityCoeff
-- name    : BosonicLearn_fugacityCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:21:38.885639+00:00
-- url     : https://prove2.me/theorems/ad0df7c9-bce7-4cad-a3fd-9f45a81111fa
-- title:
--   Passive Gaussian state $\rho_R=\det(I-R)\,\Gamma(R)$
-- statement:
--   For a matrix $R\in\mathbb C^{n\times n}$ (the **fugacity matrix**) let
--
--   $$\rho_R=\det(I-R)\,\Gamma(R).$$
--
--   By Lemma 2 this is a passive Gaussian state exactly when $R$ is Hermitian with $0\preceq R\prec I$, and every passive Gaussian state arises this way. The lower bound of Theorem 5 is built on the family $\rho_{R_X}$.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Lemma 2, Eq. (21), p. 20

import Mathlib
import Definitions.Def_BosonicLearn_gammaFock

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace BosonicLearn

/-- **The passive Gaussian state with fugacity matrix `R`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Lemma 2, Eq. (21), p. 20: "Given R, which we call the fugacity matrix, the corresponding passive
Gaussian state is ρ = det(I − R)Γ(R)."

`fugacityCoeff R` is the Fock coefficient array `det(I − R) · Γ(R)`.

**Formalization Note.** It is an array for every `R`; Lemma 2 (`lemma_2`) says it is a passive Gaussian
density operator exactly when `R` is Hermitian with `0 ⪯ R ≺ I`. -/
noncomputable def fugacityCoeff {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ :=
  (1 - R).det • gammaFock R

end BosonicLearn


