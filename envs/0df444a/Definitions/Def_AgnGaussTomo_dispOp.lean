-- Prove2me | Definitions.Def_AgnGaussTomo_dispOp
-- name    : AgnGaussTomo_dispOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:49.131856+00:00
-- url     : https://prove2.me/theorems/241ef86e-f390-41ea-ab38-d9ce4cbd59ea
-- title:
--   Displacement operator $D(y)$, $D(y)^\dagger\hat R_jD(y)=\hat R_j+y_j$
-- statement:
--   For $y\in\mathbb R^{2n}$ (grouped order), the **displacement operator** $D(y)$ is the unitary with
--
--   $$
--   D(y)^\dagger\,\hat{\mathbf R}_j\,D(y)=\hat{\mathbf R}_j+y_j I\qquad(j=1,\dots,2n).
--   $$
--
--   Explicitly $D(y)=\bigotimes_j\exp(\alpha_j\hat a_j^\dagger-\bar\alpha_j\hat a_j)$ with $\alpha_j=(y_{q_j}+i\,y_{p_j})/\sqrt2$, since $\hat q_j=(\hat a_j+\hat a_j^\dagger)/\sqrt2$ and $\hat p_j=(\hat a_j-\hat a_j^\dagger)/(i\sqrt2)$. This definition gives its matrix in the Fock basis. Displacements translate the seed state of a Gaussian measurement.
--
--   **Formalization Note** Built from the published `Claimed50.P47.weylKernel` evaluated at $-y$ (its argument convention is $z=-(\xi_q+i\xi_p)/\sqrt2$). The sign was checked: for one mode, $\langle1|D(y)|0\rangle=e^{-1/2}$ at $y=(\sqrt2,0)$ and $e^{-1/2}i$ at $y=(0,\sqrt2)$, which is $e^{-|\alpha|^2/2}\alpha$.
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), §2.2, printed p. 10 (PDF p. 13)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation weylKernel)

namespace AgnGaussTomo

/-- **The displacement operator `D(y)`, `D(y)† R̂_j D(y) = R̂_j + y_j I`.** Arulandu, Chen, Chen, Li, Ma,
*Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), §2.2,
printed p. 10 (PDF p. 13): "Here D(y) is a displacement operator satisfying D(y)† R̂_j D(y) =
R̂_j + y_j I for all j = 1, …, 2n", with `q̂_i = (â_i + â_i†)/√2`, `p̂_i = (â_i − â_i†)/(i√2)` (p. 9).

`dispOp y` is the Fock-basis matrix of `D(y) = ⊗_j exp(α_j â_j† − ᾱ_j â_j)` with
`α_j = (y_{q_j} + i y_{p_j})/√2`, so that `D(y)† q̂_j D(y) = q̂_j + √2 Re α_j = q̂_j + y_{q_j}` and
`D(y)† p̂_j D(y) = p̂_j + √2 Im α_j = p̂_j + y_{p_j}`.

**Formalization Note.** `y` is indexed in the grouped order (`inl j` = `q_j`, `inr j` = `p_j`). The
matrix is the published `Claimed50.P47.weylKernel` at `−y`: `weylKernel ξ` is the product of the
one-mode Fock matrices `displacementMatrix z` (entries of `exp(z â† − z̄ â)`) with
`z = −(ξ_{inl j} + i ξ_{inr j})/√2`, so `ξ = −y` gives `z = α_j`. -/
noncomputable def dispOp {n : ℕ} (y : Fin n ⊕ Fin n → ℝ) :
    Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ :=
  weylKernel (fun a => -y a)

end AgnGaussTomo


