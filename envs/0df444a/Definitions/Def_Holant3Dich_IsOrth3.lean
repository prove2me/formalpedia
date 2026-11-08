-- Prove2me | Definitions.Def_Holant3Dich_IsOrth3
-- name    : Holant3Dich_IsOrth3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:51.733001+00:00
-- url     : https://prove2.me/theorems/a408da27-7aa1-46a7-88e5-4b295cc618fe
-- title:
--   The dot product, $O(3,\mathbb C)$, and the vectors and matrices $e_i$, $\beta_\pm$, $Y$, $Y^{-1}$, $X$
-- statement:
--   The **dot product** on $\mathbb C^n$ is the bilinear form $\langle u,v\rangle=u^{\mathsf T}v=\sum_i u_iv_i$, with no complex conjugation; $u,v$ are orthogonal if $\langle u,v\rangle=0$.
--
--   The **complex orthogonal group** is
--   $$O(3,\mathbb C)=\{T\in\mathbb C^{3\times 3}: T^{\mathsf T}T=I\}.$$
--
--   The fixed vectors and matrices of p.12 are $e_1,e_2,e_3$ (standard basis), $\beta_\pm=\tfrac1{\sqrt2}(1,\pm i,0)$,
--   $$Y=\begin{pmatrix}Z&0\\0&1\end{pmatrix},\quad Z=\tfrac1{\sqrt2}\begin{pmatrix}1&1\\ i&-i\end{pmatrix},\qquad Y^{-1}=\begin{pmatrix}Z^{-1}&0\\0&1\end{pmatrix},\quad Z^{-1}=\tfrac1{\sqrt2}\begin{pmatrix}1&-i\\ 1&i\end{pmatrix},$$
--   and $X=Y^{\mathsf T}Y=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix}$. They satisfy $Ye_1=\beta_+$, $Ye_2=\beta_-$, $Ye_3=e_3$.
--
--   The isotropic vectors $\beta_\pm$ and the change of basis $Y$ carry the type $\mathfrak B$ and $\mathfrak C$ signatures of the paper.
--
--   **Formalization Note** Mathlib's `Matrix.orthogonalGroup` uses the star operation, which over $\mathbb C$ is the conjugate transpose (the unitary group), so it is not used. $Y^{-1}$ is written out explicitly; a verification file proves $YY^{-1}=Y^{-1}Y=I$, $Y^{\mathsf T}Y=X$, $Ye_1=\beta_+$, $Ye_2=\beta_-$, $\langle\beta_+,\beta_+\rangle=0$ and $\langle\beta_+,\beta_-\rangle=1$.
-- source:
--   Cai, Ihm, Group Action and Spin Representation Lead to a Holant* Complexity Dichotomy on Domain Size 3, STOC 2027 submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), §2.3 p.12; §2.5 p.16

import Mathlib

set_option autoImplicit false

namespace Holant3Dich

open Complex

/-- The dot product `⟨u, v⟩ = uᵀv = Σ uᵢvᵢ` on `ℂⁿ` (bilinear, no complex conjugation).
Cai–Ihm, *Group Action and Spin Representation Lead to a Holant\* Complexity Dichotomy on Domain
Size 3*, STOC 2027 submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), §2.3, p.12:
"Throughout this paper, the symbol ⟨u, v⟩ for u, v ∈ C^n denotes the dot product, i.e.
⟨u, v⟩ = uᵀv = Σ uivi. We say u, v ∈ C^n are orthogonal if ⟨u, v⟩ = 0." -/
def dot {n : ℕ} (u v : Fin n → ℂ) : ℂ := u ⬝ᵥ v

/-- `T ∈ O(3, ℂ)`: the complex orthogonal group `{M : MᵀM = I}` with the plain transpose.
Cai–Ihm, §2.5, p.16: "O(3, C) := O(3, C, I) = {M ∈ C^{3×3} : MᵀM = I}".

**Formalization Note.** Mathlib's `Matrix.orthogonalGroup` uses `star`, which over `ℂ` is the
conjugate transpose (the unitary group); it is not used. -/
def IsOrth3 (T : Matrix (Fin 3) (Fin 3) ℂ) : Prop := T.transpose * T = 1

/-- `e₁ = (1, 0, 0)`. Cai–Ihm, §2.3, p.12. -/
def e₁ : Fin 3 → ℂ := ![1, 0, 0]

/-- `e₂ = (0, 1, 0)`. Cai–Ihm, §2.3, p.12. -/
def e₂ : Fin 3 → ℂ := ![0, 1, 0]

/-- `e₃ = (0, 0, 1)`. Cai–Ihm, §2.3, p.12. -/
def e₃ : Fin 3 → ℂ := ![0, 0, 1]

/-- `β₊ = (1/√2)(1, i, 0)`. Cai–Ihm, §2.3, p.12: "Let β+ = (1/√2)(1, i, 0) and
β− = (1/√2)(1, −i, 0)". -/
noncomputable def βp : Fin 3 → ℂ := ![1 / (Real.sqrt 2 : ℂ), I / (Real.sqrt 2 : ℂ), 0]

/-- `β₋ = (1/√2)(1, −i, 0)`. Cai–Ihm, §2.3, p.12. -/
noncomputable def βm : Fin 3 → ℂ := ![1 / (Real.sqrt 2 : ℂ), -I / (Real.sqrt 2 : ℂ), 0]

/-- `Y = [[Z, 0], [0, 1]]` with `Z = (1/√2)[[1, 1], [i, −i]]`. Cai–Ihm, §2.3, p.12: "Let
Z = (1/√2)[[1, 1], [i, −i]] … Let Y = [[Z, 0], [0, 1]] … Note that Ye1 = β+, Ye2 = β− and
Ye3 = e3." -/
noncomputable def Y : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1 / (Real.sqrt 2 : ℂ), 1 / (Real.sqrt 2 : ℂ), 0;
     I / (Real.sqrt 2 : ℂ), -I / (Real.sqrt 2 : ℂ), 0;
     0, 0, 1]

/-- `Y⁻¹ = [[Z⁻¹, 0], [0, 1]]` with `Z⁻¹ = (1/√2)[[1, −i], [1, i]]`. Cai–Ihm, §2.3, p.12: "We
have Z^{−1} = (1/√2)[[1, −i], [1, i]]."

**Formalization Note.** Written out explicitly; the sanity file checks `Y * Yinv = 1` and
`Yinv * Y = 1`. -/
noncomputable def Yinv : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1 / (Real.sqrt 2 : ℂ), -I / (Real.sqrt 2 : ℂ), 0;
     1 / (Real.sqrt 2 : ℂ), I / (Real.sqrt 2 : ℂ), 0;
     0, 0, 1]

/-- `X = YᵀY = [[0, 1, 0], [1, 0, 0], [0, 0, 1]]`. Cai–Ihm, §2.3, p.12. -/
def X : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

end Holant3Dich


