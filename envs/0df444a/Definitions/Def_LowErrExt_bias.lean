-- Prove2me | Definitions.Def_LowErrExt_bias
-- name    : LowErrExt_bias
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:32.258773+00:00
-- url     : https://prove2.me/theorems/b94fd0b5-738e-44ff-837c-1187a4652dfa
-- title:
--   Bias of a parity, and $\varepsilon$-biased affine sources
-- statement:
--   For $x,y\in\mathbb F_2^n$ let $\mathrm{IP}(x,y)=\sum_i x_iy_i\in\mathbb F_2$. For a source $\mathbf X$ on $\mathbb F_2^n$ the **bias** of the parity $y$ is
--   $$\mathrm{bias}[\mathrm{IP}(\mathbf X,y)]=\big|\mathbb E\,(-1)^{\mathrm{IP}(\mathbf X,y)}\big| .$$
--   $\mathbf X$ is an **$\varepsilon$-biased affine source** if for every $y\in\mathbb F_2^n$, either $\mathrm{bias}[\mathrm{IP}(\mathbf X,y)]=1$ or $\mathrm{bias}[\mathrm{IP}(\mathbf X,y)]\le\varepsilon$ (Definition 3.28): every parity is constant or nearly unbiased.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), p.6, Definitions 3.26 and 3.28, pp.26–27

import Mathlib

namespace LowErrExt

/-- **Inner product over `𝔽₂`.** `ip x y = ∑ᵢ xᵢ yᵢ ∈ 𝔽₂` (p.6, and Definition 3.26, p.26). -/
def ip {ι : Type*} [Fintype ι] (x y : ι → ZMod 2) : ZMod 2 :=
  ∑ i, x i * y i

/-- **Bias of a parity.** `bias X y = |E[(−1)^{IP(X, y)}]|`.
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 3.26, p.26 ("bias[IP(X, α)]"); for a bit `Z`, bias[Z] = |E[(−1)^Z]|.

**Formalization Note.** `(−1)^{b}` for `b ∈ 𝔽₂` is computed through the representative
`b.val ∈ {0, 1}`. -/
noncomputable def bias {ι : Type*} [Fintype ι] (X : PMF (ι → ZMod 2)) (y : ι → ZMod 2) : ℝ :=
  |∑' x, (X x).toReal * (-1 : ℝ) ^ (ip x y).val|

/-- **`ε`-biased affine source.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Definition 3.28, p.27: "X ∼ Fn2 is an ε-biased affine source if for every y ∈ Fn2, either
bias[IP(X, y)] = 1 or bias[IP(X, y)] ≤ ε." -/
def IsBiasedAffine {ι : Type*} [Fintype ι] (ε : ℝ) (X : PMF (ι → ZMod 2)) : Prop :=
  ∀ y : ι → ZMod 2, bias X y = 1 ∨ bias X y ≤ ε

end LowErrExt


