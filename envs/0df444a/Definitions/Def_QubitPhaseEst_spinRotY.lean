-- Prove2me | Definitions.Def_QubitPhaseEst_spinRotY
-- name    : QubitPhaseEst_spinRotY
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:16:51.725671+00:00
-- url     : https://prove2.me/theorems/cbd5f29e-6031-4cfd-9612-ab567395067a
-- title:
--   Spin-$j$ matrices $J_z$, $J_\pm$, $J_y$ and rotations $e^{i\theta J_y}$, $e^{-i\psi J_z}$
-- statement:
--   For $j\in\{0,\tfrac12,1,\dots\}$ the spin-$j$ representation acts on $\mathbb C^{2j+1}$ with basis $|j,m\rangle$, $m=j,j-1,\dots,-j$; the basis vector of weight $m$ has index $i=j-m\in\{0,\dots,2j\}$. In this basis
--
--   1. $J_z|j,m\rangle=m|j,m\rangle$;
--   2. $J_+|j,m\rangle=\sqrt{j(j+1)-m(m+1)}\,|j,m+1\rangle$ (Condon–Shortley convention), and $J_-=J_+^\dagger$;
--   3. $J_y=(J_+-J_-)/(2i)$.
--
--   The **rotations** are the matrix exponentials $T^{(j)}=e^{i\theta J_y}$ and $e^{-i\psi J_z}$. The paper writes $T^{(j)}(g_{\vec b})=e^{i\theta J_y}$ for the rotation connecting the $z$ axis with the Bloch direction $\vec b$.
--
--   These matrices enter the explicit value (21) of the optimal averaged cosine.
--
--   **Formalization Note** The spin is passed as $2j\in\mathbb N$ and the index runs over `Fin (2j+1)`. The exponential is Mathlib's `NormedSpace.exp`.
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, p. 2 (|j,m⟩, J_z) and p. 3, after Eq. (21) (T(g_b) = e^{iθJ_y}, J_y = ½Σσ_y^(k))

import Mathlib

open scoped Matrix

namespace QubitPhaseEst

/-- The weight `m = j − i` of the index `i` in the spin-`j` representation, with `j2 = 2j`
(arXiv:quant-ph/0411133v3, Sec. II, Eq. (12), p. 2: `m = −j, …, j`).
Index `0` is the highest weight `m = j`. -/
noncomputable def spinM (j2 i : ℕ) : ℝ :=
  (j2 : ℝ) / 2 - (i : ℝ)

/-- The ladder coefficient `√(j(j+1) − m(m+1))` of `J₊|j, m⟩` (unnumbered; the standard basis
`|j, m⟩` of arXiv:quant-ph/0411133v3, Sec. II, Eqs. (12)–(13), p. 2), Condon–Shortley convention, where
`j2 = 2j` and `m = spinM j2 i`. -/
noncomputable def ladderCoeff (j2 i : ℕ) : ℝ :=
  Real.sqrt (((j2 : ℝ) / 2) * ((j2 : ℝ) / 2 + 1) - spinM j2 i * (spinM j2 i + 1))

/-- `J_z` in the spin-`j` representation (`j2 = 2j`), indexed by `Fin (j2 + 1)` with `i ↦ m = j − i`.
arXiv:quant-ph/0411133v3, Sec. II, p. 2 (`m` the eigenvalue of `J_z`). -/
noncomputable def spinJz (j2 : ℕ) : Matrix (Fin (j2 + 1)) (Fin (j2 + 1)) ℂ :=
  Matrix.diagonal fun i => (spinM j2 i : ℂ)

/-- `J₊` in the spin-`j` representation (arXiv:quant-ph/0411133v3, Sec. II, unnumbered): `J₊|m⟩ = √(j(j+1) − m(m+1))|m+1⟩`. Raising `m` lowers the
index, so the nonzero entries are `(i − 1, i)`. -/
noncomputable def spinJplus (j2 : ℕ) : Matrix (Fin (j2 + 1)) (Fin (j2 + 1)) ℂ :=
  Matrix.of fun i' i => if (i' : ℕ) + 1 = i then (ladderCoeff j2 i : ℂ) else 0

/-- `J_y = (J₊ − J₋)/(2i)` in the spin-`j` representation; arXiv:quant-ph/0411133v3, Sec. II, p. 3, after Eq. (21):
`J_y = ½ Σ_k σ_y^{(k)}` restricted to one irreducible block. -/
noncomputable def spinJy (j2 : ℕ) : Matrix (Fin (j2 + 1)) (Fin (j2 + 1)) ℂ :=
  (1 / (2 * Complex.I)) • (spinJplus j2 - (spinJplus j2)ᴴ)

/-- **The rotation `T^{(j)} = e^{iθJ_y}`** of arXiv:quant-ph/0411133v3, Sec. II, after Eq. (21),
p. 3, in the spin-`j` representation (`j2 = 2j`).

**Formalization Note.** Mathlib's `NormedSpace.exp`, the sum of the exponential series in the
entrywise topology of matrices. -/
noncomputable def spinRotY (j2 : ℕ) (θ : ℝ) : Matrix (Fin (j2 + 1)) (Fin (j2 + 1)) ℂ :=
  NormedSpace.exp (((θ : ℂ) * Complex.I) • spinJy j2)

/-- The rotation `e^{−iψJ_z}` in the spin-`j` representation (`j2 = 2j`); with `spinRotY` it is the
`T^{(j)}(g_b)` of arXiv:quant-ph/0411133v3, Sec. II, p. 2–3, for a Bloch direction with azimuth `ψ` (the paper has `ψ = 0`). -/
noncomputable def spinRotZ (j2 : ℕ) (ψ : ℝ) : Matrix (Fin (j2 + 1)) (Fin (j2 + 1)) ℂ :=
  NormedSpace.exp ((-(ψ : ℂ) * Complex.I) • spinJz j2)

end QubitPhaseEst


