-- Prove2me | Definitions.Def_ElectroweakWiki_defs
-- name    : ElectroweakWiki_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-27T19:30:20.761177+00:00
-- url     : https://prove2.me/theorems/04f81704-6ae3-48c2-b3d3-10c7f1e7f12a
-- title:
--   Electroweak interaction (Wikipedia): basic objects
-- statement:
--   This file sets up the objects used throughout the mission, following the Wikipedia article *Electroweak interaction*.
--
--   1. **Weak mixing angle** $\theta_W(g,g') = \arctan(g'/g)$, and the **electromagnetic coupling** $e(g,g') = gg'/\sqrt{g^2+g'^2}$ (the altitude of the Weinberg triangle).
--   2. **Neutral physical fields** $\gamma(\theta,B,W_3) = \cos\theta\,B + \sin\theta\,W_3$ and $Z^0(\theta,B,W_3) = -\sin\theta\,B+\cos\theta\,W_3$.
--   3. **Charged fields** $W^\pm(W_1,W_2) = (W_1 \mp iW_2)/\sqrt2 \in \mathbb C$.
--   4. **Tree-level masses** $m_W(g,v) = gv/2$ and $m_Z(g,g',v) = \sqrt{g^2+g'^2}\,v/2$.
--   5. **Pauli matrices** $\sigma_1 = \begin{pmatrix}0&1\\1&0\end{pmatrix}$, $\sigma_2 = \begin{pmatrix}0&-i\\i&0\end{pmatrix}$, $\sigma_3 = \begin{pmatrix}1&0\\0&-1\end{pmatrix}$ (Lean indices $0,1,2$).
--   6. **Gauge part of the covariant derivative** on a doublet of hypercharge $Y$, with the factor $-i$ removed:
--   $$M(g,g',Y,B,W_1,W_2,W_3) = \tfrac{g'}{2}YB\,\mathbb 1 + \tfrac g2\,(W_1\sigma_1+W_2\sigma_2+W_3\sigma_3).$$
--   7. **Higgs vacuum** $h_0(v) = (0, v/\sqrt2)\in\mathbb C^2$, the **squared doublet norm** $|h|^2 = |h_1|^2+|h_2|^2$, and the **Higgs potential** $V_{\lambda,v}(h) = \lambda(|h|^2 - v^2/2)^2$.
--   8. **Electric charge** $Q(T_3,Y) = T_3 + Y/2$, and the generator $\tfrac a2\sigma_3 + \tfrac b2\mathbb 1$, which is $aT_3 + bY/2$ acting on the Higgs doublet ($T_3=\sigma_3/2$, $Y=1$).
--
--   **Formalization Note** The article writes $D_\mu = \partial_\mu - i\frac{g'}{2}YB_\mu - i\frac g2 T_jW^j_\mu$; because the factor $\frac12$ is written out, $T_j$ is taken to be the Pauli matrix $\sigma_j$. Fields are real numbers at a single point and Lorentz index.
-- source:
--   Wikipedia, "Electroweak interaction", revision oldid=1360331872, https://en.wikipedia.org/w/index.php?title=Electroweak_interaction&oldid=1360331872; sections Formulation and Lagrangian (pp. 2–5 of the PDF)

import Mathlib

namespace ElectroweakWiki

open Complex

/-- The weak mixing (Weinberg) angle `θ_W`, fixed by `tan θ_W = g' / g`. -/
noncomputable def weinbergAngle (g g' : ℝ) : ℝ := Real.arctan (g' / g)

/-- The electromagnetic coupling read off the Weinberg triangle: `e = g g' / √(g² + g'²)`. -/
noncomputable def elemCharge (g g' : ℝ) : ℝ := g * g' / Real.sqrt (g ^ 2 + g' ^ 2)

/-- Photon field component `γ = cos θ · B + sin θ · W₃`. -/
noncomputable def photonField (θ B W3 : ℝ) : ℝ := Real.cos θ * B + Real.sin θ * W3

/-- Z-boson field component `Z⁰ = -sin θ · B + cos θ · W₃`. -/
noncomputable def zField (θ B W3 : ℝ) : ℝ := -Real.sin θ * B + Real.cos θ * W3

/-- Charged boson `W⁺ = (W₁ - i W₂) / √2`. -/
noncomputable def wPlus (W1 W2 : ℝ) : ℂ := ((W1 : ℂ) - I * (W2 : ℂ)) / (Real.sqrt 2 : ℂ)

/-- Charged boson `W⁻ = (W₁ + i W₂) / √2`. -/
noncomputable def wMinus (W1 W2 : ℝ) : ℂ := ((W1 : ℂ) + I * (W2 : ℂ)) / (Real.sqrt 2 : ℂ)

/-- Tree-level W mass `m_W = g v / 2`. -/
noncomputable def wMass (g v : ℝ) : ℝ := g * v / 2

/-- Tree-level Z mass `m_Z = √(g² + g'²) v / 2`. -/
noncomputable def zMass (g g' v : ℝ) : ℝ := Real.sqrt (g ^ 2 + g' ^ 2) * v / 2

/-- The Pauli matrices `σ₁, σ₂, σ₃` (indexed by `0, 1, 2`). -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -I; I, 0]
  | 2 => !![1, 0; 0, -1]

/-- The gauge-field part of the covariant derivative on a weak-isospin doublet of
hypercharge `Y`, with the factor `-i` stripped:
`(g'/2) Y B · 𝟙 + (g/2) (W¹ σ₁ + W² σ₂ + W³ σ₃)`. -/
noncomputable def gaugeTerm (g g' Y B W1 W2 W3 : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((g' / 2 * Y * B : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    ((g / 2 : ℝ) : ℂ) • ((W1 : ℂ) • pauli 0 + (W2 : ℂ) • pauli 1 + (W3 : ℂ) • pauli 2)

/-- The Higgs vacuum doublet `h₀ = (0, v / √2)`. -/
noncomputable def higgsVacuum (v : ℝ) : Fin 2 → ℂ := ![0, ((v / Real.sqrt 2 : ℝ) : ℂ)]

/-- Squared Hermitian norm `|h|² = |h₁|² + |h₂|²` of a doublet. -/
noncomputable def doubletNormSq (h : Fin 2 → ℂ) : ℝ := Complex.normSq (h 0) + Complex.normSq (h 1)

/-- The Higgs potential `λ (|h|² - v²/2)²`. -/
noncomputable def higgsPotential (lam v : ℝ) (h : Fin 2 → ℂ) : ℝ :=
  lam * (doubletNormSq h - v ^ 2 / 2) ^ 2

/-- Electric charge `Q = T₃ + Y / 2` of a state with isospin component `T₃` and hypercharge `Y`. -/
noncomputable def electricCharge (T3 Y : ℝ) : ℝ := T3 + Y / 2

/-- The generator `a T₃ + b Y / 2` acting on the Higgs doublet (hypercharge `Y = 1`),
with `T₃ = σ₃ / 2`: the matrix `(a/2) σ₃ + (b/2) 𝟙`. -/
noncomputable def isospinHyperchargeGenerator (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((a / 2 : ℝ) : ℂ) • pauli 2 + ((b / 2 : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

end ElectroweakWiki


