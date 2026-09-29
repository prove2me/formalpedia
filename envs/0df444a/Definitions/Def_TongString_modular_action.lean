-- Prove2me | Definitions.Def_TongString_modular_action
-- name    : TongString_modular_action
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T20:52:23.219049+00:00
-- url     : https://prove2.me/theorems/36caf2cd-b699-443f-b66f-5290dc89a9d7
-- title:
--   Modular transformations $\tau\mapsto\frac{a\tau+b}{c\tau+d}$, the generators $S,T$, and the measure $d^2\tau/(\operatorname{Im}\tau)^2$
-- statement:
--   1. For integers $a,b,c,d$ the **modular transformation** is the map $\tau\mapsto\dfrac{a\tau+b}{c\tau+d}$ of eq. (6.19); it is a modular transformation in Tong's sense when $ad-bc=1$.
--   2. The generators are $S=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$, acting as $\tau\mapsto-1/\tau$, and $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$, acting as $\tau\mapsto\tau+1$, viewed as elements of $SL(2,\mathbb Z)$.
--   3. The **modular-invariant measure** is $\dfrac{d^2\tau}{(\operatorname{Im}\tau)^2}$ on the upper half-plane $\mathbb H=\{\operatorname{Im}\tau>0\}$, i.e. the measure with density $(\operatorname{Im}\tau)^{-2}$ against Lebesgue measure on $\mathbb H$.
--
--   These are the objects in terms of which Tong describes the moduli space of the torus and the one-loop integration measure.
--
--   **Formalization Note** The measure is a measure on all of $\mathbb C$ that gives zero mass to $\{\operatorname{Im}\tau\le0\}$. Complex division by $0$ returns $0$ in Lean; this only happens at $\tau=-d/c$, which is not in $\mathbb H$ when $ad-bc=1$.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 6.4.1, pp. 146–147 (S, T, eq. (6.19), the measure d²τ/(Im τ)²)

import Mathlib

namespace TongString

open MeasureTheory

/-- The modular transformation `τ ↦ (aτ + b)/(cτ + d)` of eq. (6.19). -/
noncomputable def modularAction (a b c d : ℤ) (τ : ℂ) : ℂ :=
  (a * τ + b) / (c * τ + d)

/-- The matrix of `S : τ ↦ -1/τ`. -/
def modularS : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![0, -1; 1, 0], by decide⟩

/-- The matrix of `T : τ ↦ τ + 1`. -/
def modularT : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![1, 1; 0, 1], by decide⟩

/-- The measure `d²τ / (Im τ)²` on the upper half-plane, as a measure on `ℂ`:
Lebesgue measure restricted to `{Im τ > 0}` with density `(Im τ)⁻²`. -/
noncomputable def modularMeasure : Measure ℂ :=
  (volume.restrict {τ : ℂ | 0 < τ.im}).withDensity (fun τ => ENNReal.ofReal (1 / τ.im ^ 2))

end TongString


