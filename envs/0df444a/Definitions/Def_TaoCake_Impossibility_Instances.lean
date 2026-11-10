-- Prove2me | Definitions.Def_TaoCake_Impossibility_Instances
-- name    : TaoCake_Impossibility_Instances
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:06:40.596987+00:00
-- url     : https://prove2.me/theorems/e17b0341-11b5-4365-bf64-24f8f69a91e9
-- title:
--   §3 — the six instances F¹–F⁶ and the sets X₁, X₂ (Def. 3.2) and X₁₁, X₁₂, X₂₁, X₂₂ (Def. 3.5), built from a mechanism M and ε
-- statement:
--   The six instances of Section 3 (pp. 4–8, Table 1), constructed from a mechanism $M$ and a real $\varepsilon$.
--
--   1. **Instance 1** (p. 4): $F^1 = (f^1_1, f^1_2)$ with $f^1_1 \equiv f^1_2 \equiv 1$.
--   2. **Definition 3.2** (p. 4): $X_1 = M_1(F^1)$, $X_2 = M_2(F^1)$.
--   3. **Instance 2** (p. 4): $F^2 = (1, f^2_2)$, $f^2_2 = \varepsilon$ on $X_1$, $1$ on $X_2$.
--   4. **Instance 3** (p. 6): $F^3 = (f^3_1, f^3_2)$, $f^3_1 = 0.5$ on $X_1$, $1$ on $X_2$; $f^3_2 = f^2_2$.
--   5. **Definition 3.5** (p. 7): $X_{11} = M_1(F^3) \cap X_1$, $X_{12} = M_2(F^3) \cap X_1$, $X_{21} = M_1(F^3) \cap X_2$, $X_{22} = M_2(F^3) \cap X_2$.
--   6. **Instance 4** (p. 7): $F^4 = (f^4_1, f^4_2)$, $f^4_1 = 1, \varepsilon, 2\varepsilon, \varepsilon$ on $X_{11}, X_{12}, X_{21}, X_{22}$ respectively; $f^4_2 = f^2_2$.
--   7. **Instance 5** (p. 7): $F^5 = (1, f^5_2)$, $f^5_2 = 1-\varepsilon$ on $X_{11}$, $\varepsilon$ on $X_{12}$, $1$ on $X_2$.
--   8. **Instance 6** (p. 8): $F^6 = (f^6_1, f^6_2) = (f^4_1, f^5_2)$ (the paper prints the same case formulas again).
--
--   **Formalization Note** Definitions 3.2 and 3.5 are printed with length bars, $X_1 = |M_1(F^1)|$ and $X_{11} = |M_1(F^3) \cap X_1|$; the sets are meant (insight I1), and the sets are defined here. Each density lists its cases in the paper's order and the first matching case wins; a point in none of the listed sets (unallocated residue) gets the value $\varepsilon$, a choice the paper does not make because it tacitly assumes the listed sets cover $[0,1]$. Nothing is assumed about the instances: in particular they are not asserted to be piecewise-constant (insight I3), and $M$ is evaluated on them as a raw function.
-- source:
--   Biaoshuai Tao, On Existence of Truthful Fair Cake Cutting Mechanisms, arXiv:2104.07387v1, pp. 4–8 (PDF 4–8), Instances 1–6, Definitions 3.2 and 3.5, Table 1

import Mathlib
import Definitions.Def_TaoCake_Impossibility_Model

open MeasureTheory

namespace TaoCake.Impossibility

/-! # The six instances of §3 (arXiv:2104.07387v1, pp. 4–8, Table 1 on p. 5)

All objects depend on the mechanism `M` (through its outputs) and on the real `ε`. A density
built on output sets of `M` is defined branch by branch in the order the paper lists its cases
(first matching branch wins); a point lying in none of the listed sets gets the value `ε`. -/

/-- Instance 1 (p. 4): `F¹ = (f¹₁, f¹₂)` with `f¹₁(x) = f¹₂(x) = 1`. -/
def profile1 : Profile := ![fun _ => 1, fun _ => 1]

/-- Definition 3.2 (p. 4), set reading: `X₁ = M₁(F¹)`. -/
def X1 (M : Mechanism) : Set ℝ := M profile1 0

/-- Definition 3.2 (p. 4), set reading: `X₂ = M₂(F¹)`. -/
def X2 (M : Mechanism) : Set ℝ := M profile1 1

/-- `f²₂ = f³₂ = f⁴₂` (pp. 4, 6, 7): `ε` on `X₁`, `1` on `X₂`; `ε` elsewhere. -/
noncomputable def f22 (M : Mechanism) (ε : ℝ) : ℝ → ℝ := fun x =>
  open Classical in
  if x ∈ X1 M then ε else if x ∈ X2 M then 1 else ε

/-- Instance 2 (p. 4): `F² = (f²₁, f²₂)` with `f²₁ ≡ 1`. -/
noncomputable def profile2 (M : Mechanism) (ε : ℝ) : Profile := ![fun _ => 1, f22 M ε]

/-- `f³₁` (p. 6): `0.5` on `X₁`, `1` on `X₂`; `ε` elsewhere. -/
noncomputable def f13 (M : Mechanism) (ε : ℝ) : ℝ → ℝ := fun x =>
  open Classical in
  if x ∈ X1 M then 1 / 2 else if x ∈ X2 M then 1 else ε

/-- Instance 3 (p. 6): `F³ = (f³₁, f³₂)` with `f³₂ = f²₂`. -/
noncomputable def profile3 (M : Mechanism) (ε : ℝ) : Profile := ![f13 M ε, f22 M ε]

/-- Definition 3.5 (p. 7), set reading: `X₁₁ = M₁(F³) ∩ X₁`. -/
def X11 (M : Mechanism) (ε : ℝ) : Set ℝ := M (profile3 M ε) 0 ∩ X1 M

/-- Definition 3.5 (p. 7), set reading: `X₁₂ = M₂(F³) ∩ X₁`. -/
def X12 (M : Mechanism) (ε : ℝ) : Set ℝ := M (profile3 M ε) 1 ∩ X1 M

/-- Definition 3.5 (p. 7), set reading: `X₂₁ = M₁(F³) ∩ X₂`. -/
def X21 (M : Mechanism) (ε : ℝ) : Set ℝ := M (profile3 M ε) 0 ∩ X2 M

/-- Definition 3.5 (p. 7), set reading: `X₂₂ = M₂(F³) ∩ X₂`. -/
def X22 (M : Mechanism) (ε : ℝ) : Set ℝ := M (profile3 M ε) 1 ∩ X2 M

/-- `f⁴₁ = f⁶₁` (pp. 7, 8): `1` on `X₁₁`, `ε` on `X₁₂`, `2ε` on `X₂₁`, `ε` on `X₂₂`;
`ε` elsewhere. -/
noncomputable def f14 (M : Mechanism) (ε : ℝ) : ℝ → ℝ := fun x =>
  open Classical in
  if x ∈ X11 M ε then 1 else if x ∈ X12 M ε then ε else if x ∈ X21 M ε then 2 * ε
  else if x ∈ X22 M ε then ε else ε

/-- Instance 4 (p. 7): `F⁴ = (f⁴₁, f⁴₂)` with `f⁴₂ = f²₂`. -/
noncomputable def profile4 (M : Mechanism) (ε : ℝ) : Profile := ![f14 M ε, f22 M ε]

/-- `f⁵₂ = f⁶₂` (pp. 7, 8): `1 − ε` on `X₁₁`, `ε` on `X₁₂`, `1` on `X₂`; `ε` elsewhere. -/
noncomputable def f25 (M : Mechanism) (ε : ℝ) : ℝ → ℝ := fun x =>
  open Classical in
  if x ∈ X11 M ε then 1 - ε else if x ∈ X12 M ε then ε else if x ∈ X2 M then 1 else ε

/-- Instance 5 (p. 7): `F⁵ = (f⁵₁, f⁵₂)` with `f⁵₁ ≡ 1`. -/
noncomputable def profile5 (M : Mechanism) (ε : ℝ) : Profile := ![fun _ => 1, f25 M ε]

/-- Instance 6 (p. 8): `F⁶ = (f⁶₁, f⁶₂) = (f⁴₁, f⁵₂)`. -/
noncomputable def profile6 (M : Mechanism) (ε : ℝ) : Profile := ![f14 M ε, f25 M ε]

end TaoCake.Impossibility


