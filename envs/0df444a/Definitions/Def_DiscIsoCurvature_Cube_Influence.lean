-- Prove2me | Definitions.Def_DiscIsoCurvature_Cube_Influence
-- name    : DiscIsoCurvature_Cube_Influence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:07:37.228974+00:00
-- url     : https://prove2.me/theorems/253f2758-f4d8-4446-9487-8330f23e1e7a
-- title:
--   Boolean functions, sensitivity, and the influences, surface area and squared influence of §1.1 under a distribution µ
-- statement:
--   Let $\mu$ be a distribution on $\{\pm1\}^n$. A **Boolean function** is $f:\{\pm1\}^n\to\{\pm1\}$, encoded as a real function taking only the values $1$ and $-1$. With $x$ drawn from $\mu$ and $x^i$ the flipped point:
--
--   - the **pointwise sensitivity** is $s(f)(x)=\sum_{i=1}^n\mathbf 1\{f(x^i)\ne f(x)\}$;
--   - the **influence** of coordinate $i$ is $\mathrm{Inf}_{\mu,i}(f)=\Pr_{x\sim\mu}[f(x^i)\ne f(x)]$;
--   - the **total influence** is $\mathrm{Inf}_\mu(f)=\sum_i\mathrm{Inf}_{\mu,i}(f)$;
--   - the **surface area** is $\mathrm{SA}_\mu(f)=\mathbb E_\mu[\sqrt{s(f)}]$;
--   - the **total squared influence** is $\mathrm{SqInf}_\mu(f)=\sum_i\mathrm{Inf}_{\mu,i}(f)^2$.
--
--   $$\mathrm{Inf}_{\mu,i}(f)=\sum_x\mu(x)\,\mathbf 1\{f(x^i)\ne f(x)\},\qquad \mathrm{SA}_\mu(f)=\sum_x\mu(x)\sqrt{s(f)(x)}.$$
--
--   These are the four boundary measures of Theorem 1.1. Under the uniform measure they are the classical ones; here $\mu$ may be any distribution, so they are not Fourier quantities.
--
--   **Formalization Note.** The quantities are defined for every real function $f$; they are used for Boolean $f$ only.
-- source:
--   Chen, Chen, Zhang, Discrete Isoperimetric Inequalities via Curvature, arXiv:2609.24687 (version of November 3, 2026, sha256 ec30d304…), pp. 1–2, §1.1

import Mathlib
import Definitions.Def_DiscIsoCurvature_Cube_Basic

namespace DiscIsoCurvature.Cube

/-!
# Boolean functions, sensitivity, influences, surface area and squared influence under `μ`

Chen, Chen, Zhang, *Discrete Isoperimetric Inequalities via Curvature*, arXiv:2609.24687
(version of November 3, 2026, sha256 ec30d304…), §1.1, pp. 1–2.

All quantities are with respect to the (possibly non-uniform) distribution `μ` on the cube: the
point `x` is drawn from `μ`, and `x^i = flip x i` is the flipped point. Boolean functions
`{±1}^n → {±1}` are real-valued functions taking only the values `1` and `-1`.
-/

/-- `f : {±1}^n → {±1}`: `f` takes only the values `1` and `-1`. -/
def IsBoolean {n : ℕ} (f : BoolCube n → ℝ) : Prop :=
  ∀ x, f x = 1 ∨ f x = -1

/-- Pointwise sensitivity `s(f)(x) = ∑ᵢ 1{f(x^i) ≠ f(x)}` (§1.1, p. 1). -/
noncomputable def sensitivity {n : ℕ} (f : BoolCube n → ℝ) (x : BoolCube n) : ℝ :=
  ∑ i, if f (flip x i) ≠ f x then 1 else 0

/-- Influence of coordinate `i`: `Inf_{μ,i}(f) = Pr_{x∼μ}[f(x^i) ≠ f(x)]` (§1.1 (1), p. 1). -/
noncomputable def influence {n : ℕ} (μ : BoolCube n → ℝ) (f : BoolCube n → ℝ) (i : Fin n) : ℝ :=
  expect μ (fun x => if f (flip x i) ≠ f x then 1 else 0)

/-- Total influence `Inf_μ(f) = ∑ᵢ Inf_{μ,i}(f)` (§1.1 (2), p. 1). -/
noncomputable def totalInfluence {n : ℕ} (μ : BoolCube n → ℝ) (f : BoolCube n → ℝ) : ℝ :=
  ∑ i, influence μ f i

/-- Surface area (Talagrand boundary) `SA_μ(f) = E_μ[√(s(f))]` (§1.1 (3), p. 2). -/
noncomputable def surfaceArea {n : ℕ} (μ : BoolCube n → ℝ) (f : BoolCube n → ℝ) : ℝ :=
  expect μ (fun x => Real.sqrt (sensitivity f x))

/-- Total squared influence `SqInf_μ(f) = ∑ᵢ Inf_{μ,i}(f)²` (§1.1 (4), p. 2). -/
noncomputable def sqInfluence {n : ℕ} (μ : BoolCube n → ℝ) (f : BoolCube n → ℝ) : ℝ :=
  ∑ i, influence μ f i ^ 2

end DiscIsoCurvature.Cube


