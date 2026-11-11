-- Prove2me | Definitions.Def_MixedVolFPRAS_Main_Sphere
-- name    : MixedVolFPRAS_Main_Sphere
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:29:41.645125+00:00
-- url     : https://prove2.me/theorems/eca746ab-fd3c-40b8-bd72-b1475034420d
-- title:
--   Surface measure ω, spherical gradient (Definition C.1), C² and smooth functions on Sⁿ⁻¹, geodesic distance
-- statement:
--   $\omega$ is the **surface measure** on $S^{n-1}$, normalized so that $\omega(S^{n-1})=n\,\mathrm{Vol}_n(B_2^n)$. Functions on the sphere are written as functions on $\mathbb{R}^n$ of which only the values on $S^{n-1}$ matter.
--
--   **Spherical gradient** (Definition C.1). $f$ is differentiable on the sphere at $\theta\in S^{n-1}$ with gradient $g$ if $\langle g,\theta\rangle=0$ and for every $\varepsilon>0$ there is $\delta>0$ with
--
--   $$|f(v)-f(\theta)-\langle g,v-\theta\rangle|\le\varepsilon\|v-\theta\|_2\quad\text{for all }v\in S^{n-1},\ \|v-\theta\|_2<\delta;$$
--
--   then $\nabla_{S^{n-1}}f(\theta)=g$ (unique).
--
--   $f\in C^2(S^{n-1})$ means that the 1-homogeneous extension $F(x)=\|x\|_2\,f(x/\|x\|_2)$ is $C^2$ on $\mathbb{R}^n\setminus\{0\}$ (footnote 3, p. 13); $f$ is **smooth** on the sphere when $F$ is $C^\infty$ there. The geodesic distance is $d(x,y)=\arccos\langle x,y\rangle$.
--
--   **Formalization Note.** `Sph n` is the subtype `Metric.sphere (0 : E n) 1`; `surfaceMeasure n = volume.toSphere` (Mathlib), whose total mass is $n\,\mathrm{Vol}_n(B_2^n)$, the usual surface area. `IsSphGradAt f θ g` is Definition C.1; `sphGrad f θ` is the gradient when it exists and $0$ otherwise (every item that bounds a gradient either asserts existence or applies it to functions that are differentiable on the sphere). `homogExt`, `IsC2OnSphere`, `IsSmoothOnSphere`, `geodesicDist` are as above.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 8 (ω, geodesic distance); p. 13, footnote 3; p. 40, Definition C.1

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_ConvexGeometry

open scoped ContDiff

noncomputable section

namespace MixedVolFPRAS.Main

/-!
# Calculus and measure on the sphere `Sⁿ⁻¹`

Chen, Liu, *An FPRAS for Mixed Volumes*, p. 8 (ω, geodesic distance), p. 12 (§2.4),
p. 13 (footnote 3) and p. 40 (Definition C.1).

* `Sph n` is the unit sphere as a type; `surfaceMeasure n` is the surface measure `ω` on it
  (Mathlib's `volume.toSphere`, with `ω(Sⁿ⁻¹) = n · Volₙ(B₂ⁿ)`).
* Functions on the sphere are written as functions `f : ℝⁿ → ℝ`; only their values on `Sⁿ⁻¹`
  matter in what follows.
* `IsSphGradAt f θ g` is Definition C.1: `⟨g, θ⟩ = 0` and
  `|f(v) − f(θ) − ⟨g, v − θ⟩| ≤ ε‖v − θ‖` for `v ∈ Sⁿ⁻¹` near `θ`. `sphGrad f θ` is that `g`
  when it exists (and `0` otherwise).
* `homogExt f x = ‖x‖ f(x/‖x‖)` is the 1-homogeneous extension; `f ∈ C²(Sⁿ⁻¹)` means
  `homogExt f` is `C²` on `ℝⁿ \ {0}` (footnote 3, p. 13), and `f` is smooth on the sphere when it
  is `C^∞` there.
* `geodesicDist x y = arccos ⟨x, y⟩`.
-/

/-- The unit sphere `Sⁿ⁻¹` as a type. -/
abbrev Sph (n : ℕ) : Type := Metric.sphere (0 : E n) 1

/-- The surface measure `ω` on `Sⁿ⁻¹`. -/
def surfaceMeasure (n : ℕ) : MeasureTheory.Measure (Sph n) :=
  (MeasureTheory.volume : MeasureTheory.Measure (E n)).toSphere

/-- Definition C.1: `g` is the spherical gradient of `f` at `θ`. -/
def IsSphGradAt {n : ℕ} (f : E n → ℝ) (θ g : E n) : Prop :=
  inner ℝ g θ = 0 ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ unitSphere n, ‖v - θ‖ < δ →
      |f v - f θ - inner ℝ g (v - θ)| ≤ ε * ‖v - θ‖

open Classical in
/-- The spherical gradient `∇_{Sⁿ⁻¹} f(θ)` (Definition C.1), `0` where it does not exist. -/
def sphGrad {n : ℕ} (f : E n → ℝ) (θ : E n) : E n :=
  if h : ∃ g, IsSphGradAt f θ g then h.choose else 0

/-- The 1-homogeneous extension `F(x) = ‖x‖ f(x/‖x‖)`. -/
def homogExt {n : ℕ} (f : E n → ℝ) (x : E n) : ℝ := ‖x‖ * f (‖x‖⁻¹ • x)

/-- `f ∈ C²(Sⁿ⁻¹)`: its 1-homogeneous extension is `C²` on `ℝⁿ \ {0}`. -/
def IsC2OnSphere {n : ℕ} (f : E n → ℝ) : Prop :=
  ContDiffOn ℝ 2 (homogExt f) {0}ᶜ

/-- `f` is smooth on `Sⁿ⁻¹`: its 1-homogeneous extension is `C^∞` on `ℝⁿ \ {0}`. -/
def IsSmoothOnSphere {n : ℕ} (f : E n → ℝ) : Prop :=
  ContDiffOn ℝ ∞ (homogExt f) {0}ᶜ

/-- The geodesic distance `d(x, y) = arccos ⟨x, y⟩` on the sphere. -/
def geodesicDist {n : ℕ} (x y : E n) : ℝ := Real.arccos (inner ℝ x y)

end MixedVolFPRAS.Main


