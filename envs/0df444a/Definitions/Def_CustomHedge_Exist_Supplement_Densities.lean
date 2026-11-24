-- Prove2me | Definitions.Def_CustomHedge_Exist_Supplement_Densities
-- name    : CustomHedge_Exist_Supplement_Densities
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:37:48.236898+00:00
-- url     : https://prove2.me/theorems/693f601e-b85a-4f49-a1b1-3bfd34e7ea45
-- title:
--   §3.3, p. 12 — joint density of (X, Y, I) on ℝ^{3N}, marginals, Q-densities, kernel k(x, ξ) and term Π^X_0(x) of the design integral equation
-- statement:
--   Let $X,Y,I$ take values in $\mathbb R^N$, and let $\mathbb Q=\frac{d\mathbb Q}{d\mathbb P}\cdot\mathbb P$ be the risk-neutral probability.
--
--   1. A **joint density** of $(X,Y,I)$ under $\mathbb P$ is a nonnegative Borel function $f_{XYI}$ on $\mathbb R^{3N}$ with $\mathbb P\big((X,Y,I)\in B\big)=\int_B f_{XYI}$ for every Borel $B$. Its **marginals** are
--   $$f_{XY}(x,y)=\int f_{XYI}(x,y,i)\,di,\quad f_{XI}(x,i)=\int f_{XYI}(x,y,i)\,dy,\quad f_X(x)=\iint f_{XYI}\,dy\,di,\quad f_I(i)=\iint f_{XYI}\,dx\,dy.$$
--   2. A function $g\ge0$ is a **density of the law of $Z$ under $\mu$** if $\mu(Z\in B)=\int_B g$ for every Borel $B$; $f^{\mathbb Q}_X,f^{\mathbb Q}_I$ denote densities of the laws of $X$ and $I$ under $\mathbb Q$.
--   3. The **integral kernel** of the design equation is
--   $$k(x,\xi)=\int_{\mathbb R^N}\frac{f_{XI}(x,i)}{f_X(x)f_I(i)}\,f_{XI}(\xi,i)\,di .$$
--   4. The **term** $\Pi^X_0(x)$ is
--   $$\Pi^X_0(x)=-\int\pi(x,y)\frac{f_{XY}(x,y)}{f_X(x)}dy+\int_{\mathbb R^{3N}}\pi(\xi,y)\frac{f_{XYI}(\xi,y,i)\,f_{XI}(x,i)}{f_X(x)f_I(i)}\,d\xi\,dy\,di-\frac{\varrho}{a}\Big(\frac{f^{\mathbb Q}_X(x)}{f_X(x)}-\int f^{\mathbb Q}_I(i)\frac{f_{XI}(x,i)}{f_X(x)f_I(i)}di\Big).$$
--
--   These are the data of the design integral equation (8) of Theorem 2: $k$ is the kernel of the operator $w\mapsto\mathbb E[\mathbb E[w(X)\mid\mathcal F_I]\mid X=x]$ and $\Pi^X_0(x)$ is the density form of $-\mathbb E[\mathcal K-\mathbb E[\mathcal K\mid\mathcal F_I]\mid X=x]$.
--
--   **Formalization Note** The second summand of $\Pi^X_0$ is written with $f_{XYI}(\xi,y,i)f_{XI}(x,i)$; formula (9) on p. 12 prints $f_{XI}(\xi,i)f_{XYI}(x,y,i)$, which is not the density form of $\mathbb E[\mathbb E[\pi\mid\mathcal F_I]\mid X=x]$ that the proof (p. ec25) derives it from; the companion formula (EC.30) is printed in the corrected pattern. Integrals are Lebesgue (Bochner) integrals over $\mathbb R^N$ with product Lebesgue measure, and divisions are Lean's total division ($t/0=0$); both conventions only matter on sets of probability zero under the laws involved. $\mathbb R^N$ is `Fin N → ℝ`.
-- source:
--   Guiotto & Roncoroni, Combined custom hedging: optimal design, noninsurable exposure, and operational risk management, manuscript OPRE-2019-01-058.R3 (Operations Research 2022), p. 12 (PDF 12), Theorem 2, kernel k and term (9); pp. ec25–ec26 (PDF 56–57), proof of Theorem 2 and (EC.30)

import Mathlib
import Definitions.Def_CustomHedge_Exist_Model

namespace CustomHedge.Exist.Supplement

open MeasureTheory ProbabilityTheory

/-- `ℝ^N`, with the product Lebesgue measure as `volume`. -/
abbrev Rn (N : ℕ) := Fin N → ℝ

variable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}

/-- The risk-neutral probability `Q = (dQ/dP) · P`. -/
noncomputable def Qmeas {EX EY EI : Type*} [MeasurableSpace EX] [MeasurableSpace EY]
    [MeasurableSpace EI] (M : Market Ω EX EY EI) : Measure Ω :=
  M.P.withDensity (fun ω => ENNReal.ofReal (M.D ω))

/-- `f` is a joint distribution density of `(X, Y, I)` under `P` on `ℝ^{3N}`: a nonnegative
Borel function with `P ∘ (X, Y, I)⁻¹ = f · Lebesgue`. -/
def IsJointDensity (M : Market Ω (Rn N) (Rn N) (Rn N)) (f : Rn N → Rn N → Rn N → ℝ) : Prop :=
  Measurable (fun z : Rn N × Rn N × Rn N => f z.1 z.2.1 z.2.2) ∧ (∀ x y i, 0 ≤ f x y i) ∧
    M.P.map (fun ω => (M.X ω, M.Y ω, M.I ω)) =
      volume.withDensity (fun z : Rn N × Rn N × Rn N => ENNReal.ofReal (f z.1 z.2.1 z.2.2))

/-- `g` is a density of the law of `Z` under `μ`: nonnegative, Borel, `μ ∘ Z⁻¹ = g · Lebesgue`. -/
def IsLawDensity (μ : Measure Ω) (Z : Ω → Rn N) (g : Rn N → ℝ) : Prop :=
  Measurable g ∧ (∀ x, 0 ≤ g x) ∧ μ.map Z = volume.withDensity (fun x => ENNReal.ofReal (g x))

/-- Marginal density `f_XY(x, y) = ∫ f_XYI(x, y, i) di`. -/
noncomputable def fXY (f : Rn N → Rn N → Rn N → ℝ) (x y : Rn N) : ℝ := ∫ i, f x y i

/-- Marginal density `f_XI(x, i) = ∫ f_XYI(x, y, i) dy`. -/
noncomputable def fXI (f : Rn N → Rn N → Rn N → ℝ) (x i : Rn N) : ℝ := ∫ y, f x y i

/-- Marginal density `f_X(x) = ∫∫ f_XYI(x, y, i) dy di`. -/
noncomputable def fX (f : Rn N → Rn N → Rn N → ℝ) (x : Rn N) : ℝ :=
  ∫ p : Rn N × Rn N, f x p.1 p.2

/-- Marginal density `f_I(i) = ∫∫ f_XYI(x, y, i) dx dy`. -/
noncomputable def fI (f : Rn N → Rn N → Rn N → ℝ) (i : Rn N) : ℝ :=
  ∫ p : Rn N × Rn N, f p.1 p.2 i

/-- The integral kernel of (8):
`k(x, ξ) = ∫ [f_XI(x, i) / (f_X(x) f_I(i))] f_XI(ξ, i) di`. -/
noncomputable def kernel (f : Rn N → Rn N → Rn N → ℝ) (x ξ : Rn N) : ℝ :=
  ∫ i, fXI f x i / (fX f x * fI f i) * fXI f ξ i

/-- The term `Π^X_0(x)` of (9) (second summand in the form obtained by writing
`E[E[π | 𝓕_I] | X = x]` with densities; see the item's note):
`Π^X_0(x) = -∫ π(x,y) f_XY(x,y)/f_X(x) dy
  + ∫ π(ξ,y) f_XYI(ξ,y,i) f_XI(x,i) / (f_X(x) f_I(i)) dξ dy di
  - (ϱ/a) (f^Q_X(x)/f_X(x) - ∫ f^Q_I(i) f_XI(x,i) / (f_X(x) f_I(i)) di)`. -/
noncomputable def Pi0Xfun (M : Market Ω (Rn N) (Rn N) (Rn N)) (f : Rn N → Rn N → Rn N → ℝ)
    (fQX fQI : Rn N → ℝ) (x : Rn N) : ℝ :=
  -(∫ y, M.revenue x y * fXY f x y / fX f x)
    + (∫ z : Rn N × Rn N × Rn N,
        M.revenue z.1 z.2.1 * (f z.1 z.2.1 z.2.2 * fXI f x z.2.2) / (fX f x * fI f z.2.2))
    - M.rho / M.a * (fQX x / fX f x - ∫ i, fQI i * fXI f x i / (fX f x * fI f i))

end CustomHedge.Exist.Supplement


