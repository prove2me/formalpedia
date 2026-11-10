-- Prove2me | Definitions.Def_DistRobustHalfspace_Main_Estimators
-- name    : DistRobustHalfspace_Main_Estimators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:17:29.782527+00:00
-- url     : https://prove2.me/theorems/5486bc4c-cc4e-4621-8773-dace47c1bfad
-- title:
--   §2 objects: T_ε, R_ε, B, truncation, τ, E[ṽ(t̂)], ξ-good estimates, ℓ_f, α_f, ℓ_{f,N}, α̂_{f,N}, F_ε, DD, whittling, B-typicality, spectral quantities
-- statement:
--   The objects of §2 (pp. 11–18) of the paper.
--
--   **Thresholds** (p. 12): $T_\varepsilon=2\sqrt{\log(1/\varepsilon)}$, $R_\varepsilon=5\sqrt{\log(1/\varepsilon)}$ (natural log), $B=B_{n,\varepsilon}=n^{1/4}/\varepsilon$. **Truncation** (p. 11): $\operatorname{trunc}_{\pm T}(a)=\operatorname{sign}(a)\min\{T,|a|\}$, applied to extended reals so that $\operatorname{trunc}_{\pm T}(\mp\infty)=\mp T$ (`truncE`).
--
--   **Normal vector estimator** (p. 12, Def. 2.3): $\tau(t)=\mathbb E_{g\sim\mathcal N(0,1)}[g\,\operatorname{sign}(g-t)]$ (`tau`, $=2\phi(t)$). `meanNormalEst f t̂` is $\mathbb E[\tilde v(\hat t)]=\mathbb E_{x\sim\mathcal N(0,I_n)}[x f(x)]/\tau(\hat t)$. **Definition 2.4**: $\hat t$ is a $\xi$-good threshold estimate for $f$ when $f(x)=\operatorname{sign}(\langle x,v\rangle-t)$ with $\|v\|=1$ and $|t-\hat t|\le\xi$ (`IsGoodThreshold`).
--
--   **Local uniformity** (Def. 2.8, p. 14): $\ell_f(y)=\Pr_{g\sim\mathcal N(0,I_n)}[f(y+g)=f(y)]$ and $\alpha_f(y)=\Phi^{-1}(\ell_f(y))\in[-\infty,\infty]$. Here $\Phi^{-1}$ is the published `Cohen2019.Robust.PhiInv`, with $\Phi^{-1}(0)=-\infty$ and $\Phi^{-1}(1)=+\infty$. $F_\varepsilon=\operatorname{trunc}_{\pm R_\varepsilon}\circ\Phi^{-1}$ (p. 28). For a neighborhood tuple $N=(g_1,\dots,g_p)$ (Def. 2.13, p. 17), $\ell_{f,N}(y)=\frac1p\sum_i\mathbf 1[f(y+g_i)=f(y)]$ and $\hat\alpha_{f,N}(y)=F_\varepsilon(\ell_{f,N}(y))$. `alphaHatOf` computes the same value from the numbers $f(y)$ and $f(y+g_i)$.
--
--   **Distance disagreement** (Def. 2.9, p. 15): $\mathrm{DD}^{\hat t}_\beta(f,D)=\mathbb E_{y\sim D}[(f(y)(\langle y,\mathbb E[\tilde v(\hat t)]\rangle-\hat t)-\beta(y))^2]\in[0,\infty]$.
--
--   **Whittling** (Defs. 2.14, 2.16, pp. 17–18): $G^{\hat t}_f(y)=\langle y,\mathbb E[\tilde v(\hat t)]\rangle$ (`bandDist`). $y$ is $B$-typical w.r.t. $(f,\hat t)$ if $\|y\|_2\le2\sqrt n$ and $|G^{\hat t}_f(y)|\le B$. The whittled distribution $D^{\hat t}_*$ is the law of $y\cdot\mathbf 1[y\text{ is }B\text{-typical}]$ for $y\sim D$ (`whittled`). A distribution is $B$-typical if the atypical points are null (`IsTypicalDist`). `SupportedInBall D` says the complement of the $2\sqrt n$-ball is null.
--
--   **Spectral quantities** (pp. 20, 22): $\mathbb E_{y\sim D}[yy^\top]$ (`secondMoment`), the Frobenius norm $\|M\|_F=(\sum_{ij}M_{ij}^2)^{1/2}$, and the weighted centroid $\mathbb E_{y\sim D}[f(y)\hat\alpha_{f,N}(y)\,y]$.
--
--   **Formalization Note.** $\mathrm{DD}$ is a lower Lebesgue integral of a nonnegative function. It is $+\infty$ when the integrand is not integrable, never a junk $0$. $\alpha_f$ is extended-real; the extension of $\Phi^{-1}$ at $0$ and $1$ is exactly the one Definition 2.12 uses. `secondMoment` and `weightedCentroid` are Bochner integrals. They are used only for distributions supported on the $2\sqrt n$-ball or equal to $\mathcal N(0,I_n)$, where the integrands are integrable. For $p=0$ the average $\ell_{f,N}$ divides by $0$; every statement assumes $p\ge1$.
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), §2, pp. 11–18 (PDF 13–20): §2.1 p. 11, thresholds p. 12, Definitions 2.3, 2.4, 2.8, 2.9, 2.12, 2.13, 2.14, 2.16; Lemmas 2.19, 2.20 pp. 20, 22; F_ε p. 28

import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi
import Definitions.Def_DistRobustHalfspace_Main_Testers

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- `T_ε = 2 √(log(1/ε))` (p. 12), natural logarithm. -/
noncomputable def Teps (ε : ℝ) : ℝ := 2 * Real.sqrt (Real.log (1 / ε))

/-- `R_ε = 5 √(log(1/ε))` (p. 12), natural logarithm. -/
noncomputable def Reps (ε : ℝ) : ℝ := 5 * Real.sqrt (Real.log (1 / ε))

/-- `B = B_{n,ε} = n^{1/4} / ε` (p. 12). -/
noncomputable def Bne (n : ℕ) (ε : ℝ) : ℝ := (n : ℝ) ^ ((1 : ℝ) / 4) / ε

/-- The truncation `trunc_{±T}(a) = sign(a) · min{T, |a|}` (p. 11), applied to an extended real
`a`, so that `trunc_{±T}(−∞) = −T` and `trunc_{±T}(+∞) = T` (Definition 2.12). For `T > 0` this is
`−T` if `a ≤ −T`, `T` if `a ≥ T`, and `a` otherwise. -/
noncomputable def truncE (T : ℝ) (a : EReal) : ℝ :=
  if a ≤ ((-T : ℝ) : EReal) then -T else if ((T : ℝ) : EReal) ≤ a then T else a.toReal

/-- `τ(t) = E_{g∼N(0,1)}[g · sign(g − t)]` (p. 12; closed form `2ϕ(t) = √(2/π) e^{−t²/2}`). -/
noncomputable def tau (t : ℝ) : ℝ := ∫ g, g * sgn (g - t) ∂(gaussianReal 0 1)

/-- `E[ṽ(t̂)]`, the mean of the normal vector estimator `ṽ(t̂) = x f(x)/τ(t̂)`, `x ∼ N(0, Iₙ)`
(Definition 2.3, p. 13): `E[ṽ(t̂)] = E_{x∼N(0,Iₙ)}[x f(x)] / τ(t̂)`. -/
noncomputable def meanNormalEst {n : ℕ} (f : Rn n → ℝ) (t : ℝ) : Rn n :=
  (tau t)⁻¹ • ∫ x, f x • x ∂(stdGaussian (Rn n))

/-- **Definition 2.4** (p. 13): `t̂` is a `ξ`-good threshold estimate for `f`: `f` is the halfspace
`f(x) = sign(⟨x, v⟩ − t)` with `v` a unit vector and `t ∈ ℝ` (this representation is unique), and
`|t − t̂| ≤ ξ`. -/
def IsGoodThreshold {n : ℕ} (f : Rn n → ℝ) (ξ t' : ℝ) : Prop :=
  ∃ (v : Rn n) (t : ℝ), ‖v‖ = 1 ∧ (∀ x, f x = sgn (⟪x, v⟫ - t)) ∧ |t - t'| ≤ ξ

/-- **Definition 2.8** (p. 14): the local uniformity `ℓ_f(y) = P_{g∼N(0,Iₙ)}[f(y + g) = f(y)]`. -/
noncomputable def localUnif {n : ℕ} (f : Rn n → ℝ) (y : Rn n) : ℝ :=
  ((stdGaussian (Rn n)) {g | f (y + g) = f y}).toReal

/-- **Definition 2.8** (p. 14): the local distance measure `α_f(y) = Φ⁻¹(ℓ_f(y))`, with
`Φ⁻¹(0) = −∞` and `Φ⁻¹(1) = +∞` (published `Cohen2019.Robust.PhiInv`, extended-real valued). -/
noncomputable def localDist {n : ℕ} (f : Rn n → ℝ) (y : Rn n) : EReal :=
  Cohen2019.Robust.PhiInv (localUnif f y)

/-- `F_ε = trunc_{±R_ε} ∘ Φ⁻¹` (p. 28), with `Φ⁻¹(0) = −∞`, `Φ⁻¹(1) = +∞`; it is used on `[0, 1]`. -/
noncomputable def Feps (ε : ℝ) (q : ℝ) : ℝ :=
  truncE (Reps ε) (Cohen2019.Robust.PhiInv q)

/-- The local distance estimate computed from the value `f(y)` and the `p` values `f(y + gᵢ)`:
`trunc_{±R_ε}(Φ⁻¹(ℓ))` with `ℓ = (1/p) · #{i : f(y + gᵢ) = f(y)}` (Definition 2.13). -/
noncomputable def alphaHatOf (ε : ℝ) {p : ℕ} (fy : ℝ) (fyg : Fin p → ℝ) : ℝ :=
  Feps ε (((Finset.univ.filter fun i => fyg i = fy).card : ℝ) / p)

/-- **Definition 2.13** (p. 17): the local uniformity estimate
`ℓ_{f,N}(y) = (1/p) Σᵢ 1[f(y + gᵢ) = f(y)]` for a neighborhood tuple `N = (g₁, …, g_p)`. -/
noncomputable def localUnifN {n p : ℕ} (f : Rn n → ℝ) (N : Fin p → Rn n) (y : Rn n) : ℝ :=
  ((Finset.univ.filter fun i => f (y + N i) = f y).card : ℝ) / p

/-- **Definition 2.13** (p. 17): the local distance estimate
`α̂_{f,N}(y) = trunc_{±R_ε}(Φ⁻¹(ℓ_{f,N}(y)))`. -/
noncomputable def alphaHat {n p : ℕ} (ε : ℝ) (f : Rn n → ℝ) (N : Fin p → Rn n) (y : Rn n) : ℝ :=
  alphaHatOf ε (f y) (fun i => f (y + N i))

/-- **Definition 2.9** (p. 15): the distance disagreement measure
`DD^{t̂}_β(f, D) = E_{y∼D}[(f(y)(⟨y, E[ṽ(t̂)]⟩ − t̂) − β(y))²]`, as a value in `[0, ∞]`
(the integrand is nonnegative; the value is `∞` when it is not integrable). -/
noncomputable def DD {n : ℕ} (β : Rn n → ℝ) (t : ℝ) (f : Rn n → ℝ) (D : Measure (Rn n)) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal ((f y * (⟪y, meanNormalEst f t⟫ - t) - β y) ^ 2) ∂D

/-- **Definition 2.14** (p. 17): the band-distance function `G^{t̂}_f(y) = ⟨y, E[ṽ(t̂)]⟩`. -/
noncomputable def bandDist {n : ℕ} (f : Rn n → ℝ) (t : ℝ) (y : Rn n) : ℝ :=
  ⟪y, meanNormalEst f t⟫

/-- **Definition 2.14** (p. 17): `y` is `B`-typical with respect to `(f, t̂)`, `B = B_{n,ε}`:
`‖y‖₂ ≤ 2√n` (ball condition) and `|G^{t̂}_f(y)| ≤ B` (band condition). -/
def IsTypical {n : ℕ} (ε : ℝ) (f : Rn n → ℝ) (t : ℝ) (y : Rn n) : Prop :=
  ‖y‖ ≤ 2 * Real.sqrt n ∧ |bandDist f t y| ≤ Bne n ε

/-- **Definition 2.14** (p. 17): the whittled distribution `D^{t̂}_∗`, the law of
`y · 1[y is B-typical]` for `y ∼ D` (atypical points are sent to the origin). -/
noncomputable def whittled {n : ℕ} (ε : ℝ) (f : Rn n → ℝ) (t : ℝ) (D : Measure (Rn n)) :
    Measure (Rn n) :=
  D.map ({y | IsTypical ε f t y}.indicator id)

/-- **Definition 2.16** (p. 18): `D` is `B`-typical with respect to `(f, t̂)`: it is supported only on
`B`-typical points, i.e. the set of points that are not `B`-typical is `D`-null. -/
def IsTypicalDist {n : ℕ} (ε : ℝ) (f : Rn n → ℝ) (t : ℝ) (D : Measure (Rn n)) : Prop :=
  D {y | ¬ IsTypical ε f t y} = 0

/-- `D` is supported only on the `2√n`-radius ball centered at the origin. -/
def SupportedInBall {n : ℕ} (D : Measure (Rn n)) : Prop :=
  D {y | 2 * Real.sqrt n < ‖y‖} = 0

/-- The uncentered second-moment matrix `E_{y∼D}[y yᵀ]`. -/
noncomputable def secondMoment {n : ℕ} (D : Measure (Rn n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∫ y, y i * y j ∂D

/-- The Frobenius norm `‖M‖_F = (Σᵢⱼ Mᵢⱼ²)^{1/2}`. -/
noncomputable def frobNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, M i j ^ 2)

/-- The weighted centroid `E_{y∼D}[f(y) α̂_{f,N}(y) y]` (Lemma 2.20). -/
noncomputable def weightedCentroid {n p : ℕ} (ε : ℝ) (f : Rn n → ℝ) (N : Fin p → Rn n)
    (D : Measure (Rn n)) : Rn n :=
  ∫ y, (f y * alphaHat ε f N y) • y ∂D

end DistRobustHalfspace.Main


