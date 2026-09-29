-- Prove2me | Definitions.Def_RobustGeneralization_GaussUpper_Model
-- name    : RobustGeneralization_GaussUpper_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:23:12.396785+00:00
-- url     : https://prove2.me/theorems/9eeac2ed-5878-43d6-9670-7e14c3b6d8c7
-- title:
--   The (θ⋆, σ)-Gaussian model, (ℓ∞- and ℓ_p-robust) classification error, linear classifiers, dual norm and the class-weighted sample mean (Defs. 1–3)
-- statement:
--   This file fixes the objects of Schmidt, Santurkar, Tsipras, Talwar and Mądry's upper bounds for the Gaussian model.
--
--   Throughout, $\mathbb R^d$ carries the Euclidean norm $\|\cdot\|_2$ and inner product $\langle\cdot,\cdot\rangle$, and labels are $y\in\{\pm1\}$.
--
--   1. **Spherical Gaussian.** For $m\in\mathbb R^d$ and $s>0$, $\mathcal N_d(m,s^2I)$ is the law of $m+s\,v$ with $v$ a standard Gaussian vector; $s$ is the standard deviation.
--   2. **Gaussian model (Definition 1).** For $\theta^\star\in\mathbb R^d$ and $\sigma>0$, the $(\theta^\star,\sigma)$-Gaussian model is the law of a pair $(x,y)$ obtained by drawing $y$ uniformly from $\{\pm1\}$ and then $x\sim\mathcal N_d(y\,\theta^\star,\sigma^2I)$:
--   $$\mathcal P_{\theta^\star,\sigma}=\tfrac12\,\mathcal N_d(\theta^\star,\sigma^2I)\otimes\delta_{+1}+\tfrac12\,\mathcal N_d(-\theta^\star,\sigma^2I)\otimes\delta_{-1}.$$
--   3. **Linear classifier.** For $w\in\mathbb R^d$, $f_w(x)=\operatorname{sgn}\langle w,x\rangle$, with the tie $\langle w,x\rangle=0$ labelled $+1$.
--   4. **Classification error (Definition 2).** $\beta=\mathbb P_{(x,y)\sim\mathcal P}[f(x)\neq y]$.
--   5. **Robust classification error (Definition 3).** For the perturbation set $\mathcal B_\infty^\varepsilon(x)=\{x'\in\mathbb R^d:\|x'-x\|_\infty\le\varepsilon\}$, the $\ell_\infty^\varepsilon$-robust classification error of $f$ is $\mathbb P_{(x,y)\sim\mathcal P}[\exists x'\in\mathcal B_\infty^\varepsilon(x): f(x')\ne y]$. For $p\in[1,\infty]$ the $\ell_p^\varepsilon$-robust error is the same quantity with $\mathcal B_p^\varepsilon(x)=\{x':\|x'-x\|_p\le\varepsilon\}$.
--   6. **Dual norm.** $\|w\|_p^*=\sup\{\langle w,v\rangle:\|v\|_p\le1\}$.
--   7. **Class-weighted sample mean.** For a labelled sample $(x_1,y_1),\dots,(x_n,y_n)$, $\bar z=\frac1n\sum_{i=1}^n y_ix_i$ and $\widehat w=\bar z/\|\bar z\|_2$; for unlabelled vectors $z_1,\dots,z_n$, $\bar z=\frac1n\sum_i z_i$ and $\widehat w=\bar z/\|\bar z\|_2$.
--
--   These objects are shared by every statement of the mission: the lemmas on sample means of Gaussian vectors, the robust error of a fixed linear classifier (Lemma 20), and the high-probability bounds for $f_{\widehat w}$ (Theorems 18, 21, Corollary 22).
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` and labels are `Bool` (`true` = $+1$). $\mathcal N_d(m,s^2I)$ is the push-forward of Mathlib's `stdGaussian` under $v\mapsto m+s\,v$, so its covariance is $s^2I$. The $\ell_\infty$ ball is written coordinatewise, $|x'_i-x_i|\le\varepsilon$ for all $i$; $\|v\|_p$ is the norm of `PiLp p`, which for $p=\infty$ is the max norm and for $p=2$ is the Euclidean norm. The errors are measures of sets with values in $[0,\infty]$; the robust event need not be Borel, and a measure applied to it is its outer measure, i.e. its probability under the completed measure. $\widehat w$ is defined as $\|\bar z\|_2^{-1}\bar z$, which is $0$ on the null event $\bar z=0$. The paper's $\operatorname{sgn}(0)$ is not in $\{\pm1\}$; no statement of the paper depends on the tie rule.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, pp. 4–5, Definitions 1–3 and the linear classifier f_w (p. 5); p. 25, Lemma 20 (ℓ_p ball, dual norm); pp. 22–27, the sample mean z̄ and ŵ = z̄/‖z̄‖₂

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RobustGeneralization.GaussUpper

/-- The data space `ℝ^d` with the Euclidean (ℓ2) norm and inner product. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Labels: `true` is `+1`, `false` is `-1`. -/
def lab : Bool → ℝ
  | true => 1
  | false => -1

/-- The ℓ∞ perturbation set `B∞^ε(x) = {x' | ‖x' - x‖∞ ≤ ε}`, written coordinatewise
(Schmidt et al., Definition 3, p. 5). -/
def linfBall {d : ℕ} (x : E d) (ε : ℝ) : Set (E d) :=
  {x' | ∀ i, |x' i - x i| ≤ ε}

/-- The linear classifier `f_w(x) = sgn ⟨w, x⟩` (p. 5); a tie `⟨w, x⟩ = 0` is labelled `+1`. -/
noncomputable def linClf {d : ℕ} (w : E d) : E d → Bool :=
  fun x => decide (0 ≤ inner ℝ w x)

/-- The spherical Gaussian `N(m, s² I)` on `ℝ^d`, `s` the standard deviation: the law of `m + s • v`
for `v` standard Gaussian. -/
noncomputable def gaussVec {d : ℕ} (m : E d) (s : ℝ) : Measure (E d) :=
  (stdGaussian (E d)).map (fun v => m + s • v)

/-- The `(θ⋆, σ)`-Gaussian model (Definition 1, p. 4): the label `y` is uniform on `{±1}` and
`x ∼ N(y θ⋆, σ² I)`; a measure on pairs `(x, y)`. -/
noncomputable def gaussModel {d : ℕ} (θ : E d) (σ : ℝ) : Measure (E d × Bool) :=
  (1 / 2 : ℝ≥0∞) • (gaussVec θ σ).map (fun x => (x, true)) +
    (1 / 2 : ℝ≥0∞) • (gaussVec (-θ) σ).map (fun x => (x, false))

/-- Classification error `P_{(x,y)∼P}[f(x) ≠ y]` (Definition 2, p. 5). -/
noncomputable def clsErr {d : ℕ} (P : Measure (E d × Bool)) (f : E d → Bool) : ℝ≥0∞ :=
  P {p | f p.1 ≠ p.2}

/-- ℓ∞^ε-robust classification error `P_{(x,y)∼P}[∃ x' ∈ B∞^ε(x) : f(x') ≠ y]`
(Definition 3, p. 5). -/
noncomputable def robustErr {d : ℕ} (P : Measure (E d × Bool)) (f : E d → Bool) (ε : ℝ) : ℝ≥0∞ :=
  P {p | ∃ x' ∈ linfBall p.1 ε, f x' ≠ p.2}

/-- The ℓ_p norm `‖v‖_p` of a vector of `ℝ^d`, for `p ∈ [1, ∞]` (`p = ∞` is the max norm). -/
noncomputable def lpNorm {d : ℕ} (p : ℝ≥0∞) (v : E d) : ℝ :=
  ‖(WithLp.toLp p (WithLp.ofLp v) : PiLp p (fun _ : Fin d => ℝ))‖

/-- The ℓ_p perturbation set `B_p^ε(x) = {x' | ‖x' - x‖_p ≤ ε}`. -/
def lpBall {d : ℕ} (p : ℝ≥0∞) (x : E d) (ε : ℝ) : Set (E d) :=
  {x' | lpNorm p (x' - x) ≤ ε}

/-- The dual norm `‖w‖*_p = sup {⟨w, v⟩ | ‖v‖_p ≤ 1}` of `‖·‖_p`. -/
noncomputable def dualNorm {d : ℕ} (p : ℝ≥0∞) (w : E d) : ℝ :=
  sSup {t | ∃ v : E d, lpNorm p v ≤ 1 ∧ t = inner ℝ w v}

/-- ℓ_p^ε-robust classification error: Definition 3 with the perturbation set `B_p^ε`. -/
noncomputable def robustErrP {d : ℕ} (p : ℝ≥0∞) (P : Measure (E d × Bool)) (f : E d → Bool)
    (ε : ℝ) : ℝ≥0∞ :=
  P {q | ∃ x' ∈ lpBall p q.1 ε, f x' ≠ q.2}

/-- The class-weighted sample mean `z̄ = (1/n) ∑ yᵢ xᵢ` of a labelled sample. -/
noncomputable def zbar {d n : ℕ} (S : Fin n → E d × Bool) : E d :=
  ((n : ℝ)⁻¹) • ∑ i, lab (S i).2 • (S i).1

/-- The unit vector `ŵ = z̄ / ‖z̄‖₂` in the direction of `z̄` (it is `0` when `z̄ = 0`). -/
noncomputable def what {d n : ℕ} (S : Fin n → E d × Bool) : E d :=
  ‖zbar S‖⁻¹ • zbar S

/-- The sample mean `z̄ = (1/n) ∑ zᵢ` of unlabelled vectors. -/
noncomputable def zbar' {d n : ℕ} (z : Fin n → E d) : E d :=
  ((n : ℝ)⁻¹) • ∑ i, z i

/-- The unit vector `ŵ = z̄ / ‖z̄‖₂` for the sample mean of unlabelled vectors
(it is `0` when `z̄ = 0`). -/
noncomputable def what' {d n : ℕ} (z : Fin n → E d) : E d :=
  ‖zbar' z‖⁻¹ • zbar' z

end RobustGeneralization.GaussUpper


