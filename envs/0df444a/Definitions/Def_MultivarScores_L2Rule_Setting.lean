-- Prove2me | Definitions.Def_MultivarScores_L2Rule_Setting
-- name    : MultivarScores_L2Rule_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:49.581184+00:00
-- url     : https://prove2.me/theorems/8d3475bf-37ac-41d5-9457-97a113dfd42a
-- title:
--   §3, pp. 6–11 and Assumption 1, p. 32 — smoothed density f ∗ w, the L² scoring rules (2), (3), divergence (1), Assumption 1, MCRPS (5)–(6), LPM (7)
-- statement:
--   The objects of §3 of Meng, Taylor, Ben Taieb and Li.
--
--   Write $\mathbb R^d$ for the space of vectors $z=(z_1,\dots,z_d)$ with Lebesgue measure $\mathcal L^d$ and the componentwise order ($y\le z$ iff $y_j\le z_j$ for every $j$). A distribution is a probability measure $P$ on $\mathbb R^d$; integrals $\int g(s)f_P(s)\,ds$ against the paper's generalized PDF $f_P$ are integrals $\int g\,dP$. Fix a kernel $w:\mathbb R^d\to\mathbb R$ and a weight $h:\mathbb R^d\to\mathbb R$.
--
--   1. **Smoothed density** (§2, §3.1): $(f_P*w)(z)=\int_{\mathbb R^d} w(z-s)\,dP(s)$.
--   2. **L² scoring rule** (2): $$S(P,y;w,h)=\int_{\mathbb R^d}\big((f_P*w)(z)-w(z-y)\big)^2h(z)\,dz.$$
--   3. **Equivalent L² scoring rule** (3): $$S'(P,y;w,h)=\int_{\mathbb R^d}(f_P*w)^2(z)h(z)\,dz-2\int_{\mathbb R^d}(f_P*w)(z)\,w(z-y)\,h(z)\,dz.$$
--   4. **L² divergence** (1): $D(P_X,P_Y)=\int_{\mathbb R^d}\big((f_X*w)(z)-(f_Y*w)(z)\big)^2h(z)\,dz$.
--   5. **Characterization** (p. 8): $f_Y*w$ uniquely determines every $P_Y$ in a class $\mathcal V^d$ if, for $P_X,P_Y\in\mathcal V^d$, $f_X*w=f_Y*w$ $\mathcal L^d$-a.e. implies $P_X=P_Y$.
--   6. **Assumption 1** (p. 32), for $w$, $h$ and a class $\mathcal V^d$ of probability distributions: (a) $w$ and $h$ are measurable, $h\ge0$ is integrable, and $f_Y*w$ is well defined for every $P_Y\in\mathcal V^d$; (b) $(f_Y*w)^2h$ and $w(\cdot-y)^2h$ (every $y$) are integrable, and $(s,z)\mapsto w(z-s)^2h(z)$ is integrable for $P_Y\otimes\mathcal L^d$; (c) $(f_X*w)(\cdot)\,w(\cdot-y)\,h$ is integrable for every $y$, and $(s,z)\mapsto (f_X*w)(z)\,w(z-s)\,h(z)$ is integrable for $P_Y\otimes\mathcal L^d$, for all $P_X,P_Y\in\mathcal V^d$.
--   7. **Heaviside function, CDF and MCRPS** (§3.2.2): $u(z)=\mathbb 1\{z\ge0\}$, $F_P(z)=P\{s\le z\}$, $$\mathrm{MCRPS}(P,y;h)=\int_{\mathbb R^d}\big(F_P(z)-\mathbb 1\{z\ge y\}\big)^2h(z)\,dz,\qquad \mathrm{MCRPS}'(P,y;h)=\int_{\mathbb R^d}F_P^2h\,dz-2\int_{\mathbb R^d}F_P(z)\mathbb 1\{z\ge y\}h(z)\,dz.$$
--   8. **Lower partial moment of order $k\in\mathbb N$** (7): $$\mathrm{LPM}_{P,k}(z)=\int_{\mathbb R^d}\prod_{j=1}^d\frac{1}{k!}(z_j-s_j)^k\,\mathbb 1\{z_j\ge s_j\}\,dP(s).$$
--
--   These are the building blocks of Theorem 1 and its special cases (CRPS/MCRPS, LPM scores); the ambient space $\mathbb R^d$ and the smoothed density $f_P*w$ are also the setting of the level set score of §4 (Theorem 2).
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ` with its product Lebesgue measure and the Pi order. The paper lets $w$ be a local Borel measure (so that $w=\delta_0$ gives the quadratic score (4)); here $w$ is a measurable function, which excludes only the $\delta_0$ case. The convexity of $\mathcal V^d$ (§2) is never used and is not imposed. Assumption 1(b)/(c) say "then (2)/(3) is well-defined and finite"; they are formalized as the integrability hypotheses listed above, which is what makes every Bochner integral the paper's integral. Three readings are fixed: "$f_Y*w$ is well defined" is integrability of $s\mapsto w(z-s)$ for every $z$; "$w$ is square-integrable with respect to $\lambda$" is read at every shift $w(\cdot-y)$, which is what makes (2) finite for every $y$; and the two "integrable with respect to $f_Y$" clauses are stated as integrability on the product $P_Y\otimes\mathcal L^d$ (for the nonnegative integrand of (b) this is the same as the page's condition; for the signed integrand of (c) it asks for absolute integrability, which Fubini's theorem needs). $F_P$ is meant for probability measures $P$ (for an infinite measure Lean's `toReal` would return $0$). $\mathrm{LPM}$ is defined from the explicit kernel printed in (7), not as a convolution power of $u$ (the printed name "$k$th convolution power" is off by one; at $k=0$ the formula gives the CDF, as App. p. 34 says).
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, p. 6 (§2, §3), p. 7 (1), p. 8 (2), (3), Theorem 1, p. 10 (5), (6), p. 11 (7); p. 32, Assumption 1

import Mathlib

namespace MultivarScores.L2Rule

open MeasureTheory

/-- The ambient space `ℝ^d`, as functions `Fin d → ℝ`, with the product Lebesgue measure `volume`
(the paper's `𝓛^d`) and the componentwise (Pi) order, so `y ≤ z` means `yⱼ ≤ zⱼ` for every `j`. -/
abbrev E (d : ℕ) := Fin d → ℝ

/-- The smoothed density `(f_P ∗ w)(z) = ∫ w(z − s) f_P(s) ds = ∫ w(z − s) dP(s)` of a distribution
`P` on `ℝ^d` by a kernel `w` (§2 and §3.1, pp. 6–7). -/
noncomputable def smooth {d : ℕ} (P : Measure (E d)) (w : E d → ℝ) (z : E d) : ℝ :=
  ∫ s, w (z - s) ∂P

/-- The L² scoring rule (2), p. 8:
`S(P, y; w, h) = ∫ ((f_P ∗ w)(z) − w(z − y))² h(z) dz`. -/
noncomputable def S {d : ℕ} (P : Measure (E d)) (w h : E d → ℝ) (y : E d) : ℝ :=
  ∫ z, (smooth P w z - w (z - y)) ^ 2 * h z

/-- The L² scoring rule (3), p. 8:
`S′(P, y; w, h) = ∫ (f_P ∗ w)²(z) h(z) dz − 2 ∫ (f_P ∗ w)(z) w(z − y) h(z) dz`. -/
noncomputable def S' {d : ℕ} (P : Measure (E d)) (w h : E d → ℝ) (y : E d) : ℝ :=
  (∫ z, smooth P w z ^ 2 * h z) - 2 * ∫ z, smooth P w z * w (z - y) * h z

/-- The L² divergence (1), p. 7: `∫ ((f_X ∗ w)(z) − (f_Y ∗ w)(z))² h(z) dz`. -/
noncomputable def L2div {d : ℕ} (PX PY : Measure (E d)) (w h : E d → ℝ) : ℝ :=
  ∫ z, (smooth PX w z - smooth PY w z) ^ 2 * h z

/-- "`f_Y ∗ w` uniquely determines any `P_Y ∈ 𝒱^d`" (p. 8): for distributions of the class `𝒱`,
`f_X ∗ w = f_Y ∗ w` `𝓛^d`-a.e. implies `P_X = P_Y`. -/
def Characterizes {d : ℕ} (w : E d → ℝ) (𝒱 : Set (Measure (E d))) : Prop :=
  ∀ P ∈ 𝒱, ∀ Q ∈ 𝒱, smooth P w =ᵐ[volume] smooth Q w → P = Q

/-- Assumption 1 (p. 32), with "well-defined and finite" turned into explicit integrability
hypotheses, for a kernel `w` that is a measurable function, a weight `h` and a class `𝒱` of
distributions on `ℝ^d`. -/
structure Assumption1 {d : ℕ} (w h : E d → ℝ) (𝒱 : Set (Measure (E d))) : Prop where
  /-- (a) the kernel `w` is a (measurable) function. -/
  measurable_w : Measurable w
  /-- (a) `dλ = h dz` with `h` measurable, -/
  measurable_h : Measurable h
  /-- (a) non-negative -/
  h_nonneg : ∀ z, 0 ≤ h z
  /-- (a) and integrable. -/
  integrable_h : Integrable h
  /-- `𝒱^d` is a class of probability distributions. -/
  isProb : ∀ P ∈ 𝒱, IsProbabilityMeasure P
  /-- (a) `f_Y ∗ w` is well defined for every `P_Y ∈ 𝒱^d`. -/
  smooth_wd : ∀ P ∈ 𝒱, ∀ z, Integrable (fun s => w (z - s)) P
  /-- (b) `f_Y ∗ w` is square-integrable with respect to `λ`. -/
  sq_smooth : ∀ P ∈ 𝒱, Integrable (fun z => smooth P w z ^ 2 * h z)
  /-- (b) `w` is square-integrable with respect to `λ` (at every shift `z ↦ w(z − y)`). -/
  sq_w : ∀ y, Integrable (fun z => w (z - y) ^ 2 * h z)
  /-- (b) `∫ w²(z − •) h(z) f_Y(•) dz` is integrable with respect to `f_Y`. -/
  sq_w_prod : ∀ P ∈ 𝒱,
    Integrable (fun p : E d × E d => w (p.2 - p.1) ^ 2 * h p.2) (P.prod volume)
  /-- (c) `(f_X ∗ w)(•) w(• − y)` is integrable with respect to `λ`. -/
  cross : ∀ PX ∈ 𝒱, ∀ y, Integrable (fun z => smooth PX w z * w (z - y) * h z)
  /-- (c) `∫ (f_X ∗ w)(z) w(z − •) h(z) f_Y(•) dz` is integrable for any `P_Y ∈ 𝒱^d`. -/
  cross_prod : ∀ PX ∈ 𝒱, ∀ PY ∈ 𝒱,
    Integrable (fun p : E d × E d => smooth PX w p.2 * w (p.2 - p.1) * h p.2) (PY.prod volume)

/-- The Heaviside function `u(z) = ∏ⱼ 𝟙{zⱼ ≥ 0} = 𝟙{z ≥ 0}` (§3.2.2, p. 10): the indicator of the
nonnegative orthant `{z | 0 ≤ z}` (componentwise order). -/
noncomputable def heaviside {d : ℕ} (z : E d) : ℝ := (Set.Ici (0 : E d)).indicator 1 z

/-- The multivariate CDF `F_P(z) = P{s ≤ z}` (§3.2.2, p. 10). -/
noncomputable def cdf {d : ℕ} (P : Measure (E d)) (z : E d) : ℝ := (P (Set.Iic z)).toReal

/-- The MCRPS (5), p. 10: `MCRPS(P, y; h) = ∫ (F_P(z) − 𝟙{z ≥ y})² h(z) dz`, where
`𝟙{z ≥ y}` is the indicator of the upper orthant `{z | y ≤ z}` (componentwise order). -/
noncomputable def MCRPS {d : ℕ} (P : Measure (E d)) (h : E d → ℝ) (y : E d) : ℝ :=
  ∫ z, (cdf P z - (Set.Ici y).indicator 1 z) ^ 2 * h z

/-- The MCRPS′ (6), p. 10:
`MCRPS′(P, y; h) = ∫ F_P²(z) h(z) dz − 2 ∫ F_P(z) 𝟙{z ≥ y} h(z) dz`. -/
noncomputable def MCRPS' {d : ℕ} (P : Measure (E d)) (h : E d → ℝ) (y : E d) : ℝ :=
  (∫ z, cdf P z ^ 2 * h z) - 2 * ∫ z, cdf P z * (Set.Ici y).indicator 1 z * h z

/-- The lower partial moment of order `k` (7), p. 11, from its explicit kernel:
`LPM_{P,k}(z) = ∫ ∏ⱼ (1/k!) (zⱼ − sⱼ)^k 𝟙{zⱼ ≥ sⱼ} dP(s)`. At `k = 0` it is the CDF. -/
noncomputable def lpm {d : ℕ} (k : ℕ) (P : Measure (E d)) (z : E d) : ℝ :=
  ∫ s, ∏ j, ((z j - s j) ^ k / (k.factorial : ℝ) * if s j ≤ z j then 1 else 0) ∂P

end MultivarScores.L2Rule


