-- Prove2me | Definitions.Def_MultivarScores_LevelSet_Setting
-- name    : MultivarScores_LevelSet_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:17.248024+00:00
-- url     : https://prove2.me/theorems/d3b3e6ce-7d9f-4d43-ae01-d27cbb09321b
-- title:
--   §3–§4, pp. 6–16 — smoothed density f ∗ w, the L² score S′ (3), level sets L(g; α) (9), the level set score (S′)^Γ (11), CDF and Heaviside
-- statement:
--   This definition file fixes the objects of the level set part of Meng, Taylor, Ben Taieb and Li.
--
--   Write $\mathbb R^d$ for the space of $d$-dimensional real vectors with Lebesgue measure $\mathcal L^d$ and the componentwise order ($z\ge y$ means $z_j\ge y_j$ for every $j$). A distribution on $\mathbb R^d$ is a probability measure $P$; the paper writes $f_X$ for its generalized density. Let $w,h:\mathbb R^d\to\mathbb R$.
--
--   1. **Smoothed density.** $(f_P * w)(z) = \int_{\mathbb R^d} w(z-s)\,dP(s)$, the convolution of the distribution with the kernel $w$.
--   2. **The $L^2$ scoring rule (3).** For a realization $y\in\mathbb R^d$,
--   $$S'(P,y;w,h)=\int_{\mathbb R^d}(f_P*w)^2(z)\,h(z)\,dz-2\int_{\mathbb R^d}(f_P*w)(z)\,w(z-y)\,h(z)\,dz.$$
--   3. **Level sets (9).** For $g:\mathbb R^d\to\mathbb R$ and $\alpha\in\mathbb R$, $L(g;\alpha)=\{z\in\mathbb R^d : g(z)\ge\alpha\}$.
--   4. **The level set score (11).** For a set $A\subseteq\mathbb R^d$ (an estimate of a level set), a realization $y$ and $\alpha\in\mathbb R$,
--   $$(S')^\Gamma(A,y;w,h,\alpha)=\int_{\mathbb R^d}\bigl(\alpha-w(z-y)\bigr)\,\mathbb 1\{z\in A\}\,h(z)\,dz.$$
--   5. **CDF and Heaviside kernel.** $F_P(z)=P\{s : s\le z\}$ and $u(z)=\mathbb 1\{z\ge 0\}$. With $w=u$ the level set score is the CDF level set score (13), $(\mathrm{MCRPS}')^\Gamma(A,y;h,\alpha)=\int(\alpha-\mathbb 1\{z\ge y\})\mathbb 1\{z\in A\}h(z)\,dz$.
--
--   These are the objects of Theorem 2: $(S')^\Gamma$ is a consistent scoring function for $L(f_Y*w;\alpha)$, and integrating it over $\alpha$ recovers $\tfrac12 S'$.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ` with `volume` and the Pi order. Distributions are measures (with `IsProbabilityMeasure` assumed where used), and every integral is a Bochner integral, which is $0$ when the integrand is not integrable; each theorem carries the integrability hypotheses that make the integrals the paper's. The paper allows $w$ to be a local Borel measure (Assumption 1(a)); here $w$ is a measurable function, a disclosed specialization that excludes only the Dirac kernel $w=\delta_0$ (the density level set score (12)). The level set uses $\ge$, as in (9). Items 1, 2 and 5 (and the space `E`) are the shared definitions `MultivarScores.L2Rule.E`, `smooth`, `S'`, `cdf` and `heaviside` of the module `MultivarScores.L2Rule.Setting`, which this file imports; it declares only `levelSet` and `scoreΓ`.
-- source:
--   Meng, Taylor, Ben Taieb, Li, Scores for Multivariate Distributions and Level Sets, arXiv:2002.09578v6, pp. 6–8, (1)–(3); p. 10, §3.2.2 (F_X, u); p. 12, (9); p. 13, (11); p. 16, (13); p. 32, Assumption 1

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting

namespace MultivarScores.LevelSet

open MeasureTheory

/-- The `α` level set `L(g; α) = {z ∈ ℝ^d : g(z) ≥ α}`, display (9), p. 12. -/
def levelSet {d : ℕ} (g : MultivarScores.L2Rule.E d → ℝ) (α : ℝ) : Set (MultivarScores.L2Rule.E d) :=
  {z | α ≤ g z}

/-- The level set score `(S′)^Γ(A, y; w, h, α) = ∫ (α - w(z - y)) 𝟙{z ∈ A} h(z) dz`,
display (11), p. 13. -/
noncomputable def scoreΓ {d : ℕ} (w h : MultivarScores.L2Rule.E d → ℝ) (α : ℝ) (A : Set (MultivarScores.L2Rule.E d)) (y : MultivarScores.L2Rule.E d) : ℝ :=
  ∫ z in A, (α - w (z - y)) * h z

end MultivarScores.LevelSet


