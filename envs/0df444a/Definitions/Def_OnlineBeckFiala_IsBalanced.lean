-- Prove2me | Definitions.Def_OnlineBeckFiala_IsBalanced
-- name    : OnlineBeckFiala_IsBalanced
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:03.463525+00:00
-- url     : https://prove2.me/theorems/e58e4e4b-ec7b-437f-8a2d-7f556de6a817
-- title:
--   Transition probabilities (4)–(6), $v$-balanced states (Def. 2.3), curvature $\Delta^\pm$, $D_v$ (Def. 2.4), the density of §2.1
-- statement:
--   Fix $L>0$ and the open cube $(-L,L)^n$. Let $\mu$ be a probability density on $\mathbb R^n$, positive on the cube. For $x\in(-L,L)^n$ and $v\in\mathbb R^n$ set
--   $$p^+_v(x)=\tfrac13\min\Bigl\{1,\frac{\mu(x+v)}{\mu(x)}\Bigr\},\qquad p^-_v(x)=\tfrac13\min\Bigl\{1,\frac{\mu(x-v)}{\mu(x)}\Bigr\},\qquad p^0_v(x)=1-p^+_v(x)-p^-_v(x).$$
--   A point $x\in(-L,L)^n$ is **$v$-balanced** if $p^+_v(x)+p^-_v(x)\ge\tfrac13$ (Definition 2.3, eq. (7)).
--
--   In §2.1 the density is a product $\mu(x)=\prod_i\rho(x_i)$, and the marginal is written through a **potential** $u$:
--   $$\rho(x)=\frac1{LZ}e^{-u(x/L)}\ \text{ on }(-L,L),\qquad \rho=0\ \text{ elsewhere},\qquad Z=\int_{-1}^1e^{-u(y)}\,dy,$$
--   so that $\mu(x)=(LZ)^{-n}\exp\bigl(-\sum_iu(x_i/L)\bigr)$ on the cube. The law with density $Z^{-1}e^{-u}$ on $(-1,1)$ is the case $L=1$. The **curvature** of Definition 2.4 is
--   $$\Delta^\pm(x,v)=\sum_{i=1}^n\Bigl(u\Bigl(\frac{x_i\pm v_i}L\Bigr)-u\Bigl(\frac{x_i}L\Bigr)\Bigr),\qquad D_v(x)=\Delta^+(x,v)+\Delta^-(x,v),$$
--   used when $x\pm v\in(-L,L)^n$.
--
--   These are the objects of the compactly supported Metropolis walk of §2: the walk moves from $x$ to $x\pm v$ with probabilities $p^\pm_v(x)$, and balance at every step lets three coupled walks produce a genuine sign.
--
--   **Formalization Note** The paper sets $u=+\infty$ for $|y|\ge1$; here $u$ is real-valued and the zero of the density off the cube is produced by an indicator, so $u$ is never read there. The sign $\pm$ in $\Delta^\pm$ is a real parameter $\sigma=\pm1$. Statements that use $Z$ assume $e^{-u}$ integrable on $(-1,1)$, the paper's assumption that $\rho$ is a probability density.
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), pp.3–4, §2.1, eqs. (4)–(7), Definitions 2.3, 2.4

import Mathlib

open MeasureTheory Set

namespace OnlineBeckFiala

/-- The open cube `(-L, L)^n` of §2.1, p.3. -/
def cube {n : ℕ} (L : ℝ) : Set (Fin n → ℝ) := {x | ∀ i, x i ∈ Ioo (-L) L}

/-- The product density `µ(x) = ∏_{i=1}^n ρ(x_i)` of §2.1, p.3 (Altschuler, Tikhomirov,
arXiv:2607.14238, held version, sha256 5a1529d2…). -/
def prodDensity {n : ℕ} (ρ : ℝ → ℝ) (x : Fin n → ℝ) : ℝ := ∏ i, ρ (x i)

/-- `p⁺_v(x) = (1/3) min{1, µ(x + v)/µ(x)}`, eq. (4), p.4, for a density function `µ`. -/
noncomputable def pPlus {n : ℕ} (μ : (Fin n → ℝ) → ℝ) (v x : Fin n → ℝ) : ℝ :=
  1 / 3 * min 1 (μ (x + v) / μ x)

/-- `p⁻_v(x) = (1/3) min{1, µ(x − v)/µ(x)}`, eq. (5), p.4. -/
noncomputable def pMinus {n : ℕ} (μ : (Fin n → ℝ) → ℝ) (v x : Fin n → ℝ) : ℝ :=
  1 / 3 * min 1 (μ (x - v) / μ x)

/-- `p⁰_v(x) = 1 − p⁺_v(x) − p⁻_v(x)`, eq. (6), p.4. -/
noncomputable def pZero {n : ℕ} (μ : (Fin n → ℝ) → ℝ) (v x : Fin n → ℝ) : ℝ :=
  1 - pPlus μ v x - pMinus μ v x

/-- **Definition 2.3 (Balanced state), p.4.** "A vector x ∈ (−L, L)^n is v-balanced if
p⁺_v(x) + p⁻_v(x) ≥ 1/3. (7)"

**Formalization Note.** The membership `x ∈ (−L, L)^n` is part of the predicate, as in the
definition's first words; `µ` is the density function, positive on the cube. -/
def IsBalanced {n : ℕ} (L : ℝ) (μ : (Fin n → ℝ) → ℝ) (v x : Fin n → ℝ) : Prop :=
  x ∈ cube L ∧ 1 / 3 ≤ pPlus μ v x + pMinus μ v x

/-- The normalizing constant `Z = ∫_{-1}^{1} e^{-u(y)} dy` of §2.1, p.3, for a potential `u`. -/
noncomputable def Zu (u : ℝ → ℝ) : ℝ := ∫ y in Ioo (-1 : ℝ) 1, Real.exp (-u y)

/-- The marginal density `ρ(x) = (LZ)⁻¹ e^{-u(x/L)}` on `(−L, L)`, extended by zero, §2.1, p.3.

**Formalization Note.** The paper sets `u = +∞` on `|y| ≥ 1`; here `u : ℝ → ℝ` is real-valued and the
value `0` of the density off `(−L, L)` is produced by the indicator, so `u` is never read there. The
paper assumes `ρ` is a probability density; statements using `uRho` assume `e^{-u}` integrable on
`(−1, 1)` (otherwise the Bochner integral `Zu u` is `0`). -/
noncomputable def uRho (u : ℝ → ℝ) (L : ℝ) : ℝ → ℝ :=
  (Ioo (-L) L).indicator (fun x => (L * Zu u)⁻¹ * Real.exp (-u (x / L)))

/-- The product density `µ(x) = (LZ)^{-n} exp(-∑ u(x_i/L))` on the cube, `0` off it, §2.1, p.3. -/
noncomputable def uDensity {n : ℕ} (u : ℝ → ℝ) (L : ℝ) : (Fin n → ℝ) → ℝ :=
  prodDensity (uRho u L)

/-- The law on `ℝ` with density `Z⁻¹ e^{-u}` on `(−1, 1)` (the law of `Y`, §3.1, p.6, and §3.2,
p.7, with `L = 1`). -/
noncomputable def potLaw (u : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (uRho u 1 y))

/-- **Definition 2.4 (Curvature), p.4.** `∆^±(x, v) = ∑_i (u((x_i ± v_i)/L) − u(x_i/L))`; the sign
`±` is the real `σ = 1` or `σ = -1`. The paper uses it only when `x ± v ∈ (−L, L)^n`. -/
noncomputable def Delta {n : ℕ} (u : ℝ → ℝ) (L : ℝ) (σ : ℝ) (x v : Fin n → ℝ) : ℝ :=
  ∑ i, (u ((x i + σ * v i) / L) - u (x i / L))

/-- `D_v(x) = ∆⁺(x, v) + ∆⁻(x, v)`, Definition 2.4, p.4. -/
noncomputable def Dv {n : ℕ} (u : ℝ → ℝ) (L : ℝ) (x v : Fin n → ℝ) : ℝ :=
  Delta u L 1 x v + Delta u L (-1) x v

end OnlineBeckFiala


