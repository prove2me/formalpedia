-- Prove2me | Definitions.Def_AdInterm_SPE_VirtualValue
-- name    : AdInterm_SPE_VirtualValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:12:51.671177+00:00
-- url     : https://prove2.me/theorems/0d9fdb64-892b-4d85-ab2d-789ed960de9a
-- title:
--   §3.1, Defs. 3.1–3.2, pp. 14–15 — virtual value φ, its inverse, projection point z, projected virtual value ψ (4), regularity, reserve-price objectives
-- statement:
--   This module fixes the virtual-value objects of Balseiro, Candogan and Gurkan for a law $X$ on $[0,\infty)$ that is absolutely continuous, or has an atom at $0$ and is absolutely continuous on $(0,\infty)$.
--
--   Write $G_X$ for the cumulative distribution function of $X$, $g_X$ for its derivative (the density), and $\mathcal X$ for the support. Following Definition 3.1, the **virtual value** and its inverse are
--
--   $$
--   \phi_X(x)=x-\frac{1-G_X(x)}{g_X(x)},\qquad \phi_X^{-1}(w)=\inf\{x\in\mathcal X:\ \phi_X(x)\ge w\}.
--   $$
--
--   The **projection point** is $z_X=\phi_X^{-1}(0)$, and the **projected virtual value** of Definition 3.2, display (4), is
--
--   $$
--   \psi_X(x)=\begin{cases}\sup\mathcal X, & x\ge\sup\mathcal X,\\ \phi_X(x), & z_X\le x<\sup\mathcal X,\\ 0, & \text{otherwise.}\end{cases}
--   $$
--
--   For a nondecreasing reporting function $Y$, $Y^{-1}(w)=\inf\{x\ge0:\ Y(x)\ge w\}$ (§2, p. 13).
--
--   The regularity predicate collects the paper's standing assumptions on a law (§2, p. 10; §3.1, p. 14): no mass below $0$, a finite mean, not a point mass at $0$, an absolutely continuous positive part, and on the interval $\{x>0: G_X(x)<1\}$ a differentiable cdf whose derivative is continuous and strictly positive. A **buyer law** is a regular law with $G_X(0)=0$ (no atom at $0$). A law has **increasing virtual values** when $\phi_X$ is strictly increasing on $\{x>0: G_X(x)<1\}$.
--
--   Finally, for $m$ i.i.d. bidders with law $\mu$, highest bid $V^{\mathrm{FH}(m)}$ and second highest $V^{\mathrm{SH}(m)}$ ($0$ when $m=1$), the module defines the profit of a second-price auction with reserve $\delta$ and seller cost $c$ (proof of Lemma 3.1, Step 2, p. 36), and the seller's revenue with reserve $r$ (proof of Theorem 3.1, p. 37):
--
--   $$
--   \mathbb E\big[(\max(\delta,V^{\mathrm{SH}(m)})-c)\,\mathbf 1\{V^{\mathrm{FH}(m)}\ge\delta\}\big],\qquad
--   \mathbb E\big[\max(r,V^{\mathrm{SH}(m)})\,\mathbf 1\{V^{\mathrm{FH}(m)}\ge r\}\big].
--   $$
--
--   These objects are general: they describe optimal reserve prices for i.i.d. bidders on unbounded supports and with an atom at zero, and can be reused beyond this mission.
--
--   **Formalization Note** The density is the derivative of the cdf, and $\phi_X$ is read only at $x>0$. There it also equals the virtual value of the positive part $X\mid X>0$, because the factor $1-G_X(0)$ cancels; this is how Definition 3.2's atom-at-zero case is covered. The support of the positive part is read as the interval $\{x>0: G_X(x)<1\}$, and "$x\ge\sup\mathcal X$" as $G_X(x)=1$, so that $\phi_X^{-1}$ admits points at or above $\sup\mathcal X$ (the paper's convention $\phi_X(\sup\mathcal X)=\sup\mathcal X$). $\sup\mathcal X$ is the least point where the cdf reaches $1$, and is read only when such a point exists. Infima over empty sets (Lean's value $0$) are never read: $Y^{-1}(w)$ is used only where $Y$ reaches $w$.
-- source:
--   Balseiro, Candogan & Gurkan, Multi-stage Intermediation in Display Advertising, SSRN 2661459 (manuscript of 2019-08-17; M&SOM doi:10.1287/msom.2019.0854), §2 p. 10 and p. 13, §3.1 Definitions 3.1–3.2 pp. 14–15, proof of Lemma 3.1 Step 2 p. 36, proof of Theorem 3.1 p. 37

import Mathlib

open MeasureTheory

namespace AdInterm.SPE

/-! Virtual values of a law on `[0, ∞)` (Balseiro–Candogan–Gurkan, §3.1, Definitions 3.1–3.2,
pp. 14–15), possibly with an atom at `0`, and the reserve-price objectives of a second-price
auction with i.i.d. bidders. -/

/-- The cumulative distribution function `G_X(x) = P(X ≤ x)` of a law `ν` on `ℝ`. -/
noncomputable def cdf (ν : Measure ℝ) (x : ℝ) : ℝ := ProbabilityTheory.cdf ν x

/-- Definition 3.1: the virtual value `φ_X(x) = x − (1 − G_X(x)) / g_X(x)`, with `g_X` the
derivative of the cdf. Read only at `x > 0`; there it is also the virtual value of the positive
part `X | X > 0`, since the factor `1 − G_X(0)` cancels. -/
noncomputable def phi (ν : Measure ℝ) (x : ℝ) : ℝ :=
  x - (1 - cdf ν x) / deriv (cdf ν) x

/-- Definition 3.1: `φ_X^{-1}(w) = inf {x ∈ 𝒳 | φ_X(x) ≥ w}`, over `x > 0`; points at or above
`sup 𝒳` (where `G_X = 1`) are admitted, i.e. `φ_X(sup 𝒳) = sup 𝒳`. -/
noncomputable def phiInv (ν : Measure ℝ) (w : ℝ) : ℝ :=
  sInf {x : ℝ | 0 < x ∧ (cdf ν x < 1 → w ≤ phi ν x)}

/-- Definition 3.2: the projection point `z_X = φ_X^{-1}(0)`. -/
noncomputable def zproj (ν : Measure ℝ) : ℝ := phiInv ν 0

/-- `sup 𝒳`, the least point at which the cdf reaches `1`. Read only when such a point
exists. -/
noncomputable def supX (ν : Measure ℝ) : ℝ := sInf {x : ℝ | cdf ν x = 1}

/-- Definition 3.2, display (4): the projected virtual value `ψ_X(x)`, equal to `sup 𝒳` for
`x ≥ sup 𝒳` (i.e. `G_X(x) = 1`), to `φ_X(x)` for `z_X ≤ x < sup 𝒳`, and to `0` otherwise. -/
noncomputable def psi (ν : Measure ℝ) (x : ℝ) : ℝ :=
  if cdf ν x < 1 then (if zproj ν ≤ x then phi ν x else 0) else supX ν

/-- §2, p. 13: `Y^{-1}(w) = inf {x ≥ 0 | Y(x) ≥ w}` for a reporting function `Y`. -/
noncomputable def ginv (Y : ℝ → ℝ) (w : ℝ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ w ≤ Y x}

/-- The standing regularity of §2 (p. 10) and §3.1 (p. 14) for a law `X`, or for its positive
part when `X` has an atom at `0`: support in `[0, ∞)`, finite mean, not a point mass at `0`, the
positive part absolutely continuous, and on the interval `{x > 0 | G(x) < 1}` the cdf is
differentiable with a strictly positive, continuous density. -/
def RegularPos (ν : Measure ℝ) : Prop :=
  ν (Set.Iio 0) = 0 ∧
  Integrable (id : ℝ → ℝ) ν ∧
  cdf ν 0 < 1 ∧
  ν.restrict (Set.Ioi 0) ≪ (volume : Measure ℝ) ∧
  (∀ x, 0 < x → cdf ν x < 1 →
    HasDerivAt (cdf ν) (deriv (cdf ν) x) x ∧ 0 < deriv (cdf ν) x) ∧
  ContinuousOn (deriv (cdf ν)) {x | 0 < x ∧ cdf ν x < 1}

/-- `φ_X` (or `φ_{X|X>0}`) is strictly increasing on the support `{x > 0 | G(x) < 1}`. -/
def IncVV (ν : Measure ℝ) : Prop :=
  StrictMonoOn (phi ν) {x | 0 < x ∧ cdf ν x < 1}

/-- §2, p. 10: a buyers' value law — regular in the sense of `RegularPos` and with no atom at
`0` (absolutely continuous, lower end of the support `0`). -/
def BuyerLaw (ν : Measure ℝ) : Prop := RegularPos ν ∧ cdf ν 0 = 0

/-- The largest of `m` reports (`0` when `m = 0`). -/
noncomputable def maxFin (m : ℕ) (v : Fin m → ℝ) : ℝ :=
  (Finset.univ.sup (fun i => (v i : WithBot ℝ))).getD 0

/-- The second largest of `m` reports (`0` when `m ≤ 1`, i.e. no other bid). -/
noncomputable def secondMax (m : ℕ) (v : Fin m → ℝ) : ℝ :=
  (Finset.univ.filter (fun p : Fin m × Fin m => p.1 ≠ p.2)).sup
    (fun p => (min (v p.1) (v p.2) : WithBot ℝ)) |>.getD 0

/-- Proof of Lemma 3.1, Step 2, p. 36: the profit
`E[(max(δ, V^{SH(m)}) − c) 1{V^{FH(m)} ≥ δ}]` of a second-price auction with reserve `δ`,
`m` i.i.d. bidders of law `μ` and seller cost `c`. -/
noncomputable def reserveObj (m : ℕ) (μ : Measure ℝ) (cost reserve : ℝ) : ℝ :=
  ∫ v, (if reserve ≤ maxFin m v then
    max reserve (secondMax m v) - cost else 0) ∂
    (Measure.pi (fun _ : Fin m => μ))

/-- Proof of Theorem 3.1, p. 37: the seller's revenue
`E[max(r, W^{SH(m)}) 1{W^{FH(m)} ≥ r}]` with reserve `r` (cost `0`). -/
noncomputable def sellerObj (m : ℕ) (μ : Measure ℝ) (reserve : ℝ) : ℝ :=
  reserveObj m μ 0 reserve

end AdInterm.SPE


