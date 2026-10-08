-- Prove2me | Definitions.Def_BotNguyenADMM_Rates_Lojasiewicz
-- name    : BotNguyenADMM_Rates_Lojasiewicz
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:36.929682+00:00
-- url     : https://prove2.me/theorems/624b4db7-a9d7-448d-83e2-57174cbb2835
-- title:
--   The Section 3 regularized augmented Lagrangian $\mathcal F_r$, $\mathcal E_k$, the Łojasiewicz property (70), the constants $C_5$–$C_{22}$ and the subgradient $D^{k+1}$
-- statement:
--   Work in the setting of problem (1), Algorithms 1–2 and Assumption 2. Points $u=(x,z,y,x',y')$ of $\mathbb R^n\times\mathbb R^m\times\mathbb R^m\times\mathbb R^n\times\mathbb R^m$ carry the Euclidean product norm $|||u||| = (\|x\|^2+\|z\|^2+\|y\|^2+\|x'\|^2+\|y'\|^2)^{1/2}$.
--
--   The **regularized augmented Lagrangian of Section 3** is
--   $$\mathcal F_r(x,z,y,x',y') = L_r(x,z,y) + 2T_1\|A^*(y-y')\|^2 + C_1\|x - x'\|^2,$$
--   and along a run $\mathcal F_k = \mathcal F_r(x^k,z^k,y^k,x^{k-1},y^{k-1})$ for $k\ge1$. If the run converges to $(\hat x,\hat z,\hat y)$, set $\hat u = (\hat x,\hat z,\hat y,\hat x,\hat y)$, $\mathcal F_* = \mathcal F_r(\hat u) = L_r(\hat x,\hat z,\hat y)$ and $\mathcal E_k = \mathcal F_k - \mathcal F_*$.
--
--   $\mathcal F_r$ satisfies the **Łojasiewicz property at the limit with constant $C_L>0$ and exponent $\theta\in[0,1)$** if the run converges to $(\hat x,\hat z,\hat y)$ and there is $\varepsilon>0$ such that
--   $$|\mathcal F_r(u) - \mathcal F_*|^\theta \le C_L\,\|w\| \qquad (70)$$
--   for every $u$ in the open ball of radius $\varepsilon$ around $\hat u$ with $\mathcal F_r(u)\neq\mathcal F_*$ and every limiting subgradient $w\in\partial\mathcal F_r(u)$. The associated desingularization function is $\varphi(s) = \frac{C_L}{1-\theta}s^{1-\theta}$.
--
--   The constants of Lemmas 8–9 and §3.2 are, with $C_1,C_2,T_1$ from the setting,
--   $$C_5 = C_2L + \mu_1 + r\|A\|,\quad C_7 = 1 + \|A\| + \frac{1}{\rho r},\quad C_8 = 4C_1 + C_5,\quad C_9 = \mu_2,\quad C_{10} = C_7 + 8T_1\|A\|^2,$$
--   $$C_{14} = C_8 + C_9\|A\|,\quad C_{15} = C_{10} + \frac{C_9}{\rho r},\quad C_{16} = \frac{C_9}{\rho r},\quad C_{17} = \frac12\min\Big\{\frac{C_1}{4},\frac{1}{\rho r}\Big\},$$
--   $$C_{19} = \frac{\min\{C_1/4, 1/(\rho r)\}}{3C_L^2\max\{C_{14},C_{15}\}^2},\quad C_{20} = \frac{7}{\sqrt{C_{17}}} + \frac{1}{C_{17}},\quad C_{21} = \frac{7}{2\sqrt{C_{17}}} + \frac{1}{2C_{17}},\quad C_{22} = C_{20}\|A\| + \frac{2C_{21}}{\rho r}.$$
--   Finally, with $d^{k+1}_x = C_2(\nabla h(x^{k+1}) - \nabla h(x^k)) + A^*(y^{k+1}-y^k) + M_1^k(x^k - x^{k+1})$, $d^{k+1}_z = y^k - y^{k+1} + rA(x^k - x^{k+1}) + M_2^k(z^k - z^{k+1})$ and $d^{k+1}_y = \frac{1}{\rho r}(y^{k+1}-y^k)$ (Lemma 8), the vector $D^{k+1}$ has components
--   $$\big(d^{k+1}_x + 2C_1(x^{k+1}-x^k),\ d^{k+1}_z,\ d^{k+1}_y + 4T_1AA^*(y^{k+1}-y^k),\ -2C_1(x^{k+1}-x^k),\ -4T_1AA^*(y^{k+1}-y^k)\big).$$
--
--   These are the objects of the convergence-rate analysis of Section 3.
--
--   **Formalization Note** The product is the nested `WithLp 2` product, whose norm and inner product are those of the paper's (5). The Section 3 $\mathcal F_r$ follows the displayed $\mathcal F_k$ on p. 25, whose coefficient of $\|x^k - x^{k-1}\|^2$ is $C_1$ (not $C_1/2$ as in (47)) although the sentence before it mentions only $T_1\to2T_1$. $\mathcal F_*$ is defined as $\mathcal F_r(\hat u)$; the paper defines it as $\lim_k\mathcal F_k$ and shows (Lemma 12, p. 23) that the two agree. $\mathcal E_k$ is a real number (`EReal.toReal`; $\mathcal F_k$ is finite for $k\ge1$). In (70) the inequality is required for every subgradient instead of $\operatorname{dist}(0,\partial\mathcal F_r(u))$ (so $\operatorname{dist}(0,\emptyset)=+\infty$), and points with $\mathcal F_r(u)=\mathcal F_*$ are exempt (the convention $0^0=0$ of Attouch–Bolte, needed for $\theta=0$). This hypothesis is implied by the paper's Łojasiewicz property of $\mathcal F_r$ together with the convergence of the run (Theorem 14), so every statement using it is at least as strong as the paper's. The power $s^{2\theta}$ of (71) and (86) is `powLoj`, equal to $0$ at $s=0$. The paper defines $D^{k+1}$ "as in (59), replacing $T_1$ by $2T_1$" and keeps Lemma 9's $C_8 = 2C_1 + C_5$, $C_{10} = C_7 + 4T_1\|A\|^2$; for the Section 3 $\mathcal F_r$ the gradient of the regularizer doubles both terms, so $D^{k+1}$, $C_8$ and $C_{10}$ are recomputed as above (this only enlarges $C_{14}, C_{15}$ and shrinks $C_{19}$).
-- source:
--   Boţ and Nguyen, The proximal ADMM in the nonconvex setting, arXiv:1801.01994v2, pp. 17, 21, 23, 25–27: Lemma 8 (53a)–(53c), C_5–C_7; Lemma 9 (59), C_8–C_10; E_k (p. 21); Definition 3 and (70) (p. 23); F_k of §3.2 (p. 25); C_14–C_17 (p. 26), C_19 (86), C_20–C_22 (87a)–(87c), φ (Lemma 19)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_BotNguyenADMM_Rates_Setting

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace
open NonconvexSplitting.Shared

namespace BotNguyenADMM.Rates

/-- The product `ℝⁿ × ℝᵐ × ℝᵐ × ℝⁿ × ℝᵐ` with the Euclidean product norm
`|||u||| = √(Σ ‖uᵢ‖²)` and inner product `⟪u, u′⟫ = Σ ⟨uᵢ, u′ᵢ⟩` of (5), p. 4. -/
abbrev Pt5 (n m : ℕ) :=
  WithLp 2 (BotNguyenADMM.KL.E n × WithLp 2 (BotNguyenADMM.KL.E m × WithLp 2 (BotNguyenADMM.KL.E m × WithLp 2 (BotNguyenADMM.KL.E n × BotNguyenADMM.KL.E m))))

/-- The point `(x, z, y, x′, y′)` of `Pt5 n m`. -/
def pack5 {n m : ℕ} (x : BotNguyenADMM.KL.E n) (z y : BotNguyenADMM.KL.E m) (x' : BotNguyenADMM.KL.E n) (y' : BotNguyenADMM.KL.E m) : Pt5 n m :=
  WithLp.toLp 2 (x, WithLp.toLp 2 (z, WithLp.toLp 2 (y, WithLp.toLp 2 (x', y'))))

/-- The `x`, `z`, `y`, `x′`, `y′` components of a point of `Pt5 n m`. -/
def Pt5.px {n m : ℕ} (u : Pt5 n m) : BotNguyenADMM.KL.E n := (WithLp.ofLp u).1
def Pt5.pz {n m : ℕ} (u : Pt5 n m) : BotNguyenADMM.KL.E m := (WithLp.ofLp (WithLp.ofLp u).2).1
def Pt5.py {n m : ℕ} (u : Pt5 n m) : BotNguyenADMM.KL.E m :=
  (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp u).2).2).1
def Pt5.px' {n m : ℕ} (u : Pt5 n m) : BotNguyenADMM.KL.E n :=
  (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp u).2).2).2).1
def Pt5.py' {n m : ℕ} (u : Pt5 n m) : BotNguyenADMM.KL.E m :=
  (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp (WithLp.ofLp u).2).2).2).2

/-- The regularized augmented Lagrangian of **Section 3** (p. 25), where `T₁` is replaced by
`2T₁` and the coefficient of `‖x − x′‖²` is `C₁` (as in the displayed `F_k` on p. 25):
`F_r(x, z, y, x′, y′) = L_r(x, z, y) + 2T₁‖A*(y − y′)‖² + C₁‖x − x′‖²`. -/
noncomputable def Freg {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (g : BotNguyenADMM.KL.E m → EReal) (h : BotNguyenADMM.KL.E n → ℝ)
    (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m) (L r ρ lam μ₁ : ℝ) (u : Pt5 n m) : EReal :=
  augLag g h A r u.px u.pz u.py +
    ((2 * T1 lam ρ r * ‖(ContinuousLinearMap.adjoint A) (u.py - u.py')‖ ^ 2 +
      C1 v L μ₁ lam ρ r * ‖u.px - u.px'‖ ^ 2 : ℝ) : EReal)

/-- `F_k := F_r(xᵏ, zᵏ, yᵏ, x^{k−1}, y^{k−1})` (p. 25), used for `k ≥ 1`. -/
noncomputable def Fk {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (g : BotNguyenADMM.KL.E m → EReal) (h : BotNguyenADMM.KL.E n → ℝ)
    (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m) (L r ρ lam μ₁ : ℝ) (x : ℕ → BotNguyenADMM.KL.E n) (z y : ℕ → BotNguyenADMM.KL.E m) (k : ℕ) : EReal :=
  Freg v g h A L r ρ lam μ₁ (pack5 (x k) (z k) (y k) (x (k - 1)) (y (k - 1)))

/-- `F_* = F_r(x̂, ẑ, ŷ, x̂, ŷ) = L_r(x̂, ẑ, ŷ)`, the value of `F_r` at the limit point
(Lemma 12 and p. 23 of the paper: `F_*`, the limit of `F_k`, is the value of `F_r` at the
limit). -/
noncomputable def Fstar {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (g : BotNguyenADMM.KL.E m → EReal) (h : BotNguyenADMM.KL.E n → ℝ)
    (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m) (L r ρ lam μ₁ : ℝ) (xh : BotNguyenADMM.KL.E n) (zh yh : BotNguyenADMM.KL.E m) : EReal :=
  Freg v g h A L r ρ lam μ₁ (pack5 xh zh yh xh yh)

/-- `E_k := F_k − F_*` (p. 21), as a real number (used for `k ≥ 1`, where `F_k` is finite). -/
noncomputable def Ek {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (g : BotNguyenADMM.KL.E m → EReal) (h : BotNguyenADMM.KL.E n → ℝ)
    (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m) (L r ρ lam μ₁ : ℝ) (x : ℕ → BotNguyenADMM.KL.E n) (z y : ℕ → BotNguyenADMM.KL.E m)
    (xh : BotNguyenADMM.KL.E n) (zh yh : BotNguyenADMM.KL.E m) (k : ℕ) : ℝ :=
  (Fk v g h A L r ρ lam μ₁ x z y k).toReal - (Fstar v g h A L r ρ lam μ₁ xh zh yh).toReal

/-- **The Łojasiewicz property of `F_r` at the limit of the run** ((70), p. 23), with
Łojasiewicz constant `C_L > 0` and exponent `θ ∈ [0, 1)`: the run converges to `(x̂, ẑ, ŷ)`,
and there is `ε > 0` such that for every `u` in the open ball of radius `ε` around
`û = (x̂, ẑ, ŷ, x̂, ŷ)` with `F_r(u) ≠ F_*` and every limiting subgradient `w ∈ ∂F_r(u)`,
`|F_r(u) − F_*|^θ ≤ C_L ‖w‖`. Points with `F_r(u) = F_*` are exempt (the convention
`0⁰ = 0`), and the inequality is required for every subgradient instead of for
`dist(0, ∂F_r(u))` (the convention `dist(0, ∅) = +∞`). -/
def LojAt {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (g : BotNguyenADMM.KL.E m → EReal) (h : BotNguyenADMM.KL.E n → ℝ) (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m)
    (L r ρ lam μ₁ : ℝ) (x : ℕ → BotNguyenADMM.KL.E n) (z y : ℕ → BotNguyenADMM.KL.E m) (xh : BotNguyenADMM.KL.E n) (zh yh : BotNguyenADMM.KL.E m)
    (CL θ : ℝ) : Prop :=
  0 < CL ∧ 0 ≤ θ ∧ θ < 1 ∧
  Tendsto x atTop (𝓝 xh) ∧ Tendsto z atTop (𝓝 zh) ∧ Tendsto y atTop (𝓝 yh) ∧
  ∃ ε > 0, ∀ u ∈ Metric.ball (pack5 xh zh yh xh yh) ε,
    ∀ w ∈ LimitingSubdiff (Freg v g h A L r ρ lam μ₁) u,
      Freg v g h A L r ρ lam μ₁ u ≠ Fstar v g h A L r ρ lam μ₁ xh zh yh →
        |(Freg v g h A L r ρ lam μ₁ u).toReal -
            (Fstar v g h A L r ρ lam μ₁ xh zh yh).toReal| ^ θ ≤ CL * ‖w‖

/-- The desingularization function `φ(s) = C_L s^{1−θ}/(1 − θ)` of Lemma 19 (p. 27). -/
noncomputable def phiLoj (CL θ s : ℝ) : ℝ := CL * s ^ (1 - θ) / (1 - θ)

/-- The power `s^{2θ}` with the convention `0^{2θ} = 0` (also for `θ = 0`), used in (71)
and (86). For `θ > 0` and `s ≥ 0` this is `s^{2θ}`. -/
noncomputable def powLoj (s θ : ℝ) : ℝ := if s = 0 then 0 else s ^ (2 * θ)

/-! ### The constants of Lemma 8, Lemma 9 and §3.2 -/

/-- `C₅ := C₂L + μ₁ + r‖A‖` (Lemma 8, p. 17). -/
noncomputable def C5 {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m) (L μ₁ r : ℝ) : ℝ :=
  C2 v * L + μ₁ + r * ‖A‖

/-- `C₇ := 1 + ‖A‖ + 1/(ρr)` (Lemma 8, p. 17). -/
noncomputable def C7 {n m : ℕ} (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m) (ρ r : ℝ) : ℝ :=
  1 + ‖A‖ + 1 / (ρ * r)

/-- `C₈` for the Section 3 `F_r`: `4C₁ + C₅` (Lemma 9 has `2C₁ + C₅` for (47); the
coefficient of `‖x − x′‖²` doubles in Section 3). -/
noncomputable def C8 {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m) (L μ₁ lam ρ r : ℝ) : ℝ :=
  4 * C1 v L μ₁ lam ρ r + C5 v A L μ₁ r

/-- `C₉ := C₆ = μ₂` (Lemmas 8–9, p. 17). -/
def C9 (μ₂ : ℝ) : ℝ := μ₂

/-- `C₁₀` for the Section 3 `F_r`: `C₇ + 8T₁‖A‖²` (Lemma 9 has `C₇ + 4T₁‖A‖²` for (47);
`T₁` is replaced by `2T₁` in Section 3). -/
noncomputable def C10 {n m : ℕ} (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m) (lam ρ r : ℝ) : ℝ :=
  C7 A ρ r + 8 * T1 lam ρ r * ‖A‖ ^ 2

/-- `C₁₄ := C₈ + C₉‖A‖` (p. 26). -/
noncomputable def C14 {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m) (L μ₁ μ₂ lam ρ r : ℝ) : ℝ :=
  C8 v A L μ₁ lam ρ r + C9 μ₂ * ‖A‖

/-- `C₁₅ := C₁₀ + C₉/(ρr)` (p. 26). -/
noncomputable def C15 {n m : ℕ} (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m) (μ₂ lam ρ r : ℝ) : ℝ :=
  C10 A lam ρ r + C9 μ₂ / (ρ * r)

/-- `C₁₆ := C₉/(ρr)` (p. 26). -/
noncomputable def C16 (μ₂ ρ r : ℝ) : ℝ := C9 μ₂ / (ρ * r)

/-- `C₁₇ := ½ min{C₁/4, 1/(ρr)}` (p. 26). -/
noncomputable def C17 (v : BotNguyenADMM.KL.Variant) (L μ₁ lam ρ r : ℝ) : ℝ :=
  1 / 2 * min (C1 v L μ₁ lam ρ r / 4) (1 / (ρ * r))

/-- `C₁₉ := min{C₁/4, 1/(ρr)} / (3C_L² max{C₁₄, C₁₅}²)` ((86), p. 26). -/
noncomputable def C19 {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m)
    (L μ₁ μ₂ lam ρ r CL : ℝ) : ℝ :=
  min (C1 v L μ₁ lam ρ r / 4) (1 / (ρ * r)) /
    (3 * CL ^ 2 * max (C14 v A L μ₁ μ₂ lam ρ r) (C15 A μ₂ lam ρ r) ^ 2)

/-- `C₂₀ := 7/√C₁₇ + 1/C₁₇` ((87a), p. 27). -/
noncomputable def C20 (v : BotNguyenADMM.KL.Variant) (L μ₁ lam ρ r : ℝ) : ℝ :=
  7 / Real.sqrt (C17 v L μ₁ lam ρ r) + 1 / C17 v L μ₁ lam ρ r

/-- `C₂₁ := 7/(2√C₁₇) + 1/(2C₁₇)` ((87b), p. 27). -/
noncomputable def C21 (v : BotNguyenADMM.KL.Variant) (L μ₁ lam ρ r : ℝ) : ℝ :=
  7 / (2 * Real.sqrt (C17 v L μ₁ lam ρ r)) + 1 / (2 * C17 v L μ₁ lam ρ r)

/-- `C₂₂ := C₂₀‖A‖ + 2C₂₁/(ρr)` ((87c), p. 27). -/
noncomputable def C22 {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m) (L μ₁ lam ρ r : ℝ) : ℝ :=
  C20 v L μ₁ lam ρ r * ‖A‖ + 2 * C21 v L μ₁ lam ρ r / (ρ * r)

/-! ### The subgradients of Lemma 8 and of the Section 3 `F_r` -/

/-- `d^{k+1}_x := C₂(∇h(x^{k+1}) − ∇h(xᵏ)) + A*(y^{k+1} − yᵏ) + M₁ᵏ(xᵏ − x^{k+1})` (53a). -/
noncomputable def dx {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (h : BotNguyenADMM.KL.E n → ℝ) (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m)
    (M₁ : ℕ → BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E n) (x : ℕ → BotNguyenADMM.KL.E n) (y : ℕ → BotNguyenADMM.KL.E m) (k : ℕ) : BotNguyenADMM.KL.E n :=
  C2 v • (gradient h (x (k + 1)) - gradient h (x k)) +
    (ContinuousLinearMap.adjoint A) (y (k + 1) - y k) + M₁ k (x k - x (k + 1))

/-- `d^{k+1}_z := yᵏ − y^{k+1} + rA(xᵏ − x^{k+1}) + M₂ᵏ(zᵏ − z^{k+1})` (53b). -/
noncomputable def dz {n m : ℕ} (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m) (r : ℝ) (M₂ : ℕ → BotNguyenADMM.KL.E m →L[ℝ] BotNguyenADMM.KL.E m)
    (x : ℕ → BotNguyenADMM.KL.E n) (z y : ℕ → BotNguyenADMM.KL.E m) (k : ℕ) : BotNguyenADMM.KL.E m :=
  y k - y (k + 1) + r • A (x k - x (k + 1)) + M₂ k (z k - z (k + 1))

/-- `d^{k+1}_y := (1/(ρr))(y^{k+1} − yᵏ)` (53c). -/
noncomputable def dy {m : ℕ} (ρ r : ℝ) (y : ℕ → BotNguyenADMM.KL.E m) (k : ℕ) : BotNguyenADMM.KL.E m :=
  (1 / (ρ * r)) • (y (k + 1) - y k)

/-- The subgradient `D^{k+1}` of the Section 3 `F_r` at `(x^{k+1}, z^{k+1}, y^{k+1}, xᵏ, yᵏ)`,
built as in (59) for the Section 3 regularization `2T₁‖A*(y − y′)‖² + C₁‖x − x′‖²`:
`D_x = d_x + 2C₁(x^{k+1} − xᵏ)`, `D_z = d_z`, `D_y = d_y + 4T₁AA*(y^{k+1} − yᵏ)`,
`D_{x′} = −2C₁(x^{k+1} − xᵏ)`, `D_{y′} = −4T₁AA*(y^{k+1} − yᵏ)`. -/
noncomputable def Dsub {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (h : BotNguyenADMM.KL.E n → ℝ) (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m)
    (L r ρ lam μ₁ : ℝ) (M₁ : ℕ → BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E n) (M₂ : ℕ → BotNguyenADMM.KL.E m →L[ℝ] BotNguyenADMM.KL.E m)
    (x : ℕ → BotNguyenADMM.KL.E n) (z y : ℕ → BotNguyenADMM.KL.E m) (k : ℕ) : Pt5 n m :=
  let c := C1 v L μ₁ lam ρ r
  let t := T1 lam ρ r
  let AAy := A ((ContinuousLinearMap.adjoint A) (y (k + 1) - y k))
  pack5 (dx v h A M₁ x y k + (2 * c) • (x (k + 1) - x k))
    (dz A r M₂ x z y k)
    (dy ρ r y k + (4 * t) • AAy)
    (-((2 * c) • (x (k + 1) - x k)))
    (-((4 * t) • AAy))

end BotNguyenADMM.Rates


