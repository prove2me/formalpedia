-- Prove2me | Definitions.Def_FluVaccineCoord_TwoSided_Model
-- name    : FluVaccineCoord_TwoSided_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:01.717497+00:00
-- url     : https://prove2.me/theorems/bda0b159-2ef8-415d-8707-2bd91a921e85
-- title:
--   §3, (1)–(9), (15), (17)–(24), Assumption 1, pp. 7–22 — flu vaccine supply chain with random yield, threshold equilibria and the two-sided incentive program
-- statement:
--   The model of Arifoğlu and Tang: a vaccine manufacturer with random production yield, a population of self-interested individuals who decide whether to seek vaccination after seeing the realized supply, and a social planner's two-sided incentive program.
--
--   **Primitives (§3).** The manufacturer plans an input quantity $Q \ge 0$; the realized supply is $Q_r = YQ$, where the yield $Y \ge 0$ has law $F$ (written $\mu$) with finite mean $\mathbb E[Y]$; the wholesale price is $w>0$, the cost per planned unit $c>0$, and $w\,\mathbb E[Y] > c$. A unit mass of individuals have infection costs $x \sim U[0,\bar x]$, $\bar x>0$, so $G(x) = x/\bar x$ and $\bar G(x) = 1 - x/\bar x$; a healthy individual enjoys $V_H$, and vaccination costs $w + p$ with $p > 0$. When a fraction $h \in [0,1]$ is vaccinated, an unvaccinated individual is infected with probability $u(h)$ and a vaccinated one with probability $v(h)$, $0 \le v(h) \le u(h) \le 1$, both continuous on $[0,1]$.
--
--   **Zero-risk fraction and Assumption 1 (p. 10).**
--   $$h_{zr} = \begin{cases} \inf\{h\in[0,1] : (1-h)u(h)+hv(h) = 0\}, & v(1) = 0,\\ 1, & v(1)>0,\end{cases} \qquad (1)$$
--   and $u = v = 0$ on $[h_{zr}, 1]$ when $v(1) = 0$. Assumption 1: (i) $\bar x\,u(0) \ge w + p + \bar x\,v(0)$; (ii) $u'(h) < 0$ and $v'(h) \le 0$ for $h < h_{zr}$; (iii) $(1-h)u(h)+hv(h)$ is convex on $[0,h_{zr}]$; (iv) $(1-h)(u(h)-v(h))$ is strictly decreasing on $[0,h_{zr}]$; (v) $h[(1-h)u(h)+hv(h)-v(h)]$ is concave on $[0,h_{zr}]$.
--
--   **Demand, rationing and welfare (§3.3–3.4).** If only individuals with cost above a threshold $\hat x$ seek vaccination, the vaccinated fraction and the fill rate are $h(\hat x, Q_r) = \min\{\bar G(\hat x), Q_r\}$ (2) and $\phi(\hat x, Q_r) = \min\{1, Q_r/\bar G(\hat x)\}$ (3), and the ex-post social welfare is
--   $$W(\hat x, Q_r) = V_H - ph - \tfrac{\bar x}{2} G^2(\hat x)\, u(h) - \tfrac{\bar x}{2}\bigl(1 - G^2(\hat x)\bigr)\bigl[\phi\, v(h) + (1-\phi)\, u(h)\bigr]. \qquad (4)$$
--
--   **Social optimum (§4).** $x_{zr} = \bar x(1 - h_{zr})$, i.e. $\bar G(x_{zr}) = h_{zr}$ (5). The marginal social benefit is
--   $$B(\hat x) = \frac{p}{\bar x} + \tfrac12\bigl[G^2(\hat x)\,u'(\bar G(\hat x)) + (1-G^2(\hat x))\,v'(\bar G(\hat x))\bigr] - G(\hat x)\bigl(u(\bar G(\hat x)) - v(\bar G(\hat x))\bigr). \qquad (6)$$
--   A threshold $x^c_1$ satisfies (8) if either $B \le 0$ on $(x_{zr},\bar x)$ and $x^c_1 = x_{zr}$, or $B > 0$ somewhere on $(x_{zr}, \bar x)$ and $x^c_1 \in (x_{zr},\bar x)$ with $B(x^c_1) = 0$. Then $h^{(c)}(Q_r) = \min\{\bar G(x^c_1), Q_r\}$, $x^{(c)}(Q_r) = \bar x(1 - h^{(c)}(Q_r))$ (7), $x^c_2(Q_r) = \bar x(1-\min\{1,Q_r\})$ (11), and the planner's objective is $W^{(c)}(Q) = \mathbb E_Y[W(x^{(c)}(YQ), YQ)] - cQ$ (9).
--
--   **Equilibrium threshold (proofs of Propositions 3 and 5).** With a vaccination incentive $r$ paid to each vaccinated individual at supply $Q_r$, the individuals' threshold is the least $x \in [0,\bar x]$ with $x\bigl(u(h(x,Q_r)) - v(h(x,Q_r))\bigr) > w + p - r$, and $\bar x$ if there is none. With $r = 0$ it is the decentralized threshold $x^{(d)}(Q_r)$.
--
--   **Program and benchmarks (§5–§6).** The incentive and the transfer to the manufacturer are
--   $$r(Q_r) = w + p - \bar x(1-h^{(c)})(u(h^{(c)}) - v(h^{(c)})), \qquad (18)$$
--   $$T(Q_r) = K - (w+p)h^{(c)} - \tfrac{\bar x}{2}\bigl[(1-h^{(c)})^2(u(h^{(c)})-v(h^{(c)})) + v(h^{(c)})\bigr], \qquad (19)$$
--   with $h^{(c)} = h^{(c)}(Q_r)$ and a constant $K$; the planner's net payment is $S^{(I)}(Q_r) = T(Q_r) + r(Q_r)h^{(c)}(Q_r)$ (21). The manufacturer's expected profits are $\pi^{(I)}(Q) = \mathbb E_Y[w\,h(x^{(I)}(YQ),YQ) + T(YQ)] - cQ$ (17) and $\pi^{(d)}(Q) = w\,\mathbb E_Y[h(x^{(d)}(YQ),YQ)] - cQ$ (15); the decentralized welfare is $W^{(d)}(Q) = \mathbb E_Y[W(x^{(d)}(YQ),YQ)] - cQ$. Further $\bar K = V_H + \pi^{(d)} - W^{(d)}$ (22), $\underline K = V_H + \pi^{(d)} - W^{(c)}$ (23), and
--   $$K_{bn} = \tfrac{\bar x}{2}\,\mathbb E_Y\bigl[(1 - h^{(c)}(YQ^{(c)})^2)\,u(h^{(c)}(YQ^{(c)})) + h^{(c)}(YQ^{(c)})^2\, v(h^{(c)}(YQ^{(c)}))\bigr]. \qquad (24)$$
--   The individuals' ex-post total utility, at threshold $\hat x$, incentive $r$ and lump-sum tax $t$, is $V_H - (w+p-r)h - \tfrac{\bar x}{2}G^2(\hat x)u(h) - \tfrac{\bar x}{2}(1-G^2(\hat x))[\phi v(h) + (1-\phi)u(h)] - t$, the integral over $x \sim U[0,\bar x]$ of the utilities $U_u$, $U_v$ of p. 13.
--
--   These objects are everything Propositions 1, 2, 5, 6 and 7 are stated about.
--
--   **Formalization Note** The model data are a structure `Model` and the standing conditions a predicate `Standing`. Derivatives $u'$, $v'$ are taken within $[0,1]$, and Assumption 1(ii) is required on $[0, h_{zr})$. Assumption 1(iv) "decreasing" is read as strictly decreasing, and $c, w, p, \bar x > 0$ as the model's sign conventions. (4) is used in its second-line closed form. At $\hat x = \bar x$ Lean's $Q_r/0 = 0$ gives $\phi = 0$, which is multiplied by $1 - G^2 = 0$. The infimum in (1) is over a nonempty set (it contains $h = 1$), and $\bar x$ is inserted into the threshold set, so no junk $\inf\emptyset$ occurs. Expectations are Bochner integrals against the law of $Y$; $Q^{(c)}$, $Q^{(d)}$ and $K$ enter as arguments.
-- source:
--   Arifoğlu & Tang, A Two-Sided Incentive Program for Coordinating the Influenza Vaccine Supply Chain, revised manuscript of 17 June 2020 (MSOM 2022, doi:10.1287/msom.2020.0938), pp. 7–22, §3, (1)–(9), (11), (15), (17)–(24), Assumption 1; threshold rule: Online Supplement pp. 3–6, proofs of Propositions 3 and 5

import Mathlib

namespace FluVaccineCoord.TwoSided

open MeasureTheory Set

/-- The primitives of the flu vaccine supply chain of Arifoğlu–Tang (§3, pp. 7–10): the largest
infection cost `xbar` (x̄; infection costs are uniform on `[0, x̄]`), the wholesale price `w`, the
additional cost of vaccination `p`, the processing cost `c` of a planned unit, the utility `VH` of a
healthy individual, the infection probabilities `u h` (unvaccinated) and `v h` (vaccinated) as
functions of the vaccinated fraction `h ∈ [0, 1]`, and the law `μ` of the random yield `Y`
(the distribution `F` of p. 7). -/
structure Model where
  xbar : ℝ
  w : ℝ
  p : ℝ
  c : ℝ
  VH : ℝ
  u : ℝ → ℝ
  v : ℝ → ℝ
  μ : Measure ℝ

/-- `G(x) = x / x̄`, the cdf of the uniform infection cost (p. 9). -/
noncomputable def Gc (M : Model) (x : ℝ) : ℝ := x / M.xbar

/-- `Ḡ(x) = 1 − G(x) = 1 − x / x̄`, the vaccine demand of threshold `x` (p. 11). -/
noncomputable def Gbar (M : Model) (x : ℝ) : ℝ := 1 - x / M.xbar

/-- The zero-risk vaccination fraction `h_zr` of (1), p. 10. When `v 1 = 0` the set contains
`h = 1`, so it is nonempty and bounded below by `0`, and `sInf` is its true infimum. -/
noncomputable def hzr (M : Model) : ℝ :=
  if M.v 1 = 0 then sInf {h ∈ Icc (0 : ℝ) 1 | (1 - h) * M.u h + h * M.v h = 0} else 1

/-- `u′(h)`, the derivative of `u`, taken within `[0, 1]` (the domain of `u`; p. 10). -/
noncomputable def du (M : Model) (h : ℝ) : ℝ := derivWithin M.u (Icc 0 1) h

/-- `v′(h)`, the derivative of `v`, taken within `[0, 1]` (p. 10). -/
noncomputable def dv (M : Model) (h : ℝ) : ℝ := derivWithin M.v (Icc 0 1) h

/-- The standing assumptions of §3 (pp. 7–10) together with Assumption 1 (p. 10).
Assumption 1(iv) "decreasing" is read as strictly decreasing, and Assumption 1(ii) is required on
`[0, h_zr)`, where the derivatives exist. -/
structure Standing (M : Model) : Prop where
  xbar_pos : 0 < M.xbar
  w_pos : 0 < M.w
  p_pos : 0 < M.p
  c_pos : 0 < M.c
  /-- `Y` is a random variable with law `μ`. -/
  prob : IsProbabilityMeasure M.μ
  /-- `Y ∈ [0, ∞)` (p. 7). -/
  yield_nonneg : M.μ (Iio 0) = 0
  /-- `Y` has a mean `µ` (p. 7). -/
  yield_integrable : Integrable id M.μ
  /-- `wµ > c` (p. 7). -/
  wmu_gt_c : M.c < M.w * ∫ y, y ∂M.μ
  v_nonneg : ∀ h ∈ Icc (0 : ℝ) 1, 0 ≤ M.v h
  /-- `u(h) ≥ v(h)` (p. 10). -/
  v_le_u : ∀ h ∈ Icc (0 : ℝ) 1, M.v h ≤ M.u h
  u_le_one : ∀ h ∈ Icc (0 : ℝ) 1, M.u h ≤ 1
  /-- `u`, `v` are continuous in `h` (p. 10). -/
  u_cont : ContinuousOn M.u (Icc 0 1)
  v_cont : ContinuousOn M.v (Icc 0 1)
  /-- "by (1), `u(h) = v(h) = 0` for `h ≥ h_zr`" (p. 10). -/
  zero_risk : M.v 1 = 0 → ∀ h ∈ Icc (hzr M) 1, M.u h = 0 ∧ M.v h = 0
  /-- `u′`, `v′` exist (within `[0, 1]`) below `h_zr` (p. 10). -/
  diff : ∀ h ∈ Ico 0 (hzr M),
    DifferentiableWithinAt ℝ M.u (Icc 0 1) h ∧ DifferentiableWithinAt ℝ M.v (Icc 0 1) h
  /-- Assumption 1(i): `x̄ · u(0) ≥ w + p + x̄ · v(0)`. -/
  A1_i : M.w + M.p + M.xbar * M.v 0 ≤ M.xbar * M.u 0
  /-- Assumption 1(ii): `u′(h) < 0`, `v′(h) ≤ 0` for `h < h_zr`. -/
  A1_ii : ∀ h ∈ Ico 0 (hzr M), du M h < 0 ∧ dv M h ≤ 0
  /-- Assumption 1(iii): `(1 − h)u(h) + hv(h)` is convex on `[0, h_zr]`. -/
  A1_iii : ConvexOn ℝ (Icc 0 (hzr M)) (fun h => (1 - h) * M.u h + h * M.v h)
  /-- Assumption 1(iv), read strictly: `(1 − h)(u(h) − v(h))` is strictly decreasing on
  `[0, h_zr]`. -/
  A1_iv : StrictAntiOn (fun h => (1 - h) * (M.u h - M.v h)) (Icc 0 (hzr M))
  /-- Assumption 1(v): `h[((1 − h)u(h) + hv(h)) − v(h)]` is concave on `[0, h_zr]`. -/
  A1_v : ConcaveOn ℝ (Icc 0 (hzr M)) (fun h => h * (((1 - h) * M.u h + h * M.v h) - M.v h))

/-- The threshold `x_zr` of (5): `Ḡ(x_zr) = h_zr`, i.e. `x_zr = x̄ (1 − h_zr)`. -/
noncomputable def xzr (M : Model) : ℝ := M.xbar * (1 - hzr M)

/-- The vaccinated fraction ("sales") `h(x̂, Qᵣ) = min{Ḡ(x̂), Qᵣ}` of (2). -/
noncomputable def vacc (M : Model) (x Qr : ℝ) : ℝ := min (Gbar M x) Qr

/-- The fill rate `φ(x̂, Qᵣ) = min{1, Qᵣ / Ḡ(x̂)}` of (3). At `x̂ = x̄` (`Ḡ = 0`) Lean's `Qᵣ / 0 = 0`
gives `φ = 0`; every use multiplies `φ` by `1 − G² = 0` there. -/
noncomputable def fill (M : Model) (x Qr : ℝ) : ℝ := min 1 (Qr / Gbar M x)

/-- The ex-post social welfare `W(x̂, Qᵣ)` of (4), second line:
`V_H − p h − (x̄/2) G²(x̂) u(h) − (x̄/2)(1 − G²(x̂)) [φ v(h) + (1 − φ) u(h)]`. -/
noncomputable def welfare (M : Model) (x Qr : ℝ) : ℝ :=
  M.VH - M.p * vacc M x Qr - M.xbar / 2 * Gc M x ^ 2 * M.u (vacc M x Qr)
    - M.xbar / 2 * (1 - Gc M x ^ 2)
      * (fill M x Qr * M.v (vacc M x Qr) + (1 - fill M x Qr) * M.u (vacc M x Qr))

/-- The marginal social benefit `B(x̂)` of (6):
`p/x̄ + ½[G²(x̂) u′(Ḡ(x̂)) + (1 − G²(x̂)) v′(Ḡ(x̂))] − G(x̂)(u(Ḡ(x̂)) − v(Ḡ(x̂)))`. -/
noncomputable def Bm (M : Model) (x : ℝ) : ℝ :=
  M.p / M.xbar
    + 1 / 2 * (Gc M x ^ 2 * du M (Gbar M x) + (1 - Gc M x ^ 2) * dv M (Gbar M x))
    - Gc M x * (M.u (Gbar M x) - M.v (Gbar M x))

/-- `xc1` is the threshold `xᶜ₁` of (8): `xᶜ₁ = x_zr` if `lim_{x→x_zr⁺} B(x) ≤ 0`, and otherwise
`xᶜ₁ = x̌ ∈ (x_zr, x̄)` with `B(x̌) = 0`. Since `B` is monotone on `(x_zr, x̄)` (Lemma A.1(ii)), the
right limit at `x_zr` is the supremum of `B` there, so "limit `≤ 0`" is "`B ≤ 0` on `(x_zr, x̄)`". -/
def IsXc1 (M : Model) (xc1 : ℝ) : Prop :=
  ((∀ x ∈ Ioo (xzr M) M.xbar, Bm M x ≤ 0) ∧ xc1 = xzr M) ∨
  ((∃ x ∈ Ioo (xzr M) M.xbar, 0 < Bm M x) ∧ xc1 ∈ Ioo (xzr M) M.xbar ∧ Bm M xc1 = 0)

/-- The socially-optimal vaccinated fraction `h⁽ᶜ⁾(Qᵣ) = min{Ḡ(xᶜ₁), Qᵣ}` of (7). -/
noncomputable def hc (M : Model) (xc1 Qr : ℝ) : ℝ := min (Gbar M xc1) Qr

/-- The socially-optimal threshold `x⁽ᶜ⁾(Qᵣ)`, the threshold with `Ḡ(x⁽ᶜ⁾(Qᵣ)) = h⁽ᶜ⁾(Qᵣ)` (7). -/
noncomputable def xc (M : Model) (xc1 Qr : ℝ) : ℝ := M.xbar * (1 - hc M xc1 Qr)

/-- `xᶜ₂(Qᵣ) = Ḡ⁻¹(min{1, Qᵣ}) = x̄ (1 − min{1, Qᵣ})` of (11). -/
noncomputable def xc2 (M : Model) (Qr : ℝ) : ℝ := M.xbar * (1 - min 1 Qr)

/-- The planner's expected welfare `W⁽ᶜ⁾(Q) = E_Y[W(x⁽ᶜ⁾(YQ), YQ)] − cQ` of (9). -/
noncomputable def Wc (M : Model) (xc1 Q : ℝ) : ℝ :=
  (∫ y, welfare M (xc M xc1 (y * Q)) (y * Q) ∂M.μ) - M.c * Q

/-- The individuals' equilibrium threshold when the vaccination incentive at the realized supply
`Qᵣ` is `rr` (`rr = 0`: no program, `x⁽ᵈ⁾(Qᵣ)`; `rr = r(Qᵣ)`: `x⁽ᴵ⁾(Qᵣ)`). As in the proofs of
Propositions 3 and 5 (Online Supplement pp. 3–6), it is the least `x ∈ [0, x̄]` at which the
marginal individual strictly gains from seeking vaccination,
`x (u(h(x, Qᵣ)) − v(h(x, Qᵣ))) − (w + p − rr) > 0`, and `x̄` when there is no such `x`
("the threshold is equal to x̄ and nobody seeks vaccination"). Inserting `x̄` implements that
clause. -/
noncomputable def thr (M : Model) (rr Qr : ℝ) : ℝ :=
  sInf (insert M.xbar
    {x ∈ Icc 0 M.xbar | 0 < x * (M.u (vacc M x Qr) - M.v (vacc M x Qr)) - (M.w + M.p - rr)})

/-- The vaccination incentive of (18):
`r(Qᵣ) = w + p − x̄(1 − h⁽ᶜ⁾(Qᵣ))(u(h⁽ᶜ⁾(Qᵣ)) − v(h⁽ᶜ⁾(Qᵣ)))`. -/
noncomputable def rInc (M : Model) (xc1 Qr : ℝ) : ℝ :=
  M.w + M.p - M.xbar * (1 - hc M xc1 Qr) * (M.u (hc M xc1 Qr) - M.v (hc M xc1 Qr))

/-- The transfer payment to the manufacturer of (19):
`T(Qᵣ) = K − (w + p) h⁽ᶜ⁾ − (x̄/2)[(1 − h⁽ᶜ⁾)² (u(h⁽ᶜ⁾) − v(h⁽ᶜ⁾)) + v(h⁽ᶜ⁾)]`. -/
noncomputable def Tpay (M : Model) (xc1 K Qr : ℝ) : ℝ :=
  K - (M.w + M.p) * hc M xc1 Qr
    - M.xbar / 2 * ((1 - hc M xc1 Qr) ^ 2 * (M.u (hc M xc1 Qr) - M.v (hc M xc1 Qr))
      + M.v (hc M xc1 Qr))

/-- The planner's ex-post net payment `S⁽ᴵ⁾(Qᵣ) = T(Qᵣ) + r(Qᵣ) h⁽ᶜ⁾(Qᵣ)` of (21), first line. -/
noncomputable def Snet (M : Model) (xc1 K Qr : ℝ) : ℝ :=
  Tpay M xc1 K Qr + rInc M xc1 Qr * hc M xc1 Qr

/-- `K_bn = (x̄/2) E_Y[(1 − h⁽ᶜ⁾(YQ⁽ᶜ⁾)²) u(h⁽ᶜ⁾(YQ⁽ᶜ⁾)) + h⁽ᶜ⁾(YQ⁽ᶜ⁾)² v(h⁽ᶜ⁾(YQ⁽ᶜ⁾))]` of
(24), at a production quantity `Qc`. -/
noncomputable def Kbn (M : Model) (xc1 Qc : ℝ) : ℝ :=
  M.xbar / 2 * ∫ y, ((1 - hc M xc1 (y * Qc) ^ 2) * M.u (hc M xc1 (y * Qc))
    + hc M xc1 (y * Qc) ^ 2 * M.v (hc M xc1 (y * Qc))) ∂M.μ

/-- The manufacturer's expected profit under the program, (17):
`π⁽ᴵ⁾(Q) = E_Y[w h(x⁽ᴵ⁾(YQ), YQ) + T(YQ)] − cQ`, with `x⁽ᴵ⁾` the individuals' threshold `thr`
under the incentive `r`. -/
noncomputable def piI (M : Model) (xc1 K Q : ℝ) : ℝ :=
  (∫ y, (M.w * vacc M (thr M (rInc M xc1 (y * Q)) (y * Q)) (y * Q) + Tpay M xc1 K (y * Q)) ∂M.μ)
    - M.c * Q

/-- The manufacturer's expected profit without a program, (15): `w E_Y[h(x⁽ᵈ⁾(YQ), YQ)] − cQ`. -/
noncomputable def piD (M : Model) (Q : ℝ) : ℝ :=
  (∫ y, M.w * vacc M (thr M 0 (y * Q)) (y * Q) ∂M.μ) - M.c * Q

/-- The expected social welfare of the decentralized chain, `E_Y[W(x⁽ᵈ⁾(YQ), YQ)] − cQ`
(p. 20). -/
noncomputable def Wd (M : Model) (Q : ℝ) : ℝ :=
  (∫ y, welfare M (thr M 0 (y * Q)) (y * Q) ∂M.μ) - M.c * Q

/-- `K̄ = V_H + π⁽ᵈ⁾ − W⁽ᵈ⁾` of (22), at the decentralized production quantity `Qd`. -/
noncomputable def Kover (M : Model) (Qd : ℝ) : ℝ := M.VH + piD M Qd - Wd M Qd

/-- `K̲ = V_H + π⁽ᵈ⁾ − W⁽ᶜ⁾` of (23), at the decentralized `Qd` and the social optimum `Qc`. -/
noncomputable def Kunder (M : Model) (xc1 Qc Qd : ℝ) : ℝ := M.VH + piD M Qd - Wc M xc1 Qc

/-- The ex-post total utility of all individuals at threshold `x`, realized supply `Qᵣ`,
vaccination incentive `rr` and lump-sum tax `t`: everyone enjoys `V_H`; each of the `h` vaccinated
pays `w + p − rr`; an infected individual with cost `x` loses `x` (unvaccinated: probability
`u(h)`; seeking vaccination: `v(h)` if served, with probability `φ`, else `u(h)`); everyone pays
`t`. It is `∫₀^x̄ (U_u or U_v) dG − t` with `U_u`, `U_v` of p. 13 and `w + p` replaced by
`w + p − rr`. -/
noncomputable def indUtil (M : Model) (rr t x Qr : ℝ) : ℝ :=
  M.VH - (M.w + M.p - rr) * vacc M x Qr - M.xbar / 2 * Gc M x ^ 2 * M.u (vacc M x Qr)
    - M.xbar / 2 * (1 - Gc M x ^ 2)
      * (fill M x Qr * M.v (vacc M x Qr) + (1 - fill M x Qr) * M.u (vacc M x Qr))
    - t

/-- The individuals' total expected utility under the (modified) program `(t, r, T)` when the
manufacturer produces `Q` and individuals follow their equilibrium threshold `x⁽ᴵ⁾`. -/
noncomputable def EUtilI (M : Model) (xc1 t Q : ℝ) : ℝ :=
  ∫ y, indUtil M (rInc M xc1 (y * Q)) t (thr M (rInc M xc1 (y * Q)) (y * Q)) (y * Q) ∂M.μ

/-- The individuals' total expected utility without a program, at production `Q` and threshold
`x⁽ᵈ⁾`. -/
noncomputable def EUtilD (M : Model) (Q : ℝ) : ℝ :=
  ∫ y, indUtil M 0 0 (thr M 0 (y * Q)) (y * Q) ∂M.μ

end FluVaccineCoord.TwoSided


