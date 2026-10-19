-- Prove2me | Definitions.Def_CoopetSourcing_WholesalePrice_Model
-- name    : CoopetSourcing_WholesalePrice_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:29.671337+00:00
-- url     : https://prove2.me/theorems/69e3dc1e-2b70-47f8-b266-6d495e41352f
-- title:
--   §3–§4.2, pp. 9–19 — VI–DO co-opetition: thresholds (1), (3), corrected (4); Lemma 1–2 and Prop. 1 quantities; VI profits Πs, Πp, Πn; the piecewise ΠI of (6); t̲, wA bound, (7)
-- statement:
--   The model of Jung and Kouvelis. A vertically integrated firm (VI, "she", production cost normalized to $0$) and a downstream firm (DO, "he") are Cournot rivals in an end market with inverse demand $P = 1 - Q + \epsilon$, where $Q$ is total output and the demand shock $\epsilon$ equals $t > 0$ (high demand, $H$) or $-t$ (low demand, $L$), each with probability $1/2$. Only the DO observes $\epsilon$. The VI offers the DO a unit wholesale price $w_I$; the DO orders $Q_{O,1}$ from the VI and $Q_{O,2}$ from an outside supplier at the unit price $w_A$; the VI observes $Q_{O,1}$ and produces $Q_I$. All objects below are explicit functions of the two parameters $t, w_A$ and of $w_I$.
--
--   1. **Constants** (p. 18): $\underline t = 28(4 + 5\sqrt2)/1105 \approx 0.2805$; Lemma 3's bound $\underline w = 126(17 - 3\sqrt{34})/(570\sqrt{34} - 15829) \approx 0.00497$; and equation (7), the condition $153(\sqrt{5134} - 122)\,x + 125\sqrt{21x(51x + 52)} = 0$ on a real $x$.
--
--   2. **Standing assumptions** $\mathrm{Standing}(t, w_A)$: $\underline t \le t$, $\underline w < w_A$ and $w_A < 1/2 - 5t/7$.
--
--   3. **Thresholds**: $\bar w^L_{sep,1} = \big(1 + 4w_A - 3t - 2\sqrt{6t(1 + 3t - 2w_A)}\big)/6$ and $\bar w^L_{sep,2} = t + w_A - (1 + 7t - 2w_A)/(4\sqrt2)$, equation (1); Lemma 1's bound $(1 + t)/2 - \sqrt6\,(7 + 10t - 14w_A)/35$;
--   $$\bar w_{sep/pool} = \frac{1620w_A - 3426t - 60 + 17\sqrt{6\big(25(1 - 2w_A)^2 + 6064t^2 - 320t(1 - 2w_A)\big)}}{1500}\quad(3),\qquad \bar w_I = \frac{245 - 350t - 70w_A - 6\sqrt{34}\,(7 - 10t - 14w_A)}{420}\quad(4).$$
--
--   4. **Separating quantities** (Lemma 1, pp. 12–13): $\hat Q^*_{O,1}(w_I|H) = (1 + t - 2w_I)/2$, $\hat Q^*_{O,2}(w_I|H) = 0$, $\hat Q^*_I(w_I|H) = (1 + t + 2w_I)/4$; the three-branch $\hat Q^*_{O,1}(w_I|L)$ (branches $w_I \le \bar w^L_{sep,1}$, $\bar w^L_{sep,1} < w_I \le \bar w^L_{sep,2}$, $w_I > \bar w^L_{sep,2}$, the last a positive part $[\,\cdot\,]^+$), $\hat Q^*_{O,2}(w_I|L)$ and $\hat Q^*_I(w_I|L)$ exactly as printed.
--
--   5. **Pooling quantities** (Lemma 2, pp. 14–15): $\tilde Q^*_{O,1}(w_I) = (7 - 10t - 2w_A - 12w_I)/17$ in both states, $\tilde Q^*_{O,2}(w_I|H) = (2 + 4t - 4w_A - 5\tilde Q^*_{O,1}(w_I))/6$, $\tilde Q^*_{O,2}(w_I|L) = 0$, $\tilde Q^*_I(w_I) = (1 - \tilde Q^*_{O,1}(w_I) - \tilde Q^*_{O,2}(w_I|H)/2)/2$.
--
--   6. **No-partnership quantities** (Proposition 1, p. 10): $Q^*_{O,2} = (2 - 4w_A)/5 \pm 4t/7$ in state $H$/$L$ and $Q^*_I = (3 + 4w_A)/10$.
--
--   7. **Profits**. The VI's profit in a state with shock $\epsilon$ is $(1 - (Q_{O,1} + Q_{O,2} + Q_I) + \epsilon)\,Q_I + w_I Q_{O,1}$ (p. S1). $\Pi^s_I(w_I)$, $\Pi^p_I(w_I)$ and $\Pi^{n*}_I$ are its averages over the two equally likely states at the separating, pooling and no-partnership quantities; $\Pi^{n*}_I = (3 + 4w_A)^2/100$. $\Pi^{s,4}_I(w_I)$ is the separating profit on the piece where $\hat Q^*_{O,1}(w_I|L) = 0$.
--
--   8. **The VI's problem**, equation (6), p. 17:
--   $$\Pi_I(w_I) = \begin{cases}\Pi^s_I(w_I) & w_I \le \bar w_{sep/pool},\\ \Pi^p_I(w_I) & \bar w_{sep/pool} < w_I < \bar w_I,\\ \Pi^{n*}_I & w_I \ge \bar w_I.\end{cases}$$
--
--   9. $\bar{\bar w}_{equal}$, equation (16), p. S6: the solution of $\Pi^{s,4}_I(w) = \Pi^p_I(\bar w_I)$ on the increasing branch $w \le (1 + t)/2$ of the concave quadratic $\Pi^{s,4}_I$.
--
--   10. Two readings of the equilibrium price $w_I^* = \arg\max_{w_I \in \mathbb R_+}\Pi_I(w_I)$: "$w_I^* = \bar w_{sep/pool}$" means $\bar w_{sep/pool} \ge 0$ is the unique maximizer of $\Pi_I$ over $w_I \ge 0$; "$w_I^* = \bar w_I^{(-)}$" means $\Pi_I(w_I) \le \Pi^p_I(\bar w_I)$ for every $w_I \ge 0$ and $\Pi_I(w_I) \to \Pi^p_I(\bar w_I)$ as $w_I \uparrow \bar w_I$.
--
--   These objects are the input of the VI's first-stage pricing problem; every statement of the mission is about them.
--
--   **Formalization Note** Equation (4) is **corrected**: the page (p. 14, and again p. S4) typesets $6\sqrt{34(7 - 10t - 14w_A)}$; the radical belongs over $34$ alone, as the derivation of the threshold, the printed identity in the proof of Lemma 3 (p. S5) and Table 1 (p. 21) require. The quantity-subgame equilibria of Lemmas 1–2 are taken as given through their closed forms; no equilibrium concept is encoded. The positive part is `max 0`. `Real.sqrt` returns $0$ on a negative radicand; every radicand used is nonnegative on the region where the statements use it. $\bar{\bar w}_{equal}$ is written as the smaller root of the quadratic, which is the root on the increasing branch.
-- source:
--   Jung & Kouvelis, “On Co-opetitive Supply Partnerships with End-Product Rivals”, SSRN preprint 3555184 (PDF of 2020-03-06), pp. 9–19, §3, §4.1–4.2, eqs. (1)–(7); Proposition 1 (p. 10), Lemma 1 (pp. 12–13), Lemma 2 (pp. 14–15); Online Supplement pp. S1, S5–S6 (profits, (16))

import Mathlib

namespace CoopetSourcing.WholesalePrice

noncomputable section

/-! Jung & Kouvelis, "On Co-opetitive Supply Partnerships with End-Product Rivals",
SSRN preprint 3555184 (PDF of 2020-03-06). The inverse demand is `P = 1 − Q + ε` with
`ε = t` or `ε = −t`, each with probability 1/2 (p. 9); the VI's production cost is 0;
`wA` is the outside supplier's unit price and `wI` the VI's wholesale price (p. 10). -/

/-- `t̲ := 28(4 + 5√2)/1105` (≈ 0.2805), Lemma 4, p. 18. -/
def tLow : ℝ := 28 * (4 + 5 * Real.sqrt 2) / 1105

/-- The bound of Lemma 3, p. 18: `126(17 − 3√34)/(570√34 − 15829)` (≈ 0.0049659, the page's
"0.005"; numerator and denominator are both negative). -/
def wALow : ℝ := 126 * (17 - 3 * Real.sqrt 34) / (570 * Real.sqrt 34 - 15829)

/-- Equation (7), Lemma 5, p. 18: `153(√5134 − 122)x + 125√(21x(51x + 52)) = 0`. -/
def Eq7 (x : ℝ) : Prop :=
  153 * (Real.sqrt 5134 - 122) * x + 125 * Real.sqrt (21 * x * (51 * x + 52)) = 0

/-- Standing assumptions: `t ≥ t̲` (p. 18, "we impose a mild assumption ... t ≥ t̲"),
`wA` above Lemma 3's bound (p. 18, "we assume wA > 0.005", with the exact value of Lemma 3),
and `wA < 1/2 − 5t/7` (p. 10). -/
def Standing (t wA : ℝ) : Prop :=
  tLow ≤ t ∧ wALow < wA ∧ wA < 1 / 2 - 5 * t / 7

/-- `w̄L_sep,1`, equation (1), p. 12. -/
def wSep1 (t wA : ℝ) : ℝ :=
  (1 + 4 * wA - 3 * t - 2 * Real.sqrt (6 * t * (1 + 3 * t - 2 * wA))) / 6

/-- `w̄L_sep,2`, equation (1), p. 12. -/
def wSep2 (t wA : ℝ) : ℝ :=
  t + wA - (1 + 7 * t - 2 * wA) / (4 * Real.sqrt 2)

/-- The existence bound of Lemma 1, p. 12: `(1 + t)/2 − √6(7 + 10t − 14wA)/35`
(the radical covers 6 only). -/
def sepBound (t wA : ℝ) : ℝ :=
  (1 + t) / 2 - Real.sqrt 6 * (7 + 10 * t - 14 * wA) / 35

/-- `w̄sep/pool`, equation (3), p. 14. -/
def wSepPool (t wA : ℝ) : ℝ :=
  (1620 * wA - 3426 * t - 60 +
      17 * Real.sqrt (6 * (25 * (1 - 2 * wA) ^ 2 + 6064 * t ^ 2 - 320 * t * (1 - 2 * wA)))) / 1500

/-- `w̄I`, equation (4), p. 14, **corrected**: the page typesets
`(245 − 350t − 70wA − 6√(34(7 − 10t − 14wA)))/420`; the radical belongs over 34 alone
(derivation of the threshold, the Lemma 3 identity on p. S5, and Table 1 on p. 21). -/
def wIBar (t wA : ℝ) : ℝ :=
  (245 - 350 * t - 70 * wA - 6 * Real.sqrt 34 * (7 - 10 * t - 14 * wA)) / 420

/-- `Q̂∗O,1(wI|H) = (1 + t − 2wI)/2`, Lemma 1 (i), p. 12 (and `Q̂∗O,2(wI|H) = 0`). -/
def sepQO1H (t wI : ℝ) : ℝ := (1 + t - 2 * wI) / 2

/-- `Q̂∗I(wI|H) = (1 + t + 2wI)/4`, Lemma 1 (ii), p. 13. -/
def sepQIH (t wI : ℝ) : ℝ := (1 + t + 2 * wI) / 4

/-- `Q̂∗O,1(wI|L)`, Lemma 1 (i), p. 12, three branches; `[x]⁺` is `max 0 x`. -/
def sepQO1L (t wA wI : ℝ) : ℝ :=
  if wI ≤ wSep1 t wA then
    (1 + 3 * t - 2 * Real.sqrt (t * (1 + 2 * t - 2 * wI)) - 2 * wI) / 2
  else if wI ≤ wSep2 t wA then
    Real.sqrt (2 * (t ^ 2 + t * (2 + 24 * wA - 28 * wI) + (1 + 4 * wA - 6 * wI) ^ 2))
      + 8 * wI - 3 * t - 6 * wA - 1
  else
    max 0 ((36 * wA * (1 - wA) - 32 * wI * (1 - wI) - t * (14 + 32 * wI - 60 * wA)
      - 17 * t ^ 2 - 1) / (64 * (wA - wI)))

/-- `Q̂∗O,2(wI|L)`, Lemma 1 (i), p. 12. -/
def sepQO2L (t wA wI : ℝ) : ℝ :=
  if wI ≤ wSep2 t wA then 0 else (1 - t - 2 * wA) / 2 - sepQO1L t wA wI

/-- `Q̂∗I(wI|L)`, Lemma 1 (ii), p. 13. -/
def sepQIL (t wA wI : ℝ) : ℝ :=
  if wI ≤ wSep2 t wA then (1 - t - sepQO1L t wA wI) / 2 else (1 - t + 2 * wA) / 4

/-- `Q̃∗O,1(wI) = (7 − 10t − 2wA − 12wI)/17`, Lemma 2 (i), p. 14. -/
def poolQO1 (t wA wI : ℝ) : ℝ := (7 - 10 * t - 2 * wA - 12 * wI) / 17

/-- `Q̃∗O,2(wI|H) = (2 + 4t − 4wA − 5Q̃∗O,1(wI))/6`, Lemma 2 (i), p. 14 (`Q̃∗O,2(wI|L) = 0`). -/
def poolQO2H (t wA wI : ℝ) : ℝ := (2 + 4 * t - 4 * wA - 5 * poolQO1 t wA wI) / 6

/-- `Q̃∗I(wI) = (1 − Q̃∗O,1(wI) − Q̃∗O,2(wI|H)/2)/2`, Lemma 2 (ii), p. 15. -/
def poolQI (t wA wI : ℝ) : ℝ := (1 - poolQO1 t wA wI - poolQO2H t wA wI / 2) / 2

/-- `Q∗O,2 = (2 − 4wA)/5 + 4ε/7` in state `ε = t`, Proposition 1, p. 10. -/
def noQO2H (t wA : ℝ) : ℝ := (2 - 4 * wA) / 5 + 4 * t / 7

/-- `Q∗O,2 = (2 − 4wA)/5 + 4ε/7` in state `ε = −t`, Proposition 1, p. 10. -/
def noQO2L (t wA : ℝ) : ℝ := (2 - 4 * wA) / 5 - 4 * t / 7

/-- `Q∗I = (3 + 4wA)/10`, Proposition 1, p. 10. -/
def noQI (wA : ℝ) : ℝ := (3 + 4 * wA) / 10

/-- The VI's profit in a demand state with shock `ε`:
`(1 − (QO,1 + QO,2 + QI) + ε)QI + wI·QO,1` (proof of Proposition 2, p. S1). -/
def stateProfitVI (ε wI QO1 QO2 QI : ℝ) : ℝ := (1 - (QO1 + QO2 + QI) + ε) * QI + wI * QO1

/-- `Πs_I(wI) = Πs_I(wI|H)/2 + Πs_I(wI|L)/2` at the separating quantities of Lemma 1
(proof of Lemma 4, p. S5). -/
def profitSep (t wA wI : ℝ) : ℝ :=
  (stateProfitVI t wI (sepQO1H t wI) 0 (sepQIH t wI)
    + stateProfitVI (-t) wI (sepQO1L t wA wI) (sepQO2L t wA wI) (sepQIL t wA wI)) / 2

/-- `Πp_I(wI)` at the pooling quantities of Lemma 2 (proof of Lemma 5, p. S6;
`Q̃∗I(wI|H) = Q̃∗I(wI|L) = Q̃∗I(wI)` and `Q̃∗O,2(wI|L) = 0`). -/
def profitPool (t wA wI : ℝ) : ℝ :=
  (stateProfitVI t wI (poolQO1 t wA wI) (poolQO2H t wA wI) (poolQI t wA wI)
    + stateProfitVI (-t) wI (poolQO1 t wA wI) 0 (poolQI t wA wI)) / 2

/-- `Πn∗_I = (Πn∗_I|H + Πn∗_I|L)/2` at the no-partnership quantities of Proposition 1
(proof of Lemma 3, p. S5; it equals `(3 + 4wA)²/100`). -/
def profitNo (t wA : ℝ) : ℝ :=
  (stateProfitVI t 0 0 (noQO2H t wA) (noQI wA)
    + stateProfitVI (-t) 0 0 (noQO2L t wA) (noQI wA)) / 2

/-- `ΠI(wI)`, equation (6), p. 17: `Πs∗_I` if `wI ≤ w̄sep/pool`, `Πp∗_I` if
`w̄sep/pool < wI < w̄I`, `Πn∗_I` if `wI ≥ w̄I`. -/
def profitVI (t wA wI : ℝ) : ℝ :=
  if wI ≤ wSepPool t wA then profitSep t wA wI
  else if wI < wIBar t wA then profitPool t wA wI
  else profitNo t wA

/-- `Πs,4_I(wI)`: the separating profit on the piece where `Q̂∗O,1(wI|L) = 0`, so
`Q̂∗O,2(wI|L) = (1 − t − 2wA)/2` and `Q̂∗I(wI|L) = (1 − t + 2wA)/4` (proof of Lemma 4, p. S5;
proof of Proposition 5, p. S7). -/
def profitSep4 (t wA wI : ℝ) : ℝ :=
  (stateProfitVI t wI (sepQO1H t wI) 0 (sepQIH t wI)
    + stateProfitVI (-t) wI 0 ((1 - t - 2 * wA) / 2) ((1 - t + 2 * wA) / 4)) / 2

/-- `w̿equal` of (16), proof of Lemma 5, p. S6: the solution of `Πs,4_I(w) = Πp_I(w̄I)` on the
increasing branch `w ≤ (1 + t)/2` of the concave quadratic
`Πs,4_I(w) = C + 3(1 + t)w/8 − 3w²/8`, `C = ((1 + t)² + (1 − t + 2wA)²)/32`. -/
def wEqualBar (t wA : ℝ) : ℝ :=
  ((1 + t) - Real.sqrt ((1 + t) ^ 2 - 32 / 3 * (profitPool t wA (wIBar t wA)
      - ((1 + t) ^ 2 + (1 - t + 2 * wA) ^ 2) / 32))) / 2

/-- "`w∗I = arg max_{wI ∈ ℝ+} ΠI(wI) = w̄sep/pool`": `w̄sep/pool ≥ 0` and it is the unique
maximizer of (6) over `wI ≥ 0`. -/
def MaxAtSepPool (t wA : ℝ) : Prop :=
  0 ≤ wSepPool t wA ∧
    ∀ wI : ℝ, 0 ≤ wI → wI ≠ wSepPool t wA → profitVI t wA wI < profitVI t wA (wSepPool t wA)

/-- "`w∗I = w̄(−)_I`": the supremum of (6) over `wI ≥ 0` is `Πp_I(w̄I)`, approached as
`wI ↑ w̄I` (not attained: (6) drops to `Πn∗_I` at `w̄I`). -/
def SupAtPoolCap (t wA : ℝ) : Prop :=
  (∀ wI : ℝ, 0 ≤ wI → profitVI t wA wI ≤ profitPool t wA (wIBar t wA)) ∧
    Filter.Tendsto (profitVI t wA) (nhdsWithin (wIBar t wA) (Set.Iio (wIBar t wA)))
      (nhds (profitPool t wA (wIBar t wA)))

end

end CoopetSourcing.WholesalePrice


