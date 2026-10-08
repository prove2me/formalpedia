-- Prove2me | Definitions.Def_QualityEncroach_Differ_Reduced
-- name    : QualityEncroach_Differ_Reduced
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:44.915346+00:00
-- url     : https://prove2.me/theorems/cbf48a35-266e-47e3-bab6-9dbedf8c2190
-- title:
--   (7), p. 16; proofs of Lemma 1, pp. 29, 33 — closed-form quantities, wholesale price, reduced profits Π_M(t,u), optimal ratios t(u)
-- statement:
--   This file transcribes the closed-form expressions of the paper's backward induction for the game with quality differentiation. Throughout, $k>0$ is the cost-of-quality parameter, $c\ge0$ the direct selling cost, $w$ the wholesale price, $u$ the direct-channel quality and $t$ the quality ratio.
--
--   1. The subgame quantities of (7), p. 16 (for $t<1$):
--   $$
--   q_R(w,u,t)=\frac{1}{2(2-t)}-\frac{w}{t(2-t)u}+\frac{ku}{2(2-t)}+\frac{c}{2(2-t)u},\qquad
--   q_M(w,u,t)=\frac{4-3t}{4(2-t)}+\frac{w}{2(2-t)u}-\frac{(4-t)ku}{4(2-t)}-\frac{(4-t)c}{4(2-t)u}.
--   $$
--   2. The wholesale price and the manufacturer's reduced profit for $t\le1$ (proof of Lemma 1(i), p. 29):
--   $$
--   w(t,u)=\frac{tu}{2}+\frac{kt^2(7-4t)u^2}{2(8-5t)}-\frac{ct^2}{2(8-5t)},
--   $$
--   $$
--   \Pi^H(t,u)=\frac{4k^2u^3t^3-(8k^2u^3+8kcu)t^2-(k^2u^3+2kcu+c^2/u)t+8k^2u^3+16kcu+8c^2/u}{4(8-5t)}-\frac{2ku^2-u+2c}{4}.
--   $$
--   3. The manufacturer's reduced profit for $t\ge1$, (14), p. 33:
--   $$
--   \Pi^L(t,u)=\frac{4k^2u^3t^4-8ku^2t^3+4u(-2kc-2k^2u^2+2ku+1)t^2}{4(8t-5)}+\frac{8\bigl(c^2+cu(2ku-1)+ku^3(ku-1)\bigr)t}{4u(8t-5)}-\frac{(c+u(ku-1))^2}{4u(8t-5)}.
--   $$
--   4. The candidate optimal ratios of Lemma 1, p. 29, and the upper end of the feasible ratios in (16), p. 33:
--   $$
--   t^H(u)=\frac65-\frac25\sqrt{4-\frac{5c}{ku^2}},\qquad
--   t^L(u)=\frac{2+5ku+\sqrt{4-48kc+8ku-23k^2u^2}}{12ku},\qquad
--   \bar t_r(u)=\frac{1+\sqrt{4kc+4k^2u^2-4ku+1}}{2ku}.
--   $$
--   5. The profits along these ratios (proof of Lemma 1(iii), p. 29): $\Pi^H_M(u)=\Pi^H(t^H(u),u)$ and $\Pi^L_M(u)=\Pi^L(t^L(u),u)$.
--
--   These expressions are the objects of Lemma 1 and Claim 1, the technical core of the proofs of Propositions 3 and 4.
--
--   **Formalization Note.** The definitions are pure formulas. Lean's division by zero returns $0$ and its square root of a negative number returns $0$; every theorem that uses one of these expressions carries the range in which the paper uses it ($u>0$; $t\le1$ for $\Pi^H$; $t\ge1$ for $\Pi^L$; the radicands' sign conditions).
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 16, eq. (7); p. 29, Lemma 1 and proof of Lemma 1(i) and 1(iii); p. 33, proof of Lemma 1(ii), eqs. (14), (16)

import Mathlib

namespace QualityEncroach.Differ

/-!
# Closed-form expressions of the backward induction (§5 and the proofs, pp. 16, 29, 33)

Each definition transcribes a displayed formula of the paper; the page is cited.
-/

/-- `q_R(w, u, t)` of (7), p. 16 (the retailer's subgame quantity, `t < 1`). -/
noncomputable def qR7 (k c w u t : ℝ) : ℝ :=
  1 / (2 * (2 - t)) - w / (t * (2 - t) * u) + k * u / (2 * (2 - t)) + c / (2 * (2 - t) * u)

/-- `q_M(w, u, t)` of (7), p. 16 (the manufacturer's subgame quantity, `t < 1`). -/
noncomputable def qM7 (k c w u t : ℝ) : ℝ :=
  (4 - 3 * t) / (4 * (2 - t)) + w / (2 * (2 - t) * u) - (4 - t) * k * u / (4 * (2 - t))
    - (4 - t) * c / (4 * (2 - t) * u)

/-- `w(t, u)` of the proof of Lemma 1(i), p. 29 (`t ≤ 1`). -/
noncomputable def wH (k c t u : ℝ) : ℝ :=
  t * u / 2 + k * t ^ 2 * (7 - 4 * t) * u ^ 2 / (2 * (8 - 5 * t)) - c * t ^ 2 / (2 * (8 - 5 * t))

/-- `Π_M(t, u)` of the proof of Lemma 1(i), p. 29 (`t ≤ 1`). -/
noncomputable def PiH (k c t u : ℝ) : ℝ :=
  (4 * k ^ 2 * u ^ 3 * t ^ 3 - (8 * k ^ 2 * u ^ 3 + 8 * k * c * u) * t ^ 2
      - (k ^ 2 * u ^ 3 + 2 * k * c * u + c ^ 2 / u) * t
      + 8 * k ^ 2 * u ^ 3 + 16 * k * c * u + 8 * c ^ 2 / u) / (4 * (8 - 5 * t))
    - (2 * k * u ^ 2 - u + 2 * c) / 4

/-- `Π_M(t, u)` of (14), proof of Lemma 1(ii), p. 33 (`t ≥ 1`). -/
noncomputable def PiL (k c t u : ℝ) : ℝ :=
  (4 * k ^ 2 * u ^ 3 * t ^ 4 - 8 * k * u ^ 2 * t ^ 3
      + 4 * u * (-2 * k * c - 2 * k ^ 2 * u ^ 2 + 2 * k * u + 1) * t ^ 2) / (4 * (8 * t - 5))
    + 8 * (c ^ 2 + c * u * (2 * k * u - 1) + k * u ^ 3 * (k * u - 1)) * t / (4 * u * (8 * t - 5))
    - (c + u * (k * u - 1)) ^ 2 / (4 * u * (8 * t - 5))

/-- `t(u) = 6/5 − (2/5) √(4 − 5c/(k u²))` of Lemma 1(i), p. 29. -/
noncomputable def tH (k c u : ℝ) : ℝ :=
  6 / 5 - 2 / 5 * Real.sqrt (4 - 5 * c / (k * u ^ 2))

/-- `t(u) = (2 + 5ku + √(4 − 48kc + 8ku − 23k²u²)) / (12ku)` of Lemma 1(ii), p. 29. -/
noncomputable def tL (k c u : ℝ) : ℝ :=
  (2 + 5 * k * u + Real.sqrt (4 - 48 * k * c + 8 * k * u - 23 * k ^ 2 * u ^ 2)) / (12 * k * u)

/-- `t̄_r = (1 + √(4kc + 4k²u² − 4ku + 1)) / (2ku)` of (16), p. 33: for `t ≥ 1`, the retailer's
quantity is positive iff `t < t̄_r`. -/
noncomputable def tbarR (k c u : ℝ) : ℝ :=
  (1 + Real.sqrt (4 * k * c + 4 * k ^ 2 * u ^ 2 - 4 * k * u + 1)) / (2 * k * u)

/-- `Π^H_M(u) = Π_M(t(u), u)` with `t(u)` of Lemma 1(i) (proof of Lemma 1(iii), p. 29). -/
noncomputable def PiHu (k c u : ℝ) : ℝ :=
  PiH k c (tH k c u) u

/-- `Π^L_M(u) = Π_M(t(u), u)` with `t(u)` of Lemma 1(ii) (proof of Lemma 1(iii), p. 29). -/
noncomputable def PiLu (k c u : ℝ) : ℝ :=
  PiL k c (tL k c u) u

end QualityEncroach.Differ


