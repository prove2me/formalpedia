-- Prove2me | Definitions.Def_LongShortSI_ClosedForms
-- name    : LongShortSI_ClosedForms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:10.063018+00:00
-- url     : https://prove2.me/theorems/ec97b26b-5945-464b-b2dd-0fb63de99ed2
-- title:
--   Closed forms of (5)–(8), Table 2 (LL, SSI corrected, SSNI), Tables 4–5 ($h^{SS}_I$, $\widehat h$, $X$, $Y$, $P$, $Q$) and the E-Companion formulas (EC.2), (EC.4), (EC.6)
-- statement:
--   The closed-form expressions the paper prints, transcribed as named real functions of $(a,d,h)$, together with the equilibrium selector used by Proposition 3. With $D(d)=102-d(81-d(9+2(4-d)d))$:
--
--   1. **LL**, (5)–(7): $w^{LL*}=a\frac{1-d}{2-d}$, $q^{LL*}=\frac{a}{2(1+d)(2-d)}$, $\pi^{LL*}=\frac{a^2}{(2-d)^2(1+d)}$, $\Pi^{LL*}=\frac{a^2(1-d)}{(2-d)^2(1+d)}$; `MatchesLL` says an outcome is Table 2's LL column. The SSNI column is transcribed separately (`MatchesSSNI`).
--   2. **SSI**, Table 2 (p.28): $w^*_{i1}$ (the price (8)), $w^*_{i2}$, $q^*_{i1}$, $q^*_{i2}$, $s^*_{i1}$, $s^*_{i2}$, $\sum_t q^*_{it}$, $I^*_i$, and $\pi^*=X/(2(1-d)(1+d)D^2)$, $\Pi^*_i=Y/(2(1-d)(1+d)D^2)$ with $X,Y$ from Table 5. The row $s^*_{i1}$ is corrected: the page prints
--   $$
--   \frac{3a(16-d(3+d))-h(2-d)(6-9d+d^3)}{2(1+d)D(d)},
--   $$
--   and the correct sign of the $h$-term is $+$ (only then does $q^*_{i1}-I^*_i=s^*_{i1}$ hold, and only then is it (EC.6) at the price (8)). `MatchesSSI` says an outcome is this column (every row except the supply-chain total $\pi^*_{SC}$). `SSIEq` selects the SS equilibria whose first-period prices are both (8).
--   3. **Thresholds**, Table 4 and Table 5 (p.29): $h^{SS}_I(d)=P/(\dots)$ and $\widehat h(d)=Q/(\dots)$, with the square-root term of $P$ inside the $d^2(\cdots)$ bracket as printed, so that $h^{SS}_I(0)=\widehat h(0)=a/4$; and from ec5 $h^{SS}_{NI}(d)=\frac{a(1-d)}{(2-d)^2}$ and $\bar h^{SS}(d)=\frac{a(1-d)(30-d(9+d))}{(2-d)^2(30-d(9+d(3-d)))}$.
--   4. **E-Companion**: the thresholds $\bar w_{i2},\widehat w_{i2}$ and the purchases (EC.2); $\bar I_j,\widehat I_j$ and the prices (EC.4); $\bar{\bar w}_{i1}$, the inventory threshold $\bar w^{SS}_{i1}(w_{j1})=\frac{(3+d)(a(3-d)(1-d)-(2-d)^2h)+d(8-d^2)w_{j1}}{12-d^2}$ (the page multiplies by $12-d^2$; dividing is the root of $I^{SS}_{iFOC}=0$), the sales (EC.6) and $I^{SS}_{iFOC}$; the supplier's FOC profit $\Pi^{SSI}_i(w_{i1},w_{j1})$ and $\Pi^{SS}_{iFOC}$; and the deviation inducing $I_A=0$: the inventory $I^{SSI}_{BdevNIA}$, the profit $\Pi^{SSI}_{Adev}(w_{A1})$, the price $w^{SSI}_{A1devNIA}$ and $\Pi^{SSI}_{AdevNIA}=\Pi^{SSI}_{Adev}(w^{SSI}_{A1devNIA})$.
--
--   These are right-hand sides of the mission's theorems only.
--
--   **Formalization Note** The upper end $\widetilde I_j(I_i)=(a-2I_i)/(2d)$ of (EC.4)'s third branch is encoded as the condition $2dI_j<a-2I_i$, to avoid a division by zero at $d=0$; (EC.4)'s second branch, which divides by $d$, is empty at $d=0$. The expression printed for $\Pi^{SSI}_{AdevNIA}$ on ec5 repeats the deviation price, so the deviation profit is built from its printed ingredients instead. Divisions are Lean's total division; every denominator is nonzero for $d\in[0,1)$.
-- source:
--   Roy–Gilbert–Lai, The Implications of Strategic Inventory for Short-Term vs. Long-Term Supply Contracts in Nonexclusive Reselling Environments, SSRN 3752131 (version of 2022-04-20), (5)–(7), pp.9–10; (8), p.10; Table 2, p.28; Tables 4 and 5, p.29; E-Companion (EC.2), ec1 (PDF 33); (EC.4), ec2 (PDF 34); Lemma EC.3 and (EC.6), ec3 (PDF 35); (EC.8)–(EC.10), ec4 (PDF 36); §EC.1.1–EC.1.2, ec5 (PDF 37)

import Mathlib
import Definitions.Def_LongShortSI_Model

open scoped NNReal

namespace LongShortSI

/-! Closed forms printed in Roy–Gilbert–Lai, SSRN 3752131 (version of 2022-04-20): (5)–(8),
Table 2 (p.28), Tables 4–5 (p.29) and the E-Companion (ec1–ec6). They are right-hand sides of the
mission's theorems only; no equilibrium object of `Def_LongShortSI_Model` is defined through them. -/

/-- The common denominator `D(d) = 102 − d(81 − d(9 + 2(4 − d)d))` of (8) and Table 2. -/
noncomputable def D (d : ℝ) : ℝ := 102 - d * (81 - d * (9 + 2 * (4 - d) * d))

/-! ### LL, (5)–(7), pp.9–10; Table 2 column LL -/

/-- (5): `w^{LL*} = a(1 − d)/(2 − d)`. -/
noncomputable def wLL (a d : ℝ) : ℝ := a * ((1 - d) / (2 - d))

/-- (5): `q^{LL*} = a/(2(1 + d)(2 − d))`. -/
noncomputable def qLL (a d : ℝ) : ℝ := a / (2 * (1 + d) * (2 - d))

/-- Table 2, row `Σ_t q*_it`, column LL: `a/((1 + d)(2 − d))`. -/
noncomputable def sumqLL (a d : ℝ) : ℝ := a / ((1 + d) * (2 - d))

/-- (6): `π^{LL*} = a²/((2 − d)²(1 + d))`. -/
noncomputable def piLL (a d : ℝ) : ℝ := a ^ 2 / ((2 - d) ^ 2 * (1 + d))

/-- (7): `Π^{LL*} = a²(1 − d)/((2 − d)²(1 + d))`. -/
noncomputable def PiLL (a d : ℝ) : ℝ := a ^ 2 * (1 - d) / ((2 - d) ^ 2 * (1 + d))

/-- The outcome `o` is Table 2's LL column ((5)–(7)): every price is `w^{LL*}`, every purchase and
sale is `q^{LL*}`, no inventory, `Π_i = Π^{LL*}`, `π = π^{LL*}`. -/
def MatchesLL (a d : ℝ) (o : Outcome) : Prop :=
  (∀ i, o.w1 i = wLL a d ∧ o.w2 i = wLL a d ∧ o.q1 i = qLL a d ∧ o.q2 i = qLL a d ∧
    o.s1 i = qLL a d ∧ o.s2 i = qLL a d ∧ o.q1 i + o.q2 i = sumqLL a d ∧ o.inv i = 0 ∧
    o.supplier i = PiLL a d) ∧
  o.reseller = piLL a d

/-! ### Table 2 column SSNI, p.28 (transcribed separately from LL) -/

/-- Table 2, column SSNI, rows `w*_i1, w*_i2`: `a(1 − d)/(2 − d)` (also Proposition 1(ii), p.11). -/
noncomputable def wSSNI (a d : ℝ) : ℝ := a * ((1 - d) / (2 - d))

/-- Table 2, column SSNI, rows `q*_it` and `s*_it`: `a/(2(1 + d)(2 − d))`. -/
noncomputable def qSSNI (a d : ℝ) : ℝ := a / (2 * (1 + d) * (2 - d))

/-- Table 2, column SSNI, row `Σ_t q*_it`: `a/((1 + d)(2 − d))`. -/
noncomputable def sumqSSNI (a d : ℝ) : ℝ := a / ((1 + d) * (2 - d))

/-- Table 2, column SSNI, row `π*`: `a²/((2 − d)²(1 + d))`. -/
noncomputable def piSSNI (a d : ℝ) : ℝ := a ^ 2 / ((2 - d) ^ 2 * (1 + d))

/-- Table 2, column SSNI, row `Π*_i`: `a²(1 − d)/((2 − d)²(1 + d))`. -/
noncomputable def PiSSNI (a d : ℝ) : ℝ := a ^ 2 * (1 - d) / ((2 - d) ^ 2 * (1 + d))

/-- The outcome `o` is Table 2's SSNI column (no inventory held). -/
def MatchesSSNI (a d : ℝ) (o : Outcome) : Prop :=
  (∀ i, o.w1 i = wSSNI a d ∧ o.w2 i = wSSNI a d ∧ o.q1 i = qSSNI a d ∧ o.q2 i = qSSNI a d ∧
    o.s1 i = qSSNI a d ∧ o.s2 i = qSSNI a d ∧ o.q1 i + o.q2 i = sumqSSNI a d ∧ o.inv i = 0 ∧
    o.supplier i = PiSSNI a d) ∧
  o.reseller = piSSNI a d

/-! ### Table 2 column SSI, p.28, and Table 5 (X, Y), p.29 -/

/-- (8), p.10 = Table 2 row `w*_i1`, column SSI:
`(2a(3 − d)²(3 + d)(1 − d) − (2 − d)(6 − 9d + d³)h)/D(d)`. -/
noncomputable def w1SSI (a d h : ℝ) : ℝ :=
  (2 * a * (3 - d) ^ 2 * (3 + d) * (1 - d) - (2 - d) * (6 - 9 * d + d ^ 3) * h) / D d

/-- Table 2, row `w*_i2`, column SSI:
`(2 − d)(2a(3 − d)(3 + d)(1 − d) + h(30 − d(9 + (3 − d)d)))/D(d)`. -/
noncomputable def w2SSI (a d h : ℝ) : ℝ :=
  (2 - d) * (2 * a * (3 - d) * (3 + d) * (1 - d) + h * (30 - d * (9 + (3 - d) * d))) / D d

/-- Table 2, row `q*_i1`, column SSI:
`(2a(1 − d)(39 − d(9 + 2d)) − h(2 − d)(54 − d(33 + 6d − 4d²)))/(2(1 − d)(1 + d)D(d))`. -/
noncomputable def q1SSI (a d h : ℝ) : ℝ :=
  (2 * a * (1 - d) * (39 - d * (9 + 2 * d)) - h * (2 - d) * (54 - d * (33 + 6 * d - 4 * d ^ 2)))
    / (2 * (1 - d) * (1 + d) * D d)

/-- Table 2, row `q*_i2`, column SSI:
`(2 − d)(2a(3 − d)(3 + d)(1 − d) + h(30 − d(9 + (3 − d)d)))/(2(1 − d)(1 + d)D(d))`. -/
noncomputable def q2SSI (a d h : ℝ) : ℝ :=
  (2 - d) * (2 * a * (3 - d) * (3 + d) * (1 - d) + h * (30 - d * (9 + (3 - d) * d)))
    / (2 * (1 - d) * (1 + d) * D d)

/-- Table 2, row `s*_i1`, column SSI, and (EC.9), **corrected** (C1):
`(3a(16 − d(3 + d)) + h(2 − d)(6 − 9d + d³))/(2(1 + d)D(d))`. The page prints `−` before the
`h`-term; with `−` the row contradicts (EC.6) at the price (8) and the table's own `q*_i1 − I*_i`. -/
noncomputable def s1SSI (a d h : ℝ) : ℝ :=
  (3 * a * (16 - d * (3 + d)) + h * (2 - d) * (6 - 9 * d + d ^ 3)) / (2 * (1 + d) * D d)

/-- Table 2, row `s*_i2`, column SSI:
`(a(66 − d(27 + (5 − 2d)d)) − h(2 − d)(30 − d(9 + (3 − d)d)))/(2(1 + d)D(d))`. -/
noncomputable def s2SSI (a d h : ℝ) : ℝ :=
  (a * (66 - d * (27 + (5 - 2 * d) * d)) - h * (2 - d) * (30 - d * (9 + (3 - d) * d)))
    / (2 * (1 + d) * D d)

/-- Table 2, row `Σ_t q*_it`, column SSI:
`(2a(57 − d(18 + (4 − d)d)) − 3h(2 − d)(8 − d²))/(2(1 + d)D(d))`. -/
noncomputable def sumqSSI (a d h : ℝ) : ℝ :=
  (2 * a * (57 - d * (18 + (4 - d) * d)) - 3 * h * (2 - d) * (8 - d ^ 2)) / (2 * (1 + d) * D d)

/-- Table 2, row `I*_i`, column SSI, and (EC.10):
`(a(1 − d)(30 − d(9 + d)) − h(2 − d)²(30 − d(9 + (3 − d)d)))/(2(1 − d)(1 + d)D(d))`. -/
noncomputable def invSSI (a d h : ℝ) : ℝ :=
  (a * (1 - d) * (30 - d * (9 + d)) - h * (2 - d) ^ 2 * (30 - d * (9 + (3 - d) * d)))
    / (2 * (1 - d) * (1 + d) * D d)

/-- Table 5, `X`, p.29. -/
noncomputable def Xc (a d h : ℝ) : ℝ :=
  2 * a ^ 2 * (1 - d) * (2790 - d * (1512 + d * (153 - d * (198 - d * (21 + 2 * (4 - d) * d)))))
    - 2 * a * h * (1 - d) * (2124 - d * (1260 + d * (189 - d * (150 + 9 * d - 2 * d ^ 3))))
    + (2 - d) ^ 2 * h ^ 2
      * (2736 - d * (2664 - d * (432 + d * (372 - d * (171 - d * (9 + 2 * (5 - d) * d))))))

/-- Table 5, `Y`, p.29. -/
noncomputable def Yc (a d h : ℝ) : ℝ :=
  4 * a ^ 2 * (3 - d) ^ 3 * (1 - d) ^ 2 * (3 + d) * (17 - d ^ 2)
    - 4 * a * h * (2 - d) * (1 - d)
      * (306 - d * (459 - d * (54 + d * (93 - d * (18 + (5 - d) * d)))))
    + (2 - d) ^ 2 * h ^ 2 * (1224 - d * (1224 - d * (162 + d * (246 - d * (78 + d * (12 - 5 * d))))))

/-- Table 2, row `π*`, column SSI: `X/(2(1 − d)(1 + d)D(d)²)`. -/
noncomputable def piSSI (a d h : ℝ) : ℝ := Xc a d h / (2 * (1 - d) * (1 + d) * D d ^ 2)

/-- Table 2, row `Π*_i`, column SSI: `Y/(2(1 − d)(1 + d)D(d)²)`. -/
noncomputable def PiSSI (a d h : ℝ) : ℝ := Yc a d h / (2 * (1 - d) * (1 + d) * D d ^ 2)

/-- The outcome `o` is Table 2's SSI column (with C1 applied to `s*_i1`), every row except the
supply-chain total `π*_SC`. -/
def MatchesSSI (a d h : ℝ) (o : Outcome) : Prop :=
  (∀ i, o.w1 i = w1SSI a d h ∧ o.w2 i = w2SSI a d h ∧ o.q1 i = q1SSI a d h ∧
    o.q2 i = q2SSI a d h ∧ o.s1 i = s1SSI a d h ∧ o.s2 i = s2SSI a d h ∧
    o.q1 i + o.q2 i = sumqSSI a d h ∧ o.inv i = invSSI a d h ∧ o.supplier i = PiSSI a d h) ∧
  o.reseller = piSSI a d h

/-- The SSI equilibria of Proposition 1(i): subgame-perfect equilibria of the SS game whose
first-period prices are both (8). Parts (i)–(ii) of Proposition 3 compare these with LL (p.11:
"we focus on the SSI* and SSNI* equilibria"). -/
def SSIEq (a d h : ℝ) (σ : SSProfile) : Prop :=
  σ.IsSPE a d h ∧ (σ.w1A : ℝ) = w1SSI a d h ∧ (σ.w1B : ℝ) = w1SSI a d h

/-! ### Thresholds: Table 4 and Table 5 (P, Q), p.29; ec5 -/

/-- Table 5, `P`, p.29. The square-root term lies inside the `d²(…)` bracket, as printed. -/
noncomputable def Pc (a d : ℝ) : ℝ :=
  a * (1 - d) * (176256 - d ^ 2 * (47088 + d * (32184 - d * (12168 + d * (9090 - d * (2445
    + d * (819 - d * (213 + d * (23 - 6 * d))))))) + 2 * (12 - d ^ 2) * D d
      * Real.sqrt (153 - 27 * d ^ 2 + d ^ 4)))

/-- Table 4, `h^{SS}_I(d) = P/((2 − d)²(176256 − d²(83808 + d(6480 − d(17820 + d(2448
− d(2241 + d(300 − d(162 + d(12 − 5d))))))))))`, p.29. -/
noncomputable def hSSI (a d : ℝ) : ℝ :=
  Pc a d / ((2 - d) ^ 2 * (176256 - d ^ 2 * (83808 + d * (6480 - d * (17820 + d * (2448
    - d * (2241 + d * (300 - d * (162 + d * (12 - 5 * d))))))))))

/-- Table 5, `Q`, p.29. -/
noncomputable def Qc (a d : ℝ) : ℝ :=
  a * (1 - d) * (2 * (2 - d) * (306 - d * (459 - d * (54 + d * (93 - d * (18 + (5 - d) * d)))))
    - d * Real.sqrt 2 * Real.sqrt (72 + d * (30 - d * (4 - d) * (8 + 3 * d))) * D d)

/-- Table 4, `ĥ(d) = Q/((2 − d)²(1224 − d(1224 − d(162 + d(246 − d(78 + d(12 − 5d)))))))`,
p.29. -/
noncomputable def hhat (a d : ℝ) : ℝ :=
  Qc a d / ((2 - d) ^ 2 * (1224 - d * (1224 - d * (162 + d * (246 - d * (78 + d * (12 - 5 * d)))))))

/-- ec5: `h^{SS}_{NI}(d) = a(1 − d)/(2 − d)²`. -/
noncomputable def hSSNI (a d : ℝ) : ℝ := a * (1 - d) / (2 - d) ^ 2

/-- ec5: `h̄^{SS}(d) = a(1 − d)(30 − d(9 + d))/((2 − d)²(30 − d(9 + d(3 − d))))`. -/
noncomputable def hbarSS (a d : ℝ) : ℝ :=
  a * (1 - d) * (30 - d * (9 + d)) / ((2 - d) ^ 2 * (30 - d * (9 + d * (3 - d))))

/-! ### E-Companion formulas: Lemma EC.1 (ec1) -/

/-- ec1: `w̄_i2(I_i, w_j2) = a(1 − d) − 2(1 − d²)I_i + d w_j2`. -/
def wbar2 (a d Ii wj : ℝ) : ℝ := a * (1 - d) - 2 * (1 - d ^ 2) * Ii + d * wj

/-- ec1: `ŵ_i2(I_i, I_j) = a − 2(I_i + dI_j)`. -/
def what2 (a d Ii Ij : ℝ) : ℝ := a - 2 * (Ii + d * Ij)

/-- (EC.2), ec1: the purchase `q^{SS}_i2(I_i, I_j, w_i2, w_j2)` in its three branches. -/
noncomputable def q2EC2 (a d : ℝ) (I w : Product → ℝ) (i : Product) : ℝ :=
  if w i ≤ wbar2 a d (I i) (w i.other) ∧ w i.other ≤ wbar2 a d (I i.other) (w i) then
    (a * (1 - d) - 2 * (1 - d ^ 2) * I i - w i + d * w i.other) / (2 * (1 - d ^ 2))
  else if w i ≤ what2 a d (I i) (I i.other) ∧ wbar2 a d (I i.other) (w i) < w i.other then
    (a - w i - 2 * (I i + d * I i.other)) / 2
  else 0

/-! ### Lemma EC.2 (ec2) -/

/-- ec2: `Ī_j(I_i) = (1/4)(a(2 + d)/(1 + d) − 2dI_i)`. -/
noncomputable def Ibar (a d Ii : ℝ) : ℝ := (a * (2 + d) / (1 + d) - 2 * d * Ii) / 4

/-- ec2: `Î_j(I_i) = (a(2 − d) − 2dI_i)/(2(2 − d²))`. -/
noncomputable def Ihat (a d Ii : ℝ) : ℝ := (a * (2 - d) - 2 * d * Ii) / (2 * (2 - d ^ 2))

/-- (EC.4), ec2: supplier `i`'s second-period price `w^{SS}_i2(I_i, I_j)`.

**Formalization Note** The upper end `Ĩ_j(I_i) = (a − 2I_i)/(2d)` of the third branch is written
as the condition `2dI_j < a − 2I_i`, which is the printed condition for `d > 0` and avoids a
division by zero at `d = 0`. The second branch, which divides by `d`, is empty at `d = 0`
(`Ī_j = Î_j = a/2` there). -/
noncomputable def wEC4 (a d : ℝ) (I : Product → ℝ) (i : Product) : ℝ :=
  if I i < Ibar a d (I i.other) ∧ I i.other < Ibar a d (I i) then
    (1 - d) * (a * (2 + d) - 2 * (1 + d) * (2 * I i + d * I i.other)) / (4 - d ^ 2)
  else if I i < Ibar a d (I i.other) ∧ Ibar a d (I i) ≤ I i.other ∧ I i.other < Ihat a d (I i) then
    (1 - d) * (2 * (1 + d) * I i.other - a) / d
  else if I i < Ibar a d (I i.other) ∧ Ihat a d (I i) ≤ I i.other ∧
      2 * d * I i.other < a - 2 * I i then
    (a - 2 * (I i + d * I i.other)) / 2
  else 0

/-! ### Lemma EC.3 (ec3–ec4) -/

/-- ec3: `w̿_i1(w_j1) = a(1 − d) + d w_j1`. -/
def wbbar1 (a d wj : ℝ) : ℝ := a * (1 - d) + d * wj

/-- ec3, **corrected** (C4): `w̄^{SS}_i1(w_j1) = ((3 + d)(a(3 − d)(1 − d) − (2 − d)²h)
+ d(8 − d²)w_j1)/(12 − d²)`. The page multiplies by `(12 − d²)` instead of dividing; the
quotient is the root of `I^{SS}_{iFOC} = 0` on the same page. -/
noncomputable def wbarSS1 (a d h wj : ℝ) : ℝ :=
  ((3 + d) * (a * (3 - d) * (1 - d) - (2 - d) ^ 2 * h) + d * (8 - d ^ 2) * wj) / (12 - d ^ 2)

/-- (EC.6), ec3: `s^{SS}_i1(w_i1, w_j1) = (a(1 − d) − w_i1 + d w_j1)/(2(1 − d²))`. -/
noncomputable def s1EC6 (a d wi wj : ℝ) : ℝ := (a * (1 - d) - wi + d * wj) / (2 * (1 - d ^ 2))

/-- ec3: `I^{SS}_{iFOC}(w_i1, w_j1) = (a(3 − d)(1 − d) − (2 − d)²h)/(2(3 − d)(1 − d²))
− ((12 − d²)w_i1 − d(8 − d²)w_j1)/(2(9 − d²)(1 − d²))`. -/
noncomputable def invFOC (a d h wi wj : ℝ) : ℝ :=
  (a * (3 - d) * (1 - d) - (2 - d) ^ 2 * h) / (2 * (3 - d) * (1 - d ^ 2))
    - ((12 - d ^ 2) * wi - d * (8 - d ^ 2) * wj) / (2 * (9 - d ^ 2) * (1 - d ^ 2))

/-! ### §EC.1.1 (ec4–ec5): the FOC profit and the deviation that induces `I_A = 0` -/

/-- ec2: `w^{SS}_{i2FOC}(I_i, I_j) = (1 − d)(a(2 + d) − 2(1 + d)(2I_i + dI_j))/(4 − d²)`, the first
branch of (EC.4). -/
noncomputable def w2FOC (a d Ii Ij : ℝ) : ℝ :=
  (1 - d) * (a * (2 + d) - 2 * (1 + d) * (2 * Ii + d * Ij)) / (4 - d ^ 2)

/-- The first branch of (EC.2) at prices `w_i2, w_j2`. -/
noncomputable def q2FOC (a d Ii wi wj : ℝ) : ℝ :=
  (a * (1 - d) - 2 * (1 - d ^ 2) * Ii - wi + d * wj) / (2 * (1 - d ^ 2))

/-- Supplier `i`'s second-period profit `Π^{SSI}_i2(I_i, I_j)` on the first branches of (EC.2) and
(EC.4) (ec4). -/
noncomputable def profit2FOC (a d Ii Ij : ℝ) : ℝ :=
  w2FOC a d Ii Ij * q2FOC a d Ii (w2FOC a d Ii Ij) (w2FOC a d Ij Ii)

/-- ec4: `Π^{SSI}_i(w_i1, w_j1)`, supplier `i`'s two-period profit (EC.7) with `s` from (EC.6),
`I = I_FOC` and the period-2 profit on the first branches. -/
noncomputable def profitSSI (a d h wi wj : ℝ) : ℝ :=
  wi * (s1EC6 a d wi wj + invFOC a d h wi wj)
    + profit2FOC a d (invFOC a d h wi wj) (invFOC a d h wj wi)

/-- ec4: `Π^{SS}_{iFOC}`, `Π^{SSI}_i` at the prices (8) (EC.8). -/
noncomputable def PiFOC (a d h : ℝ) : ℝ := profitSSI a d h (w1SSI a d h) (w1SSI a d h)

/-- ec5: `I^{SSI}_{BdevNIA}`, the inventory of `B` when `I_A = 0` and supplier `B` offers (8):
`(2 + d)²(a(3 − d)(1 − d) − (2 − d)²(h + w^{SSI}_{B1FOC}))/(2(12 − d²)(1 − d²))`. -/
noncomputable def invDevB (a d h : ℝ) : ℝ :=
  (2 + d) ^ 2 * (a * (3 - d) * (1 - d) - (2 - d) ^ 2 * (h + w1SSI a d h))
    / (2 * (12 - d ^ 2) * (1 - d ^ 2))

/-- ec5: `Π^{SSI}_{Adev}(w_A1)`, supplier `A`'s profit when he offers `w_A1`, supplier `B` offers
(8), and the reseller holds `I_A = 0`, sells (EC.6) and holds `I^{SSI}_{BdevNIA}` of `B`. -/
noncomputable def devProfit (a d h wA : ℝ) : ℝ :=
  wA * s1EC6 a d wA (w1SSI a d h) + profit2FOC a d 0 (invDevB a d h)

/-- ec5: `w^{SSI}_{A1devNIA} = (a(1 − d)(102 − d(27 + d(9 − 2d))) − (2 − d)d(6 − 9d + d³)h)
/(204 − 2d(81 − d(9 + 2(4 − d)d)))`. -/
noncomputable def wDev (a d h : ℝ) : ℝ :=
  (a * (1 - d) * (102 - d * (27 + d * (9 - 2 * d))) - (2 - d) * d * (6 - 9 * d + d ^ 3) * h)
    / (204 - 2 * d * (81 - d * (9 + 2 * (4 - d) * d)))

/-- ec5: `Π^{SSI}_{AdevNIA}`, the deviation profit at the deviation price. (The expression printed
for it on ec5 repeats the deviation price; it is not transcribed.) -/
noncomputable def PiDev (a d h : ℝ) : ℝ := devProfit a d h (wDev a d h)

end LongShortSI


