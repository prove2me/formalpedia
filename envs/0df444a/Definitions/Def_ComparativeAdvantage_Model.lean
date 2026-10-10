-- Prove2me | Definitions.Def_ComparativeAdvantage_Model
-- name    : ComparativeAdvantage_Model
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:29:30.492055+00:00
-- url     : https://prove2.me/theorems/a46a7dd1-ceec-4b6a-8e7a-4a1ee079495c
-- title:
--   Ricardian model: countries, autarky and trade sets, competitive output
-- statement:
--   This file fixes the vocabulary of the two-country, two-good (cloth and wine) Ricardian model with labour as the only factor of production.
--
--   1. **Country.** A country is given by its labour force $L$, the labour $a_{LC}$ needed to produce one unit of cloth, and the labour $a_{LW}$ needed to produce one unit of wine, all strictly positive. Foreign's data are written $L'$, $a'_{LC}$, $a'_{LW}$.
--   2. **Comparative advantage in cloth.** Home has a comparative advantage in cloth relative to Foreign when $$\frac{a_{LC}}{a_{LW}}<\frac{a'_{LC}}{a'_{LW}}.$$
--   3. **Autarky set.** The bundles $(Q_C,Q_W)$ with $Q_C,Q_W\ge0$ and $a_{LC}Q_C+a_{LW}Q_W\le L$.
--   4. **Trade set, cloth specialization.** At world prices $P_C,P_W$: the bundles with $Q_C,Q_W\ge0$ and $a_{LC}Q_C+a_{LC}\frac{P_W}{P_C}Q_W\le L$.
--   5. **Trade set, wine specialization.** The bundles with $Q_C,Q_W\ge0$ and $a_{LW}\frac{P_C}{P_W}Q_C+a_{LW}Q_W\le L$.
--   6. **Competitive output.** A bundle $(Q_C,Q_W)$ with $Q_C,Q_W\ge0$ and full employment $a_{LC}Q_C+a_{LW}Q_W=L$, such that cloth is produced ($Q_C>0$) only if $P_W/a_{LW}\le P_C/a_{LC}$, and wine is produced ($Q_W>0$) only if $P_C/a_{LC}\le P_W/a_{LW}$: labour works only in a sector paying the highest wage.
--   7. **Ricardo's countries.** England: $L=220$, $a_{LC}=100$, $a_{LW}=120$. Portugal: $L=170$, $a_{LC}=90$, $a_{LW}=80$ (hours of work).
--
--   Every statement of the mission is phrased in these terms.
--
--   **Formalization Note** Positivity of $L$, $a_{LC}$, $a_{LW}$ is stored inside the structure. Prices are not part of the structure; theorems that divide by prices assume them positive. Division by zero in Lean returns $0$, so the trade sets are only meaningful for positive prices.
-- source:
--   Wikipedia, "Comparative advantage" (PDF export supplied with the request); https://en.wikipedia.org/wiki/Comparative_advantage, section "Ricardian model" (and "Ricardo's example" for England/Portugal)

import Mathlib

namespace ComparativeAdvantage

/-- A country of the two-good (cloth, wine) one-factor Ricardian model.
`L` is its labour force, `aLC` the amount of labour required to produce one unit of cloth,
`aLW` the amount of labour required to produce one unit of wine. All three are positive. -/
structure Country where
  L : ℝ
  aLC : ℝ
  aLW : ℝ
  L_pos : 0 < L
  aLC_pos : 0 < aLC
  aLW_pos : 0 < aLW

/-- `h` has a comparative advantage in cloth relative to `f`: its opportunity cost of cloth in
terms of wine is lower, `aLC / aLW < a'LC / a'LW`. -/
def HasComparativeAdvantageInCloth (h f : Country) : Prop :=
  h.aLC / h.aLW < f.aLC / f.aLW

/-- Autarky production (= consumption) possibilities of `c`: the bundles `(QC, QW)` of cloth
and wine with `QC, QW ≥ 0` and `aLC * QC + aLW * QW ≤ L`. -/
def autarkySet (c : Country) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ c.aLC * q.1 + c.aLW * q.2 ≤ c.L}

/-- Consumption possibilities of `c` under free trade at world prices `PC` (cloth) and `PW`
(wine) when `c` produces cloth exclusively and trades cloth for wine:
`QC, QW ≥ 0` and `aLC * QC + aLC * (PW / PC) * QW ≤ L`. -/
def tradeSetCloth (c : Country) (PC PW : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ c.aLC * q.1 + c.aLC * (PW / PC) * q.2 ≤ c.L}

/-- Consumption possibilities of `c` under free trade at world prices `PC`, `PW` when `c`
produces wine exclusively and trades wine for cloth:
`QC, QW ≥ 0` and `aLW * (PC / PW) * QC + aLW * QW ≤ L`. -/
def tradeSetWine (c : Country) (PC PW : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ c.aLW * (PC / PW) * q.1 + c.aLW * q.2 ≤ c.L}

/-- `q = (QC, QW)` is a competitive output of `c` at prices `PC`, `PW`: labour is fully
employed (`aLC * QC + aLW * QW = L`, `QC, QW ≥ 0`), and labour works in a sector only if that
sector's wage (`PC / aLC` in cloth, `PW / aLW` in wine) is at least the other sector's wage. -/
def IsCompetitiveOutput (c : Country) (PC PW : ℝ) (q : ℝ × ℝ) : Prop :=
  0 ≤ q.1 ∧ 0 ≤ q.2 ∧ c.aLC * q.1 + c.aLW * q.2 = c.L ∧
    (0 < q.1 → PW / c.aLW ≤ PC / c.aLC) ∧ (0 < q.2 → PC / c.aLC ≤ PW / c.aLW)

/-- England in Ricardo's example: 220 hours of labour, 100 hours per unit of cloth,
120 hours per unit of wine. -/
noncomputable def england : Country where
  L := 220
  aLC := 100
  aLW := 120
  L_pos := by norm_num
  aLC_pos := by norm_num
  aLW_pos := by norm_num

/-- Portugal in Ricardo's example: 170 hours of labour, 90 hours per unit of cloth,
80 hours per unit of wine. -/
noncomputable def portugal : Country where
  L := 170
  aLC := 90
  aLW := 80
  L_pos := by norm_num
  aLC_pos := by norm_num
  aLW_pos := by norm_num

end ComparativeAdvantage


