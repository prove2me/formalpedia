-- Prove2me | Definitions.Def_MastSail_Monotone_Model
-- name    : MastSail_Monotone_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:47.72054+00:00
-- url     : https://prove2.me/theorems/eb249b92-f5df-431a-9750-bdc509d8614d
-- title:
--   §3, §5, §6, pp. 7–16 — store manager under demand censoring: MLRP densities, ratio functions (9)–(10), trigger plan (11), mast and sail regions, thresholds i_s, i_m, s*, monotonicity
-- statement:
--   This file fixes the store-manager model of Dai, Ke and Ryan in the two-effort-level setting of their §5.2, together with every object their mast-and-sail analysis refers to.
--
--   **Densities.** A probability density on $[a,b]$ is a function $p$ that is continuous and strictly positive on the closed interval $[a,b]$ and integrates to $1$ over it; its cumulative distribution function is $F(x)=\int_0^x p(t)\,dt$. A *model* consists of the initial inventory $\bar I$, the demand bound $\bar Q$, two inventory densities $f(\cdot\mid e^L_o)$, $f(\cdot\mid e^H_o)$ (low and high operational effort) and two demand densities $g(\cdot\mid e^L_m)$, $g(\cdot\mid e^H_m)$ (low and high marketing effort). Write $G(\cdot\mid e_m)$ for the demand distribution function. The *standing assumptions* are
--
--   1. $0<\bar I<\bar Q$;
--   2. $f(\cdot\mid e^L_o)$ and $f(\cdot\mid e^H_o)$ are densities on $[0,\bar I]$, and $g(\cdot\mid e^L_m)$, $g(\cdot\mid e^H_m)$ are densities on $[0,\bar Q]$;
--   3. the monotone likelihood ratio property (1): $f(i\mid e^L_o)/f(i\mid e^H_o)$ is nonincreasing in $i\in[0,\bar I]$ and $g(s\mid e^L_m)/g(s\mid e^H_m)$ is nonincreasing in $s\in[0,\bar Q]$.
--
--   *Strict MLRP of $g$* means that the second ratio is strictly decreasing on $[0,\bar Q]$.
--
--   **Ratio functions and weights.** The target action is $(e^H_o,e^H_m)$. Weights are three nonnegative numbers $\omega_{e^H_o,e^L_m}$, $\omega_{e^L_o,e^H_m}$, $\omega_{e^L_o,e^L_m}$ summing to $1$, one per deviation from the target. The no-stockout and stockout ratio functions (OA6)–(OA7) are
--   $$R^{NSO}_{e^H_o,e^L_m}(i,s)=1-\frac{g(s\mid e^L_m)}{g(s\mid e^H_m)},\quad R^{NSO}_{e^L_o,e^H_m}(i,s)=R^{SO}_{e^L_o,e^H_m}(i)=1-\frac{f(i\mid e^L_o)}{f(i\mid e^H_o)},\quad R^{NSO}_{e^L_o,e^L_m}(i,s)=1-\frac{f(i\mid e^L_o)\,g(s\mid e^L_m)}{f(i\mid e^H_o)\,g(s\mid e^H_m)},$$
--   $$R^{SO}_{e^H_o,e^L_m}(i)=1-\frac{1-G(i\mid e^L_m)}{1-G(i\mid e^H_m)},\qquad R^{SO}_{e^L_o,e^L_m}(i)=1-\frac{f(i\mid e^L_o)\,(1-G(i\mid e^L_m))}{f(i\mid e^H_o)\,(1-G(i\mid e^H_m))},$$
--   and $\varphi^{NSO}(i,s)=\sum\omega R^{NSO}(i,s)$, $\varphi^{SO}(i)=\sum\omega R^{SO}(i)$.
--
--   **Domain, plan and bonus regions.** The domain of a compensation plan is $D=\{(i,s):0\le s\le i,\ 0\le i\le\bar I\}$ (inventory $i$, sales $s$). For a trigger $t$ and a bonus $\bar w$, the plan (11) pays $\bar w$ on the *sail* $B^{NSO}=\{(i,s)\in D: s<i,\ \varphi^{NSO}(i,s)\ge t\}$ and on the *mast* $B^{SO}=\{(i,s)\in D: s=i,\ \varphi^{SO}(i)\ge t\}$, and $0$ elsewhere.
--
--   **Thresholds.** The sail's critical inventory $i_s$ is the least $i\in[0,\bar I]$ with $\varphi^{NSO}(i,i)\ge t$, and $i_s=\bar I$ when there is none. The mast's foot $i_m$ is the least $i\in[0,\bar I]$ with $\varphi^{SO}(i)\ge t$, and $i_m=\bar I$ when there is none. The sail boundary $s^*(i)$ is the least $s\in[0,\bar Q]$ with $\varphi^{NSO}(i,s)\ge t$, and $s^*(i)=\bar Q$ when there is none.
--
--   **Monotonicity (§6).** A plan $w$ is *monotone in $i$* if $w(i',s)\le w(i'',s)$ whenever $(i',s),(i'',s)\in D$ and $i'\le i''$; *monotone in $s$* if $w(i,s')\le w(i,s'')$ whenever $(i,s'),(i,s'')\in D$ and $s'\le s''$; and *(strictly) jointly monotone* if $w(i',s')\le w(i'',s'')$ whenever $(i',s'),(i'',s'')\in D$, $i'<i''$ and $s'<s''$.
--
--   **Joint law.** For densities $f$ on $[0,\bar I]$ and $g$ on $[0,\bar Q]$, the joint law of inventory $I$ and demand $Q$ is the product of the two laws (independence, p. 7).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Points of $D$ are pairs $(i,s)$, inventory first. Positivity of the densities on the *closed* supports and $\bar I<\bar Q$ (the paper has $\bar Q\ge\bar I$) are added so that $1-G(i\mid e^H_m)>0$ for $i\le\bar I$ and no ratio divides by zero; §4 (p. 9) assumes positive densities. The paper's "$\min\{s:\varphi^{NSO}(i,s)=t\}$" in (OA8) and "$\min\{i:\varphi^{SO}(i)=t\}$" are read as the least point where $\varphi\ge t$, which is defined in every case; the fallback values $\bar I$, $\bar I$, $\bar Q$ follow footnote 7 and the proof of Proposition 2. The weights are on the three incentive constraints of Theorem 2 (the target's own ratio is identically $0$).
-- source:
--   Dai, Ke & Ryan, SSRN 3235866, pp. 7–16 and oa4–oa5: §3 (MLRP (1), p. 7), §4 (positivity, p. 9), §5.1 (D, p. 12; (9)–(13), p. 13), §5.2 (p. 13), footnote 7 (p. 14), §6 (p. 16), (OA6)–(OA10) (p. oa4), i_m (p. oa5)

import Mathlib

namespace MastSail.Monotone

open MeasureTheory Classical

/-- `p` is a probability density on `[a, b]` (§3, p. 7; §4, p. 9): continuous and strictly
positive on the closed interval, with total mass `1` there. Values outside `[a, b]` are never
read. -/
def IsDensityOn (a b : ℝ) (p : ℝ → ℝ) : Prop :=
  ContinuousOn p (Set.Icc a b) ∧ (∀ x ∈ Set.Icc a b, 0 < p x) ∧ ∫ x in a..b, p x = 1

/-- The cumulative distribution function `F(x) = ∫₀ˣ p` of a density supported from `0`. -/
noncomputable def cdf (p : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, p t

/-- The store-manager model of §3 in the two-effort-level setting of §5.2 (target `(e^H_o, e^H_m)`):
initial inventory `Ī`, demand bound `Q̄`, inventory densities `f(·|e^L_o)`, `f(·|e^H_o)` on `[0, Ī]`
and demand densities `g(·|e^L_m)`, `g(·|e^H_m)` on `[0, Q̄]`. -/
structure Model where
  /-- initial inventory `Ī`; realized inventory lives in `[0, Ī]` -/
  Ibar : ℝ
  /-- upper bound `Q̄` on demand; demand lives in `[0, Q̄]` -/
  Qbar : ℝ
  /-- inventory density under low operational effort, `f(i | e^L_o)` -/
  fL : ℝ → ℝ
  /-- inventory density under high operational effort, `f(i | e^H_o)` -/
  fH : ℝ → ℝ
  /-- demand density under low marketing effort, `g(q | e^L_m)` -/
  gL : ℝ → ℝ
  /-- demand density under high marketing effort, `g(q | e^H_m)` -/
  gH : ℝ → ℝ

/-- The standing assumptions of §3 and §4: `0 < Ī < Q̄`, the four densities continuous, positive
and normalized on their closed supports, and the monotone likelihood ratio property (1). -/
def Model.Standing (M : Model) : Prop :=
  0 < M.Ibar ∧ M.Ibar < M.Qbar ∧
  IsDensityOn 0 M.Ibar M.fL ∧ IsDensityOn 0 M.Ibar M.fH ∧
  IsDensityOn 0 M.Qbar M.gL ∧ IsDensityOn 0 M.Qbar M.gH ∧
  AntitoneOn (fun i => M.fL i / M.fH i) (Set.Icc 0 M.Ibar) ∧
  AntitoneOn (fun s => M.gL s / M.gH s) (Set.Icc 0 M.Qbar)

/-- Strict MLRP of the demand densities: `g(s|e^L_m)/g(s|e^H_m)` strictly decreasing on `[0, Q̄]`. -/
def Model.StrictMLRPg (M : Model) : Prop :=
  StrictAntiOn (fun s => M.gL s / M.gH s) (Set.Icc 0 M.Qbar)

/-- The weights `ω` of (11) on the three deviations from the target:
`wHL = ω_{e^H_o,e^L_m}`, `wLH = ω_{e^L_o,e^H_m}`, `wLL = ω_{e^L_o,e^L_m}`. -/
structure Weights where
  wHL : ℝ
  wLH : ℝ
  wLL : ℝ

/-- Nonnegative weights summing to `1` ((11), p. 13). -/
def Weights.Valid (ω : Weights) : Prop :=
  0 ≤ ω.wHL ∧ 0 ≤ ω.wLH ∧ 0 ≤ ω.wLL ∧ ω.wHL + ω.wLH + ω.wLL = 1

/-- `R^NSO_{e^H_o,e^L_m}(i, s) = 1 − g(s|e^L_m)/g(s|e^H_m)` (OA6). -/
noncomputable def RNSO_HL (M : Model) (s : ℝ) : ℝ := 1 - M.gL s / M.gH s

/-- `R^NSO_{e^L_o,e^H_m}(i, s) = 1 − f(i|e^L_o)/f(i|e^H_o)` (OA6); also `R^SO_{e^L_o,e^H_m}` (OA7). -/
noncomputable def RNSO_LH (M : Model) (i : ℝ) : ℝ := 1 - M.fL i / M.fH i

/-- `R^NSO_{e^L_o,e^L_m}(i, s) = 1 − f(i|e^L_o)g(s|e^L_m)/(f(i|e^H_o)g(s|e^H_m))` (OA6). -/
noncomputable def RNSO_LL (M : Model) (i s : ℝ) : ℝ :=
  1 - (M.fL i * M.gL s) / (M.fH i * M.gH s)

/-- `R^SO_{e^H_o,e^L_m}(i) = 1 − (1 − G(i|e^L_m))/(1 − G(i|e^H_m))` (OA7). -/
noncomputable def RSO_HL (M : Model) (i : ℝ) : ℝ :=
  1 - (1 - cdf M.gL i) / (1 - cdf M.gH i)

/-- `R^SO_{e^L_o,e^L_m}(i) = 1 − f(i|e^L_o)(1 − G(i|e^L_m))/(f(i|e^H_o)(1 − G(i|e^H_m)))` (OA7). -/
noncomputable def RSO_LL (M : Model) (i : ℝ) : ℝ :=
  1 - (M.fL i * (1 - cdf M.gL i)) / (M.fH i * (1 - cdf M.gH i))

/-- `φ^NSO(i, s) = Σ ω R^NSO(i, s)` (OA9). -/
noncomputable def phiNSO (M : Model) (ω : Weights) (i s : ℝ) : ℝ :=
  ω.wHL * RNSO_HL M s + ω.wLH * RNSO_LH M i + ω.wLL * RNSO_LL M i s

/-- `φ^SO(i) = Σ ω R^SO(i)` (proof of Proposition 2, p. oa5). -/
noncomputable def phiSO (M : Model) (ω : Weights) (i : ℝ) : ℝ :=
  ω.wHL * RSO_HL M i + ω.wLH * RNSO_LH M i + ω.wLL * RSO_LL M i

/-- The domain `D = {(i, s) : 0 ≤ s ≤ i, 0 ≤ i ≤ Ī}` of a compensation plan (p. 12). -/
def inD (M : Model) (i s : ℝ) : Prop := 0 ≤ s ∧ s ≤ i ∧ i ≤ M.Ibar

/-- The sail `B^NSO = {(i, s) ∈ D : s < i, φ^NSO(i, s) ≥ t}` (12); pairs are `(i, s)`. -/
def bonusNSO (M : Model) (ω : Weights) (t : ℝ) : Set (ℝ × ℝ) :=
  {p | inD M p.1 p.2 ∧ p.2 < p.1 ∧ t ≤ phiNSO M ω p.1 p.2}

/-- The mast `B^SO = {(i, s) ∈ D : s = i, φ^SO(i) ≥ t}` (13); pairs are `(i, s)`. -/
def bonusSO (M : Model) (ω : Weights) (t : ℝ) : Set (ℝ × ℝ) :=
  {p | inD M p.1 p.2 ∧ p.2 = p.1 ∧ t ≤ phiSO M ω p.1}

/-- The information-trigger plan (11) with weights `ω`, trigger `t` and bonus `w̄`:
`w̄` on `B^NSO ∪ B^SO`, `0` elsewhere. Only its values on `D` matter. -/
noncomputable def plan (M : Model) (ω : Weights) (t wbar : ℝ) (i s : ℝ) : ℝ :=
  if (i, s) ∈ bonusNSO M ω t ∪ bonusSO M ω t then wbar else 0

/-- The sail's critical inventory `i_s` (OA10): the least `i ∈ [0, Ī]` with `φ^NSO(i, i) ≥ t`,
and `Ī` when there is none (footnote 7, p. 14). -/
noncomputable def iS (M : Model) (ω : Weights) (t : ℝ) : ℝ :=
  if ∃ i ∈ Set.Icc 0 M.Ibar, t ≤ phiNSO M ω i i then
    sInf {i | i ∈ Set.Icc 0 M.Ibar ∧ t ≤ phiNSO M ω i i}
  else M.Ibar

/-- The mast's foot `i_m` (proof of Proposition 2, p. oa5): the least `i ∈ [0, Ī]` with
`φ^SO(i) ≥ t`, and `Ī` when there is none. -/
noncomputable def iM (M : Model) (ω : Weights) (t : ℝ) : ℝ :=
  if ∃ i ∈ Set.Icc 0 M.Ibar, t ≤ phiSO M ω i then
    sInf {i | i ∈ Set.Icc 0 M.Ibar ∧ t ≤ phiSO M ω i}
  else M.Ibar

/-- The sail's lower boundary `s*(i)` (OA8): the least `s ∈ [0, Q̄]` with `φ^NSO(i, s) ≥ t`,
and `Q̄` when there is none. -/
noncomputable def sStar (M : Model) (ω : Weights) (t : ℝ) (i : ℝ) : ℝ :=
  if ∃ s ∈ Set.Icc 0 M.Qbar, t ≤ phiNSO M ω i s then
    sInf {s | s ∈ Set.Icc 0 M.Qbar ∧ t ≤ phiNSO M ω i s}
  else M.Qbar

/-- `w` is monotone in `i` on `D` (§6, p. 16). -/
def MonotoneInI (M : Model) (w : ℝ → ℝ → ℝ) : Prop :=
  ∀ i' i'' s, inD M i' s → inD M i'' s → i' ≤ i'' → w i' s ≤ w i'' s

/-- `w` is monotone in `s` on `D` (§6, p. 16). -/
def MonotoneInS (M : Model) (w : ℝ → ℝ → ℝ) : Prop :=
  ∀ i s' s'', inD M i s' → inD M i s'' → s' ≤ s'' → w i s' ≤ w i s''

/-- `w` is (strictly) jointly monotone on `D` (§6, p. 16, footnote 8): strict increase in both
coordinates. -/
def JointlyMonotone (M : Model) (w : ℝ → ℝ → ℝ) : Prop :=
  ∀ i' s' i'' s'', inD M i' s' → inD M i'' s'' → i' < i'' → s' < s'' → w i' s' ≤ w i'' s''

/-- The joint law of inventory `I` (first coordinate) and demand `Q` (second coordinate):
the product of the law with density `f` on `[0, Ī]` and the law with density `g` on `[0, Q̄]`
(independence, p. 7). -/
noncomputable def jointLaw (Ibar Qbar : ℝ) (f g : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  ((volume.restrict (Set.Icc 0 Ibar)).withDensity (fun x => ENNReal.ofReal (f x))).prod
    ((volume.restrict (Set.Icc 0 Qbar)).withDensity (fun x => ENNReal.ofReal (g x)))

end MastSail.Monotone


