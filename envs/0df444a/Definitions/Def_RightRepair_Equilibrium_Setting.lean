-- Prove2me | Definitions.Def_RightRepair_Equilibrium_Setting
-- name    : RightRepair_Equilibrium_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:45.748988+00:00
-- url     : https://prove2.me/theorems/698f6e51-e775-4a7a-afa2-de393078a99a
-- title:
--   §3–§4.1 and Appendix G — identical-quality repair market, cutoffs, Bellman system, and reduced pricing problems
-- statement:
--   The model describes a two-period durable good. A product fails after its first period with probability $f$, a functional used product gives a type-$\theta$ consumer utility $\delta\theta$, and repairs cost the manufacturer $c_M$ or an independent repairer $c_I$. Consumer types are uniformly distributed on $[0,1]$. The repair price is either a nonnegative real number or $\infty$, meaning that manufacturer repair is unavailable.
--
--   For a new-product price $p_n$, used-product price $p_u$, and effective repair cost $m=\min\{c_I,p_r\}$, the three per-period utilities are
--
--   $$
--   0,\qquad \delta\theta-p_u,\qquad
--   \theta-p_n+(1-f)p_u+f[p_u-m]^+.
--   $$
--
--   A secondary-market equilibrium assigns consumers to the utility-maximizing inactive, used, and new segments, applies the repair rule, and clears the market. At $p_u=0$, excess supply of used products is allowed. The manufacturer's profit is new-product margin times new-product demand plus its repair margin on manufacturer repairs. An optimal outcome has an equilibrium and earns at least as much as every equilibrium at every admissible competing price pair.
--
--   The file also defines the Table 1 prices and cutoffs, the Bellman equations (G.25), and the authors' reduced Problems 1, 4, and 5. Its polynomial $\pi_5$ extends the rational expression of (G.36) continuously across the denominator-zero line; the rational expression is retained separately.
--
--   **Formalization Note** The standing hypotheses include $0\le c$ and $0\le c_M$, as disclosed nonnegative unit-cost pins, alongside $0<f,\delta<1$, $c_M\le c_I$, and Assumption 1. The symbol $p_r=\infty$ is represented by `none`, rather than by a real number. At $p_u=0$ the market may have excess supply. An optimum need not be unique.
-- source:
--   Jin, Yang & Zhu, Right to Repair: Pricing, Welfare, and Environmental Implications, authors' manuscript of Management Science (2022), doi:10.1287/mnsc.2022.4401 (PDF sha256 b869b33a…1763), pp. 7, 12–14, Lemma 1, Assumption 1, Table 1; OA pp. 17, 20–22, 40, 43–44 (PDF 50, 53–55, 73, 76–77)

import Mathlib

namespace RightRepair.Equilibrium

structure Params where
  f : ℝ
  δ : ℝ
  c : ℝ
  cM : ℝ
  cI : ℝ

structure Standing (P : Params) : Prop where
  f_pos : 0 < P.f
  f_lt_one : P.f < 1
  δ_pos : 0 < P.δ
  δ_lt_one : P.δ < 1
  cM_le_cI : P.cM ≤ P.cI
  cM_lt_δ : P.cM < P.δ
  c_lt : P.c < 1 + P.δ - P.cM * P.f
  c_nonneg : 0 ≤ P.c
  cM_nonneg : 0 ≤ P.cM

def repairAdmissible (pr : Option ℝ) : Prop :=
  ∀ r, pr = some r → 0 ≤ r

def effRepair (P : Params) (pr : Option ℝ) : ℝ :=
  match pr with
  | none => P.cI
  | some r => min P.cI r

def uNew (P : Params) (pn : ℝ) (pr : Option ℝ) (pu θ : ℝ) : ℝ :=
  θ - pn + (1 - P.f) * pu + P.f * max (pu - effRepair P pr) 0

def uUsed (P : Params) (pu θ : ℝ) : ℝ := P.δ * θ - pu

def MarketEq (P : Params) (pn : ℝ) (pr : Option ℝ)
    (pu α θ₁ θ₂ : ℝ) : Prop :=
  0 ≤ pu ∧ 0 ≤ α ∧ α ≤ 1 ∧ 0 ≤ θ₁ ∧ θ₁ ≤ θ₂ ∧ θ₂ ≤ 1 ∧
  ((θ₁ = 1 ∧ θ₂ = 1 ∧
      (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
        uNew P pn pr pu θ ≤ 0 ∧ uUsed P pu θ ≤ 0)) ∨
    (∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      (θ < θ₁ → uNew P pn pr pu θ ≤ 0 ∧ uUsed P pu θ ≤ 0) ∧
      (θ₁ ≤ θ → θ < θ₂ → 0 ≤ uUsed P pu θ ∧
        uNew P pn pr pu θ ≤ uUsed P pu θ) ∧
      (θ₂ ≤ θ → 0 ≤ uNew P pn pr pu θ ∧
        uUsed P pu θ ≤ uNew P pn pr pu θ))) ∧
  (effRepair P pr < pu → α = 1) ∧
  (pu < effRepair P pr → α = 0) ∧
  (θ₂ - θ₁ = (1 - θ₂) * (1 - P.f + P.f * α) ∨
    (pu = 0 ∧ θ₂ - θ₁ ≤ (1 - θ₂) * (1 - P.f + P.f * α)))

noncomputable def profit (P : Params) (pn : ℝ) (pr : Option ℝ) (α θ₂ : ℝ) : ℝ :=
  (pn - P.c) * (1 - θ₂) +
    match pr with
    | none => 0
    | some r => if r ≤ P.cI then (r - P.cM) * (1 - θ₂) * P.f * α else 0

def OptimalOutcome (P : Params) (pn : ℝ) (pr : Option ℝ)
    (pu α : ℝ) : Prop :=
  0 ≤ pn ∧ repairAdmissible pr ∧
  ∃ θ₁ θ₂ : ℝ, MarketEq P pn pr pu α θ₁ θ₂ ∧
    ∀ pn' pr' pu' α' θ₁' θ₂',
      0 ≤ pn' → repairAdmissible pr' →
      MarketEq P pn' pr' pu' α' θ₁' θ₂' →
      profit P pn' pr' α' θ₂' ≤ profit P pn pr α θ₂

noncomputable def alphaHat (P : Params) (pn pr : ℝ) : ℝ :=
  ((P.δ * P.f ^ 2 - 4 * P.δ * P.f + 3 * P.δ + 1) * pr -
      P.δ * (2 - P.f) * pn + P.δ * (1 - P.δ) * (1 - P.f)) /
    (P.δ * P.f * (pn - (2 - P.f) * pr + P.δ - 1))

noncomputable def deltaBar (P : Params) : ℝ :=
  2 * P.f / (P.f ^ 2 - 2 * P.f + 4)

noncomputable def cIHat (P : Params) : ℝ :=
  (P.cM + P.δ + P.f * (P.δ - P.cM) * (1 - P.δ) /
    (2 * (1 - P.δ) - (2 - P.f) * Real.sqrt ((1 - P.δ) * (1 + 3 * P.δ)))) / 2

noncomputable def cILow (P : Params) : ℝ :=
  P.δ * P.f * (1 - P.δ) / (2 - P.δ + P.δ * (1 - P.f) * (3 - P.f))

noncomputable def cLow (P : Params) : ℝ :=
  ((P.δ * (1 - P.f) * (3 - P.f) + 1) * P.cM +
    P.δ * (1 - P.δ) * (1 - P.f)) / (P.δ * (2 - P.f))

noncomputable def cBar (P : Params) : ℝ :=
  (P.cM - P.δ ^ 2 + P.δ * (1 + P.cM * (3 - 2 * P.f))) / (2 * P.δ)

noncomputable def cPrimeLow (P : Params) : ℝ :=
  2 * P.cM - P.δ - P.cM * P.f + 1 -
    2 * (P.δ - P.cI) * (1 - P.δ) / (P.δ * (2 - P.f))

noncomputable def c2 (P : Params) : ℝ :=
  2 * (P.cI * (1 + P.δ * (1 - P.f) * (3 - P.f)) +
    P.δ * (1 - P.δ) * (1 - P.f)) / (P.δ * (2 - P.f)) -
      1 - P.δ * (1 - P.f)

noncomputable def c9 (P : Params) : ℝ :=
  1 + P.δ - P.cM * P.f +
    2 * (1 + 3 * P.δ) *
      (P.cI - P.δ + P.δ * Real.sqrt
        (P.f * (P.δ - P.cI) *
          (2 * P.cM - 4 * P.cI + 2 * P.δ + P.cI * P.f - P.cM * P.f) /
          (P.δ * (1 + 3 * P.δ)))) / (P.δ * (2 - P.f))

noncomputable def c10 (P : Params) : ℝ :=
  (P.δ * (1 - P.δ) + P.cM * (1 + 3 * P.δ - 2 * P.δ * P.f) +
    (2 * P.cI - P.δ - P.cM) * Real.sqrt ((1 - P.δ) * (1 + 3 * P.δ))) /
      (2 * P.δ)

noncomputable def c11 (P : Params) : ℝ :=
  if P.cI < cIHat P then c9 P else cPrimeLow P

noncomputable def c12 (P : Params) : ℝ :=
  if P.cI < cIHat P then c9 P else c10 P

noncomputable def cHat1 (P : Params) : ℝ := c2 P

noncomputable def cHat2 (P : Params) : ℝ :=
  if P.δ < deltaBar P ∨ (deltaBar P ≤ P.δ ∧ cIHat P < cILow P)
  then cPrimeLow P else c11 P

noncomputable def cHat3 (P : Params) : ℝ :=
  if P.δ < deltaBar P ∨ (deltaBar P ≤ P.δ ∧ cIHat P < cILow P)
  then c10 P else c12 P

noncomputable def pnNo (P : Params) : ℝ :=
  (P.c + 1 + P.δ * (1 - P.f)) / 2

noncomputable def puNo (P : Params) : ℝ :=
  P.δ * ((P.c + 1 + P.δ * (1 - P.f)) * (2 - P.f) -
    2 * (1 - P.f) * (1 - P.δ)) /
    (2 * (1 + P.δ * (1 - P.f) * (3 - P.f)))

noncomputable def pnFull (P : Params) : ℝ :=
  (P.c + 1 + P.δ + P.cM * P.f) / 2

noncomputable def puFull (P : Params) : ℝ :=
  P.δ * (2 * P.δ + P.c + P.cM * P.f) / (1 + 3 * P.δ)

noncomputable def pnNoLowI (P : Params) : ℝ :=
  (P.cI * (1 + P.δ * (1 - P.f) * (3 - P.f)) +
    P.δ * (1 - P.δ) * (1 - P.f)) / (P.δ * (2 - P.f))

noncomputable def pnPartialLowI (P : Params) : ℝ :=
  (1 + P.c - P.δ + (2 - P.f) * (2 * P.cI - P.cM)) / 2

noncomputable def theta2Problem1 (P : Params) (pn : ℝ) : ℝ :=
  if pn < (1 - P.f) * (1 - P.δ) / (2 - P.f) then
    pn / (1 - P.δ)
  else ((1 - P.f) * (2 - P.f) * P.δ + pn) /
    (1 + P.δ * (1 - P.f) * (3 - P.f))

noncomputable def profit1 (P : Params) (pn : ℝ) : ℝ :=
  (pn - P.c) * (1 - theta2Problem1 P pn)

def feasible1 (P : Params) (pn pr : ℝ) : Prop :=
  P.c ≤ pn ∧ pn < 1 + P.δ * (1 - P.f) ∧
  pn < P.cI * ((1 - P.f) * P.δ * (3 - P.f) + 1) /
    (P.δ * (2 - P.f)) + P.δ * (1 - P.δ) * (1 - P.f) /
      (P.δ * (2 - P.f)) ∧
  max 0 ((P.δ * (pn * (2 - P.f) - (1 - P.f) * (1 - P.δ))) /
    (1 + P.δ * (1 - P.f) * (3 - P.f))) < pr

noncomputable def theta2Problem4 (P : Params) (pn pr : ℝ) : ℝ :=
  (2 * P.δ + pn + P.f * pr) / (1 + 3 * P.δ)

noncomputable def profit4 (P : Params) (pn pr : ℝ) : ℝ :=
  (pn - P.c + (pr - P.cM) * P.f) * (1 - theta2Problem4 P pn pr)

def feasible4 (P : Params) (pn pr : ℝ) : Prop :=
  (1 - P.δ) / 2 ≤ pn ∧ pn ≤ 1 + P.δ ∧ 0 ≤ pr ∧
    pr ≤ P.cI ∧ pr ≤ (1 + P.δ - pn) / P.f ∧
    pr ≤ P.δ * (P.δ + 2 * pn - 1) /
      (1 + P.δ + 2 * P.δ * (1 - P.f))

noncomputable def theta2Problem5 (P : Params) (pn pr : ℝ) : ℝ :=
  (pn - pr - pr * (1 - P.f)) / (1 - P.δ)

noncomputable def profit5Raw (P : Params) (pn pr : ℝ) : ℝ :=
  (pn - P.c) * (1 - theta2Problem5 P pn pr) +
    (pr - P.cM) * (1 - theta2Problem5 P pn pr) * P.f * alphaHat P pn pr

-- The continuous polynomial extension of the displayed rational objective in (G.36).
noncomputable def profit5 (P : Params) (pn pr : ℝ) : ℝ :=
  (pn - P.c) * (1 - theta2Problem5 P pn pr) -
    (pr - P.cM) *
      ((P.δ * P.f ^ 2 - 4 * P.δ * P.f + 3 * P.δ + 1) * pr -
        P.δ * (2 - P.f) * pn + P.δ * (1 - P.δ) * (1 - P.f)) /
      (P.δ * (1 - P.δ))

def feasible5 (P : Params) (pn pr : ℝ) : Prop :=
  (1 - P.f) * (1 - P.δ) / (2 - P.f) ≤ pn ∧
  pn < 1 + P.δ * (1 - P.f) ∧
  pn < ((3 * P.δ - 2 * P.δ * P.f + 1) * P.cI - P.δ ^ 2 + P.δ) /
    (2 * P.δ) ∧
  P.δ * (P.δ + 2 * pn - 1) /
    (1 + P.δ + 2 * P.δ * (1 - P.f)) ≤ pr ∧
  pr ≤ P.cI ∧
  pr ≤ P.δ * (pn * (2 - P.f) - (1 - P.f) * (1 - P.δ)) /
    (1 + P.δ * (1 - P.f) * (3 - P.f))

def Bellman (P : Params) (pn : ℝ) (pr : Option ℝ) (pu θ lam G0 G1bar G1 : ℝ) : Prop :=
  lam + G0 = max (θ - pn + (1 - P.f) * G1bar + P.f * G1)
    (max (P.δ * θ - pu + G0) G0) ∧
  lam + G1bar = max (pu + θ - pn + (1 - P.f) * G1bar + P.f * G1)
    (max (P.δ * θ + G0) (pu + G0)) ∧
  lam + G1 = max (max (pu - effRepair P pr) 0 + θ - pn +
      (1 - P.f) * G1bar + P.f * G1)
    (max (max (pu - effRepair P pr) 0 + G0)
      (max (P.δ * θ - effRepair P pr) 0 + G0))

end RightRepair.Equilibrium


