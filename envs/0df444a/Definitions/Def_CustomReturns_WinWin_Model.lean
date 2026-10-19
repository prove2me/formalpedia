-- Prove2me | Definitions.Def_CustomReturns_WinWin_Model
-- name    : CustomReturns_WinWin_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:15:26.216964+00:00
-- url     : https://prove2.me/theorems/32940563-22fd-4d8e-a314-0b7c79d0a524
-- title:
--   Consumer choice, returns, and firm profit in Customization and Returns
-- statement:
--   Consumers have tastes $t$ uniformly distributed on $[0,1]$. The standard product has willingness to pay $t$; the customized product has willingness to pay $1+\alpha_c-(1-\beta_c)(1-t)$. Product $i$ matches a buyer's preference with probability $m_i$. A mismatch scales willingness to pay by $\theta$. After learning whether the product matches, the buyer keeps it if the keep payoff is at least the negative return fee, and otherwise returns it. Before purchase, a consumer chooses the product with the highest strictly positive expected utility, with a product tie assigned to the standard product.
--
--   A feasible policy has nonnegative prices $p_c,p_s$ and return fees $f_c,f_s$. The quantities $Q_i$, $Q_i^R$ and $Q_i^K$ are lengths of the respective buyer, mismatch-return, and keep segments of $[0,1]$. The expected number of returns is $R_i=(1-m_i)Q_i^R$. The firm's profit is
--
--   $$
--   \Pi=\sum_{i\in\{c,s\}}\bigl[Q_i(p_i-k_i)+R_i(f_i+r_i-p_i)\bigr],
--   $$
--
--   where $k_i$ is production cost and $r_i$ is recovery value. The module also defines an optimal feasible policy and the counterfactual that keeps the standard product's terms fixed while reoptimizing the customized price and fee subject to $R_c=0$. It records the thresholds and Solution 2/2b segment formulas used in the proposition's proof.
--
--   **Formalization Note** Consumers with zero expected utility do not buy. The proof of Proposition B1 and Table 2 use this rule, although the purchase prose on p. 7 uses a weak inequality. A buyer who would return on a match has nonpositive expected utility, so $R_i=(1-m_i)Q_i^R$ counts all purchased returns. The paper's probability and cost lower bounds $m_s\ge0$ and $k_s\ge0$ are stated explicitly. All segment lengths are Lebesgue measures on $[0,1]$.
-- source:
--   Esenduran, Letizia & Ovchinnikov, Customization and Returns, accepted manuscript (Management Science, accepted Dec. 13, 2021; SSRN 3444244), pp. 5–10 (PDF 5–10), eqs. (1)–(3), Table 1; Online Appendix pp. 3–5, 11–12, 14–15 (PDF 19–21, 27–28, 30–31), Table 6

import Mathlib

namespace CustomReturns.WinWin

/-- Parameters of the two-product consumer and firm model, Table 1. -/
structure Params where
  αc : ℝ
  βc : ℝ
  θ : ℝ
  mc : ℝ
  ms : ℝ
  kc : ℝ
  ks : ℝ
  rc : ℝ
  rs : ℝ

def Params.μc (P : Params) : ℝ := P.mc + (1 - P.mc) * P.θ
def Params.μs (P : Params) : ℝ := P.ms + (1 - P.ms) * P.θ

/-- Table 1, ordering 17, and the two assumptions in Appendix A.2.
The lower bounds on `ms` and `ks` make explicit the paper's probability and cost ranges. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.βc ∧ P.βc ≤ 1 ∧ 0 ≤ P.θ ∧ P.θ < 1 ∧
  0 ≤ P.ms ∧ P.ms < P.mc ∧ P.mc < 1 ∧
  0 ≤ P.ks ∧ P.ks ≤ P.kc ∧ P.kc < 1 ∧
  0 ≤ P.rc ∧ P.rc < 1 ∧ P.rc ≤ P.rs ∧
  P.μc * (1 - P.βc) < P.ms ∧
  P.kc < P.μc ∧ P.ks < P.μs ∧
  P.kc < P.mc + P.rc * (1 - P.mc) ∧
  P.ks < P.ms + P.rs * (1 - P.ms)

/-- Prices and return fees, problem (3). -/
structure Policy where
  pc : ℝ
  ps : ℝ
  fc : ℝ
  fs : ℝ

def Policy.Feasible (x : Policy) : Prop :=
  0 ≤ x.pc ∧ 0 ≤ x.ps ∧ 0 ≤ x.fc ∧ 0 ≤ x.fs

def wtpC (P : Params) (t : ℝ) : ℝ :=
  1 + P.αc - (1 - P.βc) * (1 - t)
def wtpS (t : ℝ) : ℝ := t

/-- Expected consumer utility with the return decision taken after match is learned. -/
def euC (P : Params) (x : Policy) (t : ℝ) : ℝ :=
  P.mc * max (wtpC P t - x.pc) (-x.fc) +
    (1 - P.mc) * max (P.θ * wtpC P t - x.pc) (-x.fc)
def euS (P : Params) (x : Policy) (t : ℝ) : ℝ :=
  P.ms * max (wtpS t - x.ps) (-x.fs) +
    (1 - P.ms) * max (P.θ * wtpS t - x.ps) (-x.fs)

/-- A consumer buys only with strictly positive expected utility; product ties go to `s`. -/
def buysC (P : Params) (x : Policy) (t : ℝ) : Prop :=
  0 < euC P x t ∧ euS P x t < euC P x t
def buysS (P : Params) (x : Policy) (t : ℝ) : Prop :=
  0 < euS P x t ∧ euC P x t ≤ euS P x t

/-- A mismatch is returned exactly when keeping yields less than the negative fee. -/
def returnsC (P : Params) (x : Policy) (t : ℝ) : Prop :=
  P.θ * wtpC P t - x.pc < -x.fc
def returnsS (P : Params) (x : Policy) (t : ℝ) : Prop :=
  P.θ * wtpS t - x.ps < -x.fs

noncomputable def QC (P : Params) (x : Policy) : ℝ :=
  (MeasureTheory.volume {t : ℝ | t ∈ Set.Icc 0 1 ∧ buysC P x t}).toReal
noncomputable def QRC (P : Params) (x : Policy) : ℝ :=
  (MeasureTheory.volume {t : ℝ | t ∈ Set.Icc 0 1 ∧ buysC P x t ∧ returnsC P x t}).toReal
noncomputable def QKC (P : Params) (x : Policy) : ℝ := QC P x - QRC P x
noncomputable def QS (P : Params) (x : Policy) : ℝ :=
  (MeasureTheory.volume {t : ℝ | t ∈ Set.Icc 0 1 ∧ buysS P x t}).toReal
noncomputable def QRS (P : Params) (x : Policy) : ℝ :=
  (MeasureTheory.volume {t : ℝ | t ∈ Set.Icc 0 1 ∧ buysS P x t ∧ returnsS P x t}).toReal
noncomputable def QKS (P : Params) (x : Policy) : ℝ := QS P x - QRS P x

noncomputable def RC (P : Params) (x : Policy) : ℝ := (1 - P.mc) * QRC P x
noncomputable def RS (P : Params) (x : Policy) : ℝ := (1 - P.ms) * QRS P x

/-- Expected profit in problem (3). -/
noncomputable def profit (P : Params) (x : Policy) : ℝ :=
  QC P x * (x.pc - P.kc) + RC P x * (x.fc + P.rc - x.pc) +
    QS P x * (x.ps - P.ks) + RS P x * (x.fs + P.rs - x.ps)
noncomputable def totalReturns (P : Params) (x : Policy) : ℝ := RC P x + RS P x

noncomputable def IsOptimal (P : Params) (x : Policy) : Prop :=
  x.Feasible ∧ ∀ y : Policy, y.Feasible → profit P y ≤ profit P x

/-- Problem (5): standard terms stay at the original optimum while customized returns
are disallowed and the customized price and fee are optimized. -/
noncomputable def IsOptimalNoCReturns (P : Params) (x y : Policy) : Prop :=
  y.Feasible ∧ y.ps = x.ps ∧ y.fs = x.fs ∧ RC P y = 0 ∧
    ∀ z : Policy, z.Feasible → z.ps = x.ps → z.fs = x.fs → RC P z = 0 →
      profit P z ≤ profit P y

/-- Thresholds in the proof of Proposition B1. Their displayed formulas require
positive denominators when used as consumer thresholds. -/
noncomputable def TLc (P : Params) (x : Policy) : ℝ :=
  (x.pc - x.fc - (P.αc + P.βc)) / (1 - P.βc)
noncomputable def THc (P : Params) (x : Policy) : ℝ :=
  (x.pc - x.fc - P.θ * (P.αc + P.βc)) / (P.θ * (1 - P.βc))
noncomputable def Zc (P : Params) (x : Policy) : ℝ :=
  (x.pc + ((1 - P.mc) / P.mc) * x.fc - (P.αc + P.βc)) / (1 - P.βc)
def TLs (x : Policy) : ℝ := x.ps - x.fs
noncomputable def THs (P : Params) (x : Policy) : ℝ := (x.ps - x.fs) / P.θ
noncomputable def Zs (P : Params) (x : Policy) : ℝ := x.ps + ((1 - P.ms) / P.ms) * x.fs
noncomputable def Tsc (P : Params) (x : Policy) : ℝ :=
  ((1 - P.ms) * x.fs - x.pc + P.ms * x.ps + P.μc * (P.αc + P.βc)) /
    (P.ms - (1 - P.βc) * P.μc)

/-- Table 6 and the proof of Proposition 2. -/
noncomputable def rSB1 (P : Params) : ℝ :=
  (P.μc * (1 - P.βc) * (P.ks - P.ms) +
    P.ms * ((1 + P.αc) * P.μc - P.kc)) /
    (P.μc * (1 - P.βc) * (1 - P.ms))
noncomputable def rSB2 (P : Params) : ℝ :=
  (P.ms * (1 - P.mc) * P.rc + P.ms * ((1 + P.αc) * P.mc - P.kc) +
    P.mc * (P.ks - P.ms) * (1 - P.βc)) /
    (P.mc * (1 - P.ms) * (1 - P.βc))
noncomputable def rbarbar_c (P : Params) : ℝ :=
  (P.θ * ((P.αc + P.βc) * P.ms - (1 - P.βc) * (P.kc - P.ks)) -
    (1 - P.βc) * (P.μs - P.ms) * P.rs) /
    (P.ms - (1 - P.βc) * P.μc)
def W (P : Params) : ℝ :=
  P.ms * (1 - P.mc) - P.mc * (1 - P.ms) * (1 - P.βc)

/-- Segment sizes of Solution 2, Appendix A.2, p. 4. -/
noncomputable def QRs2 (P : Params) : ℝ :=
  (P.θ * (P.kc - P.ks) - (P.μc - P.mc) * P.rc +
    (P.μs - (1 - P.βc) * P.mc) * P.rs -
    P.mc * P.θ * (P.αc + P.βc)) /
    (2 * P.θ * (P.ms - (1 - P.βc) * P.mc))
noncomputable def QKs2 (P : Params) : ℝ := (P.θ - P.rs) / (2 * P.θ)
noncomputable def QRc2 (P : Params) : ℝ :=
  ((1 + P.αc) * P.mc * P.ms - (1 - P.βc) * P.mc * (1 - P.ms) * P.rs +
    P.ms * (1 - P.mc) * P.rc + (1 - P.βc) * P.ks * P.mc -
    (1 - P.βc) * P.mc * P.ms - P.kc * P.ms) /
    (2 * (1 - P.βc) * P.mc * (P.ms - (1 - P.βc) * P.mc))

/-- Standard return-segment size of Solution 2b, proof of Proposition 2, p. 15. -/
noncomputable def QRs2b (P : Params) : ℝ :=
  (P.μs * P.rs - P.ks * P.θ) / (2 * P.θ * P.ms)

end CustomReturns.WinWin


