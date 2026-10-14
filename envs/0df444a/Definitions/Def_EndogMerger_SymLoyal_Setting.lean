-- Prove2me | Definitions.Def_EndogMerger_SymLoyal_Setting
-- name    : EndogMerger_SymLoyal_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:19.242921+00:00
-- url     : https://prove2.me/theorems/45ac8311-a32e-4e4e-853d-7fd0cb234158
-- title:
--   §3, (1a)–(2b), Table A1, PDF pp. 7–10, 19, 32 — Table A1 price-support bounds and equilibrium profits, merger conditions, equilibrium structure
-- statement:
--   Three firms $A$, $B$, $C$ sell a homogeneous product at zero marginal cost to a unit mass of buyers, each demanding one unit and valuing it at the reservation price $r$. Each firm has $\alpha$ loyal buyers ($0<\alpha<1/3$); the remaining $1-3\alpha$ buyers are switchers who buy from the cheapest firm. Firm $A$ has ample capacity; the small firms $B$ and $C$ have capacity $k$ each, with $k>\alpha$. Write
--   $$
--   s_1=(1-3\alpha)\Bigl(1-\frac{k}{1-2\alpha}\Bigr),\qquad s_2=s_1\Bigl(1-\frac{k}{\alpha+s_1}\Bigr),\qquad s_3=(1-3\alpha)\Bigl(1-\frac{2k}{1-\alpha}\Bigr),
--   $$
--   and $\bar k=(1-2\alpha)^2/(2-5\alpha)$, $k^*=\alpha(1-2\alpha)/(1-3\alpha)$.
--
--   This file defines, as functions of $(\alpha,k,r)$, the lower bounds of price support and the equilibrium profits of Table A1 of the paper in the three market structures:
--
--   1. the independent structure $\{A,B,C\}$: $L^{(0)}$, $\Pi^{(0)}_A$, and $\Pi^{(0)}_B=\Pi^{(0)}_C$;
--   2. the mixed merger $\{AB,C\}$ (firm $A$ merged with firm $B$): $L^{(AB)}$, the merged entity's profit $\Pi^{(AB)}$, and firm $C$'s profit $\Pi^{(AB)}_C$;
--   3. the small merger $\{A,BC\}$: $L^{(BC)}$, $\Pi^{(BC)}_A$, the merged entity's profit $\Pi^{(BC)}$, and each small firm's half share $\Pi^{(BC)}_B=\Pi^{(BC)}_C=\Pi^{(BC)}/2$.
--
--   Each is transcribed row by row from Table A1, whose rows are $k\in(\alpha,\bar k)$, $[\bar k,(1-\alpha)/2)$, $[(1-\alpha)/2,1-2\alpha)$ and $[1-2\alpha,1)$, with the maxima the table prints; for example $L^{(0)}=\max\{r(\alpha+s_2)/(1-2\alpha),\,r\alpha/k\}$ for $k<\bar k$, $L^{(0)}=r\alpha/k$ for $\bar k\le k<1-2\alpha$, and $L^{(0)}=r\alpha/(1-2\alpha)$ for $k\ge 1-2\alpha$.
--
--   It then defines the merger conditions
--   $$
--   \text{(1a) } \Pi^{(AB)}>\Pi^{(0)}_A+\Pi^{(0)}_B,\quad \text{(1b) } \Pi^{(AB)}>\Pi^{(BC)}_A+\Pi^{(BC)}_B \text{ or } \Pi^{(AB)}_C\ge\Pi^{(BC)}_C,
--   $$
--   $$
--   \text{(2a) } \Pi^{(BC)}_C>\Pi^{(0)}_C,\quad \text{(2b) } \Pi^{(BC)}_A+\Pi^{(BC)}_B\ge\Pi^{(AB)},
--   $$
--   and the notion of equilibrium structure: $\{AB,C\}$ is an equilibrium structure iff (1a) and (1b) hold; $\{A,BC\}$ iff (2a) and (2b) hold; and the status quo $\{A,B,C\}$ iff neither condition (1) nor condition (2) holds.
--
--   These are the objects of the paper's main result (Proposition 3) and of the region-wise comparisons in its proof.
--
--   **Formalization Note** All quantities are explicit real functions of $(\alpha,k,r)$; the standing assumptions $0<\alpha<1/3$, $\alpha<k<1$, $r>0$ are hypotheses of each theorem, not part of the definitions. Table A1 is the definition: that these values are the equilibrium outcomes of the underlying mixed-strategy price game with random rationing is the paper's derivation and is not formalized. Firm $A$'s capacity $k_A\ge 1-2\alpha$ does not enter Table A1 and is not modelled. The split of $\Pi^{(AB)}$ between $A$ and $B$ is left unspecified, as in the paper.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, PDF pp. 7–10, 13–15, 19, 32: §3, conditions (1a)–(2b), s1/s2 (PDF p. 14), s3 (PDF p. 15), Table A1

import Mathlib

namespace EndogMerger.SymLoyal

noncomputable section

/-! Wang, Wu, Tang & Dai (Management Science 2024), accepted manuscript.
Three firms A, B, C; each has `α` loyal buyers, `1 - 3α` switchers buy from the cheapest firm,
buyers' reservation value `r`, small firms B and C have capacity `k` each, firm A is
unconstrained. All quantities below are explicit in `(α k r : ℝ)`; the standing assumptions
(`0 < α < 1/3`, `α < k < 1`, `0 < r`) are hypotheses of the theorems, not of the definitions. -/

/-- `s₁ ≡ (1 - 3α)(1 - k/(1 - 2α))` (PDF p. 14). -/
def s1 (α k : ℝ) : ℝ := (1 - 3 * α) * (1 - k / (1 - 2 * α))

/-- `s₂ ≡ s₁(1 - k/(α + s₁))` (PDF p. 14). -/
def s2 (α k : ℝ) : ℝ := s1 α k * (1 - k / (α + s1 α k))

/-- `s₃ ≡ (1 - 3α)(1 - 2k/(1 - α))` (PDF p. 15). -/
def s3 (α k : ℝ) : ℝ := (1 - 3 * α) * (1 - 2 * k / (1 - α))

/-- The first row boundary of Table A1, `(1 - 2α)²/(2 - 5α)` (PDF p. 32). -/
def kCut (α : ℝ) : ℝ := (1 - 2 * α) ^ 2 / (2 - 5 * α)

/-- The threshold of Proposition 3, `k* = α(1 - 2α)/(1 - 3α)` (PDF p. 19). -/
def kStar (α : ℝ) : ℝ := α * (1 - 2 * α) / (1 - 3 * α)

/-! ### Table A1 (PDF p. 32), transcribed row by row.
Rows: `(α, kCut)`, `[kCut, (1-α)/2)`, `[(1-α)/2, 1-2α)`, `[1-2α, 1)`. -/

/-- Independent structure `{A,B,C}`: lower bound of price support `L^(0)`. -/
def L0 (α k r : ℝ) : ℝ :=
  if k < kCut α then max (r * (α + s2 α k) / (1 - 2 * α)) (r * α / k)
  else if k < 1 - 2 * α then r * α / k
  else r * α / (1 - 2 * α)

/-- Independent structure: firm A's equilibrium profit `Π^(0)_A`. -/
def piIndepA (α k r : ℝ) : ℝ :=
  if k < kCut α then (1 - 2 * α) * L0 α k r
  else if k < 1 - 2 * α then r * α * (1 - 2 * α) / k
  else r * α

/-- Independent structure: the equilibrium profit `Π^(0)_B = Π^(0)_C` of each small firm
(one definition, used for both firm B and firm C). -/
def piIndepB (α k r : ℝ) : ℝ :=
  if k < kCut α then k * L0 α k r
  else if k < 1 - 2 * α then r * α
  else r * α

/-- Mixed merger `{AB,C}`: lower bound of price support `L^(AB)`. -/
def LAB (α k r : ℝ) : ℝ :=
  if k < (1 - α) / 2 then max (r * (2 * α + s1 α k) / (1 - α)) (r * α / k)
  else if k < 1 - 2 * α then r * (2 * α + s1 α k) / (1 - α)
  else 2 * r * α / (1 - α)

/-- Mixed merger: the merged entity's equilibrium profit `Π^(AB)`. -/
def piAB (α k r : ℝ) : ℝ :=
  if k < (1 - α) / 2 then (1 - α) * LAB α k r
  else if k < 1 - 2 * α then r * (2 * α + s1 α k)
  else 2 * r * α

/-- Mixed merger: firm C's equilibrium profit `Π^(AB)_C`. -/
def piABC (α k r : ℝ) : ℝ :=
  if k < (1 - α) / 2 then k * LAB α k r
  else if k < 1 - 2 * α then r * (2 * α + s1 α k) * k / (1 - α)
  else 2 * r * α * (1 - 2 * α) / (1 - α)

/-- Small merger `{A,BC}`: lower bound of price support `L^(BC)`. -/
def LBC (α k r : ℝ) : ℝ :=
  if k < kCut α then max (r * (α + s3 α k) / (1 - 2 * α)) (r * α / k)
  else if k < (1 - α) / 2 then r * α / k
  else 2 * r * α / (1 - α)

/-- Small merger: firm A's equilibrium profit `Π^(BC)_A`. -/
def piBCA (α k r : ℝ) : ℝ :=
  if k < kCut α then (1 - 2 * α) * LBC α k r
  else if k < (1 - α) / 2 then r * α * (1 - 2 * α) / k
  else 2 * r * α * (1 - 2 * α) / (1 - α)

/-- Small merger: the merged entity's equilibrium profit `Π^(BC)`. -/
def piBC (α k r : ℝ) : ℝ :=
  if k < kCut α then 2 * k * LBC α k r
  else if k < (1 - α) / 2 then 2 * r * α
  else 2 * r * α

/-- Each small firm's share in `{A,BC}`: `Π^(BC)_B = Π^(BC)_C = Π^(BC)/2` (PDF p. 8). -/
def piBCB (α k r : ℝ) : ℝ := piBC α k r / 2

/-! ### Market structures and the equilibrium conditions (PDF pp. 9–10). -/

/-- The three market structures: `indep` = `{A,B,C}`, `mixed` = `{AB,C}`, `small` = `{A,BC}`. -/
inductive MarketStructure
  | indep
  | mixed
  | small
  deriving DecidableEq

/-- (1a): `Π^(AB) > Π^(0)_A + Π^(0)_B`. -/
def cond1a (α k r : ℝ) : Prop := piIndepA α k r + piIndepB α k r < piAB α k r

/-- (1b): `Π^(AB) > Π^(BC)_A + Π^(BC)_B` or `Π^(AB)_C ≥ Π^(BC)_C`. -/
def cond1b (α k r : ℝ) : Prop :=
  piBCA α k r + piBCB α k r < piAB α k r ∨ piBCB α k r ≤ piABC α k r

/-- (2a): `Π^(BC)_C > Π^(0)_C`. -/
def cond2a (α k r : ℝ) : Prop := piIndepB α k r < piBCB α k r

/-- (2b): `Π^(BC)_A + Π^(BC)_B ≥ Π^(AB)`. -/
def cond2b (α k r : ℝ) : Prop := piAB α k r ≤ piBCA α k r + piBCB α k r

/-- Equilibrium structure (PDF pp. 9–10): `{AB,C}` iff (1a) and (1b); `{A,BC}` iff (2a) and
(2b); the status quo `{A,B,C}` iff neither condition (1) nor condition (2) holds. -/
def IsEquilibriumStructure (α k r : ℝ) : MarketStructure → Prop
  | .mixed => cond1a α k r ∧ cond1b α k r
  | .small => cond2a α k r ∧ cond2b α k r
  | .indep => ¬ (cond1a α k r ∧ cond1b α k r) ∧ ¬ (cond2a α k r ∧ cond2b α k r)

end

end EndogMerger.SymLoyal


