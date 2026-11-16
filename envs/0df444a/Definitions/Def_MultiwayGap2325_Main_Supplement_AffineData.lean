-- Prove2me | Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData
-- name    : MultiwayGap2325_Main_Supplement_AffineData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:21:33.677267+00:00
-- url     : https://prove2.me/theorems/06ecf324-62fc-4013-a0b0-8865b3b795d4
-- title:
--   The specified affine data (23)–(24) and the formulas in (25)
-- statement:
--   For each face size $2\le r\le q$, define
--
--   $$a_r=\frac{(rT-1)(r-2)!(q-r)!}{T^{r-2}q!},\qquad z=\frac{1-T}{T}.$$
--
--   Every truncated face is one cell. For $|S|=r$ and $s\in S$ set
--
--   $$p_s^S(x)=\frac{T-x_s}{rT-1},\quad F_i^S(x)=a_r(e_i-p^S(x)),\quad F_*^S=0,\quad
--   w_{st}^S=\frac{a_r}{r-1},\quad g_i^S=a_r.$$
--
--   The allowance vanishes on every proper face, while on the top face it is the constant density $(q-1)a_q/(qT-1)$. This is a density, not its integral $R$.
--
--   The bundle also names the explicit sum and closed expression for $B$, the closed expressions for $R$ and $B-R$, and the interior sum for $L$ displayed in (25). Theorem 6.1 asserts that these expressions equal the actual integrals of the raw data, as well as asserting flow-instance validity. Neither validity nor any integral identity is assumed by these definitions.
--
--   **Formalization Note** Factorials are natural factorials cast to the reals, exponents use natural differences in their valid ranges, and division is real division. Components outside the face are zero. All constants and fields are computed from $q,T,S,x$, not supplied as certificates.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), Theorem 6.1, p. 23, equations (23)–(25)

import Definitions.Def_MultiwayGap2325_Main_Supplement_Flows

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace MultiwayGap2325.Main.Supplement

attribute [local instance] Classical.propDecidable

/-- Equation (23), with real division and natural factorials cast to the reals. -/
def affineScale (q : ℕ) (T : ℝ) (r : ℕ) : ℝ :=
  ((r : ℝ) * T - 1) * (r - 2).factorial * (q - r).factorial /
    (T ^ (r - 2) * q.factorial)

/-- The normalized margin point p^S, equation (24). -/
def affineMargin {q : ℕ} (T : ℝ) (S : Face q) (x : Vec q) : Vec q :=
  fun s => if s ∈ S.val then (T - x s) / ((S.val.card : ℝ) * T - 1) else 0

/-- Exactly one cell per face, constant interior and terminal densities. -/
def affineWeighting (q : ℕ) (T : ℝ) : Weighting q where
  cells := fun S => {omega T S}
  weight := fun S _ _ _ => affineScale q T S.val.card / (S.val.card - 1 : ℝ)
  cellWeight := fun S _ _ _ _ => affineScale q T S.val.card / (S.val.card - 1 : ℝ)
  terminal := fun S _ _ => affineScale q T S.val.card

/-- Raw geometric data (23)–(24). Validity and all integrated identities are theorem conclusions. -/
def affineData (q : ℕ) (T : ℝ) : FlowData q where
  weighting := affineWeighting q T
  field := fun S _ l x => match l with
    | none => 0
    | some i => fun s => affineScale q T S.val.card *
        ((if s = i then 1 else 0) - affineMargin T S x s)
  allowance := fun S _ => if S.val = Finset.univ then
    ((q : ℝ) - 1) * affineScale q T q / ((q : ℝ) * T - 1) else 0

def affineZ (T : ℝ) : ℝ := (1 - T) / T

/-- The first expression for B in (25). -/
def affineBSum (q : ℕ) (T : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 q,
    ((r : ℝ) * T - 1) * affineZ T ^ (r - 2) / (r - 1).factorial

/-- The telescoped expression for B in (25). -/
def affineBClosed (q : ℕ) (T : ℝ) : ℝ :=
  T * (1 - affineZ T ^ (q - 1) / (q - 1).factorial)

def affineRClosed (q : ℕ) (T : ℝ) : ℝ :=
  (1 - (q : ℝ) * (1 - T) ^ (q - 1)) / (q.factorial * T ^ (q - 2))

def affineNetClosed (q : ℕ) (T : ℝ) : ℝ :=
  T - 1 / (q.factorial * T ^ (q - 2))

/-- Interior contribution to L in (25); the terminal contribution remains (1-T) times actual B. -/
def affineInteriorClosed (q : ℕ) (T : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 2 q,
    (((r : ℝ) * T - 1) * (1 - (r : ℝ) * (1 - T) ^ (r - 1))) /
      (2 * ((r : ℝ) - 1) * (r - 1).factorial * T ^ (r - 2))

end MultiwayGap2325.Main.Supplement


