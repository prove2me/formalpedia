-- Prove2me | Definitions.Def_FixpReciprocal_squareCircuit
-- name    : FixpReciprocal_squareCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:50:08.337962+00:00
-- url     : https://prove2.me/theorems/a1f128ff-d39e-4bd6-8dcf-7d8b7b9d428a
-- title:
--   The seven-gate squaring circuit of Lemma 4.1
-- statement:
--   For a rational $\tau$, this is the straight-line circuit with input $x$ (wire $0$) and seven gates, in this order:
--   $$a_+=[\![\tfrac12x+\tfrac12]\!],\quad r_+=R_\tau(a_+),\quad a_-=[\![-\tfrac12x+\tfrac12]\!],\quad r_-=R_\tau(a_-),$$
--   $$t=[\![\tfrac{2+\tau}{4\tau}(r_++r_-)-\tfrac1\tau]\!],\quad R=R_\tau(t),\quad s=[\![\tfrac{(2+\tau)^2}{\tau^2}(1-R)]\!].$$
--   The file also defines in-order evaluation of a straight-line gate list, and acyclicity: gate $k$ reads only wires $0,\dots,k$.
--
--   Lemma 4.1 says the output $s$ equals $x^2$ for every $x\in[0,1]$.
--
--   **Formalization Note** The last gate is written $[\![-Dr+D]\!]$ with $D=(2+\tau)^2/\tau^2$, which is the paper's $[\![D(1-R)]\!]$ as a clipped affine gate. In-order evaluation is for these acyclic gadgets only; a generalized circuit is a system of equations.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Lemma 4.1, p.11 (PDF p.13); proof, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_FixpReciprocal_RGate

namespace FixpReciprocal

/-- The first six gates of the gadget of Lemma 4.1. Wire `0` is the input `x`; gate `k` defines wire `k + 1`:
`a₊ = ⟦x/2 + 1/2⟧`, `r₊ = R_τ(a₊)`, `a₋ = ⟦−x/2 + 1/2⟧`, `r₋ = R_τ(a₋)`,
`t = ⟦((2+τ)/(4τ))(r₊ + r₋) − 1/τ⟧`, `R = R_τ(t)`.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), proof of Lemma 4.1, p.12. -/
def gadgetBody (τ : ℚ) : List RGate :=
  [.aff (1 / 2) 0 (1 / 2) 0 0,
   .recip 1,
   .aff (-1 / 2) 0 (1 / 2) 0 0,
   .recip 3,
   .aff ((2 + τ) / (4 * τ)) ((2 + τ) / (4 * τ)) (-1 / τ) 2 4,
   .recip 5]

/-- The last gate of the gadget: `s = ⟦((2+τ)²/τ²)(1 − R)⟧`, written as `⟦−D R + D⟧` with `D = (2+τ)²/τ²`.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), proof of Lemma 4.1, p.12. -/
def gadgetOut (τ : ℚ) : RGate :=
  .aff (-(2 + τ) ^ 2 / τ ^ 2) 0 ((2 + τ) ^ 2 / τ ^ 2) 6 6

/-- **The seven-gate squaring circuit of Lemma 4.1.**

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Lemma 4.1, p.11, and its proof, p.12. -/
def squareCircuit (τ : ℚ) : List RGate := gadgetBody τ ++ [gadgetOut τ]

/-- Evaluate gates in order, appending each value as a new wire. -/
noncomputable def runGates (τ : ℚ) : List ℝ → List RGate → List ℝ
  | w, [] => w
  | w, g :: gs => runGates τ (w ++ [g.eval τ (fun n => w.getD n 0)]) gs

/-- All wire values of a straight-line gate list on input `x` (wire `0` is `x`).

**Formalization Note.** For acyclic gadgets only; a generalized circuit is a system of equations
(`RCircuitSol`). -/
noncomputable def seqWires (τ : ℚ) (gs : List RGate) (x : ℝ) : List ℝ := runGates τ [x] gs

/-- Acyclicity: gate `k` (which defines wire `k + 1`) reads only wires `0, …, k`. -/
def StraightLine (gs : List RGate) : Prop :=
  ∀ (k : ℕ) (h : k < gs.length), gs[k].ReadsBelow (k + 1)

/-- Whether a gate is clipped affine. -/
def RGate.isAff : RGate → Bool
  | .aff _ _ _ _ _ => true
  | .recip _ => false

/-- Whether a gate is reciprocal. -/
def RGate.isRecip : RGate → Bool
  | .aff _ _ _ _ _ => false
  | .recip _ => true

end FixpReciprocal


