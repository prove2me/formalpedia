-- Prove2me | Definitions.Def_OnlineMaxWeightMatch_Approx_Algorithm1
-- name    : OnlineMaxWeightMatch_Approx_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:36.185421+00:00
-- url     : https://prove2.me/theorems/f66f3945-ee01-40a8-a12d-5d728bb2648e
-- title:
--   Algorithm 1 (Rounding LP-Match Online) with c = 0.01 and its expected profit
-- statement:
--   This file defines **Algorithm 1** of the paper as a random matching, for a RideHail instance $I$ (bins $i$, balls $t$, arrival probabilities $p_t$, weights $w_{i,t}$) and a vector $x=(x_{i,t})$.
--
--   **Constants.** $c:=0.01$, the threshold $\theta:=\frac{1/2-c}{1/2+c}$, and the acceptance probabilities
--
--   $$
--   q_{i,t}:=\min\Big(1,\ \frac{1/2+c}{1-\sum_{t'<t}x_{i,t'}\cdot(1/2+c)}\Big).
--   $$
--
--   **Randomness.** For every ball $t$, independently: an arrival indicator $A_t\sim\mathrm{Ber}(p_t)$; a first pick, equal to bin $i$ with probability $x_{i,t}/p_t$; acceptance coins $Y_{i,t}\sim\mathrm{Ber}(q_{i,t})$, independent over bins $i$; and a second pick with the same law as the first. The pick has the leftover value "no bin" with probability $1-\sum_i x_{i,t}/p_t$, which is $0$ when $p_t>0$ and $\sum_i x_{i,t}=p_t$.
--
--   **The rounding (Lines 3–13).** Start with $M=\emptyset$ and process the balls in order. If ball $t$ does not arrive, nothing happens. If it arrives:
--   1. (Lines 5–8) if its first pick $i$ is unmatched and the coin $Y_{i,t}$ accepts, add $(i,t)$ to $M$ (to the part $M_1$);
--   2. (Lines 9–12) if $t$ is still unmatched, and its second pick $i$ is unmatched and satisfies $\sum_{t'<t}x_{i,t'}>\theta$, add $(i,t)$ to $M$ (to the part $M_2$).
--
--   The output is $M=M_1\sqcup M_2$.
--
--   **Dummy bins (Line 2).** For each ball $t$ a dummy bin $i_t$ is added with $w_{i_t,t'}=0$ for all $t'$, $x_{i_t,t}:=p_t-\sum_i x_{i,t}$ and $x_{i_t,t'}:=0$ for $t'\neq t$, so that $\sum_i x_{i,t}=p_t$ for every $t$. **Algorithm 1 on $(I,x)$** is the rounding run on the augmented instance and augmented $x$; its expected profit is
--
--   $$
--   \mathrm{ALG}(I,x)=\mathbb E\Big[\sum_{(i,t)\in M}w_{i,t}\Big].
--   $$
--
--   **Formalization Note** The probability space is the finite set of outcomes (one draw per ball), with the product weights above and the discrete $\sigma$-algebra. A first pick of a dummy bin is a genuine pick: the dummy is vacant, so it accepts with probability $q=1/2+c$ and then consumes the ball's turn. A pick is `Option` valued; when $p_t=0$ the quotient $x_{i,t}/p_t$ is $0$ in Lean, the pick is "no bin", and the ball never arrives anyway. The coins of bins other than the first pick are drawn but never read, which does not change the law of $M$. This is the coupling the proof of Lemma 4.9 uses. The measure is a probability measure for every LP-Match-feasible $x$ (checked in a local sorry-free verification file). Line 1 (solving the LP) is not part of this definition: the goal theorem quantifies over optimal solutions $x$.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, pp. 10–11, §4.1, Algorithm 1 and the dummy-bin paragraph; c := 0.01 (p. 10)

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_LPMatch

open Classical MeasureTheory

namespace OnlineMaxWeightMatch.Approx

variable {ι : Type*} {n : ℕ}

/-- The constant `c := 0.01` of §4 (p. 10). -/
noncomputable def c : ℝ := 1 / 100

/-- The threshold `(1/2 - c) / (1/2 + c)` of Line 11 of Algorithm 1 (and of Definition 4.3). -/
noncomputable def threshold : ℝ := (1 / 2 - c) / (1 / 2 + c)

/-- The acceptance probability of Line 7,
`q_{i,t} := min(1, (1/2 + c) / (1 - Σ_{t'<t} x_{i,t'} · (1/2 + c)))`. -/
noncomputable def acceptProb (x : ι → Fin n → ℝ) (i : ι) (t : Fin n) : ℝ :=
  min 1 ((1 / 2 + c) / (1 - cumX x i t * (1 / 2 + c)))

/-- The randomness Algorithm 1 uses for one ball: whether it arrives, its first pick (Line 5),
one acceptance coin per bin (Line 7; only the coin of the first-picked bin is ever read), and its
second pick (Line 10). A pick is `some i` for bin `i`; `none` is the leftover mass
`1 - Σ_i x_{i,t}/p_t`, which is `0` when `p_t > 0` and Constraint (10) is tight. -/
abbrev BallDraw (ι : Type*) := Bool × Option ι × (ι → Bool) × Option ι

/-- whether the ball arrives -/
def BallDraw.arrives (d : BallDraw ι) : Bool := d.1
/-- the first pick (Line 5) -/
def BallDraw.firstPick (d : BallDraw ι) : Option ι := d.2.1
/-- the acceptance coin of each bin (Line 7) -/
def BallDraw.coin (d : BallDraw ι) : ι → Bool := d.2.2.1
/-- the second pick (Line 10) -/
def BallDraw.secondPick (d : BallDraw ι) : Option ι := d.2.2.2

/-- The probability space of Algorithm 1: one independent `BallDraw` per ball. -/
def Outcome (ι : Type*) (n : ℕ) : Type _ := Fin n → BallDraw ι

noncomputable instance [Fintype ι] : Fintype (Outcome ι n) :=
  inferInstanceAs (Fintype (Fin n → BallDraw ι))

instance : MeasurableSpace (Outcome ι n) := ⊤

/-- The law of a pick at ball `t`: bin `i` with probability `x_{i,t}/p_t`, and `none` with the
remaining probability. (When `p_t = 0` every `x_{i,t}/p_t` is `0` in Lean, so the pick is
`none`; the ball never arrives and its picks are never read.) -/
noncomputable def pickWeight [Fintype ι] (I : RideHailInstance ι n) (x : ι → Fin n → ℝ)
    (t : Fin n) : Option ι → ℝ
  | some i => x i t / I.p t
  | none => 1 - ∑ i, x i t / I.p t

/-- The probability of the draw `d` for ball `t`: arrival `~ Ber(p_t)`, first pick, the
independent coins `Y_{i,t} ~ Ber(q_{i,t})`, and second pick, all independent. -/
noncomputable def ballWeight [Fintype ι] (I : RideHailInstance ι n) (x : ι → Fin n → ℝ)
    (t : Fin n) (d : BallDraw ι) : ℝ :=
  (if d.arrives then I.p t else 1 - I.p t) * pickWeight I x t d.firstPick *
    (∏ i, if d.coin i then acceptProb x i t else 1 - acceptProb x i t) *
    pickWeight I x t d.secondPick

/-- The probability of a full outcome: the draws of different balls are independent. -/
noncomputable def outcomeWeight [Fintype ι] (I : RideHailInstance ι n) (x : ι → Fin n → ℝ)
    (ω : Outcome ι n) : ℝ :=
  ∏ t, ballWeight I x t (ω t)

/-- The probability measure of Algorithm 1's randomness (a probability measure whenever `x` is
LP-Match feasible). -/
noncomputable def algMeasure [Fintype ι] (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) :
    Measure (Outcome ι n) :=
  ∑ ω, ENNReal.ofReal (outcomeWeight I x ω) • Measure.dirac ω

/-- The state of Algorithm 1: the edges `M1` added in Line 8 and the edges `M2` added in
Line 12. The matching is `M = M1 ∪ M2`. -/
abbrev AlgState (ι : Type*) (n : ℕ) := Finset (ι × Fin n) × Finset (ι × Fin n)

/-- Bin `i` is vacant (unmatched) in state `S`. -/
def IsVacantIn (S : AlgState ι n) (i : ι) : Prop :=
  ∀ s, (i, s) ∉ S.1 ∧ (i, s) ∉ S.2

/-- One iteration of the loop of Algorithm 1 (Lines 5–12) for ball `t` with draw `d`. Nothing
happens if `t` does not arrive. Otherwise: if the first pick `i` is vacant and its coin accepts,
`(i, t)` joins `M1` (Lines 5–8); if `t` is still unmatched, the second pick `i` is matched,
into `M2`, provided it is vacant and `Σ_{t'<t} x_{i,t'} > (1/2 - c)/(1/2 + c)` (Lines 9–12). -/
noncomputable def step (x : ι → Fin n → ℝ) (t : Fin n) (d : BallDraw ι) (S : AlgState ι n) :
    AlgState ι n :=
  if d.arrives = true then
    let M1' : Finset (ι × Fin n) :=
      match d.firstPick with
      | some i => if IsVacantIn S i ∧ d.coin i = true then insert (i, t) S.1 else S.1
      | none => S.1
    if ∃ i, (i, t) ∈ M1' then (M1', S.2)
    else
      match d.secondPick with
      | some i => if IsVacantIn S i ∧ threshold < cumX x i t then (S.1, insert (i, t) S.2) else S
      | none => S
  else S

/-- The state of Algorithm 1 after the first `k` balls have been processed (Line 3 starts from
`M = ∅`). -/
noncomputable def stateAfter (x : ι → Fin n → ℝ) (ω : Outcome ι n) : ℕ → AlgState ι n
  | 0 => (∅, ∅)
  | k + 1 =>
    if h : k < n then step x ⟨k, h⟩ (ω ⟨k, h⟩) (stateAfter x ω k) else stateAfter x ω k

/-- `M1`: the edges matched as a first pick (Line 8). -/
noncomputable def M1 (x : ι → Fin n → ℝ) (ω : Outcome ι n) : Finset (ι × Fin n) :=
  (stateAfter x ω n).1

/-- `M2`: the edges matched as a second pick (Line 12). -/
noncomputable def M2 (x : ι → Fin n → ℝ) (ω : Outcome ι n) : Finset (ι × Fin n) :=
  (stateAfter x ω n).2

/-- `M = M1 ⊔ M2`: the matching output by Algorithm 1 (Line 13). -/
noncomputable def algMatching (x : ι → Fin n → ℝ) (ω : Outcome ι n) : Finset (ι × Fin n) :=
  M1 x ω ∪ M2 x ω

/-- Line 2 of Algorithm 1: the instance with a dummy bin `i_t` (here `Sum.inr t`) added for each
ball `t`, with weight `0` on all its edges. -/
def augment (I : RideHailInstance ι n) : RideHailInstance (ι ⊕ Fin n) n where
  w := Sum.elim I.w (fun _ _ => 0)
  p := I.p
  w_nonneg := by
    rintro (i | s) t
    · exact I.w_nonneg i t
    · exact le_refl 0
  p_nonneg := I.p_nonneg
  p_le_one := I.p_le_one

/-- Line 2 of Algorithm 1: the LP solution extended to the dummy bins,
`x_{i_t, t} := p_t - Σ_i x_{i,t}` and `x_{i_t, t'} := 0` for `t' ≠ t`, so that
`Σ_i x_{i,t} = p_t` for every ball `t`. -/
noncomputable def augmentX [Fintype ι] (I : RideHailInstance ι n) (x : ι → Fin n → ℝ) :
    ι ⊕ Fin n → Fin n → ℝ :=
  Sum.elim x (fun s t => if s = t then I.p t - ∑ i, x i t else 0)

/-- The expected profit `E[Σ_{(i,t) ∈ M} w_{i,t}]` of Algorithm 1 run on instance `I` with the
LP solution `x` (Lines 2–13: augment, then round online). Dummy edges have weight `0`. -/
noncomputable def algorithm1Value [Fintype ι] (I : RideHailInstance ι n)
    (x : ι → Fin n → ℝ) : ℝ :=
  ∫ ω, ∑ e ∈ algMatching (augmentX I x) ω, (augment I).w e.1 e.2
    ∂(algMeasure (augment I) (augmentX I x))

end OnlineMaxWeightMatch.Approx


