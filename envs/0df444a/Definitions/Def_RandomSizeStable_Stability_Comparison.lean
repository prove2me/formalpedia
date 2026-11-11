-- Prove2me | Definitions.Def_RandomSizeStable_Stability_Comparison
-- name    : RandomSizeStable_Stability_Comparison
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:13.817185+00:00
-- url     : https://prove2.me/theorems/cef3ae34-4a15-4cd3-a309-558a9a95c332
-- title:
--   Independent draws and random-label singleton comparisons
-- statement:
--   Fix a profile $E$, voter $v$, candidate $c$, and lottery $P$. A labeled copy $(c,s)$ is better than $(c',s')$ when $v$ ranks $c$ above $c'$, or $c=c'$ and $s>s'$. All copies, including the challenger, receive independent uniform labels in $[0,1]$.
--
--   For an ordered tuple $x=(x_1,\ldots,x_k)$ of independent draws, let $N_c(x)$ count its occurrences of $c$. The conditional singleton win probability is
--   $$W_{v,c}(x)=\begin{cases}0&\text{if some }x_i\succ_v c,\\
--   1/(N_c(x)+1)&\text{otherwise.}\end{cases}$$
--   Average this finite experiment first over tuples with product masses and then over the independently chosen count:
--   $$L_{v,c}(P)=\sum_{k\ge1}\Pr[D=k]\sum_{x\in C^k}
--   \left(\prod_{i=1}^kP(x_i)\right)W_{v,c}(x).$$
--   This is the operational probability that $c$ defeats all draws. It retains duplicate draws and zero masses. It does not define the probability by the integral that Lemma 1 is to establish. One fixed base lottery is used for all draw counts.
-- source:
--   Nisarg Shah, Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission #1342 (October 2026), p. 9, Section 3, Comparing multisets and Random sample size.

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_DrawLaw

set_option autoImplicit false

open MeasureTheory PctDistortion

namespace RandomSizeStable.Stability

/-- §3 p.9: labeled copies are compared by candidate first, then by larger label.
Every occurrence, including the challenger, has its own independent uniform label. -/
def labeledPrefers {V C : Type} (E : Election V C) (v : V)
    (x y : C × ℝ) : Prop :=
  E.prefers v x.1 y.1 ∨ (x.1 = y.1 ∧ y.2 < x.2)

/-- §3 p.9: conditional win probability of a singleton challenger against a fixed
ordered tuple. If a better candidate occurs it is zero; otherwise the challenger
wins among its k+1 independently labeled copies with probability 1/(k+1).
This is the finite random-label experiment, not the PGF integral. -/
noncomputable def tupleWin {V C : Type} (E : Election V C) (v : V) (c : C)
    {k : ℕ} (draws : Fin k → C) : ℝ := by
  classical
  exact if ∃ i, E.prefers v (draws i) c then 0
    else ((Finset.univ.filter (fun i => draws i = c)).card + 1 : ℝ)⁻¹

/-- §3 p.9: independent draws use product masses, averaged over all ordered tuples,
then over the positive-integer draw law. One fixed base lottery is used throughout. -/
noncomputable def comparison {V C : Type} [Fintype C] (D : PMF ℕ+)
    (E : Election V C) (P : C → ℝ) (v : V) (c : C) : ℝ :=
  ∑' k : ℕ+, (D k).toReal *
    ∑ draws : Fin (k : ℕ) → C, (∏ i, P (draws i)) * tupleWin E v c draws

end RandomSizeStable.Stability


