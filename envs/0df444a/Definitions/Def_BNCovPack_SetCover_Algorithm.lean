-- Prove2me | Definitions.Def_BNCovPack_SetCover_Algorithm
-- name    : BNCovPack_SetCover_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:19:32.871751+00:00
-- url     : https://prove2.me/theorems/b3d0fa39-5545-4098-881e-7df2528892ff
-- title:
--   The deterministic online unweighted set-cover algorithm of Section 5.1 (fractional scheme plus potential-function rounding)
-- statement:
--   This file defines the online integral set-cover algorithm of Section 5.1 of Buchbinder and Naor (2009).
--
--   The state consists of the state of the fractional scheme of Section 3 (weights $w(s)$, loads and the dual value) and the chosen family $\mathcal C$. Initially all weights are $0$ and $\mathcal C=\emptyset$. The algorithm is run with a parameter $B>0$, the frequency bound $d$ (used as $\ell$ in the fractional scheme), the known optimum value $OPT$, and an order of the sets: a list in which every set appears.
--
--   When an element $e$ arrives:
--
--   1. **Fractional round.** The fractional scheme with $\ell=d$ processes $e$, giving new weights $w'$ (only sets containing $e$ change, and weights never decrease).
--   2. **Rounding.** The sets are processed one at a time in the given order. When set $s$ is reached and its weight was augmented in this round ($w(s)<w'(s)$), its weight is raised to $w'(s)$, and $s$ is added to $\mathcal C$ if $s\notin\mathcal C$ and
--   $$\Phi\big(w+\delta_s\mathbf 1_s,\ \mathcal C\cup\{s\}\big)\le\Phi\big(w,\ \mathcal C\big),\qquad \delta_s=w'(s)-w(s),$$
--   where $\Phi$ is the potential of Section 5.1 with $\alpha=\max\{1,\ln(rn/OPT)\}$ and $n$ the number of elements. Sets whose weight did not change are skipped.
--
--   The paper's rule (p. 12) is "Each time the weight of a set $s$ is augmented in Line 2(b) of the algorithm, add $s$ to the cover $\mathcal C$ if its addition does not increase the value of the potential function $\Phi$." The run of the algorithm on an arrival list is the result of these rounds in order.
--
--   **Formalization Note** The paper describes the augmentation continuously; here each set's increase within a round is treated as one augmentation, the sets augmented in the same round are processed sequentially in the order of the list `ord`, and the comparison is with $\Phi$ before the augmentation of $s$, as in Lemma 5.1 (ii). The algorithm is a function of the instance, $B$, $d$, $OPT$, the order and the arrival list, so every run exists and is unique. Set costs are not used by the rounding; Lemma 5.2 assumes unit costs.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 12, Section 5.1 (the rounding rule and the use of the Section 3 scheme with a(i,j) in {0,1}); p. 5 (scheme with n replaced by ℓ = d)

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_BNCovPack_SetCover_FracScheme
import Definitions.Def_BNCovPack_SetCover_Potential

namespace BNCovPack.SetCover

open OnlinePrimalDual.OnlineSetCover

/-- State of the online integral set-cover algorithm of §5.1 (p. 12): the state of the fractional
scheme of Section 3 (whose weights are the `w(s)` of the potential) and the chosen family `C`. -/
structure State (T : Type*) where
  frac : FracState T
  cover : Finset T

/-- Processing one set `s` after a fractional round whose new weights are `w'` (p. 12, the
rounding rule: "Each time the weight of a set `s` is augmented in Line 2(b) of the algorithm, add
`s` to the cover `C` if its addition does not increase the value of the potential function `Φ`").
If the weight of `s` was augmented (`w s < w' s`), it is raised to `w' s`, and `s` is added to
`C` when `s ∉ C` and `Φ(raised weights, C ∪ {s}) ≤ Φ(w, C)`, the value of `Φ` before the
augmentation of `s`. Otherwise nothing changes. -/
noncomputable def augmentSet {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (α : ℝ) (OPT : ℕ) (w' : T → ℝ)
    (p : (T → ℝ) × Finset T) (s : T) : (T → ℝ) × Finset T :=
  if p.1 s < w' s then
    let w₁ := Function.update p.1 s (w' s)
    if s ∉ p.2 ∧ potential inst α OPT w₁ (insert s p.2) ≤ potential inst α OPT p.1 p.2 then
      (w₁, insert s p.2)
    else (w₁, p.2)
  else p

/-- One round of the integral algorithm on arrival of element `e`: run the fractional scheme of
Section 3 with `ℓ = d` (p. 5 and p. 12), then process the sets one at a time in the order of the
list `ord`, applying `augmentSet` with `α = alphaParam n OPT`, `n = |E|`. -/
noncomputable def step {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (d OPT : ℕ) (ord : List T) (st : State T) (e : E) :
    State T :=
  let f' := fracStep inst B d st.frac e
  let p := ord.foldl (augmentSet inst (alphaParam (Fintype.card E) OPT) OPT f'.w)
    (st.frac.w, st.cover)
  { frac := f', cover := p.2 }

/-- The state of the integral algorithm after the arrival list `σ`, starting from all weights `0`
and the empty cover. -/
noncomputable def run {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (B : ℝ) (d OPT : ℕ) (ord : List T) (σ : List E) : State T :=
  σ.foldl (step inst B d OPT ord) ⟨FracState.init T, ∅⟩

end BNCovPack.SetCover


