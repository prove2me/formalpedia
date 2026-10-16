-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
-- name    : OAI_Probability_ThorpShuffle_ConditionalFlow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:23:42.816195+00:00
-- url     : https://prove2.me/theorems/89d60ff7-ceb6-4caa-8252-398950fe71df
-- title:
--   The conditional Thorp step on weights, centered states and expected energy
-- statement:
--   Consider a deck of $2^{d+1}$ cards with positions $Q_{d+1}=\{0,1\}^{d+1}$. Booleans are identified with bits and $\oplus$ is addition modulo $2$. For $b\in\{0,1\}$ and $s=(s_0,\dots,s_{d-1})\in Q_d$, write $bs=(b,s_0,\dots,s_{d-1})$ (prepend $b$) and $sb=(s_0,\dots,s_{d-1},b)$ (append $b$). A coin vector is $c:Q_d\to\{0,1\}$, and the Thorp step $T_c\in\mathrm{Sym}(Q_{d+1})$ is $T_c(bs)=s\,(b\oplus c(s))$.
--
--   1. *Split and scatter.* The bijection $Q_{d+1}\to\{0,1\}\times Q_d$, $bs\mapsto(b,s)$, removes the leading bit. The scatter bijection $\{0,1\}\times Q_d\to Q_{d+1}$, $(b,s)\mapsto sb$, appends the bit at the end; it is the inverse of the split followed by the cyclic rotation of coordinates. With these, $T_c^{-1}(s\beta)=(\beta\oplus c(s))\,s$.
--   2. *Physical flow.* For a free marker $B:Q_{d+1}\to\{0,1\}$, a weight $w:Q_{d+1}\to\mathbb{R}$ and a coin vector $c$, the new weight $\Phi_{B,c}w:Q_{d+1}\to\mathbb{R}$ is defined for $s\in Q_d$ and $\beta\in\{0,1\}$ by
--   $$
--   (\Phi_{B,c}w)(s\beta)=\begin{cases}\tfrac12\bigl(w(0s)+w(1s)\bigr)&\text{if }B(0s)=B(1s)=1,\\w\bigl((\beta\oplus c(s))\,s\bigr)&\text{otherwise.}\end{cases}
--   $$
--   So the weight is transported by $T_c$, except on pairs whose two positions are both free, where it is averaged.
--   3. *Physical free marker.* $B_c(y)=B(T_c^{-1}y)$: the free positions move with the cards.
--   4. *Centered states.* A centered state on $Q_n$ is a pair $(B,w)$ with $B:Q_n\to\{0,1\}$ and $w:Q_n\to\mathbb{R}$ such that $\sum_xw(x)=0$, $w(x)=0$ whenever $B(x)=0$, and $\sum_xw(x)^2\le1$.
--   5. *Next state and iteration.* For a centered state $v=(B,w)$ on $Q_{d+1}$, $\operatorname{next}(v;c)=(B_c,\Phi_{B,c}w)$, which is again centered. For a history $\omega=(\omega_0,\dots,\omega_{t-1})$ of coin vectors, $v_0^\omega=v$ and $v_{k+1}^\omega=\operatorname{next}(v_k^\omega;\omega_k)$; write $w_t^\omega$ for the weight of $v_t^\omega$.
--   6. *Expected energy.* The average energy after $t$ steps over all $2^{2^dt}$ histories:
--   $$
--   \mathcal E_t(v)=\frac{1}{2^{2^d t}}\sum_{\omega}\ \sum_{x\in Q_{d+1}}w_t^\omega(x)^2 .
--   $$
--
--   The module also proves the facts that make $\operatorname{next}$ well defined. The physical flow preserves total mass and does not increase $\sum_xw(x)^2$. If $w$ vanishes off $\{B=1\}$, then $\Phi_{B,c}w$ vanishes off $\{B_c=1\}$.
--
--   In the analysis of the Thorp shuffle, $B$ marks the positions not occupied by a set of exposed cards, and $w$ is a signed deviation supported on the free positions, for example a point mass minus the uniform distribution on the free positions. Averaging over the coins of fully free pairs turns the random evolution of such a deviation into this deterministic recursion, and the expected energy $\mathcal E_t$ is the quantity whose decay is then estimated.
--
--   **Formalization Note** The bijections are `splitPosition` and `scatterPosition`, and the flow `physicalFlow` is the pair flow `flow` transported through them. `CenteredState` is a structure that bundles the three conditions as proof fields, and `nextState` discharges them with `physicalFlow_sum`, `physicalFlow_support` and `physicalFlow_energy_le`. `iterateState` applies the coin vectors in chronological order. `expectedEnergy` is the uniform `mean` over `History (d + 1) t`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/ConditionalFlow.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/ConditionalFlow.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def splitPosition (d : ℕ) : Position (d + 1) ≃ Bool × Position d :=
  (Fin.consEquiv (fun _ : Fin (d + 1) => Bool)).symm

def scatterPosition (d : ℕ) : Bool × Position d ≃ Position (d + 1) :=
  (splitPosition d).symm.trans (rotate (d + 1))

def physicalFlow (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) (x : Position (d + 1)) : ℝ :=
  flow (B ∘ (splitPosition d).symm) (w ∘ (splitPosition d).symm) c
    ((scatterPosition d).symm x)

def physicalFree (d : ℕ) (B : Position (d + 1) → Bool)
    (c : Coins (d + 1)) (x : Position (d + 1)) : Bool :=
  B ((step (d + 1) c).symm x)

theorem step_symm_scatter (d : ℕ) (c : Coins (d + 1)) (p : Bool × Position d) :
    (step (d + 1) c).symm (scatterPosition d p) =
      (splitPosition d).symm (pairMap c p) := by
  simp [step, scatterPosition, splitPosition, pairSwitch, pairMap]

@[simp] theorem physicalFlow_scatter (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) (p : Bool × Position d) :
    physicalFlow d B w c (scatterPosition d p) =
      flow (B ∘ (splitPosition d).symm) (w ∘ (splitPosition d).symm) c p := by
  simp [physicalFlow]

@[simp] theorem physicalFree_scatter (d : ℕ) (B : Position (d + 1) → Bool)
    (c : Coins (d + 1)) (p : Bool × Position d) :
    physicalFree d B c (scatterPosition d p) =
      B ((splitPosition d).symm (pairMap c p)) := by
  rw [physicalFree, step_symm_scatter]

theorem physicalFlow_sum (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) :
    (∑ x, physicalFlow d B w c x) = ∑ x, w x := by
  calc
    _ = ∑ p, physicalFlow d B w c (scatterPosition d p) :=
      (Equiv.sum_comp (scatterPosition d) (physicalFlow d B w c)).symm
    _ = ∑ p, w ((splitPosition d).symm p) := by
      simp only [physicalFlow_scatter]
      exact flow_sum (B ∘ (splitPosition d).symm)
        (w ∘ (splitPosition d).symm) c
    _ = _ := Equiv.sum_comp (splitPosition d).symm w

theorem physicalFlow_energy_le (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) :
    (∑ x, physicalFlow d B w c x ^ 2) ≤ ∑ x, w x ^ 2 := by
  calc
    _ = ∑ p, physicalFlow d B w c (scatterPosition d p) ^ 2 :=
      (Equiv.sum_comp (scatterPosition d) (fun x => physicalFlow d B w c x ^ 2)).symm
    _ ≤ ∑ p, w ((splitPosition d).symm p) ^ 2 := by
      simp only [physicalFlow_scatter]
      exact flow_energy_le (B ∘ (splitPosition d).symm)
        (w ∘ (splitPosition d).symm) c
    _ = _ := Equiv.sum_comp (splitPosition d).symm (fun x => w x ^ 2)

theorem physicalFlow_support (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (hw : ∀ x, B x = false → w x = 0)
    (c : Coins (d + 1)) (x : Position (d + 1))
    (hx : physicalFree d B c x = false) : physicalFlow d B w c x = 0 := by
  obtain ⟨p, rfl⟩ := (scatterPosition d).surjective x
  rw [physicalFree_scatter] at hx
  rw [physicalFlow_scatter]
  exact flow_support _ _ (fun p => hw ((splitPosition d).symm p)) c p hx

structure CenteredState (d : ℕ) where
  free : Position d → Bool
  weight : Position d → ℝ
  mass_zero : ∑ x, weight x = 0
  supported : ∀ x, free x = false → weight x = 0
  energy_le_one : ∑ x, weight x ^ 2 ≤ 1

def nextState (d : ℕ) (v : CenteredState (d + 1)) (c : Coins (d + 1)) :
    CenteredState (d + 1) where
  free := physicalFree d v.free c
  weight := physicalFlow d v.free v.weight c
  mass_zero := by rw [physicalFlow_sum]; exact v.mass_zero
  supported := physicalFlow_support d v.free v.weight v.supported c
  energy_le_one := (physicalFlow_energy_le d v.free v.weight c).trans v.energy_le_one

def iterateState (d : ℕ) (v : CenteredState (d + 1)) :
    (t : ℕ) → History (d + 1) t → CenteredState (d + 1)
  | 0, _ => v
  | t + 1, ω => nextState d (iterateState d v t (fun i => ω i.castSucc)) (ω (Fin.last t))

def expectedEnergy (d : ℕ) (v : CenteredState (d + 1)) (t : ℕ) : ℝ :=
  mean (fun ω : History (d + 1) t => ∑ x, (iterateState d v t ω).weight x ^ 2)

end Conditional

end Thorp

end

end OAI


