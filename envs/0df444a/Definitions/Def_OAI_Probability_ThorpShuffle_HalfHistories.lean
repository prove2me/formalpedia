-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
-- name    : OAI_Probability_ThorpShuffle_HalfHistories
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:29:38.230976+00:00
-- url     : https://prove2.me/theorems/9da70d6f-478b-4447-86c0-06b69f1b00db
-- title:
--   Unconstrained marker-and-weight states and their iteration under the conditional Thorp step
-- statement:
--   Consider a deck of $2^{d+1}$ cards with positions $Q_{d+1}=\{0,1\}^{d+1}$. For $b\in\{0,1\}$ and $s\in Q_d$, write $bs$ for $s$ with $b$ prepended and $sb$ for $s$ with $b$ appended. A coin vector $c:Q_d\to\{0,1\}$ defines the Thorp step $T_c(bs)=s\,(b\oplus c(s))$, where $\oplus$ is addition modulo $2$.
--
--   1. *Raw states.* A raw state on $Q_n$ is a pair $v=(B,w)$ of a marker $B:Q_n\to\{0,1\}$ and a weight $w:Q_n\to\mathbb{R}$, with no further conditions.
--   2. *One raw step.* For a raw state $v=(B,w)$ on $Q_{d+1}$ and a coin vector $c$, $\operatorname{next}(v;c)=(B\circ T_c^{-1},\ \Phi_{B,c}w)$, where
--   $$
--   (\Phi_{B,c}w)(s\beta)=\begin{cases}\tfrac12\bigl(w(0s)+w(1s)\bigr)&\text{if }B(0s)=B(1s)=1,\\w\bigl((\beta\oplus c(s))\,s\bigr)&\text{otherwise,}\end{cases}\qquad s\in Q_d,\ \beta\in\{0,1\}.
--   $$
--   3. *Iteration.* For a history $\omega=(\omega_0,\dots,\omega_{t-1})$ of coin vectors, $v_0^\omega=v$ and $v_{k+1}^\omega=\operatorname{next}(v_k^\omega;\omega_k)$ for $k<t$.
--
--   This is the same recursion as for centered states (zero mass, support in the free set, energy at most $1$), with those three conditions dropped. Without them the recursion can be applied to pieces of a state, such as its restriction to half of the deck, which need not have zero mass.
--
--   **Formalization Note** The structure is `Conditional.RawState` with fields `free` and `weight`. The step `rawNext` uses `physicalFree` and `physicalFlow`, and `rawIterate` is defined by recursion on $t$, applying `ω (Fin.last t)` last.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/HalfHistories.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/HalfHistories.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins

namespace OAI

universe uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

structure RawState (d : ℕ) where
  free : Position d → Bool
  weight : Position d → ℝ

def rawNext (d : ℕ) (v : RawState (d + 1)) (c : Coins (d + 1)) : RawState (d + 1) where
  free := physicalFree d v.free c
  weight := physicalFlow d v.free v.weight c

def rawIterate (d : ℕ) (v : RawState (d + 1)) :
    (t : ℕ) → History (d + 1) t → RawState (d + 1)
  | 0, _ => v
  | t + 1, ω => rawNext d (rawIterate d v t (fun i => ω i.castSucc)) (ω (Fin.last t))

end Conditional

namespace Conditional

end Conditional

end Thorp

end

end OAI


