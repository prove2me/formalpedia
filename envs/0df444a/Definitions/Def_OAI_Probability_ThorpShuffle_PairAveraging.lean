-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
-- name    : OAI_Probability_ThorpShuffle_PairAveraging
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:20:12.862967+00:00
-- url     : https://prove2.me/theorems/2c04d8bc-c25f-440a-9205-d65c70c93113
-- title:
--   Uniform means, signs, coin toggles and the pairwise averaging flow
-- statement:
--   This module provides elementary tools for averaging over coins, together with a one-step update of a real weight that acts separately on pairs of points. Booleans are identified with bits and $\oplus$ is addition modulo $2$.
--
--   1. *Uniform mean.* For a finite set $\Omega$ and $f:\Omega\to\mathbb{R}$, $\operatorname{mean}(f)=\frac{1}{|\Omega|}\sum_{\omega\in\Omega}f(\omega)$.
--   2. *Sign.* $\operatorname{sgn}(b)=(-1)^b$, so $\operatorname{sgn}(0)=1$ and $\operatorname{sgn}(1)=-1$. It satisfies $\operatorname{sgn}(1-b)=-\operatorname{sgn}(b)$ and $\operatorname{sgn}(b)^2=1$.
--   3. *Coin toggle.* For a set $A$ and $i\in A$, the involution of $\{0,1\}^A$ that flips the $i$-th coordinate and leaves the others unchanged.
--   4. *Pair update.* For flags $u_0,u_1\in\{0,1\}$, reals $a,b$ and a coin $\gamma\in\{0,1\}$,
--   $$
--   \operatorname{pu}(u_0,u_1;a,b;\gamma)=\begin{cases}\bigl(\tfrac{a+b}{2},\tfrac{a+b}{2}\bigr)&\text{if }u_0=u_1=1,\\ (b,a)&\text{if not }u_0=u_1=1\text{, and }\gamma=1,\\ (a,b)&\text{otherwise.}\end{cases}
--   $$
--   5. *Pair flow.* Let $A$ be a set, $B:\{0,1\}\times A\to\{0,1\}$ a marker of free points, $w:\{0,1\}\times A\to\mathbb{R}$ a weight and $c:A\to\{0,1\}$ a coin vector. The flow $F_{B,w,c}:\{0,1\}\times A\to\mathbb{R}$ applies the pair update to each pair $\{(0,s),(1,s)\}$ separately:
--   $$
--   \bigl(F_{B,w,c}(0,s),\,F_{B,w,c}(1,s)\bigr)=\operatorname{pu}\bigl(B(0,s),B(1,s);\,w(0,s),w(1,s);\,c(s)\bigr).
--   $$
--   A pair whose two points are both free has its weights replaced by their average. Every other pair has its two weights exchanged when $c(s)=1$ and kept when $c(s)=0$.
--   6. *Pair map.* $\pi_c(b,s)=(b\oplus c(s),\,s)$ on $\{0,1\}\times A$.
--
--   The module also records three properties of the flow. For finite $A$ it preserves the total mass, $\sum_xF_{B,w,c}(x)=\sum_xw(x)$, and it does not increase the energy, $\sum_xF_{B,w,c}(x)^2\le\sum_xw(x)^2$. Both already hold pair by pair: $\operatorname{pu}$ preserves $a+b$ and does not increase $a^2+b^2$. The flow also respects supports: if $w(x)=0$ whenever $B(x)=0$, then $F_{B,w,c}(x)=0$ whenever $B(\pi_c(x))=0$.
--
--   The flow is the pair-coordinate form of one shuffle step acting on a signed weight after part of the randomness has been averaged out. When both points of a pair are free, the coin of that pair moves no marked (non-free) card, so averaging over it replaces both weights by their mean. At the other pairs the coin is kept and the weights move with it. Mass preservation and the energy inequality are the invariants behind the later energy-decay estimates for the Thorp shuffle.
--
--   **Formalization Note** `mean` divides by `Fintype.card Ω`. For an empty $\Omega$, Lean's convention $x/0=0$ makes the mean $0$. The objects are `Conditional.mean`, `sign`, `toggleCoin`, `pairUpdate`, `flow` and `pairMap`. The lemmas `pairUpdate_sum`, `pairUpdate_energy_le`, `flow_sum`, `flow_energy_le` and `flow_support` state the properties above, and `sign_not`, `sign_sq`, `sign_mul_self` and `toggleCoin_apply` are simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/PairAveraging.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/PairAveraging.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uΩ uα

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def mean {Ω : Type uΩ} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ ω, f ω) / Fintype.card Ω

def sign (b : Bool) : ℝ := if b then -1 else 1

@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

@[simp] theorem sign_mul_self (b : Bool) : sign b * sign b = 1 := by
  simpa only [pow_two] using sign_sq b

def toggleCoin {α : Type uα} [DecidableEq α] (i : α) : Equiv.Perm (α → Bool) :=
  Function.Involutive.toPerm (fun c => Function.update c i (!(c i))) (by
    intro c
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h])

@[simp] theorem toggleCoin_apply {α : Type uα} [DecidableEq α]
    (i : α) (c : α → Bool) (j : α) :
    toggleCoin i c j = Function.update c i (!(c i)) j := rfl

def pairUpdate (free₀ free₁ : Bool) (a b : ℝ) (coin : Bool) : ℝ × ℝ :=
  if free₀ && free₁ then ((a + b) / 2, (a + b) / 2)
  else if coin then (b, a) else (a, b)

@[simp] theorem pairUpdate_sum (free₀ free₁ : Bool) (a b : ℝ) (coin : Bool) :
    (pairUpdate free₀ free₁ a b coin).1 + (pairUpdate free₀ free₁ a b coin).2 = a + b := by
  cases free₀ <;> cases free₁ <;> cases coin <;> simp [pairUpdate] <;> ring

def flow {α : Type uα} (B : Bool × α → Bool) (w : Bool × α → ℝ)
    (c : α → Bool) (x : Bool × α) : ℝ :=
  let p := pairUpdate (B (false, x.2)) (B (true, x.2))
    (w (false, x.2)) (w (true, x.2)) (c x.2)
  if x.1 then p.2 else p.1

end Conditional

namespace Conditional

def pairMap {α : Type uα} (c : α → Bool) (x : Bool × α) : Bool × α :=
  (x.1 ^^ c x.2, x.2)

theorem flow_support {α : Type uα} (B : Bool × α → Bool) (w : Bool × α → ℝ)
    (hw : ∀ x, B x = false → w x = 0) (c : α → Bool) (x : Bool × α)
    (hx : B (pairMap c x) = false) : flow B w c x = 0 := by
  rcases x with ⟨b, i⟩
  have h₀ := hw (false, i)
  have h₁ := hw (true, i)
  cases b <;> cases hb₀ : B (false, i) <;> cases hb₁ : B (true, i) <;>
    cases hc : c i <;> simp_all [flow, pairUpdate, pairMap]

theorem flow_sum {α : Type uα} [Fintype α] (B : Bool × α → Bool)
    (w : Bool × α → ℝ) (c : α → Bool) :
    (∑ x, flow B w c x) = ∑ x, w x := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [flow, Bool.false_eq_true, ↓reduceIte, add_comm] using
    (pairUpdate_sum (B (false, i)) (B (true, i)) (w (false, i)) (w (true, i)) (c i))

theorem pairUpdate_energy_le (free₀ free₁ : Bool) (a b : ℝ) (coin : Bool) :
    (pairUpdate free₀ free₁ a b coin).1 ^ 2 +
        (pairUpdate free₀ free₁ a b coin).2 ^ 2 ≤ a ^ 2 + b ^ 2 := by
  have h := sq_nonneg (a - b)
  cases free₀ <;> cases free₁ <;> cases coin <;> simp [pairUpdate] <;> nlinarith

theorem flow_energy_le {α : Type uα} [Fintype α] (B : Bool × α → Bool)
    (w : Bool × α → ℝ) (c : α → Bool) :
    (∑ x, flow B w c x ^ 2) ≤ ∑ x, w x ^ 2 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [flow, Bool.false_eq_true, ↓reduceIte, add_comm] using
    pairUpdate_energy_le (B (false, i)) (B (true, i)) (w (false, i)) (w (true, i)) (c i)

end Conditional

end Thorp

end

end OAI


