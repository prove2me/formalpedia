-- Prove2me | Definitions.Def_OnlineCombOpt_Exp2LB_Setting
-- name    : OnlineCombOpt_Exp2LB_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:01:23.069011+00:00
-- url     : https://prove2.me/theorems/0797fbd9-5087-46bb-8160-04e31867adea
-- title:
--   §1, §2.1, App. A, pp. 2–15 — binary action sets, full-information EXP2 (Figure 2), the regret Rₙ, and the action set and adversaries of App. A
-- statement:
--   This file sets up the objects of the lower bound for the exponentially weighted forecaster EXP2 in online combinatorial optimization (Audibert, Bubeck, Lugosi, arXiv:1204.4710v2).
--
--   1. **Binary action sets** (p. 2). A finite set $\mathcal A\subseteq\{0,1\}^d\subseteq\mathbb R^d$ is a *binary action set with norm $m$* if it is nonempty, every $a\in\mathcal A$ has entries in $\{0,1\}$, and $\|a\|_1=\sum_{i=1}^d a(i)=m$ for every $a\in\mathcal A$.
--   2. **Losses.** A loss sequence is $z_1,z_2,\dots\in\mathbb R^d$; playing $a$ at round $t$ costs $a^\top z_t$. The cumulative loss of a fixed action over $n$ rounds is $L_n(a)=\sum_{t=1}^n a^\top z_t$.
--   3. **EXP2 in the full-information game** (Figure 2, p. 7, with $\tilde z_t=z_t$). With learning rate $\eta\in\mathbb R$, EXP2 plays $a_t\sim p_t$, where $p_1$ is uniform on $\mathcal A$ and, for every $a\in\mathcal A$,
--   $$p_{t+1}(a)=\frac{\exp(-\eta\,a^\top z_t)\,p_t(a)}{\sum_{b\in\mathcal A}\exp(-\eta\,b^\top z_t)\,p_t(b)}.$$
--   So $p_t$ depends only on $z_1,\dots,z_{t-1}$.
--   4. **Regret** (p. 2). Against a fixed loss sequence, the regret of EXP2 over $n$ rounds is
--   $$R_n=\sum_{t=1}^n\sum_{a\in\mathcal A}p_t(a)\,a^\top z_t-\min_{a\in\mathcal A}\sum_{t=1}^n a^\top z_t,$$
--   the expected cumulative loss of the forecaster minus the cumulative loss of the best fixed action in hindsight.
--   5. **The action set of App. A** (p. 14). For $d$ a multiple of $4$, $\mathcal A_d$ is the set of $a\in\{0,1\}^d$ with exactly $d/4$ ones among the coordinates $1,\dots,d/2$, and with exactly one of the two intervals $\{d/2+1,\dots,d/2+d/4\}$ and $\{d/2+d/4+1,\dots,d\}$ filled with ones, the other with zeros. Every $a\in\mathcal A_d$ has $\|a\|_1=d/2$, and $|\mathcal A_d|=2\binom{d/2}{d/4}$.
--   6. **The first adversary** (p. 15). $z_t(i)=1$ if $i\in\{d/2+1,\dots,d/2+d/4\}$ and $t$ is odd, $z_t(i)=1$ if $i\in\{d/2+d/4+1,\dots,d\}$ and $t$ is even, and $z_t(i)=0$ otherwise.
--   7. **The second adversary** (p. 15). For a parameter $\varepsilon$, $z_t(i)=1-\varepsilon$ if $i\le d/4$, $z_t(i)=1$ if $i\in\{d/4+1,\dots,d/2\}$, and $z_t(i)=0$ otherwise, at every round.
--
--   These are the objects of Theorem 1 and of the steps of its proof in App. A.
--
--   **Formalization Note** Actions are real vectors `Fin d → ℝ`, so $a^\top z$ is the dot product `a ⬝ᵥ z`. Coordinates and rounds are 0-based: coordinate $i$ of the paper is index $i-1$, and round $t$ of the paper is index $t-1$, so the paper's *odd* rounds are the *even* indices of `adv1`. `exp2Weights A η z t` is $p_{t+1}$ (index $0$ is the uniform $p_1$); it is the recursion of Figure 2, not its closed form, and it is $0$ off $\mathcal A$. The regret is defined for a deterministic, oblivious loss sequence, for which the expectation is the finite sum above. The minimum is `Finset.inf'`; the empty-set branch of `exp2Regret` (value $0$) is never used, because every statement assumes a nonempty action set. The paper's set $\mathcal A$ on p. 14 is printed as "$a_i=1$ on the first interval or $a_i=1$ on the second interval"; following the accompanying prose ("choosing one of the two first disjoint intervals") and the setting $\|a\|_1=m$ of p. 2, exactly one interval is filled and the other is zero. The adversaries are defined for every $d$ and every real $\varepsilon$; the statements use them only for $4\mid d$ and $\varepsilon\in(0,1]$.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 2 (setting and regret), p. 3 Figure 1, p. 7 Figure 2 (EXP2), App. A p. 14 (the set 𝒜), App. A p. 15 (the two adversaries)

import Mathlib

namespace OnlineCombOpt.Exp2LB

open Finset

noncomputable section

/-- The setting of online combinatorial optimization (Audibert, Bubeck, Lugosi, arXiv:1204.4710v2,
p. 2): the action set `A ⊆ {0,1}^d` is nonempty, every `a ∈ A` has 0/1 entries, and every `a ∈ A`
has `‖a‖₁ = m`. Actions are real vectors so that the loss `aᵀz` is the dot product `a ⬝ᵥ z`. -/
def IsBinaryActionSet {d : ℕ} (A : Finset (Fin d → ℝ)) (m : ℕ) : Prop :=
  A.Nonempty ∧ ∀ a ∈ A, (∀ i, a i = 0 ∨ a i = 1) ∧ ∑ i, a i = (m : ℝ)

/-- EXP2 in the full-information game (Figure 2, p. 7, with `z̃ₜ = zₜ`), against a fixed loss
sequence `z` (round `t` of the paper is index `t - 1` here).

`exp2Weights A η z t a` is the probability `p_{t+1}(a)` that EXP2 with learning rate `η` puts on the
action `a` at the paper's round `t + 1`; it depends on `z 0, …, z (t - 1)` only.
* `p₁` is uniform on `A` (and `0` off `A`);
* `p_{t+1}(a) = exp(-η aᵀz_t) p_t(a) / Σ_{b ∈ A} exp(-η bᵀz_t) p_t(b)`. -/
def exp2Weights {d : ℕ} (A : Finset (Fin d → ℝ)) (η : ℝ) (z : ℕ → Fin d → ℝ) :
    ℕ → (Fin d → ℝ) → ℝ
  | 0, a => if a ∈ A then 1 / (A.card : ℝ) else 0
  | t + 1, a => Real.exp (-η * (a ⬝ᵥ z t)) * exp2Weights A η z t a /
      ∑ b ∈ A, Real.exp (-η * (b ⬝ᵥ z t)) * exp2Weights A η z t b

/-- The cumulative loss `Σ_{t=1}^n aᵀz_t` of a fixed action `a` over the first `n` rounds. -/
def cumLoss {d : ℕ} (a : Fin d → ℝ) (z : ℕ → Fin d → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ range n, a ⬝ᵥ z t

/-- The expected cumulative loss `𝔼 Σ_{t=1}^n a_tᵀz_t` of EXP2 against the fixed loss sequence `z`,
where `a_t ∼ p_t`. -/
def exp2ExpectedLoss {d : ℕ} (A : Finset (Fin d → ℝ)) (η : ℝ) (z : ℕ → Fin d → ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ range n, ∑ a ∈ A, exp2Weights A η z t a * (a ⬝ᵥ z t)

/-- The regret (p. 2) of full-information EXP2 against the fixed (deterministic, oblivious) loss
sequence `z` over `n` rounds:
`R_n = 𝔼 Σ_{t=1}^n a_tᵀz_t − min_{a ∈ A} Σ_{t=1}^n aᵀz_t`.
The minimum is `A.inf'`; the branch `A = ∅` (value `0`) is never used, since every statement
requires `IsBinaryActionSet A m`, which includes `A.Nonempty`. -/
def exp2Regret {d : ℕ} (A : Finset (Fin d → ℝ)) (η : ℝ) (z : ℕ → Fin d → ℝ) (n : ℕ) : ℝ :=
  exp2ExpectedLoss A η z n -
    (if h : A.Nonempty then A.inf' h (fun a => cumLoss a z n) else 0)

/-- The 0/1 indicator vector of a Boolean vector. -/
def boolToReal {d : ℕ} (b : Fin d → Bool) : Fin d → ℝ :=
  fun i => if b i then 1 else 0

/-- The predicate defining the action set of App. A (p. 14), on Boolean vectors, with 0-based
coordinates: exactly `d/4` ones among the first half `i < d/2`, and exactly one of the two
intervals `d/2 ≤ i < d/2 + d/4` and `d/2 + d/4 ≤ i < d` is all ones while the other is all zeros. -/
def IsThmOneVertex {d : ℕ} (b : Fin d → Bool) : Prop :=
  (univ.filter (fun i : Fin d => i.val < d / 2 ∧ b i = true)).card = d / 4 ∧
    (((∀ i : Fin d, d / 2 ≤ i.val → i.val < d / 2 + d / 4 → b i = true) ∧
        (∀ i : Fin d, d / 2 + d / 4 ≤ i.val → b i = false)) ∨
      ((∀ i : Fin d, d / 2 ≤ i.val → i.val < d / 2 + d / 4 → b i = false) ∧
        (∀ i : Fin d, d / 2 + d / 4 ≤ i.val → b i = true)))

/-- The action set `𝒜 ⊆ {0,1}^d` of App. A (p. 14): choose `d/4` coordinates among the first half,
and one of the two disjoint intervals of length `d/4` in the second half. -/
def thmOneSet (d : ℕ) : Finset (Fin d → ℝ) :=
  by classical exact (univ.filter (fun b : Fin d → Bool => IsThmOneVertex b)).image boolToReal

/-- The first adversary of App. A (p. 15). The paper's round `t` is index `t - 1`, so the paper's
odd rounds are the even indices: at even indices the loss is `1` on the first interval
`d/2 ≤ i < d/2 + d/4`, at odd indices it is `1` on the second interval `d/2 + d/4 ≤ i < d`, and
`0` elsewhere. -/
def adv1 (d : ℕ) : ℕ → Fin d → ℝ :=
  fun t i =>
    if (d / 2 ≤ i.val ∧ i.val < d / 2 + d / 4 ∧ Even t) ∨ (d / 2 + d / 4 ≤ i.val ∧ Odd t) then 1
    else 0

/-- The second adversary of App. A (p. 15), constant in time: loss `1 - ε` on the first quarter
`i < d/4`, loss `1` on the second quarter `d/4 ≤ i < d/2`, and `0` on the second half. -/
def adv2 (d : ℕ) (ε : ℝ) : ℕ → Fin d → ℝ :=
  fun _ i => if i.val < d / 4 then 1 - ε else if i.val < d / 2 then 1 else 0

end

end OnlineCombOpt.Exp2LB


