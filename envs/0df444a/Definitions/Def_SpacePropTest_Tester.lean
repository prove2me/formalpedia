-- Prove2me | Definitions.Def_SpacePropTest_Tester
-- name    : SpacePropTest_Tester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:35.883449+00:00
-- url     : https://prove2.me/theorems/20834d3e-b2d4-4a79-a265-92a0c3321b93
-- title:
--   $M$-state testers (Definition 7), the chain $A_f$, $\hat p_{A_f}(S_{\mathrm{Acc}})$, $(\varepsilon,\delta)$-testers, normal form (Definition 12)
-- statement:
--   An **$M$-state tester** $A$ has a set of $M$ states with an initial state, and for each state $s$:
--
--   1. a distribution $Q_s$ on $\{0,1\}^n$ (the point to query);
--   2. for each queried point $x$ and answer $b\in\{0,1\}$, a distribution $M_s(x,b,\cdot)$ on states (the next state);
--   3. a value $v(s)\in\{\mathrm{Acc},\mathrm{Rej}\}$.
--
--   On input $f$ the tester runs forever as the Markov chain
--
--   $$A_f(s,s')=\sum_{x\in\{0,1\}^n}\delta_{s,s'}(x,f(x)),\qquad \delta_{s,s'}(x,b)=Q_s(x)\,M_s(x,b,s').$$
--
--   Its acceptance probability is $\hat p_{A_f}(S_{\mathrm{Acc}})=\sum_{s:\,v(s)=\mathrm{Acc}}\hat p_{A_f}(s)$. $A$ is an **$(\varepsilon,\delta)$-tester** for $\mathcal P$ if $\hat p_{A_f}(S_{\mathrm{Acc}})\ge1-\delta$ for every $f\in\mathcal P$ and $\hat p_{A_g}(S_{\mathrm{Acc}})\le\delta$ for every $g$ that is $\varepsilon$-far from $\mathcal P$. $A$ is in **normal form** (Definition 12) if for every state $s'$ there is a bit $b_{s'}$ with $\delta_{s,s'}(x,1-b_{s'})=0$ for all $s,x$.
--
--   This is the paper's bounded-memory testing model; its memory is $\lceil\log_2 M\rceil$ bits.
--
--   **Formalization Note** States are a finite type with a designated start state ($M$ is its cardinality). The paper defines $(\varepsilon,\delta)$-testers for $\varepsilon,\delta\in(0,1]$; the range is stated in the theorems that use the notion.
-- source:
--   Canonne, Chen, Pires, Pitassi, Servedio, The Space Complexity of Property Testing, manuscript of November 2, 2026 (sha256 65850aa6…), Definition 7, p.15 (PDF 17), eqs. (3)–(4); p.16 (PDF 18); Definition 12, p.17 (PDF 19)

import Mathlib
import Definitions.Def_SpacePropTest_Cube
import Definitions.Def_SpacePropTest_MarkovChain

set_option autoImplicit false

namespace SpacePropTest

noncomputable section

/-- **M-state tester** (C. Canonne, X. Chen, W. Pires, T. Pitassi, R. A. Servedio, *The Space
Complexity of Property Testing*, manuscript of November 2, 2026, sha256 65850aa6…; Definition 7,
p.15 (PDF 17)).

A tester with finite state type `σ` (an `M`-state tester when `Fintype.card σ = M`) has an initial
state `start`, and for each state `s`: a query distribution `Q s` on `{0,1}ⁿ`, next-state
distributions `Mt s x b` on `σ` for each queried point `x` and answer `b`, and a value
`acc s` (`true` = Acc, `false` = Rej).

**Formalization Note.** States are an arbitrary finite type with a designated start state instead
of `[M]` with start state `1`. There are no halting states: the tester runs forever. -/
structure Tester (n : ℕ) (σ : Type*) [Fintype σ] where
  /-- The initial state. -/
  start : σ
  /-- `Q s x`: probability of querying `x` in state `s`. -/
  Q : σ → Cube n → ℝ
  /-- `Mt s x b s'`: probability of entering `s'` from `s` after querying `x` and receiving `b`. -/
  Mt : σ → Cube n → Bool → σ → ℝ
  /-- `acc s = true` iff `v(s) = Acc`. -/
  acc : σ → Bool
  Q_nonneg : ∀ s x, 0 ≤ Q s x
  Q_sum : ∀ s, ∑ x, Q s x = 1
  Mt_nonneg : ∀ s x b s', 0 ≤ Mt s x b s'
  Mt_sum : ∀ s x b, ∑ s', Mt s x b s' = 1

namespace Tester

variable {n : ℕ} {σ : Type*} [Fintype σ]

/-- `δ_{s,s'}(x, b) = Q_s(x) · M_s(x, b, s')` (eq. (4), p.15). -/
def delta (A : Tester n σ) (s s' : σ) (x : Cube n) (b : Bool) : ℝ :=
  A.Q s x * A.Mt s x b s'

/-- The Markov chain `A_f`: `A_f(s, s') = ∑_x δ_{s,s'}(x, f(x))` (eq. (3), p.15). -/
def chain (A : Tester n σ) (f : BoolFn n) : Matrix σ σ ℝ :=
  fun s s' => ∑ x, A.delta s s' x (f x)

variable [DecidableEq σ]

/-- `p̂_{A_f}(s)`, the long-run probability of state `s` (p.15). -/
def longRunT (A : Tester n σ) (f : BoolFn n) (s : σ) : ℝ :=
  longRun (A.chain f) A.start s

/-- `p̂_{A_f}(S_Acc) = ∑_{s : v(s) = Acc} p̂_{A_f}(s)` (p.16). -/
def accProb (A : Tester n σ) (f : BoolFn n) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s => A.acc s = true), A.longRunT f s

/-- `A` is an `(ε, δ)`-tester for `P` (p.16): every `f ∈ P` has `p̂_{A_f}(S_Acc) ≥ 1 − δ`, and
every `g` that is `ε`-far from every `f ∈ P` has `p̂_{A_g}(S_Acc) ≤ δ`.

**Formalization Note.** The paper defines this for `ε, δ ∈ (0, 1]`; the range is stated as a
hypothesis in the statements that use it. -/
def IsTester (A : Tester n σ) (P : Set (BoolFn n)) (ε δ : ℝ) : Prop :=
  (∀ f ∈ P, 1 - δ ≤ A.accProb f) ∧ (∀ g, IsFar P g ε → A.accProb g ≤ δ)

/-- Normal form (Definition 12, p.17): for every state `s'` there is a bit `b_{s'}` with
`δ_{s,s'}(x, 1 − b_{s'}) = 0` for all `s, x`. -/
def IsNormalForm (A : Tester n σ) : Prop :=
  ∀ s', ∃ b : Bool, ∀ s x, A.delta s s' x (!b) = 0

end Tester

end

end SpacePropTest


