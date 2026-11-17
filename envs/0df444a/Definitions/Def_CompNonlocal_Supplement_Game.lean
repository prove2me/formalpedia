-- Prove2me | Definitions.Def_CompNonlocal_Supplement_Game
-- name    : CompNonlocal_Supplement_Game
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:05:54.991802+00:00
-- url     : https://prove2.me/theorems/05cba003-f14e-49a2-8d42-1045b48355fb
-- title:
--   The k-round distinguishing game (Definitions 8–9)
-- statement:
--   A **distinguishing game** on a bipartite state of $n_A+n_B$ qubits consists of the verifier's question generation $Q(1^\kappa)\to(x,y,\mathrm{td})$ (classical, possibly correlated questions and a private register $\mathrm{td}$, which may be quantum), Alice's and Bob's algorithms $A(x,\omega_A)\to a$, $B(y,\omega_B)\to b$, the score $\mathrm{Val}(a,b,x,y;\mathrm{td})\to v\in[-1,1]\cup\{\bot\}$, and a number of rounds $k(\kappa)$.
--
--   The game is played in $k$ independent rounds, each with a fresh execution of $Q$, a fresh copy of the state and the same local algorithms. With $S=\{i: v_i\ne\bot\}$, the verifier accepts iff
--   $$|S|>0\quad\text{and}\quad\frac1{|S|}\sum_{i\in S}v_i<0.$$
--
--   Derived functions: the joint and marginal laws of the questions, the decoding of scores, the one-round law of Val's output for given players and state, the acceptance rule, and the acceptance probability of the $k$-round game.
--
--   **Formalization Note** Val's output encodes $\bot$ by a leading $1$, otherwise a signed dyadic score (`decDyadic`) clipped to $[-1,1]$. The $k$-round law is the product of the one-round law.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Definition 8, pp.23–24; Definition 9, pp.24–25

import Mathlib
import Definitions.Def_CompNonlocal_Family
import Definitions.Def_CompNonlocal_ICirc_effectOn
import Definitions.Def_CompNonlocal_ICirc_branchOn
import Definitions.Def_CompNonlocal_fit
import Definitions.Def_CompNonlocal_decDyadic

set_option autoImplicit false

open scoped Kronecker

namespace CompNonlocal.Supplement

open QAlgorithms.Complexity

/-- The `k`-round distinguishing game on a bipartite state of `n_A + n_B` qubits. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…),
Definition 8, pp.23–24 and Definition 9, pp.24–25: the verifier `V = (Q, Val)` with "Q(1^κ) →
(x, y, td) … jointly generates classical questions x, y and a private register td, which may be
quantum … The questions may be correlated", Alice's and Bob's algorithms `A(x, ω_A) → a`,
`B(y, ω_B) → b`, and the score "v_i ← Val(a_i, b_i, x_i, y_i, td_i), v_i ∈ [−1, 1] ∪ {⊥}. If v_i = ⊥,
the round is discarded. Let S := {i ∈ [k] : v_i ≠ ⊥} be the set of accepted rounds. After the k-th
round, V outputs Accept if |S| > 0 and (1/|S|) Σ_{i∈S} v_i < 0, and Reject otherwise. The same local
response algorithms are used in every round. Each round uses an independent execution of Q, fresh
independent copies of the chosen state, fresh local workspaces, and independent randomness."

The derived functions in this module, at security parameter `κ`: `qProb κ x y`, `xProb κ x`,
`yProb κ y`, the joint and marginal laws of the questions; `decScore w`, the score `∈ [−1,1] ∪ {⊥}`
encoded by Val's output `w`; `roundProb κ A' B' τ w`, the probability that one round, played by
`A'`, `B'` on one copy of `τ`, ends with Val's output `w`; `kAccept v`, the acceptance rule on the
scores `v` of all rounds; `accK κ A' B' τ`, the acceptance probability of the `k κ`-round game.

**Formalization Note** `Qg` has no input; its classical output `o` is split as `x = o.take (lx κ)`,
`y = o.drop (lx κ)` and its quantum output is `td`. Alice reads `x` classically and her `n_A` qubits
on her quantum-input wires, Bob likewise with `y` and `n_B` qubits (Alice's register is the first
tensor factor). Val reads `fit (la κ) a ++ fit (lb κ) b ++ x ++ y` and `td`. Its output `w` encodes
`⊥` when its first bit is `1`, and otherwise the score `decDyadic` of the rest, clipped to
`[−1, 1]`. Independent rounds with fresh copies make the law of the `k` outputs the product of the
one-round law. A ⊥ round adds `0` to the sum, and with `|S| > 0` the average is negative iff the sum
over `S` is. -/
structure Game where
  /-- The verifier's question generation `Q`. -/
  Qg : Family
  /-- Alice's honest algorithm `A`. -/
  A : Family
  /-- Bob's honest algorithm `B`. -/
  B : Family
  /-- The verifier's score `Val`. -/
  Val : Family
  /-- The length of Alice's question `x` inside `Q`'s classical output `x ++ y`. -/
  lx : ℕ → ℕ
  /-- The length of Alice's answer. -/
  la : ℕ → ℕ
  /-- The length of Bob's answer. -/
  lb : ℕ → ℕ
  /-- The number of rounds `k(κ)`. -/
  k : ℕ → ℕ

namespace Game

/-- The probability that `Q` outputs the classical string `o`. -/
noncomputable def oProb (G : Game) (κ : ℕ) (o : Bits (G.Qg κ).outC.length) : ℝ :=
  ((G.Qg κ).effectOn 0 [] (fun t => decide (t = List.ofFn o))).trace.re

/-- `Pr[(X, Y) = (x, y)]`. -/
noncomputable def qProb (G : Game) (κ : ℕ) (x y : Str) : ℝ :=
  ∑ o : Bits (G.Qg κ).outC.length,
    if (List.ofFn o).take (G.lx κ) = x ∧ (List.ofFn o).drop (G.lx κ) = y then G.oProb κ o else 0

/-- `Pr[X = x]`. -/
noncomputable def xProb (G : Game) (κ : ℕ) (x : Str) : ℝ :=
  ∑ o : Bits (G.Qg κ).outC.length, if (List.ofFn o).take (G.lx κ) = x then G.oProb κ o else 0

/-- `Pr[Y = y]`. -/
noncomputable def yProb (G : Game) (κ : ℕ) (y : Str) : ℝ :=
  ∑ o : Bits (G.Qg κ).outC.length, if (List.ofFn o).drop (G.lx κ) = y then G.oProb κ o else 0

/-- The score encoded by Val's output: `none` is `⊥`. -/
noncomputable def decScore (w : Str) : Option ℝ :=
  if w.headD false then none else some (max (-1) (min 1 (decDyadic w.tail).1))

/-- The probability that one round, played by `A'`, `B'` on one copy of `τ`, ends with Val's
output `w`. -/
noncomputable def roundProb (G : Game) (κ : ℕ) {nA nB : ℕ} (A' B' : Family)
    (τ : Matrix (Bits nA × Bits nB) (Bits nA × Bits nB) ℂ) (w : Str) : ℝ :=
  ∑ o : Bits (G.Qg κ).outC.length, ∑ a : Bits (A' κ).outC.length, ∑ b : Bits (B' κ).outC.length,
    ((((A' κ).effectOn nA ((List.ofFn o).take (G.lx κ)) (fun t => decide (t = List.ofFn a))) ⊗ₖ
        ((B' κ).effectOn nB ((List.ofFn o).drop (G.lx κ)) (fun t => decide (t = List.ofFn b)))) *
        τ).trace.re *
      ((G.Val κ).effectOn (G.Qg κ).outQ.length
          (fit (G.la κ) (List.ofFn a) ++ fit (G.lb κ) (List.ofFn b) ++ List.ofFn o)
          (fun t => decide (t = w)) *
        (G.Qg κ).branchOn 0 [] 1 (fun t => decide (t = List.ofFn o))).trace.re

/-- The verifier's decision on the scores of all rounds: some round is not discarded and the sum
(equivalently, the average) of the retained scores is negative. -/
def kAccept {n : ℕ} (v : Fin n → Option ℝ) : Prop :=
  (∃ i, v i ≠ none) ∧ ∑ i, (v i).getD 0 < 0

open Classical in
/-- The acceptance probability of the `k κ`-round game played by `A'`, `B'` on fresh copies of `τ`. -/
noncomputable def accK (G : Game) (κ : ℕ) {nA nB : ℕ} (A' B' : Family)
    (τ : Matrix (Bits nA × Bits nB) (Bits nA × Bits nB) ℂ) : ℝ :=
  ∑ w : Fin (G.k κ) → Bits (G.Val κ).outC.length,
    (∏ i, G.roundProb κ A' B' τ (List.ofFn (w i))) *
      if kAccept (fun i => decScore (List.ofFn (w i))) then 1 else 0

end Game

end CompNonlocal.Supplement


