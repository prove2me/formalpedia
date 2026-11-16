-- Prove2me | Definitions.Def_DDNNFNeg_Supplement_IsAcceptingRun
-- name    : DDNNFNeg_Supplement_IsAcceptingRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:44:09.267886+00:00
-- url     : https://prove2.me/theorems/1316050b-e0b9-4aa1-87f0-18b5b5f18f5c
-- title:
--   Accepting run of a nondeterministic finite automaton
-- statement:
--   Let $M$ be a nondeterministic finite automaton with transition relation $\delta$ and input $x = x_1 \cdots x_m$. An **accepting run** ("sequence of moves leading to an accept state") of $M$ on $x$ is a sequence of states $p_0, p_1, \dots, p_m$ with $p_0$ an initial state, $p_i \in \delta(p_{i-1}, x_i)$ for $i = 1, \dots, m$, and $p_m$ an accept state.
--
--   Runs are what unambiguity counts.
--
--   **Formalization Note** Mathlib's `NFA` allows a set of initial states; the paper's single initial state is imposed in `IsUFAOfSize`.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), Definition 8.4, p.20

import Mathlib

namespace DDNNFNeg.Supplement

/-- `p` is an accepting run (a "sequence of moves leading to an accept state") of the
nondeterministic finite automaton `M` on the input `x` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), Definition 8.4, p.20): a
sequence of states `p₀, …, p_{|x|}` with `p₀` a start state, `p_i ∈ δ(p_{i−1}, x_i)` for each
`i`, and `p_{|x|}` an accept state.

**Formalization Note** Mathlib's `NFA` has a set of start states; the paper's single initial
state is imposed in `IsUFAOfSize`. -/
def IsAcceptingRun {α σ : Type*} (M : NFA α σ) (x : List α) (p : Fin (x.length + 1) → σ) :
    Prop :=
  p 0 ∈ M.start ∧ (∀ i : Fin x.length, p i.succ ∈ M.step (p i.castSucc) (x.get i)) ∧
    p (Fin.last x.length) ∈ M.accept

end DDNNFNeg.Supplement


