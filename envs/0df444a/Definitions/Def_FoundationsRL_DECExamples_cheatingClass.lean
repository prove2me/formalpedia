-- Prove2me | Definitions.Def_FoundationsRL_DECExamples_cheatingClass
-- name    : FoundationsRL_DECExamples_cheatingClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:20:45.246989+00:00
-- url     : https://prove2.me/theorems/c4044761-656b-4aff-8dd0-64f747501e38
-- title:
--   Cheating code class of Example 4.2
-- statement:
--   Let $A=2^n$. The decision space is $\Pi=[A]\cup\mathcal C$, where $\mathcal C=\{c_1,\dots,c_{\log_2 A}\}$ is a set of $n$ "cheating" actions. The **cheating code** class $\mathcal F$ consists of all $f:\Pi\to\mathbb R$ such that
--
--   1. $f(\pi)\in[0,1]$ for every $\pi\in[A]$, with no other assumption on these rewards;
--   2. $f(c_i)=-b_i(f)$ for every cheating action, where $b(f)=(b_1(f),\dots,b_n(f))$ is the binary encoding of $\pi_f$, the action in $[A]$ with highest reward.
--
--   The cheating actions never pay a positive reward, yet together they reveal the optimal action; UCB and posterior sampling ignore them, while the Decision-Estimation Coefficient exploits them (Proposition 15).
--
--   **Formalization Note** $\Pi$ is the sum type $\{0,\dots,2^n-1\}\oplus\{0,\dots,n-1\}$. When several actions of $[A]$ share the highest reward, any of them may be the one encoded, so the class contains every tie-breaking rule. The values on $\mathcal C$ lie in $\{-1,0\}$, so the class takes values in $[-1,1]$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Example 4.2, pp. 62–63

import Mathlib
import Definitions.Def_FoundationsRL_DECExamples_codeBit

namespace FoundationsRL.DECExamples

/-- The cheating code class of Example 4.2, for `A = 2^n` and `log₂(A) = n` cheating actions, on the
decision space `D = [A] ∪ C`.
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Example 4.2, pp. 62–63.

`f` belongs to the class when `f(π) ∈ [0, 1]` for every `π ∈ [A]` and `f(c_j) = −b_j(π_f)` for every
cheating action, where `π_f ∈ [A]` has the highest reward in `[A]`.

**Formalization Note.** The decision space is the sum type `Fin (2 ^ n) ⊕ Fin n`. The notes speak of
"the" highest-reward action; under ties any maximizer may be the one encoded, so the class contains
every tie-breaking rule. Values leave `[0, 1]` on `C` and stay in `[−1, 1]`. -/
def cheatingClass (n : ℕ) : Set (Fin (2 ^ n) ⊕ Fin n → ℝ) :=
  {f | (∀ i, f (Sum.inl i) ∈ Set.Icc (0 : ℝ) 1) ∧
    ∃ i, (∀ i', f (Sum.inl i') ≤ f (Sum.inl i)) ∧ ∀ j, f (Sum.inr j) = -codeBit i j}

end FoundationsRL.DECExamples


