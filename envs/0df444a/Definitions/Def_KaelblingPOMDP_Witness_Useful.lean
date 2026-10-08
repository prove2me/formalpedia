-- Prove2me | Definitions.Def_KaelblingPOMDP_Witness_Useful
-- name    : KaelblingPOMDP_Witness_Useful
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:10.324777+00:00
-- url     : https://prove2.me/theorems/eaaf15d8-a1f1-483d-8720-20ecc8604b27
-- title:
--   Useful policy trees R(α, V) ≠ ∅, V_{t−1}, the candidates for Q^a_t, the set Q^a_t, the Q-function Q^a_t(b) and the upper surface Q̂^a_t(b) (§4.2–§4.4, Appendix A)
-- statement:
--   This file defines the sets of policy trees that the witness algorithm manipulates.
--
--   For a finite set $\tilde V$ of policy trees of the same depth and a tree $p \in \tilde V$, the **dominance region** of $p$ is
--   $$R(\alpha_p, \tilde V) = \{ b \in B \mid b \cdot \alpha_p > b \cdot \alpha_q \text{ for every } q \in \tilde V \text{ with } \alpha_q \ne \alpha_p \},$$
--   where $B$ is the set of belief states. Trees with the same value function are identified, so ties with such trees do not count. The tree $p$ is **useful in** $\tilde V$ if this region is nonempty; the useful trees of $\tilde V$ form its parsimonious representation.
--
--   For $t \ge 2$:
--
--   1. $\mathcal V_{t-1}$ is the set of useful $(t-1)$-step trees, usefulness being measured in the set of all $(t-1)$-step trees;
--   2. the **candidates** $C^a_t$ are the $t$-step trees with root action $a$ whose every subtree belongs to $\mathcal V_{t-1}$;
--   3. $\mathcal Q^a_t$, the complete set of useful policy trees for action $a$, is the set of trees useful in $C^a_t$;
--   4. the **Q-function** is
--   $$Q^a_t(b) = \sum_{s} b(s) R(s, a) + \gamma \sum_{o \in \Omega} \Pr(o \mid a, b)\, V_{t-1}(SE(b, a, o)),$$
--   the value of taking action $a$ in belief state $b$ and continuing optimally for $t-1$ steps;
--   5. for a finite nonempty set $U$ of trees, the **upper surface** is $b \mapsto \max_{p \in U} V_p(b)$. For $U = U_a$ this is the approximate Q-function $\hat Q^a_t$.
--
--   These are the sets in which the witness theorem compares the current approximation $U_a$ with $\mathcal Q^a_t$.
--
--   **Formalization Note** `Useful M W p` requires `p ∈ W` and a belief state $b$ with $V_q(b) < V_p(b)$ for every $q \in W$ with `value M q ≠ value M p`. `usefulSet M W` is the filter of `W` by this predicate, `usefulTrees M n` is $\mathcal V_{n+1}$, and `candidates M a n` and `Qset M a n` are $C^a_{n+2}$ and $\mathcal Q^a_{n+2}$. `Qfun M a n` is $Q^a_{n+2}$ written as on p. 114, with $V_{t-1}$ the maximum over all $(t-1)$-step trees. A term with $\Pr(o \mid a, b) = 0$ is multiplied by zero. `upper M W hW b` is $\max_{p \in W} V_p(b)$ and takes a proof that $W$ is nonempty.
-- source:
--   Kaelbling, Littman, Cassandra, Planning and acting in partially observable stochastic domains, Artificial Intelligence 101:99–134 (1998), DOI 10.1016/S0004-3702(98)00023-X, p. 112 (§4.2, R(α, V) and footnote 6), p. 113 (§4.3), p. 114 (§4.4, Q^a_t(b)), p. 115 (§4.4.1, Q̂^a_t), p. 130 (Appendix A)

import Mathlib
import Definitions.Def_KaelblingPOMDP_Witness_Model

namespace KaelblingPOMDP.Witness

open Finset

universe u

variable {S A Ω : Type u} [Fintype S] [Fintype Ω]

/-- The upper surface `b ↦ max_{p ∈ W} V_p(b)` of the value functions of a finite nonempty set `W` of
policy trees (p. 110: "V_t is the upper surface of this collection of functions"). For `W = U_a` this is
the approximate Q-function `Q̂^a_t(b) = max_{p ∈ U_a} V_p(b)` of §4.4.1, p. 115. -/
noncomputable def upper (M : POMDP S A Ω) {n : ℕ} (W : Finset (PolicyTree A Ω n)) (hW : W.Nonempty)
    (b : S → ℝ) : ℝ :=
  W.sup' hW (fun p => valueAt M p b)

/-- A policy tree `p` is **useful in** the finite set `W` (§4.2, p. 112) when `p ∈ W` and its region
`R(α_p, W) = {b ∈ B | b · α_p > b · α̃ for all α̃ ∈ W − α_p}` is nonempty: some belief state `b` gives `p`
a strictly larger value than every tree of `W` whose value function differs from that of `p`.
Trees with the same value function are identified (footnote 6, p. 112), so ties with such trees are
not counted against `p`. -/
def Useful (M : POMDP S A Ω) {n : ℕ} (W : Finset (PolicyTree A Ω n)) (p : PolicyTree A Ω n) : Prop :=
  p ∈ W ∧ ∃ b ∈ stdSimplex ℝ S, ∀ q ∈ W, value M q ≠ value M p → valueAt M q b < valueAt M p b

open Classical in
/-- The set of useful trees of `W`: the parsimonious representation of the value function of `W`
(§4.2, p. 112), up to the identification of trees with equal value functions. -/
noncomputable def usefulSet (M : POMDP S A Ω) {n : ℕ} (W : Finset (PolicyTree A Ω n)) :
    Finset (PolicyTree A Ω n) :=
  W.filter (Useful M W)

/-- `V_{n+1}`: the set of useful (n + 1)-step policy trees, i.e. the useful trees of the set of **all**
(n + 1)-step policy trees (§4.3, p. 113: "V_{t−1}, the set of useful (t − 1)-step policy trees"). -/
noncomputable def usefulTrees [DecidableEq Ω] [Fintype A] (M : POMDP S A Ω) (n : ℕ) :
    Finset (PolicyTree A Ω n) :=
  usefulSet M Finset.univ

open Classical in
/-- The candidate set `C^a_t` for `t = n + 2`: the t-step policy trees with action `a` at the root
whose every subtree is a useful (t − 1)-step tree, i.e. lies in `V_{t−1}` (§4.3, p. 113: "We propose to
restrict our choice of subtrees to those (t − 1)-step policy trees that were useful"; §4.4.1, p. 115:
"the (t − 1)-step policy tree p_o ∈ V_{t−1}"). -/
noncomputable def candidates [DecidableEq Ω] [Fintype A] (M : POMDP S A Ω) (a : A) (n : ℕ) :
    Finset (PolicyTree A Ω (n + 1)) :=
  Finset.univ.filter (fun p : PolicyTree A Ω (n + 1) =>
    p.action = a ∧ ∀ o, p.subtree o ∈ usefulTrees M n)

/-- `Q^a_t` for `t = n + 2`: "the complete set of useful policy trees" for action `a` (Appendix A,
p. 130), i.e. the useful trees of the candidate set `C^a_t` — the parsimonious set of t-step trees
representing the Q-function of action `a` (§4.4, p. 114). -/
noncomputable def Qset [DecidableEq Ω] [Fintype A] (M : POMDP S A Ω) (a : A) (n : ℕ) :
    Finset (PolicyTree A Ω (n + 1)) :=
  usefulSet M (candidates M a n)

/-- The true Q-function `Q^a_t(b)` for `t = n + 2` (§4.4, p. 114): the value of taking action `a` in
belief state `b` and continuing optimally for `t − 1` steps,
`Q^a_t(b) = Σ_s b(s) R(s, a) + γ Σ_o Pr(o | a, b) V_{t−1}(b'_o)`, `b'_o = SE(b, a, o)`.
Here `V_{t−1} = optValue M n` is the maximum over all (t − 1)-step trees. A term with
`Pr(o | a, b) = 0` is multiplied by zero, so the junk value `SE(b, a, o) = 0` there does not matter. -/
noncomputable def Qfun [DecidableEq Ω] [Fintype A] [Nonempty A] (M : POMDP S A Ω) (a : A) (n : ℕ)
    (b : S → ℝ) : ℝ :=
  ∑ s, b s * M.R s a +
    M.γ * ∑ o, obsProb M b a o * optValue M n (stateEstimator M b a o)

end KaelblingPOMDP.Witness


