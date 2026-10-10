-- Prove2me | Definitions.Def_FSS23105365_DFARun
-- name    : FSS23105365_DFARun
-- status  : Definition
-- author  : @YY
-- created : 2026-10-09T15:53:46.51785+00:00
-- url     : https://prove2.me/theorems/b841db57-bb48-455a-9f46-7c637f0acf17
-- title:
--   DFA prefix states and block-boundary path observations
-- statement:
--   For all natural numbers $r,m$, every deterministic binary automaton $B$ with $r$ states, and every binary word $x$ of length $m$, the function $B.\mathrm{stateAfter}(x,t)$, defined for each natural number $t$, is the state obtained by starting at the specified initial state of $B$ and applying its transition function successively to the first $\min(t,m)$ bits of $x$ in index order. Thus at $t=0$ it returns the initial state; at $t\ge m$ it returns the state after the entire word, and for $m=0$ it returns the initial state for every $t$. The accepting set plays no role. An automaton with $r=0$ cannot be supplied because its structure requires an initial state.
--
--   For all natural numbers $q,r,n$, every deterministic binary automaton $B$ with $r$ states, every map $\varphi$ from its state set to the set of $q$ states, all natural numbers $v,s$, and every binary word $x$ of length $v+ns$, the function $B.\mathrm{sampledPath}(\varphi,v,s,x)$ is the sequence of $n+1$ states whose entry at each index $i=0,\ldots,n$ is $\varphi$ applied to the state of $B$ after it reads the first $v+si$ bits of $x$. The automaton starts at its specified initial state and reads prefixes from that same start for these evaluations. The final observation is at the full word length $v+ns$. This definition imposes no positivity conditions on $v$ or $s$: if $v=0$, the first observed state is the projection of the initial state, and if $s=0$, all entries are the projection of the same state reached after $v$ bits. If $n=0$, the sequence has just the observation after $v$ bits. The accepting set is unused. The initial-state field requires $r>0$, and existence of the supplied map from that inhabited state set requires $q>0$.
-- source:
--   Jiarui Zhang, Chengwei Liang, Haozhe Jiang, Binhang Yuan, Jingzhao Zhang. Revision Provably Reduces Sequential Computation in Diffusion Language Models. https://doi.org/10.5281/zenodo.23105365, Appendix E. Lemma E.3, Eq. (35), printed pp. 33–34.

import Definitions.Def_FSS23105365_FiniteState

set_option autoImplicit false
namespace FSS23105365

/-- The state after reading the first `t` bits of the supplied word. -/
def BinaryDFA.stateAfter {r m : ℕ} (B : BinaryDFA r) (x : Bits m) (t : ℕ) : Fin r :=
  ((List.ofFn x).take t).foldl B.step B.start

/-- States of a binary DFA observed after the initial `v` bits and then at
successive `s`-bit block boundaries. The last time is the full word length. -/
def BinaryDFA.sampledPath {q r n : ℕ} (B : BinaryDFA r)
    (φ : Fin r → Fin q) (v s : ℕ) (x : Bits (v + n * s)) : Path q n :=
  fun i => φ (B.stateAfter x (v + s * i.val))

end FSS23105365


