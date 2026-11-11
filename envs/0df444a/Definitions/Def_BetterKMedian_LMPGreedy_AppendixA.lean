-- Prove2me | Definitions.Def_BetterKMedian_LMPGreedy_AppendixA
-- name    : BetterKMedian_LMPGreedy_AppendixA
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:21:02.816257+00:00
-- url     : https://prove2.me/theorems/10ef0ca0-ec51-4691-adb9-627f33244b1c
-- title:
--   Appendix A — $\alpha^\star_j$, the client order, $S(k)$, $r_{j,k}$, and the re-indexing on $D'$
-- statement:
--   For an execution: `removalIndex j` is the (1-based) number of the event in which client $j$ becomes inactive; $\alpha^\star_j$ (`alphaStar`) is its final $\alpha_j$; $S(k)$ (`openBefore`) is the set of open facilities just before the event in which $k$ becomes inactive.
--
--   `IsAppendixAOrder steps ord`: `ord` lists every client exactly once, in non-decreasing order of $\alpha^\star$, and clients with equal $\alpha^\star$ in non-decreasing order of the event in which they become inactive (clients of the same event in either order). Client index $j\in\{1,\dots,n\}$, $n=|D|$, is position $j$ of `ord`.
--
--   `rA j k` $=r_{j,k}$ for $1\le j\le k\le n$: $\alpha^\star_j$ if $j$ and $k$ become inactive in the same event, and $d(j,S(k))$ otherwise; $r_{j,n+1}=d(j,S^\star)$. `charge j` $=\sum_{i=j}^n\beta(r_{j,i},r_{j,i+1})+r_{j,n+1}$.
--
--   For $D'\subseteq D$: `positionsOf ord D'` are the indices of the clients of $D'$; `reindex` maps $1,\dots,|D'|$ to these indices in increasing order and $|D'|+1$ to $n+1$; `subR a b` $=r_{\sigma(a),\sigma(b)}$ and `subD istar a` $=d(i^\star,k)$ for the client $k$ of re-indexed index $a$ (the variables of Claim A.4).
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Appendix A, printed pp. 30–32 (PDF 32–34)

import Mathlib
import Definitions.Def_BetterKMedian_LMPGreedy_Algorithm1

set_option autoImplicit false

/-!
# The quantities of an execution used in Appendix A: `α⋆_j`, the client order, `S(k)`, `r_{j,k}`

Buhai et al., *A Better-than-2 Approximation for k-Median* (2026), STOC 2027 submission,
SHA-256 5c2605b2…f461, Appendix A, printed p. 30 (PDF 32); re-indexing on a client subset `D′`
in the proof of Lemma A.3, printed pp. 31–32 (PDF 33–34).

Conventions.
* An execution is a list of events (`Def_BetterKMedian_LMPGreedy_Algorithm1`). A client `j`
  "becomes inactive in event number `m`" (1-based) when it is active after `m − 1` events and
  not after `m`; `removalIndex` is that `m` (the least number of processed events after which
  `j` is inactive). Two clients become inactive in the same event iff their `removalIndex`
  agree.
* The order of Appendix A is a list `ord` of all clients, without repetition, in increasing
  order of `α⋆`, ties broken by the order of the events in which the clients become inactive.
  Clients that become inactive in the same event may appear in either order: every such list
  is allowed. Client positions are the paper's indices `1, …, n` with `n = |D|`, so the client
  with index `j` is `ord[j − 1]`.
* `r j k` uses the paper's 1-based indices `1 ≤ j ≤ k ≤ n + 1`; its value elsewhere is `0` and
  never used.
-/

namespace BetterKMedian.LMPGreedy

open Finset

namespace Instance

variable (I : Instance)

/-- The number of the event (1-based) in which client `j` becomes inactive: the least `m` such
that `j` is inactive after the first `m` events. -/
noncomputable def removalIndex (steps : List (Step I.N)) (j : Fin I.N) : ℕ :=
  sInf {m : ℕ | j ∉ (I.stateAfter steps m).active}

/-- `α⋆_j`: the final value `α_j` of client `j` (frozen when `j` became inactive). -/
noncomputable def alphaStar (steps : List (Step I.N)) (j : Fin I.N) : ℝ :=
  (I.finalState steps).alpha j

/-- `S(k)`: the set of open facilities just before the event in which client `k` becomes
inactive. -/
noncomputable def openBefore (steps : List (Step I.N)) (k : Fin I.N) : Finset (Fin I.N) :=
  (I.stateAfter steps (I.removalIndex steps k - 1)).opened

/-- `ord` is an order of the clients as in Appendix A (p. 30): it lists every client of `D`
exactly once, in increasing order of `α⋆`, and clients with equal `α⋆` in the order of the
events in which they become inactive. -/
def IsAppendixAOrder (steps : List (Step I.N)) (ord : List (Fin I.N)) : Prop :=
  ord.Nodup ∧ (∀ x : Fin I.N, x ∈ ord ↔ x ∈ I.clients) ∧
  ∀ (p q : ℕ) (hp : p < ord.length) (hq : q < ord.length), p < q →
    I.alphaStar steps ord[p] ≤ I.alphaStar steps ord[q] ∧
    (I.alphaStar steps ord[p] = I.alphaStar steps ord[q] →
      I.removalIndex steps ord[p] ≤ I.removalIndex steps ord[q])

/-- `r_{j,k}` of Appendix A (p. 30), for client indices `1 ≤ j ≤ k ≤ n` in the order `ord`:
`α⋆_j` if `j` and `k` become inactive in the same event, and `d(j, S(k))` otherwise; and
`r_{j,n+1} = d(j, S⋆)` with `S⋆` the output. -/
noncomputable def rA (steps : List (Step I.N)) (ord : List (Fin I.N)) (j k : ℕ) : ℝ :=
  match ord[j - 1]? with
  | none => 0
  | some a =>
    if k = ord.length + 1 then I.distToSet (I.output steps) a
    else
      match ord[k - 1]? with
      | none => 0
      | some b =>
        if I.removalIndex steps a = I.removalIndex steps b then I.alphaStar steps a
        else I.distToSet (I.openBefore steps b) a

/-- The bound of Lemma A.2 on the cost charged to the client of index `j`:
`Σ_{i=j}^n β(r_{j,i}, r_{j,i+1}) + r_{j,n+1}`. -/
noncomputable def charge (β : ℝ → ℝ → ℝ) (steps : List (Step I.N)) (ord : List (Fin I.N))
    (j : ℕ) : ℝ :=
  (∑ i ∈ Icc j ord.length, β (I.rA steps ord j i) (I.rA steps ord j (i + 1))) +
    I.rA steps ord j (ord.length + 1)

/-- The indices (positions `1, …, n` in `ord`) of the clients of `D′`. -/
noncomputable def positionsOf (ord : List (Fin I.N)) (D' : Finset (Fin I.N)) : Finset ℕ := by
  classical
  exact (Icc 1 ord.length).filter (fun p => ∃ x ∈ D', ord[p - 1]? = some x)

/-- The re-indexing of the proof of Lemma A.3 (p. 31): the clients of `D′` become
`1, …, |D′|` in their original order, and `|D′| + 1` becomes the original `n + 1`. -/
noncomputable def reindex (ord : List (Fin I.N)) (D' : Finset (Fin I.N)) (a : ℕ) : ℕ :=
  let P := (I.positionsOf ord D').sort (· ≤ ·)
  if 1 ≤ a ∧ a ≤ P.length then P.getD (a - 1) 0 else ord.length + 1

/-- The re-indexed variables `r` of Claim A.4: `r'_{a,b} = r_{σ(a), σ(b)}` with `σ = reindex`. -/
noncomputable def subR (steps : List (Step I.N)) (ord : List (Fin I.N)) (D' : Finset (Fin I.N))
    (a b : ℕ) : ℝ :=
  I.rA steps ord (I.reindex ord D' a) (I.reindex ord D' b)

/-- The re-indexed variables `d` of Claim A.4: `d'_a = d(i⋆, k)` for the client `k` of
re-indexed index `a`. -/
noncomputable def subD (ord : List (Fin I.N)) (D' : Finset (Fin I.N)) (istar : Fin I.N)
    (a : ℕ) : ℝ :=
  match ord[I.reindex ord D' a - 1]? with
  | none => 0
  | some k => I.d istar k

end Instance

end BetterKMedian.LMPGreedy


