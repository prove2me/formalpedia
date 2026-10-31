-- Prove2me | Definitions.Def_WeightedCoordGames_Algorithm
-- name    : WeightedCoordGames_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:41.562465+00:00
-- url     : https://prove2.me/theorems/b15d08a3-ddf6-411d-93a0-f893386570a9
-- title:
--   Algorithm 1 for open chains — link bonuses $\beta^s_j$, grades, NBR, guard, prefix, the progress measure $\mu$ and one round of the algorithm
-- statement:
--   This file defines the objects of §5 (pp.16–19) used in the analysis of Algorithm 1 on an open chain $\mathcal C_1,\dots,\mathcal C_m$ with a colour assignment $C$. Best responses are taken in the coordination game on the open chain.
--
--   1. **Link bonus** (p.16). For a joint strategy $s$ and a cycle $\mathcal C_j$, $\beta^s_j(u,c)=1$ if $u$ is a link node and $c=s(x)$ for the predecessor $x$ of $u$ that lies in the adjacent cycle, and $0$ otherwise. The *game on $\mathcal C_j$* is the unweighted simple cycle on the $v$ nodes of $\mathcal C_j$ with bonus $\beta^s_j$ and the colour sets of the chain. A joint strategy $t$ of it lifts to the chain: nodes of $\mathcal C_j$ play $t$, the other nodes keep $s$.
--   2. **Grades** (p.16). The grade of $\mathcal C_j$ given $s$ is $\mathrm{U}{+}$ (respectively $+$) if all its nodes play a best response and $s([j,v])=s([j,1])$ (respectively $\neq$). It is $\mathrm{U}{-}$ (respectively $-$) if $[j,2]$ is the only node of $\mathcal C_j$ not playing a best response and $s([j,v])=s([j,1])$ (respectively $\neq$). It is $?$ otherwise.
--   3. **$\mathrm{NBR}(s)$** (p.16) is the least $j\in\{1,\dots,m\}$ such that some node of $\mathcal C_j$ does not play a best response.
--   4. **$\mathrm{guard}(s)$** (p.18) is the largest $j$ such that $\mathcal C_j$ has grade $\mathrm U{+}$ and $\mathcal C_1,\dots,\mathcal C_{j-1}$ have grades $+$ or $\mathrm U{+}$, and $0$ if there is none.
--   5. **$|\mathrm{prefix}(s)|$** (p.18) is the length of the longest prefix of $(\mathrm{grade}_s(\mathcal C_1),\dots,\mathrm{grade}_s(\mathcal C_m))$ that contains at most one of the grades $-$, $\mathrm U{-}$, $?$ and that stops after a cycle with grade $?$.
--   6. **Progress measure** (p.19). $\mu(s)=(m+1,0,0,0)$ if $s$ is a Nash equilibrium. Otherwise
--   $$
--   \mu(s)=\begin{cases}(\mathrm{guard}(s),1,0,-\mathrm{NBR}(s)) & \text{if }\mathrm{prefix}(s)\text{ contains }\mathrm U{-}\text{ or contains }\mathrm U{+}\text{ somewhere after }-,\\ (\mathrm{guard}(s),0,|\mathrm{prefix}(s)|,-\mathrm{NBR}(s)) & \text{otherwise,}\end{cases}
--   $$
--   ordered lexicographically ($<_{\mathrm{lex}}$).
--   7. **One round of Algorithm 1** (lines 3–8, p.17). $s\Rightarrow s'$ holds when $s$ is a joint strategy that is not a Nash equilibrium, $j=\mathrm{NBR}(s)$, and $s'$ is the lift of the last element of a run, in the game on $\mathcal C_j$ started at the restriction of $s$ to $\mathcal C_j$, of the construction in the proof of Theorem 3 (for $j=1$: clockwise from $[1,2]$, any best responses) or Theorem 7 (for $j>1$: clockwise from $[j,1]$, a best response equal to the predecessor's colour whenever that colour is a best response). The run stops once every node of $\mathcal C_j$ plays a best response in the game on $\mathcal C_j$. A scheduled node that already plays a best response is skipped.
--
--   **Formalization Note** $\mathrm{NBR}$, $\mathrm{guard}$ and $|\mathrm{prefix}|$ take the paper's 1-based values, while cycles in Lean are 0-based (`i : Fin m` is $\mathcal C_{i+1}$). $\mathrm{NBR}$ is set to $0$ when every node plays a best response (the paper leaves it undefined there). The predecessor $x$ "in $\mathcal C_{j-1}$ or $\mathcal C_{j+1}$" in $\beta^s_j$ is read as a predecessor not on $\mathcal C_j$; in an open chain this is the predecessor in the adjacent cycle. The round of Algorithm 1 is a relation: every choice of best responses that the constructions of Theorems 3 and 7 leave open is allowed.
-- source:
--   Apt–Simon–Wojtczak, Coordination Games on Weighted Directed Graphs, arXiv:1910.02693v2 (preprint), §5 p.16 (β^s_j display, grade display, NBR), p.17 (Algorithm 1), p.18 (guard, prefix), p.19 (µ display); proofs of Theorems 3 (p.11) and 7 (p.13) for the schedules; §2 p.8 (path(s, seq))

import Mathlib
import Definitions.Def_WeightedCoordGames_Model

namespace WeightedCoordGames

/-- The five grades of a cycle (Apt–Simon–Wojtczak, arXiv:1910.02693v2, §5, p.16):
`U+`, `+`, `U–`, `–`, `?`. -/
inductive Grade
  | Uplus
  | plus
  | Uminus
  | minus
  | ques
  deriving DecidableEq, Repr

/-- The good grades `U+` and `+` (every node of the cycle plays a best response). -/
def Grade.good : Grade → Bool
  | .Uplus => true
  | .plus => true
  | _ => false

/-- The progress-measure type `ℕ × ℕ × ℕ × ℤ` with the lexicographic order `<lex` (§5, p.19). -/
abbrev Measure4 : Type := Lex (ℕ × Lex (ℕ × Lex (ℕ × ℤ)))

/-- Update rule for Theorem 3's construction (p.11): any best response. -/
def anyBR {ι M : Type*} : (ι → M) → ι → M → Prop := fun _ _ _ => True

/-- Update rule for Theorem 7's construction (p.13, Phase 1): a best response is either the
colour of the predecessor or a colour with maximal bonus, and "in case of equal payoffs of these
two options we give a preference to the former": if the predecessor's colour `t (pred p)` is a best
response of `p`, then `p` switches to it. -/
def preferPred {ι M : Type*} [DecidableEq ι] (Γ : StrategicGame ι M) (pred : ι → ι) :
    (ι → M) → ι → M → Prop :=
  fun t p c => Γ.IsBRValue p t (t (pred p)) → c = t (pred p)

namespace OpenChain

variable {V M : Type*} [Fintype V] [DecidableEq V] [DecidableEq M] {m v : ℕ}
  (O : OpenChain V m v) (C : V → Finset M)

/-- Position `1` of a cycle (the paper's `[j,1]`, the up-link node of `C_j` for `j < m`). -/
def pos1 : Fin v := ⟨0, by have := O.three_le_v; omega⟩

/-- Position `2` of a cycle (the paper's `[j,2]`). -/
def pos2 : Fin v := ⟨1, by have := O.three_le_v; omega⟩

/-- Position `v` of a cycle (the paper's `[j,v]`, the predecessor of `[j,1]` in `C_j`). -/
def posLast : Fin v := ⟨v - 1, by have := O.three_le_v; omega⟩

/-- `u` is a node of the cycle `C_j`. -/
def OnCycle (j : Fin m) (u : V) : Prop := ∃ i, O.node j i = u

open scoped Classical in
/-- The bonus function `β^s_j` of the cycle `C_j` given the joint strategy `s` (§5, p.16):
`β^s_j([j,i], c) = 1` if `[j,i]` is a link node and `c = s(x)` where `x → [j,i]` is an edge from
the adjacent cycle (a node `x` not on `C_j`), and `0` otherwise.

**Formalization Note.** "`x` belongs to `C_{j−1}` or to `C_{j+1}` and `x → u` is an edge" is read
as "`x` is not a node of `C_j`": in an open chain the in-neighbours of a node of `C_j` are its
predecessor in `C_j` and, for a link node, its predecessor in the adjacent cycle, which is never
on `C_j`. -/
noncomputable def linkBonus (s : V → M) (j : Fin m) (i : Fin v) (c : M) : ℕ :=
  if ∃ x, ¬ O.OnCycle j x ∧ O.Adj x (O.node j i) ∧ c = s x then 1 else 0

/-- The coordination game on the cycle `C_j` with the bonus function `β^s_j` (§5, p.16): the
unweighted simple cycle on the `v` positions of `C_j` (position `i` is `[j, i+1]`), with the colour
sets of the chain. -/
noncomputable def cycleGameAt (s : V → M) (j : Fin m) : CoordGame (Fin v) M :=
  cycleGame v (fun _ _ => 1) (O.linkBonus s j) (fun i => C (O.node j i))

/-- The restriction `ŝ` of `s` to the nodes of `C_j` (Algorithm 1, line 5, p.17). -/
def restrict (s : V → M) (j : Fin m) : Fin v → M := fun i => s (O.node j i)

open scoped Classical in
/-- The lift to the open chain of a joint strategy `t` of the game on `C_j` (§5, p.16, the path
`χ̄` corresponding to `χ`): nodes of `C_j` play `t`, all other nodes keep their strategy in `s`. -/
noncomputable def lift (s : V → M) (j : Fin m) (t : Fin v → M) : V → M :=
  fun u => if h : O.OnCycle j u then t (Classical.choose h) else s u

open scoped Classical in
/-- The grade `grade_s(C_j)` of the cycle `C_j` given `s` (§5, p.16), best responses being taken
in the coordination game on the open chain:
* `U+` if all nodes of `C_j` play a best response and `s([j,v]) = s([j,1])`;
* `+` if all nodes of `C_j` play a best response and `s([j,v]) ≠ s([j,1])`;
* `U–` if `[j,2]` is the only node of `C_j` not playing a best response and `s([j,v]) = s([j,1])`;
* `–` if `[j,2]` is the only node of `C_j` not playing a best response and `s([j,v]) ≠ s([j,1])`;
* `?` otherwise. -/
noncomputable def grade (s : V → M) (j : Fin m) : Grade :=
  if ∀ i, (chainGame O C).toGame.PlaysBR (O.node j i) s then
    (if s (O.node j O.posLast) = s (O.node j O.pos1) then .Uplus else .plus)
  else if ¬ (chainGame O C).toGame.PlaysBR (O.node j O.pos2) s ∧
      ∀ i, i ≠ O.pos2 → (chainGame O C).toGame.PlaysBR (O.node j i) s then
    (if s (O.node j O.posLast) = s (O.node j O.pos1) then .Uminus else .minus)
  else .ques

open scoped Classical in
/-- `NBR(s)` (§5, p.16): the least `j ∈ {1, …, m}` such that some node of `C_j` does not play a
best response in `s`.

**Formalization Note.** The value is the paper's 1-based index (`= 1 +` the 0-based index of the
cycle). It is only meaningful when `s` is not a Nash equilibrium; when every node plays a best
response it is `0`. -/
noncomputable def nbr (s : V → M) : ℕ :=
  let bad := Finset.univ.filter
    (fun j : Fin m => ∃ i, ¬ (chainGame O C).toGame.PlaysBR (O.node j i) s)
  if h : bad.Nonempty then (bad.min' h).val + 1 else 0

open scoped Classical in
/-- `guard(s)` (§5, p.18): the largest `j ∈ {1, …, m}` such that the grade of `C_j` is `U+` and
the grade of each of `C_1, …, C_{j−1}` is `+` or `U+`; `0` if there is no such `j`. -/
noncomputable def guard (s : V → M) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => O.grade C s j = .Uplus ∧
      ∀ i : Fin m, i < j → (O.grade C s i).good = true)).sup (fun j => j.val + 1)

open scoped Classical in
/-- `|prefix(s)|` (§5, p.18): the length of the longest prefix of
`grade(s) = (grade_s(C_1), …, grade_s(C_m))` that contains at most one of the grades `–`, `U–`,
`?`, and that stops after a cycle with grade `?` (a `?` can only be its last entry). -/
noncomputable def prefixLen (s : V → M) : ℕ :=
  ((Finset.range (m + 1)).filter (fun p =>
      (Finset.univ.filter (fun j : Fin m => j.val < p ∧ (O.grade C s j).good = false)).card ≤ 1 ∧
        ∀ j : Fin m, j.val + 1 < p → O.grade C s j ≠ .ques)).sup id

/-- The condition of the first case of `µ` (§5, p.19): `prefix(s)` contains `U–`, or it contains
`U+` somewhere after `–`. -/
def prefixFlag (s : V → M) : Prop :=
  (∃ j : Fin m, j.val < O.prefixLen C s ∧ O.grade C s j = .Uminus) ∨
    (∃ j j' : Fin m, j < j' ∧ j'.val < O.prefixLen C s ∧
      O.grade C s j = .minus ∧ O.grade C s j' = .Uplus)

open scoped Classical in
/-- The progress measure `µ(s)` (§5, p.19), ordered by `<lex`:
* `µ(s) = (m + 1, 0, 0, 0)` if `s` is a Nash equilibrium;
* `µ(s) = (guard(s), 1, 0, −NBR(s))` if `prefix(s)` contains `U–` or contains `U+` somewhere
  after `–`;
* `µ(s) = (guard(s), 0, |prefix(s)|, −NBR(s))` otherwise. -/
noncomputable def mu (s : V → M) : Measure4 :=
  if (chainGame O C).toGame.IsNash s then toLex (m + 1, toLex (0, toLex (0, 0)))
  else if O.prefixFlag C s then
    toLex (O.guard C s, toLex (1, toLex (0, -(O.nbr C s : ℤ))))
  else toLex (O.guard C s, toLex (0, toLex (O.prefixLen C s, -(O.nbr C s : ℤ))))

/-- The round-robin (clockwise) schedule on the positions of a cycle starting at position
`start`: the `k`-th scheduled position is `start + k (mod v)` (proofs of Theorems 3 and 7,
pp.11, 13). -/
def roundRobin (start : Fin v) (k : ℕ) : Fin v := ⟨(start.val + k) % v, Nat.mod_lt _ start.pos⟩

/-- One round of Algorithm 1 (lines 3–8, p.17): `AlgStep s s'` holds when `s` is a joint strategy
that is not a Nash equilibrium, `C_j` is the cycle with `j = NBR(s)` (some node of `C_j` does not
play a best response, every node of `C_1, …, C_{j−1}` does), and `s'` is the last element of the
lift `χ̄` of a run `χ`, in the coordination game on `C_j` with bonus `β^s_j` started at `ŝ`, of the
construction of
* Theorem 3 (p.11) when `j = 1`: the round-robin schedule starting at `[1,2]` (the bonus node
  `[1,1]` playing the role of node `n`), each update to an arbitrary best response;
* Theorem 7 (p.13) when `1 < j ≤ m`: the round-robin schedule starting at `[j,1]` (in the role of
  node `1`), each update to a best response, preferring the predecessor's colour on ties;

where the run ends when every node of `C_j` plays a best response in the game on `C_j`.

**Formalization Note.** The schedule semantics is §2's `path(s, seq)` (p.8): a scheduled player
that already plays a best response is skipped. All choices of best responses the constructions
leave open are allowed, so `AlgStep` is a relation. -/
def AlgStep (s s' : V → M) : Prop :=
  (chainGame O C).toGame.IsJoint s ∧ ¬ (chainGame O C).toGame.IsNash s ∧
    ∃ j : Fin m,
      (∃ i, ¬ (chainGame O C).toGame.PlaysBR (O.node j i) s) ∧
      (∀ j' : Fin m, j' < j → ∀ i, (chainGame O C).toGame.PlaysBR (O.node j' i) s) ∧
      ∃ (K : ℕ) (t : ℕ → Fin v → M),
        t 0 = O.restrict s j ∧
        (O.cycleGameAt C s j).toGame.ScheduleRun
          (if j.val = 0 then anyBR
            else preferPred (O.cycleGameAt C s j).toGame (finRotate v).symm)
          (roundRobin (if j.val = 0 then O.pos2 else O.pos1)) K t ∧
        (O.cycleGameAt C s j).toGame.IsNash (t K) ∧
        s' = O.lift s j (t K)

end OpenChain

end WeightedCoordGames


