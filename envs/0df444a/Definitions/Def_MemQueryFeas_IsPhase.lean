-- Prove2me | Definitions.Def_MemQueryFeas_IsPhase
-- name    : MemQueryFeas_IsPhase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:43.663666+00:00
-- url     : https://prove2.me/theorems/7b274524-249f-47fb-8222-21fb2c2ac015
-- title:
--   Layer-$p$ phases $V_p$
-- statement:
--   The skeleton tree has vertex set $V=\bigsqcup_{p=0}^P V_p$ with $V_p=[N_1]\times\dots\times[N_p]$, the **layer-$p$ phases**. A phase $v=(i_1,\dots,i_p)$ has children $(i_1,\dots,i_p,i_{p+1})$, $i_{p+1}\in[N_{p+1}]$; the root is the empty tuple.
--
--   **Formalization Note** Phases are lists of natural numbers; the parent of $v$ is $v$ without its last entry.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §3.1, p.8 (PDF p.9)

import Mathlib

namespace MemQueryFeas

/-- **Layer-`p` phases `V_p`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.1, p.8 (PDF p.9): "the full `(N_1, …, N_P)`-ary tree with
vertices `V := ⊔_{p=0}^P V_p` where `V_p := [N_1] × ⋯ × [N_p]` corresponds to the set of layer-`p`
phases."

`IsPhase N p v`: `v = (i_1, …, i_p)` has length `p` and `1 ≤ i_s ≤ N_s` for every `s`.

**Formalization Note.** Phases are lists; the entry at list position `s` (0-based) is `i_{s+1}`. The
root `∅ ∈ V_0` is the empty list; the parent of `v` is `v.dropLast` and its children are
`v ++ [i]`. -/
def IsPhase (N : ℕ → ℕ) (p : ℕ) (v : List ℕ) : Prop :=
  v.length = p ∧ ∀ (s : ℕ) (h : s < v.length), 1 ≤ v[s] ∧ v[s] ≤ N (s + 1)

end MemQueryFeas


