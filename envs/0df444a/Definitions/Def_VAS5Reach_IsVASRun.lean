-- Prove2me | Definitions.Def_VAS5Reach_IsVASRun
-- name    : VAS5Reach_IsVASRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:42.229209+00:00
-- url     : https://prove2.me/theorems/f5a3dc39-541d-408a-8743-601f9fd1750a
-- title:
--   Run $s \xrightarrow{w} t$ of a vector addition system
-- statement:
--   A $d$-dimensional **vector addition system** ($d$-VAS) is a finite set $T \subseteq \mathbb Z^d$ of transition vectors; a configuration is a vector of $\mathbb N^d$. A word $w = a_1 \cdots a_k$ is a **run** from $s$ to $t$ if every letter $a_j$ belongs to $T$, every intermediate configuration is nonnegative,
--   $$
--   s + a_1 + \dots + a_j \in \mathbb N^d \qquad (0 \le j \le k),
--   $$
--   and $s + a_1 + \dots + a_k = t$. Its length is $k$. The target $t$ is **reachable** from $s$, written $s \xrightarrow{*} t$ (`VASReach`), if some run leads from $s$ to $t$.
--
--   This is the semantics of the goal theorem: a 5-VAS is a finite subset of $\mathbb Z^5$, and the paper identifies a VAS with its transition set and omits its unique state.
--
--   **Formalization Note** Intermediate configurations are checked as integer vectors ($s$ cast to $\mathbb Z$ plus a prefix sum).
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3, pp.13–14 (PDF pp.15–16), definitions of N-run, d-VAS

import Mathlib

namespace VAS5Reach

/-- A run of a vector addition system. A `d`-VAS is a finite set `T ⊆ ℤ^d` of transition vectors;
a configuration is a vector of `ℕ^d`. The word `w = a₁ ⋯ a_k` is a run from `s` to `t`
(written `s −w→ t`) if every letter `aⱼ` is a transition of `T`, every intermediate configuration
`s + a₁ + ⋯ + aⱼ` (`0 ≤ j ≤ k`) is nonnegative, and `s + a₁ + ⋯ + a_k = t`. The length of the run
is `k = w.length`.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3, printed pp. 13–14
(PDF pp. 15–16): "A path induces an N-run (or simply a run) when all intermediate counter values
remain nonnegative", and "A d-dimensional vector addition system (d-VAS) is a d-VASS with a single
state. In this case, transitions are determined by their effects, so we identify T with a finite
subset of Z^d and omit the unique state from configurations and runs."

**Formalization Note** The unique state is omitted, as in the paper. Intermediate configurations
are checked as integer vectors (`s` cast to `ℤ` plus the prefix sum of the first `j` letters);
`j = 0` and `j = k` are the endpoints, which are nonnegative by type. -/
def IsVASRun {ι : Type} (T : Finset (ι → ℤ)) (s : ι → ℕ) (w : List (ι → ℤ)) (t : ι → ℕ) : Prop :=
  (∀ a ∈ w, a ∈ T) ∧
  (∀ j ≤ w.length, ∀ i, 0 ≤ (s i : ℤ) + (w.take j).sum i) ∧
  (∀ i, (t i : ℤ) = (s i : ℤ) + w.sum i)

/-- Reachability `s −∗→ t` in a VAS: some run leads from `s` to `t`. -/
def VASReach {ι : Type} (T : Finset (ι → ℤ)) (s t : ι → ℕ) : Prop :=
  ∃ w, IsVASRun T s w t

end VAS5Reach


