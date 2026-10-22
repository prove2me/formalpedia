-- Prove2me | Definitions.Def_QCircMITM_Search_Algorithm
-- name    : QCircMITM_Search_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:38:25.691645+00:00
-- url     : https://prove2.me/theorems/0a066ee7-12d7-4e6f-84a4-14e7a82b7674
-- title:
--   §2–§3, pp. 4–7 — layer products S_i, circuits of i layers, MITM-factor and its counted cost
-- statement:
--   This file fixes the objects of the meet-in-the-middle search of Amy, Maslov, Mosca and Roetteler.
--
--   **Unitaries.** $U(2^n)$ is the group of $2^n\times 2^n$ complex matrices $U$ with $UU^\dagger = U^\dagger U = I$, indexed by bit strings of length $n$. In this group the inverse of $U$ is its adjoint $U^\dagger$.
--
--   **Layers and circuits.** Fix a finite set $V \subseteq U(2^n)$. It stands for the set $\mathcal V_{n,\mathcal G}$ of unitaries of depth-one circuits over an instruction set $\mathcal G$. A *circuit of $i$ layers* over $V$ is a list $[U_1,\dots,U_i]$ with every $U_j \in V$. It implements the product $U_1U_2\cdots U_i$ (the empty circuit implements $I$).
--
--   **The sets $S_i$.** $S_i$ is the set of unitaries implementable in depth $i$:
--   $$S_0 = \{I\}, \qquad S_i = V S_{i-1} = \{\,W X : W \in V,\ X \in S_{i-1}\,\}.$$
--
--   **Iteration $i$ of MITM-factor.** First test whether $S_{i-1}^\dagger U \cap S_i \neq \emptyset$, i.e. whether some circuit $a$ of $i-1$ layers and some circuit $b$ of $i$ layers satisfy $(\prod a)^\dagger U = \prod b$. If so, return the circuit $a$ followed by $b$. Otherwise test $S_i^\dagger U \cap S_i \neq \emptyset$ in the same way, with $a$ now of $i$ layers. If both tests fail, the iteration returns nothing.
--
--   **MITM-factor$(\mathcal G, U, l)$.** Run the iterations $i = 1, 2, \dots, \lceil l/2\rceil$ in order and return the circuit of the first iteration that succeeds; return nothing if none succeeds.
--
--   **Stopping iteration and counted cost.** The run stops at the first successful iteration, or at $\lceil l/2\rceil$ if none succeeds. Its counted cost is
--   $$\mathrm{cost}(U,l) = \sum_{i=1}^{\text{stop}} \Big( |V|\,|S_{i-1}| + |S_i|\log_2|S_i| + \big(|S_{i-1}|+|S_i|\big)\log_2|S_i| \Big),$$
--   one term for generating $S_i = VS_{i-1}$, one for sorting $S_i$, and one for looking up every element of $S_{i-1}^\dagger U$ and of $S_i^\dagger U$ in the sorted $S_i$. This is the operation count of the running-time paragraph on pp. 6–7.
--
--   These definitions carry the mission's goal (the paper's main result) and every milestone.
--
--   **Formalization Note.** Unitaries are elements of `Matrix.unitaryGroup (Fin n → Bool) ℂ`; `U⁻¹` is $U^\dagger$. The layer set $V$ is an arbitrary `Finset` of $n$-qubit unitaries: the paper's argument uses nothing about $\mathcal V_{n,\mathcal G}$ beyond its being a finite set of unitaries, and $\mathcal V_{n,\mathcal G}$ itself is defined in `QCircMITM.Search.Layers`. $\lceil l/2\rceil$ is `(l + 1) / 2`. The "any circuit" of the pseudocode is a choice of witnesses (`Classical.choose`), and the definitions are noncomputable. Logarithms are `Real.logb 2`, with $\log_2 0 = 0$.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, pp. 4–7, §2 (circuits, depth, V_{n,G}) and §3 (Lemma 1, MITM-factor pseudocode p. 6, running-time paragraph pp. 6–7)

import Mathlib

namespace QCircMITM.Search
open scoped Classical

/-- The `n`-qubit unitary group `U(2^n)` (Amy–Maslov–Mosca–Roetteler, §2, p. 3): matrices indexed
by `Fin n → Bool` with `U U† = U† U = I`. In this group `U⁻¹` is the adjoint `U†` and `1` is `I`. -/
abbrev Unitary (n : ℕ) := Matrix.unitaryGroup (Fin n → Bool) ℂ

/-- Circuits of exactly `i` layers over the layer set `V` (§2, p. 4): the lists `[U₁, …, U_i]`
with every `U_j ∈ V`. The list `[U₁, …, U_i]` implements `U₁ U₂ ⋯ U_i` (`List.prod`). -/
noncomputable def circuits {n : ℕ} (V : Finset (Unitary n)) : ℕ → Finset (List (Unitary n))
  | 0 => {[]}
  | i + 1 => (V ×ˢ circuits V i).image (fun p => p.1 :: p.2)

/-- `S_i`, the unitaries implementable in depth `i` over `V` (pseudocode, p. 6):
`S_0 = {I}` and `S_i = V S_{i−1} = {W X : W ∈ V, X ∈ S_{i−1}}`. -/
noncomputable def S {n : ℕ} (V : Finset (Unitary n)) : ℕ → Finset (Unitary n)
  | 0 => {1}
  | i + 1 => (V ×ˢ S V i).image (fun p => p.1 * p.2)

/-- Iteration `i` of MITM-factor (pseudocode, p. 6). First test `S†_{i−1}U ∩ S_i ≠ ∅`: if some
circuit `a` of `i − 1` layers and some circuit `b` of `i` layers satisfy `(∏ a)† U = ∏ b`, return
the circuit `a ++ b`. Otherwise test `S†_i U ∩ S_i ≠ ∅` in the same way with `a` of `i` layers.
Otherwise return `none`. -/
noncomputable def mitmStep {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (i : ℕ) :
    Option (List (Unitary n)) :=
  if h₁ : ∃ a ∈ circuits V (i - 1), ∃ b ∈ circuits V i, a.prod⁻¹ * U = b.prod then
    some (Classical.choose h₁ ++ Classical.choose (Classical.choose_spec h₁).2)
  else if h₂ : ∃ a ∈ circuits V i, ∃ b ∈ circuits V i, a.prod⁻¹ * U = b.prod then
    some (Classical.choose h₂ ++ Classical.choose (Classical.choose_spec h₂).2)
  else none

/-- MITM-factor(G, U, l) (pseudocode, p. 6): run the iterations `i = 1, …, ⌈l/2⌉` in order and
return the circuit of the first iteration that succeeds; `none` if none succeeds.
`⌈l/2⌉ = (l + 1) / 2` in `ℕ`. -/
noncomputable def mitmFactor {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (l : ℕ) :
    Option (List (Unitary n)) :=
  (List.range' 1 ((l + 1) / 2)).findSome? (mitmStep V U)

/-- The last iteration MITM-factor executes: the first `i ∈ {1, …, ⌈l/2⌉}` whose iteration
succeeds, or `⌈l/2⌉` if none does. -/
noncomputable def mitmStop {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (l : ℕ) : ℕ :=
  ((List.range' 1 ((l + 1) / 2)).find? (fun i => (mitmStep V U i).isSome)).getD ((l + 1) / 2)

/-- The counted cost of MITM-factor (§3, p. 6), summed over the iterations `i = 1, …, mitmStop`
the run executes. Iteration `i` costs `|V|·|S_{i−1}|` (generating `S_i = V S_{i−1}`),
`|S_i| log₂|S_i|` (sorting `S_i`), and `(|S_{i−1}| + |S_i|) log₂|S_i|` (searching each element of
`S†_{i−1}U` and of `S†_i U` in the sorted `S_i`). -/
noncomputable def mitmCost {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (l : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (mitmStop V U l),
    (((V.card : ℝ) * (S V (i - 1)).card)
      + ((S V i).card : ℝ) * Real.logb 2 ((S V i).card)
      + (((S V (i - 1)).card : ℝ) + (S V i).card) * Real.logb 2 ((S V i).card))

end QCircMITM.Search


