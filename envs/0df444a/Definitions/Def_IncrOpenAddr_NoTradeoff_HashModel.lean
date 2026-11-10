-- Prove2me | Definitions.Def_IncrOpenAddr_NoTradeoff_HashModel
-- name    : IncrOpenAddr_NoTradeoff_HashModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:35:35.623252+00:00
-- url     : https://prove2.me/theorems/607961c2-da63-42ab-a84a-eac876dc5228
-- title:
--   The idealized hashes of the construction: uniform independent leaves and uniform real priorities
-- statement:
--   For a finite set $K$ of keys and a table size $n$, an **outcome** $\omega$ assigns to every key $x\in K$ and every tree $T_i$ ($1\le i\le\alpha$) a **home leaf** $L_i(x)\in\{0,\dots,2^{h_i-1}-1\}$ of $T_i$ and a **priority** $g_i(x)\in[0,1]$. Under the law `hashLaw K n` all of these are independent, each $L_i(x)$ is uniform on the leaves of $T_i$, and each $g_i(x)$ is uniform on $[0,1]$ (Lebesgue measure).
--
--   For a priority $g$, $J(g)$ is the largest integer $j$ with $g<1/j^4$, that is,
--   $$J(g)=\max\{j\ge 0 : j^4 g<1\},$$
--   which is $0$ when $g=1$ and $+\infty$ when $g=0$.
--
--   **Formalization Note.** Leaves are `Fin (numLeaves n i)`, priorities are `unitInterval`; the product law is `Measure.pi`. Outside $1\le i\le\alpha$ the accessors return the dummy values $0$ and $1$.
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 7 (PDF 8), §2.1 'Hashing'; p. 19 (PDF 20), Table 1 (J_i)

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout

set_option autoImplicit false

/-!
# The idealized hashes of the construction: uniform leaves and uniform real priorities

Farach-Colton, Krapivin, Kuszmaul, arXiv:2611.04186 (manuscript sha256 9486c2b8…), §2.1,
"Hashing" (p. 7, PDF 8): "Each element x selects … leaf L_i(x) in tree T_i via a set of uniformly
and independently random hash functions L_i. … each x is given a uniformly random priority
g_i(x) ∈ [0, 1] for each tree T_i."

Keys range over a finite type `K` (any finite set of keys containing those of the instance).  An
outcome assigns to every key `x` and every tree `i = 1, …, α` a leaf of `T_i` and a priority in
`[0, 1]`; the law makes all of these independent, leaves uniform and priorities uniform on
`[0, 1]`.
-/

namespace IncrOpenAddr.NoTradeoff

open MeasureTheory

/-- Every tree has at least one leaf. -/
instance (n i : ℕ) : NeZero (numLeaves n i) := ⟨by unfold numLeaves; positivity⟩

/-- The hashes of one key: for each tree `t` (paper index `t + 1`), a leaf and a priority. -/
abbrev KeyHash (n : ℕ) := (t : Fin (numTrees n)) → Fin (numLeaves n (t.val + 1)) × unitInterval

/-- An outcome of all hashes. -/
abbrev Outcome (K : Type) (n : ℕ) := K → KeyHash n

/-- The law of the hashes of one key: independent uniform leaves and uniform priorities. -/
noncomputable def keyLaw (n : ℕ) : Measure (KeyHash n) :=
  Measure.pi fun t => (PMF.uniformOfFintype (Fin (numLeaves n (t.val + 1)))).toMeasure.prod volume

/-- The law of all hashes: the keys' hashes are independent. -/
noncomputable def hashLaw (K : Type) [Fintype K] (n : ℕ) : Measure (Outcome K n) :=
  Measure.pi fun _ => keyLaw n

/-- `L_i(x)`: the home leaf of key `x` in tree `i` (`1 ≤ i ≤ α`; `0` otherwise). -/
def leafOf {K : Type} {n : ℕ} (ω : Outcome K n) (x : K) (i : ℕ) : ℕ :=
  if h : 1 ≤ i ∧ i ≤ numTrees n then (ω x ⟨i - 1, by omega⟩).1.val else 0

/-- `g_i(x)`: the priority of key `x` in tree `i` (`1 ≤ i ≤ α`; `1` otherwise). -/
def prio {K : Type} {n : ℕ} (ω : Outcome K n) (x : K) (i : ℕ) : ℝ :=
  if h : 1 ≤ i ∧ i ≤ numTrees n then ((ω x ⟨i - 1, by omega⟩).2 : ℝ) else 1

/-- `J(g)`: the largest `j` with `g < 1/j⁴` (`0` if there is none, `⊤` if `g ≤ 0`). -/
noncomputable def Jof (g : ℝ) : ℕ∞ := by
  classical
  exact if h : ∃ j : ℕ, 1 ≤ (j : ℝ) ^ 4 * g then ((Nat.find h - 1 : ℕ) : ℕ∞) else ⊤

end IncrOpenAddr.NoTradeoff


