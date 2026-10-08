-- Prove2me | Definitions.Def_PersistClust_Count_Algorithm
-- name    : PersistClust_Count_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T08:37:41.820808+00:00
-- url     : https://prove2.me/theorems/33f93e5c-4951-4299-8ac0-80454d1cac2e
-- title:
--   §3, Procedures 1–2 — the persistence-based clustering algorithm and its number of output clusters
-- statement:
--   The clustering algorithm of §3. The input is a vector $g\in\mathbb R^n$ of function values, an $n\times n$ symmetric distance matrix $D$, and parameters $\delta,\tau\ge0$.
--
--   1. **Sort (line 1).** A permutation $\sigma$ sorts the indices so that $g_{\sigma(0)}\le g_{\sigma(1)}\le\dots\le g_{\sigma(n-1)}$; ties are broken arbitrarily. Vertices are processed in the order $\sigma(n-1),\dots,\sigma(0)$, by decreasing value.
--   2. **Union-find state.** Each processed vertex belongs to an entry; the root $r(e)$ of an entry is its vertex of highest value, i.e. its vertex processed first.
--   3. **Step at vertex $i$.** The upper star $S_i$ is the set of Rips neighbors $j\ne i$ ($D_{ij}\le\delta$) already processed.
--      - If $S_i=\emptyset$, $i$ is a peak and starts a new entry $\{i\}$ (lines 5–7).
--      - Otherwise $i$ joins the entry of its highest neighbor (lines 9–10). Then (Procedure 2) every neighboring entry $e_j\ne e_i$ with $g_{r(e_j)}-g_i<\tau$ is merged into $e_i$; $\bar e$ is the neighboring entry whose root is highest; and if $\bar e\ne e_i$ and $g_{r(e_i)}-g_i<\tau$, $e_i$ is merged into $\bar e$. A merged entry keeps the higher root.
--   4. **Output.** The clusters are the final entries $e$ with $g_{r(e)}\ge\tau$; $\mathrm{numClusters}(g,D,\delta,\tau,\sigma)$ is their number.
--
--   This is the object of the main theorem: the number of clusters the algorithm returns on $n$ random sample points.
--
--   **Formalization Note** The upper star of $i$ is taken to be its Rips neighbors processed before $i$ (footnote 5, "these involve only previously visited vertices"); reading "higher function values" strictly would disconnect equal-valued neighbors. Among equal values, "highest" means processed first. The spanning forest of approximate gradients (lines 6, 9, 10) does not affect the entries and is not recorded. The loop of Procedure 2, lines 2–7, is implemented as one simultaneous merge; its result does not depend on the order of the loop, since each test uses the tested entry's own root.
-- source:
--   Chazal, Guibas, Oudot, Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA RR-6968 (HAL inria-00389390v1, 2009), pp. 11–13, §3, Procedure 1 (Clustering) and Procedure 2 (Merge), footnote 5

import Mathlib

namespace PersistClust.Count

open Classical

noncomputable section

variable {n : ℕ}

/-- Line 1 of Procedure 1: `σ` sorts the index set so that `g (σ 0) ≤ g (σ 1) ≤ ⋯ ≤ g (σ (n-1))`.
Vertices are then processed in the order `σ (n-1), …, σ 0`; ties are broken arbitrarily. -/
def IsSortOrder (g : Fin n → ℝ) (σ : Fin n ≃ Fin n) : Prop :=
  Monotone (g ∘ σ)

/-- The element of `S` processed first in the order `σ (n-1), …, σ 0` (largest `σ.symm`), or `i₀`
if `S` is empty. -/
def firstProcessed (σ : Fin n ≃ Fin n) (S : Finset (Fin n)) (i₀ : Fin n) : Fin n :=
  if h : S.Nonempty then σ ((S.image σ.symm).max' (h.image _)) else i₀

/-- The state of the union-find structure: `lab v = some r` when `v` has been processed and `r` is the
root of the entry containing `v`; `lab v = none` when `v` has not been processed yet. -/
abbrev UFState (n : ℕ) := Fin n → Option (Fin n)

/-- One iteration (lines 4–11 of Procedure 1, with Procedure 2) at vertex `i`.
* The upper star `S` of `i` is the set of its Rips neighbors (`j ≠ i`, `Dm i j ≤ δ`) already
  processed (footnote 5).
* If `S = ∅`, `i` is a peak and starts a new entry with root `i` (lines 5–7).
* Otherwise `i` joins the entry of `g(i)`, its neighbor of highest value (processed first)
  (lines 9–10). Procedure 2, lines 2–7: every neighboring entry `e_j ≠ e_i` whose root `r(e_j)`
  satisfies `g r(e_j) - g i < τ` is merged with `e_i`. Lines 8–14: `ē` is the neighboring entry with
  the highest root. Lines 15–17: if `ē ≠ e_i` and `g r(e_i) - g i < τ`, `e_i` is merged into `ē`.
* An entry's root is its vertex of highest value, i.e. its vertex processed first; a merge keeps
  the root processed first. -/
def ufStep (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ τ : ℝ) (σ : Fin n ≃ Fin n)
    (lab : UFState n) (i : Fin n) : UFState n :=
  let S : Finset (Fin n) := Finset.univ.filter (fun j => j ≠ i ∧ Dm i j ≤ δ ∧ (lab j).isSome)
  if S = ∅ then Function.update lab i (some i)
  else
    let root : Fin n → Fin n := fun j => (lab j).getD j
    -- lines 9–10: `i` joins the entry of its highest neighbor
    let ri := root (firstProcessed σ S i)
    -- Procedure 2, lines 2–7: merge the non-prominent neighboring entries with `e_i`
    let M : Finset (Fin n) := insert ri ((S.image root).filter (fun r => g r - g i < τ))
    let R := firstProcessed σ M ri
    let lab2 : UFState n := fun v =>
      if v = i then some R
      else match lab v with
        | some r => if r ∈ M then some R else some r
        | none => none
    -- Procedure 2, lines 8–14: the neighboring entry with the highest root
    let E := firstProcessed σ (S.image (fun j => (lab2 j).getD j)) R
    -- Procedure 2, lines 15–17: merge `e_i` into `ē` if `r(e_i)` is not `τ`-prominent
    if E ≠ R ∧ g R - g i < τ then
      fun v => if lab2 v = some R then some E else lab2 v
    else lab2

/-- The final union-find state of Procedure 1, processing `σ (n-1), …, σ 0` from the empty state. -/
def ufRun (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ τ : ℝ) (σ : Fin n ≃ Fin n) : UFState n :=
  (List.finRange n).reverse.foldl (fun lab k => ufStep g Dm δ τ σ lab (σ k)) (fun _ => none)

/-- The number of clusters output by Procedure 1: the entries `e` of the final union-find structure
whose root satisfies `g r(e) ≥ τ`. -/
def numClusters (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ τ : ℝ) (σ : Fin n ≃ Fin n) : ℕ :=
  (Finset.univ.filter (fun r : Fin n => (∃ v, ufRun g Dm δ τ σ v = some r) ∧ τ ≤ g r)).card

end

end PersistClust.Count


