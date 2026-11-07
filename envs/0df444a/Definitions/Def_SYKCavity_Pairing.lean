-- Prove2me | Definitions.Def_SYKCavity_Pairing
-- name    : SYKCavity_Pairing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:33:41.521963+00:00
-- url     : https://prove2.me/theorems/a53c20db-cee6-4065-8d97-fd6fe7d4b734
-- title:
--   Pairings $\mathcal P_2([2k])$, crossings $\mathrm{cr}(\sigma)$ and the matrix $\mathcal G_{k,N}$
-- statement:
--   $\mathcal P_2([2k])$ is the set of partitions of $\{1,\dots,2k\}$ into pairs. Two pairs $\{r,s\},\{u,v\}$ with $r<s$, $u<v$ **cross** if $r<u<s<v$ or $u<r<v<s$, and $\operatorname{cr}(\sigma)$ counts the crossing pairs of pairs of $\sigma$. For $\pi,\sigma\in\mathcal P_2([2k])$ the reconstruction matrix is
--   $$(\mathcal G_{k,N})_{\pi\sigma}=N^{\#\{\text{connected components of }\pi\cup\sigma\}-k}.\qquad(4.5)$$
--   Also $\prod_{\{a,b\}\in\pi}\delta_{j_aj_b}$ for sites $j_1,\dots,j_{2k}$.
--
--   $\mathcal G_{k,N}$ is the Gram matrix of the pairing contractions; its inverse gives the orthogonal reconstruction of Lemma 43.
--
--   **Formalization Note** Points are `Fin (2k)`; a pairing is stored as its list of pairs $(r_l<s_l)$ ordered by increasing smaller element, a unique representation. Components are those of the simple graph with the edges of $\pi$ and $\sigma$.
-- source:
--   Schmidhuber–Zlokapa, Polynomial-time algorithms for mean-field models up to the glass transition, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5), (3.8), pp.21–22; (4.5), p.26; (E.16), p.97

import Mathlib

namespace SYKCavity

/-!
# Pairings of `[2k]`, crossings, and the orthogonal reconstruction matrix `G_{k,N}`

A. Schmidhuber, A. Zlokapa, *Polynomial-time algorithms for mean-field models up to the glass
transition*, arXiv:2610.06807 (held version, sha256 25d817ba…cfc5): `P2([2k])` and `cr(σ)`, (3.8),
pp.21–22; the matrix `G_{k,N}` (4.5), p.26; the pair order of (E.16), p.97.

**Formalization Note.**
* Points are `Fin (2k)` (the page's `{1, …, 2k}` shifted to start at `0`). A pairing
  `σ ∈ P2([2k])` is stored as its list of pairs `(r_l, s_l)`, `l ∈ Fin k`, with `r_l < s_l`, ordered by
  increasing smaller element (as in (E.16)), every point lying in exactly one pair. This
  representation is unique, so `Pairing k` is in bijection with `P2([2k])`.
* `cross σ` is `cr(σ)`: the number of pairs of pairs `{r, s}`, `{u, v}` (`r < s`, `u < v`) with
  `r < u < s < v` or `u < r < v < s`.
* `ncomp π σ` is the number of connected components of the multigraph `π ∪ σ` on `[2k]` (simple
  graph of the union of the two edge sets; components are the same).
* `Gmat k N π σ = N^{#components(π ∪ σ) − k}`, (4.5), as a real matrix indexed by pairings.
* `deltaProd j π = ∏_{{a,b} ∈ π} δ_{j_a j_b}`.
-/

/-- `σ` lists the pairs of a pairing of `Fin (2k)`, each as `(smaller, larger)`, by increasing
smaller element, covering every point exactly once. -/
def IsPairing {k : ℕ} (σ : Fin k → Fin (2 * k) × Fin (2 * k)) : Prop :=
  (∀ l, (σ l).1 < (σ l).2) ∧ StrictMono (fun l => (σ l).1) ∧
    Function.Bijective (fun x : Fin k × Fin 2 => if x.2 = 0 then (σ x.1).1 else (σ x.1).2)

/-- `P2([2k])`, the pairings (perfect matchings) of `Fin (2k)`. -/
def Pairing (k : ℕ) : Type := {σ : Fin k → Fin (2 * k) × Fin (2 * k) // IsPairing σ}

noncomputable instance (k : ℕ) : Fintype (Pairing k) := by
  classical
  unfold Pairing
  infer_instance

noncomputable instance (k : ℕ) : DecidableEq (Pairing k) := Classical.decEq _

/-- The number of crossings `cr(σ)`. -/
noncomputable def cross {k : ℕ} (σ : Pairing k) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin k × Fin k)).filter (fun x =>
    x.1 < x.2 ∧
      (((σ.1 x.1).1 < (σ.1 x.2).1 ∧ (σ.1 x.2).1 < (σ.1 x.1).2 ∧ (σ.1 x.1).2 < (σ.1 x.2).2) ∨
       ((σ.1 x.2).1 < (σ.1 x.1).1 ∧ (σ.1 x.1).1 < (σ.1 x.2).2 ∧ (σ.1 x.2).2 < (σ.1 x.1).2)))).card

/-- The number of connected components of the multigraph `π ∪ σ` on `Fin (2k)`. -/
noncomputable def ncomp {k : ℕ} (π σ : Pairing k) : ℕ :=
  Nat.card (SimpleGraph.fromRel (fun a b : Fin (2 * k) =>
    (∃ l, π.1 l = (a, b)) ∨ ∃ l, σ.1 l = (a, b))).ConnectedComponent

/-- `(G_{k,N})_{πσ} = N^{#components(π ∪ σ) − k}`, (4.5). -/
noncomputable def Gmat (k N : ℕ) : Matrix (Pairing k) (Pairing k) ℝ :=
  fun π σ => (N : ℝ) ^ ((ncomp π σ : ℤ) - k)

/-- `∏_{{a,b} ∈ π} δ_{j_a j_b}`. -/
noncomputable def deltaProd {k N : ℕ} (j : Fin (2 * k) → Fin N) (π : Pairing k) : ℝ := by
  classical
  exact ∏ l, if j (π.1 l).1 = j (π.1 l).2 then 1 else 0

end SYKCavity


