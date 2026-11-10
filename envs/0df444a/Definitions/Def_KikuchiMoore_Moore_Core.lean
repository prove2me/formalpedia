-- Prove2me | Definitions.Def_KikuchiMoore_Moore_Core
-- name    : KikuchiMoore_Moore_Core
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:41:17.500372+00:00
-- url     : https://prove2.me/theorems/4a9e567e-a38e-4b41-b86b-e03d06ba0517
-- title:
--   Even covers and the Moore scales
-- statement:
--   A hypergraph is the published finite simple hypergraph object on the full ambient vertex set $[n]$, allowing isolated vertices and no edges. Uniformity means every edge has cardinality $k$. An even cover is a nonempty subfamily of distinct edges in which every vertex has even incidence. The predicate $\mathrm{HasCoverLE}(H,t)$ asserts an even cover of size at most the real bound $t$; it is false when no cover exists. The density and cover scales are $D=n^{k/2}/\ell^{k/2-1}$ and $L=\ell\log(en/\ell)$, with real exponents. The central range is $2k\le\ell$ and $100k\ell\le n$, and $s=\lceil3L/k\rceil$. Rows are all $\ell$-subsets. Window representatives choose distinct incident vertices for edges entirely contained in a window whenever such a system exists; an optional-value fallback outside that domain defines a total function without asserting existence. These are the common objects of Theorem 1.1 and Section 3.
-- source:
--   Schmidhuber and Hastings (2026), Sharp Spectral Bounds for Kikuchi Matrices: The Hypergraph Moore Bound and Optimal Trade-offs for kXOR, supplied STOC 2027 submission, Even covers and Theorem 1.1 setup, printed p. 2 = PDF p. 2, PDF SHA-256 44f00c2d419b40d2f4d664d6eedb7dda4c80a7da27e71ed4fccd6a5a613725ea

import Mathlib
import Definitions.Def_TenChallenges_Hypergraph

noncomputable section
open scoped BigOperators

namespace KikuchiMoore.Moore

/-- The published simple hypergraph object, with the full ambient vertex set. -/
abbrev Hypergraph (n : ℕ) := {H : FinHypergraph (Fin n) // H.vertices = Finset.univ}

def edges {n : ℕ} (H : Hypergraph n) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter (· ∈ H.val.edges)

def Uniform {n : ℕ} (H : Hypergraph n) (k : ℕ) : Prop := H.val.IsUniform k

def EvenCover {n : ℕ} (H : Hypergraph n) (Q : Finset (Finset (Fin n))) : Prop :=
  Q.Nonempty ∧ Q ⊆ edges H ∧ ∀ v : Fin n, Even ((Q.filter (v ∈ ·)).card)

/-- Equivalent to finite upper bounds on even girth, including the cover-free case. -/
def HasCoverLE {n : ℕ} (H : Hypergraph n) (t : ℝ) : Prop :=
  ∃ Q, EvenCover H Q ∧ (Q.card : ℝ) ≤ t

def densityScale (n k l : ℕ) : ℝ :=
  Real.rpow (n : ℝ) ((k : ℝ) / 2) / Real.rpow (l : ℝ) ((k : ℝ) / 2 - 1)

def coverScale (n l : ℕ) : ℝ := (l : ℝ) * Real.log (Real.exp 1 * n / l)

def Central (n k l : ℕ) : Prop := 2 * k ≤ l ∧ 100 * k * l ≤ n

def evenLength (n k l : ℕ) : ℕ := ⌈3 * coverScale n l / k⌉₊

abbrev Row (n l : ℕ) := {S : Finset (Fin n) // S.card = l}

def inducedEdges {n : ℕ} (H : Hypergraph n) (W : Finset (Fin n)) :=
  (edges H).filter (· ⊆ W)

/-- A representative is only required on edges contained in the window. -/
def RepSystem {n : ℕ} (H : Hypergraph n) (W : Finset (Fin n))
    (rho : Finset (Fin n) → Option (Fin n)) : Prop :=
  (∀ F ∈ inducedEdges H W, ∃ v ∈ F, rho F = some v) ∧
  ∀ F ∈ inducedEdges H W, ∀ J ∈ inducedEdges H W, rho F = rho J → F = J

def representative {n : ℕ} (H : Hypergraph n) (W : Finset (Fin n)) :
    Finset (Fin n) → Option (Fin n) := by
  classical
  exact if h : ∃ rho, RepSystem H W rho then Classical.choose h else fun _ => none

end KikuchiMoore.Moore


