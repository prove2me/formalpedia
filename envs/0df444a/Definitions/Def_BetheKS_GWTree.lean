-- Prove2me | Definitions.Def_BetheKS_GWTree
-- name    : BetheKS_GWTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:16.340011+00:00
-- url     : https://prove2.me/theorems/8ddaaf9d-a6fd-438d-8f56-bce7e71a212c
-- title:
--   Rooted trees $\Omega$, the Poisson Galton–Watson law $\nu$, and the root cavity weight $\Gamma(T)$
-- statement:
--   $\Omega$ is the space of locally finite rooted trees, encoded by offspring functions (Ulam–Harris words, children ordered), and $\nu$ is the law of a Galton–Watson tree with $\mathrm{Poi}(d)$ offspring (Definition A.2). For $T\in\Omega$ let $K$ be the root degree and $T_1,\dots,T_K$ the forward subtrees. The **root cavity weight** (Definition A.1, with $\Gamma_o$ of Definition 3.3) is the limit of the iteration
--   $$
--   \Gamma^{(0)}(T)=0,\qquad\Gamma^{(M+1)}(T)=\frac{t}{t^2+K+\delta-t\sum_{j=1}^K\Gamma^{(M)}(T_j)},
--   $$
--   so that $\Gamma(T)=t/(t^2+K+\delta-t\sum_j\Gamma(T_j))$ (3.3). The file also defines finite trees and the tree as a graph on its words.
--
--   **Formalization Note** $\nu$ is the product of i.i.d. $\mathrm{Poi}(d)$ coordinates over all words; the tree read off is a $\mathrm{Poi}(d)$ Galton–Watson tree, and the coordinates at non-vertices are additional independent randomness. Given $K$, the forward subtrees are i.i.d. with law $\nu$, which is the only structure the paper's arguments in §4 and App. A–B use.
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), §4, p.7; Definitions A.1, A.2, p.13; Definition 3.3 (3.3), p.7

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace BetheKS

/-- Rooted locally finite (ordered) trees in Ulam–Harris form: an offspring function
`K : List ℕ → ℕ`. Words are read **from the vertex up to the root**: `[]` is the root `o`, and
`j :: w` is the `j`-th child of `w`. Only the values of `K` at vertices matter for the tree. -/
abbrev Offspring := List ℕ → ℕ

/-- `w` is a vertex of the tree `K`: the root is, and `j :: w` is iff `w` is and `j < K w`. -/
def IsVertex (K : Offspring) : List ℕ → Prop
  | [] => True
  | j :: w => IsVertex K w ∧ j < K w

/-- The forward subtree `T_j` rooted at the `j`-th child of the root (Definition A.1, p.13). -/
def subtree (K : Offspring) (j : ℕ) : Offspring := fun w => K (w ++ [j])

/-- The tree `K` is finite. -/
def IsFiniteTree (K : Offspring) : Prop := {w | IsVertex K w}.Finite

/-- **The Poisson Galton–Watson law `ν`** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256
4da41e16…), Definition A.2, p.13 (PDF p.14): the law on `Ω` of a Galton–Watson tree with offspring
distribution `Poi(d)`.

**Formalization Note.** `Ω` is encoded by offspring functions `List ℕ → ℕ` with the product
σ-algebra, and `ν` is the product of i.i.d. `Poi(d)` coordinates (`Measure.infinitePi`). The tree
read off from `K` is then a `Poi(d)` Galton–Watson tree; the coordinates at non-vertices are extra
independent randomness. Children are ordered; the space `L²(Ω, ν)` contains the paper's functions of
the (unordered) tree, and the operators of §4 act on the larger space with the same spectral data
(the paper's arguments use only that, given `K`, the forward subtrees are i.i.d. with law `ν`). -/
noncomputable def gwLaw (d : ℝ) : Measure Offspring :=
  Measure.infinitePi (fun _ : List ℕ => poissonMeasure d.toNNReal)

instance (d : ℝ) : IsProbabilityMeasure (gwLaw d) := by
  unfold gwLaw; infer_instance

/-- The root iteration `Γ^{(M)}(T)` of the cavity weight on a rooted tree (Definition 3.3, p.7,
"for the root `o`, we define `Γ_o^{(M)}` analogously without excluding any neighbor"):
`Γ^{(0)} = 0`, `Γ^{(M+1)}(T) = t / (t² + K + δ − t ∑_{j<K} Γ^{(M)}(T_j))`, `K` the root degree. -/
noncomputable def treeGammaIter (t δ : ℝ) : ℕ → Offspring → ℝ
  | 0, _ => 0
  | M + 1, K => t / (t ^ 2 + (K [] : ℝ) + δ -
      t * ∑ j ∈ Finset.range (K []), treeGammaIter t δ M (subtree K j))

/-- **The cavity weight at the root `Γ(T) := Γ_o = lim_M Γ_o^{(M)}`** — Definition A.1, p.13, with
`Γ_o` as in Definition 3.3 (3.3), p.7: `Γ_o = t / (t² + deg(o) + δ − t ∑_{w∼o} Γ_w)`. -/
noncomputable def treeGamma (t δ : ℝ) (K : Offspring) : ℝ :=
  limUnder atTop (fun M => treeGammaIter t δ M K)

/-- The tree `K` as a graph on words: `w ∼ v` iff both are vertices and one is a child of the other.
Non-vertex words are isolated. -/
def treeGraph (K : Offspring) : SimpleGraph (List ℕ) where
  Adj w v := IsVertex K w ∧ IsVertex K v ∧ ((∃ j, v = j :: w) ∨ (∃ j, w = j :: v))
  symm := by
    refine ⟨fun w v h => ?_⟩
    exact ⟨h.2.1, h.1, h.2.2.symm⟩
  loopless := by
    refine ⟨fun w h => ?_⟩
    rcases h.2.2 with ⟨j, hj⟩ | ⟨j, hj⟩ <;>
      exact absurd (congrArg List.length hj) (by simp)

theorem treeGraph_neighborSet_finite (K : Offspring) (w : List ℕ) :
    ((treeGraph K).neighborSet w).Finite := by
  apply Set.Finite.subset
    (((({w.tail} : Finset (List ℕ)) ∪ (Finset.range (K w)).image (· :: w)) : Finset _).finite_toSet)
  intro v hv
  simp only [SimpleGraph.mem_neighborSet, treeGraph] at hv
  obtain ⟨_, hvV, h⟩ := hv
  rcases h with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp only [IsVertex] at hvV
    simp [hvV.2]
  · simp

noncomputable instance (K : Offspring) : (treeGraph K).LocallyFinite :=
  fun w => (treeGraph_neighborSet_finite K w).fintype

end BetheKS


