-- Prove2me | Definitions.Def_SublinearSteiner_ThresholdGraph
-- name    : SublinearSteiner_ThresholdGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:40:47.154433+00:00
-- url     : https://prove2.me/theorems/265292cc-9a99-4ef1-a451-46365bcc8204
-- title:
--   Threshold graphs $G_a(X)$, zero links, the contraction benefit $B_T(\mathcal F)$ and the cost $c(Y)$
-- statement:
--   For $X\subseteq V$ and a threshold $a$, $G_a(X)$ is the graph on $X$ whose edges are the pairs at distance less than $a$. Its connected components form $\mathrm{comp}(G_a(X))$, and $\kappa_T(a)=|\mathrm{comp}(G_a(T))|$.
--
--   A family $\mathcal F$ of subsets of $T$ acts by *zero links*: all points of a common set are joined at no cost. The **contraction benefit** is the decrease of the MST weight when every set of $\mathcal F$ is identified at zero cost,
--   $$B_T(\mathcal F)=\mathrm{mst}(T,\emptyset)-\mathrm{mst}(T,\mathcal F),$$
--   where $\mathrm{mst}(T,\mathcal F)$ is the least weight of an edge set on $T$ which, together with the zero links of $\mathcal F$, connects $T$. For one set we write $B_T(Y)$. Finally, $c(Y)$ is the least weight of a tree spanning $Y$ and at most one additional point of $V$.
--
--   These quantities are the language of the structural theorem and of the estimator's soundness.
--
--   **Formalization Note.** $B_T$ is defined as a difference of minima; its expression as an integral is the content of Lemma 2.1. `contractedCost` and `pointCost` are real infima of finite sets, nonempty in the cases used (for $Y\neq\emptyset$), and hence minima. A sanity file proves that `contractedCost` at $\mathcal F=\emptyset$ is the terminal MST weight. `rankDecrease` is the decrease in the number of components caused by a family of links given earlier links.
-- source:
--   Mahabadi, Roghani, Tarnawski, Vakilian, Tight Bounds for Sublinear Metric Steiner Tree, STOC 2027 submission (manuscript sha256 ae133037…), Section 2, p.12

import Mathlib
import Definitions.Def_SublinearSteiner_FinMetric

open scoped Classical

namespace SublinearSteiner

/-!
# Threshold graphs, zero links, contraction benefit, and `c(Y)`

Mahabadi, Roghani, Tarnawski, Vakilian, *Tight Bounds for Sublinear Metric Steiner Tree*, STOC 2027
submission (manuscript sha256 ae133037…), Section 2, p.12.

`G_a(X)` is the graph on `X` whose edges are the pairs at distance less than `a`; `comp` is its set of connected
components; `κ_T(a) = |comp(G_a(T))|`. For a family `F` of subsets of `T`, the benefit `B_T(F)` is the decrease of
the MST weight when every set of `F` is identified at zero cost. `c(Y)` is the least weight of a tree spanning `Y`
and at most one additional point of `V`.

**Formalization Note.**
* Graphs live on all of `Fin n`, with the points outside `X` isolated. A component is a `Finset` of points.
* The strict `<` of `G_a` is as printed.
* `B_T(F)` is a difference of two minima, not an integral (the integral is Lemma 2.1). The contracted MST weight is
  the least weight of an edge set on `T` that connects `T` together with the zero links of `F`. Weights are positive, so
  this minimum is attained by a forest; for `F = ∅` it is the MST weight `L`.
* `contractedCost` and `pointCost` use real `sInf`. Each set is finite (there are finitely many edge sets), and it is
  nonempty: all pairs of `T` connect `T`, and a nonempty `Y` has a spanning tree. So `sInf` is a minimum there.
-/

variable {n : ℕ}

/-- `G_a(X)`: the pairs of points of `X` at distance less than `a`. -/
def thresholdGraph (w : FinMetric n) (X : Finset (Fin n)) (a : ℝ) : SimpleGraph (Fin n) where
  Adj x y := x ∈ X ∧ y ∈ X ∧ x ≠ y ∧ w.d x y < a
  symm := ⟨fun x y h => ⟨h.2.1, h.1, h.2.2.1.symm, by rw [w.d_symm]; exact h.2.2.2⟩⟩
  loopless := ⟨fun x h => h.2.2.1 rfl⟩

/-- The connected components, as point sets, of a graph restricted to the points of `X`. -/
noncomputable def compOf (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  X.image fun x => X.filter fun y => G.Reachable x y

/-- The component of `x` in `G_a(X)`. -/
noncomputable def component (w : FinMetric n) (X : Finset (Fin n)) (a : ℝ) (x : Fin n) : Finset (Fin n) :=
  X.filter fun y => (thresholdGraph w X a).Reachable x y

/-- `comp(G_a(X))`. -/
noncomputable def comp (w : FinMetric n) (X : Finset (Fin n)) (a : ℝ) : Finset (Finset (Fin n)) :=
  compOf (thresholdGraph w X a) X

/-- `κ_T(a) = |comp(G_a(T))|`. -/
noncomputable def kappa (w : FinMetric n) (T : Finset (Fin n)) (a : ℝ) : ℕ :=
  (comp w T a).card

/-- The zero links of a family: every pair of distinct points in a common set of `F`. -/
def linkGraph (F : Finset (Finset (Fin n))) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ ∃ Y ∈ F, x ∈ Y ∧ y ∈ Y
  symm := ⟨fun _ _ h => ⟨h.1.symm, by obtain ⟨Y, hY, hx, hy⟩ := h.2; exact ⟨Y, hY, hy, hx⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The number of components of `G_a(T)` once the zero links of `F` are added. -/
noncomputable def kappaLinked (w : FinMetric n) (T : Finset (Fin n)) (a : ℝ)
    (F : Finset (Finset (Fin n))) : ℕ :=
  (compOf (thresholdGraph w T a ⊔ linkGraph F) T).card

/-- The decrease of the number of components of `G_a(T)` caused by the zero links `F`, given the earlier zero
links `Z` (Lemma 2.1). -/
noncomputable def rankDecrease (w : FinMetric n) (T : Finset (Fin n)) (a : ℝ)
    (Z F : Finset (Finset (Fin n))) : ℝ :=
  (kappaLinked w T a Z : ℝ) - kappaLinked w T a (Z ∪ F)

/-- `E` is a set of non-loop pairs of `T` that connects `T` together with the zero links of `F`. -/
def IsConnectingSet (T : Finset (Fin n)) (F : Finset (Finset (Fin n)))
    (E : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ E, ¬ e.IsDiag ∧ ∀ x ∈ e, x ∈ T) ∧
    ∀ x ∈ T, ∀ y ∈ T, (edgeGraph E ⊔ linkGraph F).Reachable x y

/-- The MST weight of the metric on `T` with every set of `F` identified at zero cost. -/
noncomputable def contractedCost (w : FinMetric n) (T : Finset (Fin n))
    (F : Finset (Finset (Fin n))) : ℝ :=
  sInf {c | ∃ E, IsConnectingSet T F E ∧ c = w.weight E}

/-- `B_T(F)`: the decrease of the MST weight when every set of `F` is identified at zero cost (p.12). -/
noncomputable def benefitFamily (w : FinMetric n) (T : Finset (Fin n))
    (F : Finset (Finset (Fin n))) : ℝ :=
  contractedCost w T ∅ - contractedCost w T F

/-- `B_T(Y)`, the benefit of one set (p.12). -/
noncomputable def benefit (w : FinMetric n) (T Y : Finset (Fin n)) : ℝ :=
  benefitFamily w T {Y}

/-- `c(Y)`: the least weight of a tree spanning `Y` and at most one additional point of `V` (p.12). -/
noncomputable def pointCost (w : FinMetric n) (Y : Finset (Fin n)) : ℝ :=
  sInf {c | ∃ U E, (U = Y ∨ ∃ v, U = insert v Y) ∧ IsTreeOn U E ∧ c = w.weight E}

end SublinearSteiner


