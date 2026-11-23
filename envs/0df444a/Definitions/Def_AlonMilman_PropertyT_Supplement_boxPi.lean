-- Prove2me | Definitions.Def_AlonMilman_PropertyT_Supplement_boxPi
-- name    : AlonMilman_PropertyT_Supplement_boxPi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:26:07.700075+00:00
-- url     : https://prove2.me/theorems/6d14a79c-9e2a-4fb8-a909-04bded6ca713
-- title:
--   Cartesian product of finitely many graphs and Cartesian powers $H^i$
-- statement:
--   Let $G_1, \dots, G_l$ be graphs on vertex sets $W_1, \dots, W_l$. Their **Cartesian product** $G = G_1 \times \dots \times G_l$ has vertex set $W_1 \times \dots \times W_l$, and two vertices $x = (x_1, \dots, x_l)$ and $y = (y_1, \dots, y_l)$ are adjacent iff there is a coordinate $j$ such that
--
--   $$x_j \text{ is adjacent to } y_j \text{ in } G_j \quad\text{and}\quad x_{j'} = y_{j'} \text{ for every } j' \ne j.$$
--
--   For two factors this is the product of Alon and Milman, Section 3: $(v_1, u_1)$ and $(v_2, u_2)$ are adjacent if $v_1 = v_2$ and $u_1 u_2$ is an edge of $G_2$, or $u_1 = u_2$ and $v_1 v_2$ is an edge of $G_1$. For $l$ factors it is the iterated product, up to the canonical identification of vertex sets. The **Cartesian power** $H^i$ is the product of $i$ copies of a graph $H$, with vertex set $W^i$ (functions from $\{1, \dots, i\}$ to $W$).
--
--   These are the graphs of Proposition 3.1 and Theorem 3.2.
--
--   **Formalization Note** The product is defined directly for a family indexed by any type (in the theorems, `Fin l`), on the dependent function type $\prod_j W_j$, rather than by iterating the two-factor product `SimpleGraph.boxProd`.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 80, Section 3 (cartesian product); p. 81, Theorem 3.2 (cartesian product of i copies)

import Mathlib

namespace AlonMilman.PropertyT.Supplement

/-- The Cartesian product of a family of simple graphs `G j` on vertex types `W j`
(Alon–Milman 1985, Section 3, p. 80): the vertex set is the product `∏ j, W j`, and `x`, `y` are
adjacent iff they differ in exactly one coordinate `j`, where `x j` and `y j` are adjacent in
`G j`. For two factors this is the product `G₁ × G₂` of p. 80; for `l` factors it is the iterated
product. -/
def boxPi {ι : Type} {W : ι → Type} (G : ∀ j, SimpleGraph (W j)) : SimpleGraph (∀ j, W j) where
  Adj x y := ∃ j, (G j).Adj (x j) (y j) ∧ ∀ j', j' ≠ j → x j' = y j'
  symm := ⟨fun _ _ ⟨j, h, h'⟩ => ⟨j, h.symm, fun j' hj => (h' j' hj).symm⟩⟩
  loopless := ⟨fun _ ⟨j, h, _⟩ => (G j).irrefl h⟩

instance boxPi.decidableAdj {ι : Type} [Fintype ι] [DecidableEq ι] {W : ι → Type}
    [∀ j, DecidableEq (W j)] (G : ∀ j, SimpleGraph (W j)) [∀ j, DecidableRel (G j).Adj] :
    DecidableRel (boxPi G).Adj :=
  fun x y => inferInstanceAs (Decidable (∃ j, (G j).Adj (x j) (y j) ∧ ∀ j', j' ≠ j → x j' = y j'))

/-- The Cartesian product of `i` copies of a simple graph `H` (Alon–Milman 1985, Theorem 3.2,
p. 81), on the vertex type `Fin i → V`. -/
def cartesianPower {V : Type} (H : SimpleGraph V) (i : ℕ) : SimpleGraph (Fin i → V) :=
  boxPi (fun _ : Fin i => H)

instance cartesianPower.decidableAdj {V : Type} [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (i : ℕ) : DecidableRel (cartesianPower H i).Adj :=
  boxPi.decidableAdj (fun _ : Fin i => H)

end AlonMilman.PropertyT.Supplement


