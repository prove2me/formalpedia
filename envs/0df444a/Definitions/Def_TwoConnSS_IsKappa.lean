-- Prove2me | Definitions.Def_TwoConnSS_IsKappa
-- name    : TwoConnSS_IsKappa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:47:29.814779+00:00
-- url     : https://prove2.me/theorems/d2f6f567-62d6-4db0-9812-57504bd7b2f7
-- title:
--   The final configuration of Algorithm B and the parameter $\kappa$
-- statement:
--   The **final configuration** of Algorithm B is a canonical 2-edge-cover $S$ for Algorithm B consisting of one large 2EC component $L$ (not a 4- or 5-cycle) and 4-cycle components $C_1, \dots, C_s$, each adjacent to no component other than $L$.
--
--   For each $i$, every choice of edges $ax, yb \in E(G)$ with $a, b \in V(L)$ and $\{x, y\}$ a shortcut pair of $C_i$ gives an **artificial edge** $ab$ of colour $i$. Choosing one artificial edge of each colour so as to minimize the number of connected components of the resulting spanning multigraph on $V(L)$ (isolated vertices counted) defines
--   $$\kappa = \min_{\text{selections}} \#\text{components}.$$
--
--   **Formalization Note** `IsKappa G S L κ` says $\kappa$ is attained by some selection and no selection does better; it is a minimum with a witness, not an infimum.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.3.4, pp.67–68

import Mathlib
import Definitions.Def_TwoConnSS_IsCanonB
import Definitions.Def_TwoConnSS_IsShortcutPair

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- **The final configuration of Algorithm B** (§8.3.4, p.67): "a 2-edge-cover consisting of one
large component L and 4-cycles C1, …, Cs, each adjacent only to L." Here `S` is canonical for B,
`L` is a 2EC component of `S` that is neither a 4-cycle nor a 5-cycle, every other component is a
4-cycle, and a 4-cycle component is adjacent to no component other than `L`. -/
def IsFinalConfigB (G : SimpleGraph V) (S : Finset (Sym2 V)) (L : Finset V) : Prop :=
  IsCanonB G S ∧ IsTwoECComp S L ∧ ¬ IsCycleComp S L 4 ∧ ¬ IsCycleComp S L 5 ∧
  ∀ C ∈ comps S, C ≠ L → IsCycleComp S C 4 ∧
    ∀ D ∈ comps S, D ≠ C → (∃ u ∈ C, ∃ v ∈ D, G.Adj u v) → D = L

/-- The 4-cycle components `C₁, …, C_s` of `S`; `s` is their number. -/
noncomputable def cyc4 (S : Finset (Sym2 V)) : Finset (Finset V) :=
  (comps S).filter fun C => IsCycleComp S C 4

/-- A selection of one artificial edge of each colour (p.68): for each 4-cycle `C_i`, the pair
`sel C_i = (a, b)` with `a, b ∈ V(L)` and edges `ax, yb ∈ E(G)` for a shortcut pair `{x, y}` of
`C_i`. -/
def IsArtSel (G : SimpleGraph V) (S : Finset (Sym2 V)) (L : Finset V) (sel : Finset V → V × V) :
    Prop :=
  ∀ C ∈ cyc4 S, ∃ x y, IsShortcutPair G S C x y ∧ (sel C).1 ∈ L ∧ (sel C).2 ∈ L ∧
    G.Adj (sel C).1 x ∧ G.Adj y (sel C).2

/-- The graph of the selected artificial edges (loops dropped; parallel edges do not change
connectivity). -/
def selGraph (S : Finset (Sym2 V)) (sel : Finset V → V × V) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ C ∈ cyc4 S, s((sel C).1, (sel C).2) = s(a, b)
  symm := ⟨fun _ _ h => ⟨h.1.symm, let ⟨C, hC, he⟩ := h.2; ⟨C, hC, he.trans Sym2.eq_swap⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The number of connected components of the spanning multigraph on `V(L)` formed by the
selected artificial edges, counting isolated vertices. -/
noncomputable def nComp (S : Finset (Sym2 V)) (L : Finset V) (sel : Finset V → V × V) : ℕ :=
  (L.image fun v => (selGraph S sel).connectedComponentMk v).card

/-- **`κ` of the final configuration of Algorithm B.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §8.3.4, p.68: "For each such
choice, introduce an artificial edge ab with colour i, and record the corresponding set Qi. Let Γ be
the resulting multigraph on V(L). Parallel edges and loops are allowed. … We choose one artificial edge of each colour so as to
minimize the number of connected components of the resulting spanning multigraph on V(L), counting
isolated vertices. Denote this minimum by κ."

`IsKappa G S L κ` says `κ` is attained by some selection and no selection does better. Also
defined here: the final configuration (`IsFinalConfigB`), the 4-cycle components (`cyc4`),
selections (`IsArtSel`), their graph and its component count.

**Formalization Note.** `κ` is a minimum with a witness, never an infimum of a possibly empty
set; when no selection exists no `κ` satisfies `IsKappa`. -/
def IsKappa (G : SimpleGraph V) (S : Finset (Sym2 V)) (L : Finset V) (κ : ℕ) : Prop :=
  (∃ sel, IsArtSel G S L sel ∧ nComp S L sel = κ) ∧
  ∀ sel, IsArtSel G S L sel → κ ≤ nComp S L sel

end TwoConnSS


