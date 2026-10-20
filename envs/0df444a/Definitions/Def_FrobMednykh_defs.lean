-- Prove2me | Definitions.Def_FrobMednykh_defs
-- name    : FrobMednykh_defs
-- status  : Definition
-- author  : @Alien60
-- created : 2026-10-19T19:14:16.087978+00:00
-- url     : https://prove2.me/theorems/9b638816-c564-4957-99e2-34bedbca4415
-- title:
--   Surface groups, commutator-tuple counts, and complete families of irreducible complex representations
-- statement:
--   `surfaceRelator g` $=[a_1,b_1]\cdots[a_g,b_g]$ in the free group on $a_j=(j,\mathrm{false})$, $b_j=(j,\mathrm{true})$; `SurfaceGroup g` is the group presented by this single relator; `commProd x` $=[x_1,y_1]\cdots[x_g,y_g]$ (left-to-right product, $[x,y]=xyx^{-1}y^{-1}$); `commCount G g z` $=\#\{x\in(G\times G)^g:\mathrm{commProd}(x)=z\}$; `IrrepFamily G ι` bundles a family of simple objects of `FDRep ℂ G` that are pairwise non-isomorphic and complete (every simple object is isomorphic to a member); `IrrepFamily.dim` is the complex dimension of a member.
-- source:
--   N. Snyder, Mednykh's formula via lattice topological quantum field theories, arXiv:math/0703073 (2007), https://arxiv.org/abs/math/0703073, §1 and §3 (Ĝ, d(V), Hom(π₁(S), G))

import Mathlib.RepresentationTheory.Character
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Data.Complex.Basic

/-! Definitions for the Frobenius–Mednykh mission (Snyder, arXiv:math/0703073, eq. (1)). -/

open CategoryTheory

namespace FrobMednykh


/-- Relator of the closed orientable genus-`g` surface group on generators
`a_j = (j, false)`, `b_j = (j, true)`: the ordered product `∏_j [a_j, b_j]`. -/
def surfaceRelator (g : ℕ) : FreeGroup (Fin g × Bool) :=
  (List.ofFn fun j : Fin g => FreeGroup.of (j, false) * FreeGroup.of (j, true) *
    (FreeGroup.of (j, false))⁻¹ * (FreeGroup.of (j, true))⁻¹).prod

/-- `π₁(Σ_g) = ⟨a_1,b_1,…,a_g,b_g | [a_1,b_1]⋯[a_g,b_g]⟩`. -/
abbrev SurfaceGroup (g : ℕ) : Type :=
  PresentedGroup ({surfaceRelator g} : Set (FreeGroup (Fin g × Bool)))

/-- Ordered product of commutators `[x_1,y_1]⋯[x_g,y_g]` of a `g`-tuple of pairs. -/
def commProd {G : Type} [Group G] {g : ℕ} (x : Fin g → G × G) : G :=
  (List.ofFn fun j => (x j).1 * (x j).2 * (x j).1⁻¹ * (x j).2⁻¹).prod

/-- `N_g(z)`: number of `g`-tuples of pairs whose product of commutators is `z`. -/
noncomputable def commCount (G : Type) [Group G] (g : ℕ) (z : G) : ℕ :=
  Nat.card {x : Fin g → G × G // commProd x = z}

/-- A complete list `(V_i)_{i ∈ ι}` of pairwise non-isomorphic irreducible
finite-dimensional complex representations of `G`. -/
structure IrrepFamily (G : Type) [Group G] (ι : Type) where
  V : ι → FDRep ℂ G
  simple : ∀ i, Simple (V i)
  injective : ∀ i j, Nonempty (V i ≅ V j) → i = j
  complete : ∀ W : FDRep ℂ G, Simple W → ∃ i, Nonempty (W ≅ V i)

/-- Dimension `d_i` of the `i`-th irreducible representation. -/
noncomputable def IrrepFamily.dim {G ι : Type} [Group G] (B : IrrepFamily G ι) (i : ι) : ℕ :=
  Module.finrank ℂ (B.V i)

end FrobMednykh


