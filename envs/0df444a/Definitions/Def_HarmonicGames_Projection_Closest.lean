-- Prove2me | Definitions.Def_HarmonicGames_Projection_Closest
-- name    : HarmonicGames_Projection_Closest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:45:42.965979+00:00
-- url     : https://prove2.me/theorems/cc47abf6-b7f3-489c-9170-bb53ecb66010
-- title:
--   The weighted inner product (55) and norm (56) on games, harmonic games, and closest potential and harmonic games (Section 6)
-- statement:
--   Consider a finite game with players $\mathcal M$, nonempty finite strategy sets $E^m$ of cardinality $h_m = |E^m|$, and utilities $u = (u^m)_m$, $u^m : E \to \mathbb R$.
--
--   1. The **inner product** (55) and the **norm** (56) on games are
--   $$
--   \langle G, \hat G \rangle_{M,E} = \sum_{m \in \mathcal M} h_m \langle u^m, \hat u^m \rangle = \sum_{m \in \mathcal M} h_m \sum_{p \in E} u^m(p)\, \hat u^m(p), \qquad \|G\|_{M,E}^2 = \langle G, G \rangle_{M,E},
--   $$
--   a weighted version of the standard inner product on $C_0^M$.
--   2. A **harmonic game** is a game in $\mathcal H \oplus \mathcal N$ (p. 23), the sum of the harmonic and nonstrategic subspaces of Definition 4.2.
--   3. $\hat G$ is a **closest potential game** to $G$ if $\hat G$ is a potential game (Definition 2.1) and $\|G - \hat G\|_{M,E} \le \|G - G'\|_{M,E}$ for every potential game $G'$.
--   4. $\hat G$ is a **closest harmonic game** to $G$ if $\hat G$ is a harmonic game and $\|G - \hat G\|_{M,E} \le \|G - G'\|_{M,E}$ for every harmonic game $G'$.
--
--   These are the notions of Section 6: under (55) the subspaces $\mathcal P$, $\mathcal H$, $\mathcal N$ become orthogonal, and the closest potential and harmonic games are orthogonal projections.
--
--   **Formalization Note** Games are plain functions `u : ι → (∀ m, E m) → ℝ`; `toGames E u` is the same game as an element of the space `C_0^M` of the operator layer. The weighted inner product and norm are plain real-valued functions `innerME`, `normME` (with $h_m$ = `Fintype.card (E m)`), not an `InnerProductSpace` instance, because the space of games already carries the unweighted inner product of Section 4, for which $D^\dagger$, $\Pi_m$, $\mathcal P$, $\mathcal H$, $\mathcal N$ are defined. Potential games are the published `MondererShapley.ClosedPath.IsPotentialGame`, which is condition (3) of Definition 2.1 verbatim. "Closest" is the minimizing property itself, not an infimum over a set of distances; existence and uniqueness are the content of Theorem 6.2.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 35, Section 6, (55), (56); p. 23 (harmonic games H ⊕ N); p. 36, Theorem 6.2 (closest potential and harmonic games)

import Mathlib
import Definitions.Def_HarmonicGames_Projection_Games
import Definitions.Def_MondererShapley_ClosedPath_IsPotentialGame

/-!
Section 6 of Candogan, Menache, Ozdaglar, Parrilo: the weighted inner product (55) and norm
(56) on the space of games, harmonic games (`H ⊕ N`, p. 23), and closest potential and closest
harmonic games with respect to the norm (56).

Games are plain utility functions `u : ι → (∀ m, E m) → ℝ`, `u m p = u^m(p)`. The weighted
inner product is a plain function, not an `InnerProductSpace` instance: the space of games
`Games E` of the operator layer already carries the unweighted inner product of §4, for which
`D†`, `Π_m`, `P`, `H`, `N` are defined.
-/

noncomputable section

namespace HarmonicGames.Projection

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι] (E : ι → Type) [∀ m, Fintype (E m)]
  [∀ m, DecidableEq (E m)]

/-- A game, given by its utilities `u : ι → (∀ m, E m) → ℝ`, as an element of the space
`Games E = C0^M` of the operator layer. -/
def toGames (u : ι → (∀ k, E k) → ℝ) : HarmonicGames.Decomposition.Games E :=
  WithLp.toLp 2 (fun m => WithLp.toLp 2 (u m))

@[simp] theorem toGames_apply (u : ι → (∀ k, E k) → ℝ) (m : ι) (p : ∀ k, E k) :
    toGames E u m p = u m p := rfl

/-- The inner product (55) on games: `⟨G, Ĝ⟩_{M,E} = ∑_m h_m ⟨u^m, û^m⟩`, where
`h_m = |E^m|` and `⟨u^m, û^m⟩ = ∑_{p ∈ E} u^m(p) û^m(p)` is the inner product (7) of `C0`. -/
def innerME (u v : ι → (∀ k, E k) → ℝ) : ℝ :=
  ∑ m, (Fintype.card (E m) : ℝ) * ∑ p : (∀ k, E k), u m p * v m p

/-- The norm (56) on games: `‖G‖_{M,E} = √⟨G, G⟩_{M,E}`. -/
def normME (u : ι → (∀ k, E k) → ℝ) : ℝ := Real.sqrt (innerME E u u)

/-- A **harmonic game** (p. 23): a game in `H ⊕ N`, the sum of the harmonic and nonstrategic
subspaces of Definition 4.2. -/
def IsHarmonicGame (u : ι → (∀ k, E k) → ℝ) : Prop :=
  toGames E u ∈ HarmonicGames.Decomposition.harmonicSubspace E ⊔ HarmonicGames.Decomposition.nonstrategicSubspace E

/-- `û` is a **closest potential game** to `u` with respect to the norm (56): `û` is a potential
game (Definition 2.1) and `‖u - û‖_{M,E} ≤ ‖u - v‖_{M,E}` for every potential game `v`. -/
def IsClosestPotential (u û : ι → (∀ k, E k) → ℝ) : Prop :=
  MondererShapley.ClosedPath.IsPotentialGame û ∧
    ∀ v : ι → (∀ k, E k) → ℝ, MondererShapley.ClosedPath.IsPotentialGame v →
      normME E (u - û) ≤ normME E (u - v)

/-- `û` is a **closest harmonic game** to `u` with respect to the norm (56): `û` is a harmonic
game and `‖u - û‖_{M,E} ≤ ‖u - v‖_{M,E}` for every harmonic game `v`. -/
def IsClosestHarmonic (u û : ι → (∀ k, E k) → ℝ) : Prop :=
  IsHarmonicGame E û ∧
    ∀ v : ι → (∀ k, E k) → ℝ, IsHarmonicGame E v → normME E (u - û) ≤ normME E (u - v)

end HarmonicGames.Projection

end


