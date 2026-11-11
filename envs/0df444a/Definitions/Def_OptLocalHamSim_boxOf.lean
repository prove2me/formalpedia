-- Prove2me | Definitions.Def_OptLocalHamSim_boxOf
-- name    : OptLocalHamSim_boxOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:44.894175+00:00
-- url     : https://prove2.me/theorems/e16b2bb4-2b27-48a6-a3c6-569bad432516
-- title:
--   Regions, signs and the layered product $\mathcal V(t)=\mathcal V_{L_H}(t)\cdots\mathcal V_1(t)$ of Lemma 4
-- statement:
--   A **region** is a box in $\Lambda$, given classically by its corner $c$ and its side lengths $s$: the sites $x$ with $c_j\le x_j<c_j+s_j$ for every $j$. A layer $\mathcal B_a$ is a list of regions $Y$ with signs $\sigma_{a,Y}\in\{-1,1\}$ (forward or inverse evolution). For a Hamiltonian $\bar H$ with terms $h$,
--
--   $$
--   \mathcal V_a(t):=\prod_{Y\in\mathcal B_a}\bar U_Y(\sigma_{a,Y}t),\qquad \mathcal V(t):=\mathcal V_{L_H}(t)\cdots\mathcal V_1(t),\qquad \bar U_Y(t)=e^{-i\bar H_Yt}.
--   $$
--
--   A region **fits** with side bounds $[\ell,\ell']$ if it lies inside $\Lambda$ and all its sides are in $[\ell,\ell']$.
--
--   These are the objects of Lemma 4 (eq. (8)), which decomposes a short-time evolution into a constant number of layers of restricted evolutions.
--
--   **Formalization Note** Corners and sides are lists of natural numbers (a missing entry reads as $0$; fitting requires length $D$). The sign is a Boolean, `true` for $+1$. The factors of a layer are multiplied in list order; for disjoint regions they commute. The first layer of the list acts first.
-- source:
--   Shen, Wu, Yao, Yuan, Zhang, Toward an Optimal Quantum Algorithm for Geometrically Local Hamiltonian Simulation, STOC 2027 submission (held version, sha256 44a9768a…), §2.1, Lemma 4, eq. (8), p.11

import Mathlib
import Definitions.Def_OptLocalHamSim_IsLocalHam

namespace OptLocalHamSim

variable {D : ℕ} {q : ℕ}

/-- The rectangular region with corner `c` and side lengths `s` (two lists of length `D`): the sites
`x` with `c_j ≤ x_j < c_j + s_j` for every coordinate `j`. This is how the regions `Y ∈ B_a` of Lemma 4
(Shen, Wu, Yao, Yuan, Zhang, STOC 2027 submission, held version, sha256 44a9768a…, p.11) are encoded as
classical data.

**Formalization Note** A missing list entry reads as `0`; `BoxFits` requires both lists to have length
`D`. -/
def boxOf (L : Fin D → ℕ) (cs : List ℕ × List ℕ) : Finset (Site L) :=
  Finset.univ.filter fun x => ∀ j : Fin D,
    cs.1.getD j 0 ≤ (x j : ℕ) ∧ (x j : ℕ) < cs.1.getD j 0 + cs.2.getD j 0

/-- The region data `cs = (corner, sides)` describes a box inside the lattice `Λ` (`corner_j + side_j ≤
L_j`) whose side lengths lie in `[lo, hi]`. -/
def BoxFits (L : Fin D → ℕ) (lo hi : ℝ) (cs : List ℕ × List ℕ) : Prop :=
  cs.1.length = D ∧ cs.2.length = D ∧ ∀ j : Fin D,
    lo ≤ (cs.2.getD j 0 : ℝ) ∧ (cs.2.getD j 0 : ℝ) ≤ hi ∧ cs.1.getD j 0 + cs.2.getD j 0 ≤ L j

/-- The sign `σ_{a,Y} ∈ {−1, 1}` of a region (p.11): `true` is forward evolution (`+1`), `false` inverse
evolution (`−1`). -/
def signOf (b : Bool) : ℝ := if b then 1 else -1

/-- One layer `𝒱_a(t) := ∏_{Y∈B_a} Ū_Y(σ_{a,Y} t)` of eq. (8), p.11, with `Ū_Y(t) = e^{−i H̄_Y t}` and
`H̄_Y` the restriction (4) of the (normalized) Hamiltonian `h`.

**Formalization Note** The factors are multiplied in list order; for pairwise disjoint regions they
commute, so the order is immaterial. -/
noncomputable def layerUnitary (L : Fin D → ℕ)
    (h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ)
    (layer : List ((List ℕ × List ℕ) × Bool)) (t : ℝ) :
    Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ :=
  (layer.map fun Y => evol (HamOn h (boxOf L Y.1)) (signOf Y.2 * t)).prod

/-- The product `𝒱(t) := 𝒱_{L_H}(t) ⋯ 𝒱_1(t)` of eq. (8), p.11, for the layers `[B_1, …, B_{L_H}]` (the
head of the list is layer 1, which acts first). -/
noncomputable def layersProduct (L : Fin D → ℕ)
    (h : Finset (Site L) → Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ)
    (lay : List (List ((List ℕ × List ℕ) × Bool))) (t : ℝ) :
    Matrix (Dat L q → Bool) (Dat L q → Bool) ℂ :=
  (lay.map fun layer => layerUnitary L h layer t).reverse.prod

end OptLocalHamSim


