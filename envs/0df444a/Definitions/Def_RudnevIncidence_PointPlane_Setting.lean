-- Prove2me | Definitions.Def_RudnevIncidence_PointPlane_Setting
-- name    : RudnevIncidence_PointPlane_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:15:46.444409+00:00
-- url     : https://prove2.me/theorems/f5889c1b-1584-4df7-a26e-0268302c34ab
-- title:
--   pp. 2, 7–9, 12 — incidences I(P,Π), Plücker coordinates, Klein quadric, α/β-planes, the three-quadric G = K ∩ S
-- statement:
--   The objects of Rudnev's point–plane incidence theorem in the projective space $\mathbb P^3$ over a field $\mathbb F$.
--
--   1. **Points, planes, incidences** ((1), p. 2). A point $q=(q_0:q_1:q_2:q_3)$ and a plane $\pi=(\pi_0:\pi_1:\pi_2:\pi_3)$ of $\mathbb P^3$ are both elements of the projectivisation of $\mathbb F^4$; the point lies on the plane, $q\in\pi$, when $q_0\pi_0+q_1\pi_1+q_2\pi_2+q_3\pi_3=0$. For finite sets $P$ of points and $\Pi$ of planes,
--   $$|I(P,\Pi)|=\#\{(q,\pi)\in P\times\Pi:\ q\in\pi\}.$$
--   A **line** of $\mathbb P^3$ is a 2-dimensional subspace $W\subseteq\mathbb F^4$; a plane contains $W$ when its covector annihilates $W$, and a point lies on $W$ when its coordinate vector belongs to $W$. We write $\Pi_W$ for the planes of $\Pi$ containing $W$ and $P_W$ for the points of $P$ on $W$.
--   2. **Plücker coordinates** ((7), p. 7). The line through $q$ and $u$ has Plücker vector $L=(P_{01}:P_{02}:P_{03}:P_{23}:P_{31}:P_{12})\in\mathbb P^5$ with $P_{ij}=q_iu_j-q_ju_i$, in this order.
--   3. **Klein quadric** ((8), p. 8): $\mathcal K=\{P_{01}P_{23}+P_{02}P_{31}+P_{03}P_{12}=0\}$, and the **reciprocal product** ((9), p. 8)
--   $$\langle L,L'\rangle=P_{01}P'_{23}+P_{02}P'_{31}+P_{03}P'_{12}+P'_{01}P_{23}+P'_{02}P_{31}+P'_{03}P_{12}.$$
--   The hyperplane tangent to $\mathcal K$ at $L$ is $T_L\mathcal K=\{L':\langle L,L'\rangle=0\}$.
--   4. **α- and β-planes** (p. 9): the α-plane of a point $q$ is the span of the Plücker vectors of all lines through $q$; the β-plane of a plane $\pi$ is the span of the Plücker vectors of all lines lying in $\pi$.
--   5. **The three-quadric** $\mathcal G=\mathcal K\cap S$ (pp. 9, 12). A hyperplane $S$ of $\mathbb P^5$ is given by a covector $(\boldsymbol u:\boldsymbol w)\in\mathbb F^6$, $S=\{\boldsymbol u\cdot\boldsymbol\omega+\boldsymbol w\cdot\boldsymbol v=0\}$ for $L=(\boldsymbol\omega:\boldsymbol v)$. It is **not tangent** to $\mathcal K$ (so $\mathcal K\cap S$ is the Klein image of a regular line complex) when $\boldsymbol u\cdot\boldsymbol w\neq0$. A line of $\mathcal G$ is a 2-dimensional subspace of $\mathbb F^6$ inside $S$ on which the Klein form vanishes. For a point $q$ and a plane $\pi$ of $\mathbb P^3$, the lines of $\mathcal G$ they define are the α-plane of $q$, resp. the β-plane of $\pi$, intersected with $S$. For two finite families $L_\alpha,L_\beta$ of lines of $\mathbb P^5$, $|I(L_\alpha,L_\beta)|$ counts the pairs that meet.
--   6. **Ruled surfaces.** The surface $Z(Q)\subset\mathbb P^3$ of a homogeneous polynomial $Q\in\mathbb F[x_0,x_1,x_2,x_3]$ is ruled when every point of $Z(Q)$ lies on a line of $\mathbb P^3$ contained in $Z(Q)$.
--
--   These are the objects of Theorem 3 and of the steps of its proof: the passage from point–plane incidences in $\mathbb P^3$ to line–line incidences in $\mathcal G$ (Lemma 9) and the incidence bound in $\mathcal G$ (Theorem 12).
--
--   **Formalization Note** Points and planes are both elements of `ℙ F (Fin 4 → F)`, so a finite set of them is a set of distinct projective objects; incidence is Mathlib's `Projectivization.orthogonal`. Lines of $\mathbb P^3$, of $\mathbb P^5$ and of $\mathcal G$ are 2-dimensional subspaces; two lines of $\mathbb P^5$ meet when their intersection subspace is nonzero. Plücker vectors are indexed $0,\dots,5$ in the order $(P_{01},P_{02},P_{03},P_{23},P_{31},P_{12})$, and $P_{31}=q_3u_1-q_1u_3$. A hyperplane is encoded by its covector $U\in\mathbb F^6$; the tangent hyperplane $T_L\mathcal K$ is the hyperplane of the covector $(L_3,L_4,L_5,L_0,L_1,L_2)$, and the lemma `mem_tangentHyperplane_iff` records that its points are those with $\langle L,L'\rangle=0$. "Ruled" is the incidence-geometric meaning (p. 11: "an algebraic ruled surface is a surface in $\mathbb P^3$ composed of a polynomial family of lines"), not the birational definition of p. 11 (a smooth projective surface birationally equivalent to $\mathbb P^1\times C$); for irreducible surfaces in $\mathbb P^3$ over an algebraically closed field the two agree classically, and no item claims that agreement.
-- source:
--   Rudnev, On the number of incidences between points and planes in three dimensions, arXiv:1407.0426v5, p. 2, (1); pp. 7–8, (7)–(9); p. 9, §4.1.1 (α/β-planes, regular line complexes); p. 11, §4.1.3 (ruled surfaces); p. 12, §4.2 (G = K ∩ S)

import Mathlib

namespace RudnevIncidence.PointPlane

open Classical Projectivization
open scoped LinearAlgebra.Projectivization

variable {F : Type*} [Field F]

/-- (1), p. 2: the number `|I(P, Π)|` of incident pairs `(q, π) ∈ P × Π` with `q ∈ π`. Points and
planes of `P³` are both elements of `ℙ F (Fin 4 → F)`: a point is the class of its homogeneous
coordinates `(q₀ : q₁ : q₂ : q₃)`, a plane the class of its covector `(π₀ : π₁ : π₂ : π₃)`, and
`q ∈ π` is `q₀π₀ + q₁π₁ + q₂π₂ + q₃π₃ = 0` (`Projectivization.orthogonal`). -/
noncomputable def incidences (P Pl : Finset (ℙ F (Fin 4 → F))) : ℕ :=
  ((P ×ˢ Pl).filter (fun x => x.1.orthogonal x.2)).card

/-- The planes of `Pl` containing the line of `P³` given by the subspace `W` of `F⁴` (a line is a
2-dimensional subspace): every vector of `W` is annihilated by the plane's covector. -/
noncomputable def planesThrough (Pl : Finset (ℙ F (Fin 4 → F))) (W : Submodule F (Fin 4 → F)) :
    Finset (ℙ F (Fin 4 → F)) :=
  Pl.filter (fun π => ∀ w ∈ W, w ⬝ᵥ π.rep = 0)

/-- The points of `P` lying on the line of `P³` given by the subspace `W` of `F⁴`. -/
noncomputable def pointsOn (P : Finset (ℙ F (Fin 4 → F))) (W : Submodule F (Fin 4 → F)) :
    Finset (ℙ F (Fin 4 → F)) :=
  P.filter (fun q => q.rep ∈ W)

/-- (7), p. 7: the Plücker vector `(P01, P02, P03, P23, P31, P12)` of the line through `q` and `u`,
with `Pij = qᵢuⱼ − qⱼuᵢ`; the coordinates are indexed `0, …, 5` in this order. -/
def plucker (q u : Fin 4 → F) : Fin 6 → F :=
  ![q 0 * u 1 - q 1 * u 0, q 0 * u 2 - q 2 * u 0, q 0 * u 3 - q 3 * u 0,
    q 2 * u 3 - q 3 * u 2, q 3 * u 1 - q 1 * u 3, q 1 * u 2 - q 2 * u 1]

/-- (8), p. 8: the quadratic form `P01P23 + P02P31 + P03P12` whose zero set is the Klein quadric `K`. -/
def klein (L : Fin 6 → F) : F := L 0 * L 3 + L 1 * L 4 + L 2 * L 5

/-- (9), p. 8: the reciprocal product
`P01P′23 + P02P′31 + P03P′12 + P′01P23 + P′02P31 + P′03P12` of two Plücker vectors. -/
def recip (L L' : Fin 6 → F) : F :=
  L 0 * L' 3 + L 1 * L' 4 + L 2 * L' 5 + L' 0 * L 3 + L' 1 * L 4 + L' 2 * L 5

/-- The α-plane of the point `q` (p. 9): the span of the Plücker vectors of the lines through `q`. -/
noncomputable def alphaPlane (q : ℙ F (Fin 4 → F)) : Submodule F (Fin 6 → F) :=
  Submodule.span F (Set.range (plucker q.rep))

/-- The β-plane of the plane `π` (p. 9): the span of the Plücker vectors of the lines lying in `π`. -/
noncomputable def betaPlane (π : ℙ F (Fin 4 → F)) : Submodule F (Fin 6 → F) :=
  Submodule.span F {L | ∃ a b : Fin 4 → F, a ⬝ᵥ π.rep = 0 ∧ b ⬝ᵥ π.rep = 0 ∧ L = plucker a b}

/-- The hyperplane `S = {L | U₀L₀ + ⋯ + U₅L₅ = 0}` of `P⁵` defined by the covector
`U = (u : w)`, `u = (U₀, U₁, U₂)`, `w = (U₃, U₄, U₅)`. -/
def hyperplane (U : Fin 6 → F) : Submodule F (Fin 6 → F) where
  carrier := {L | U ⬝ᵥ L = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [dotProduct_add, ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq] at *
    rw [dotProduct_smul, hx, smul_zero]

/-- The covector of the hyperplane tangent to `K` at `L`: `L′ ↦ recip L L′`. -/
def polarCovector (L : Fin 6 → F) : Fin 6 → F := ![L 3, L 4, L 5, L 0, L 1, L 2]

/-- `T_L K` (p. 8): the hyperplane `{L′ | recip L L′ = 0}`, tangent to `K` at a point `L ∈ K`. -/
def tangentHyperplane (L : Fin 6 → F) : Submodule F (Fin 6 → F) := hyperplane (polarCovector L)

theorem mem_tangentHyperplane_iff (L L' : Fin 6 → F) :
    L' ∈ tangentHyperplane L ↔ recip L L' = 0 := by
  show polarCovector L ⬝ᵥ L' = 0 ↔ recip L L' = 0
  simp [polarCovector, recip, dotProduct, Fin.sum_univ_six]
  constructor <;> intro h <;> linear_combination h

/-- The hyperplane `S` with covector `U = (u : w)` is not tangent to `K` (p. 9: `u · w ≠ 0`, so
`K ∩ S` is the Klein image of a regular line complex; equivalently `U` is not in the dual Klein
quadric, p. 12). -/
def NonTangent (U : Fin 6 → F) : Prop := U 0 * U 3 + U 1 * U 4 + U 2 * U 5 ≠ 0

/-- `W` is a line of the three-quadric `G = K ∩ S`, `S` the hyperplane with covector `U`: a
2-dimensional subspace of `F⁶` inside `S` on which the Klein form vanishes. -/
def IsLineIn (U : Fin 6 → F) (W : Submodule F (Fin 6 → F)) : Prop :=
  Module.finrank F W = 2 ∧ W ≤ hyperplane U ∧ ∀ L ∈ W, klein L = 0

/-- The line of `G = K ∩ S` cut out of the α-plane of `q` by the hyperplane with covector `U`
(§4.2, p. 12). -/
noncomputable def alphaLine (U : Fin 6 → F) (q : ℙ F (Fin 4 → F)) : Submodule F (Fin 6 → F) :=
  alphaPlane q ⊓ hyperplane U

/-- The line of `G = K ∩ S` cut out of the β-plane of `π` by the hyperplane with covector `U`
(§4.2, p. 12). -/
noncomputable def betaLine (U : Fin 6 → F) (π : ℙ F (Fin 4 → F)) : Submodule F (Fin 6 → F) :=
  betaPlane π ⊓ hyperplane U

/-- `|I(Lα, Lβ)|` (Lemma 9, p. 12): the number of pairs `(l, l′) ∈ Lα × Lβ` of lines of `P⁵`
(2-dimensional subspaces of `F⁶`) that meet. -/
noncomputable def lineIncidences (A B : Finset (Submodule F (Fin 6 → F))) : ℕ :=
  ((A ×ˢ B).filter (fun x => x.1 ⊓ x.2 ≠ ⊥)).card

/-- The surface `Z(Q) ⊂ P³` of the homogeneous polynomial `Q` is ruled, in the incidence-geometric
sense: every point of `Z(Q)` lies on a line of `P³` contained in `Z(Q)`. -/
def IsRuled (Q : MvPolynomial (Fin 4) F) : Prop :=
  ∀ x : Fin 4 → F, x ≠ 0 → MvPolynomial.eval x Q = 0 →
    ∃ W : Submodule F (Fin 4 → F), Module.finrank F W = 2 ∧ x ∈ W ∧
      ∀ w ∈ W, MvPolynomial.eval w Q = 0

end RudnevIncidence.PointPlane


