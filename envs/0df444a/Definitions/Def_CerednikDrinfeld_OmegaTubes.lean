-- Prove2me | Definitions.Def_CerednikDrinfeld_OmegaTubes
-- name    : CerednikDrinfeld_OmegaTubes
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/df639976-4322-507d-96a0-08bbb401c2e1
-- title:
--   Vertex and edge tubes in the Drinfeld upper half-plane
-- statement:
--   Throughout, $K_0$ is a field, $K$ a valued field extension of it with value group $\Gamma_0$, and $\varpi$ a pseudo-uniformiser, i.e. an element $\varpi \in K_0$ whose image in $K$ satisfies $0 < v(\varpi) < 1$ together with the scaling condition that every nonzero $a \in K_0$ has $v(\varpi)^N \le v(a) \le v(\varpi)^{-N}$ for some $N$. Here $\Omega =$ `upperHalfPlane K₀ K` is the complement in $K$ of the image of $K_0$, and `affinoid ϖ n` is the set of $z$ with $v(z) \le v(\varpi)^{-n}$ and $v(\varpi)^{n} \le v(z-a)$ for every $a \in K_0$ with $v(a) \le v(\varpi)^{-n}$; at $n = 0$ both bounds are $1$.
--
--   Three sets are defined. `stdEdgeTube ϖ` consists of the $z \in \Omega$ lying in the open annulus $v(\varpi) < v(z) < 1$. For $g \in \mathrm{PGL}_2(K_0)$, `vertexTube ϖ g` consists of the $z \in \Omega$ with $g^{-1}z \in$ `affinoid ϖ 0`, and `edgeTube ϖ g` of the $z \in \Omega$ with $g^{-1}z \in$ `stdEdgeTube ϖ`, the action being by the projective Möbius map `pmoebius`. The accompanying lemmas record the membership criteria, that all three sets lie in $\Omega$, and that at $g = 1$ one recovers `affinoid ϖ 0` and `stdEdgeTube ϖ` respectively (for the vertex tube, membership in $\Omega$ is automatic on the level-$0$ affinoid).
--
--   The remaining results concern `IsometricAut K₀ K`, the group of ring automorphisms $s$ of $K$ with $v(s x) = v(x)$ for all $x$ and $s$ fixing the image of $K_0$ pointwise: each such $s$ maps `stdEdgeTube ϖ`, `vertexTube ϖ g` and `edgeTube ϖ g` into themselves, and since the inverse of $s$ is again such an automorphism, $s(z)$ lies in a vertex or edge tube precisely when $z$ does.
--
--   **Relation to Mathlib.** Mathlib has no Drinfeld upper half-plane, affinoid subdomains or tubes; these are the project's own notions, built on Mathlib's valued fields, `Set.MapsTo` and the projective general linear group.
--
--   **Where it is used.** These sets provide the vocabulary for the reduction dictionary of the Mumford–Čerednik–Drinfeld uniformisation: vertex tubes are the prospective chart domains of the covering of $\Gamma \backslash \Omega$ and edge tubes the annuli glueing them, with the $\mathrm{PGL}_2(K_0)$-translation indexing matching that of vertices and edges of the Bruhat–Tits tree. The invariance statements under isometric automorphisms of $K$ fixing $K_0$ are what allows the tubes, and hence the reduction data, to be compared with their Galois conjugates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_OmegaTubes.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups
open CerednikDrinfeld.Omega

namespace CerednikDrinfeld.Omega

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

def stdEdgeTube : Set K :=
  {z | z ∈ upperHalfPlane K₀ K ∧ Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v z ∧ Valued.v z < 1}

omit [DecidableEq K] in
theorem mem_stdEdgeTube_iff (z : K) : z ∈ stdEdgeTube ϖ ↔
    z ∈ upperHalfPlane K₀ K ∧ Valued.v (algebraMap K₀ K ϖ.ϖ) < Valued.v z ∧ Valued.v z < 1 := Iff.rfl

omit [DecidableEq K] in
theorem stdEdgeTube_subset_upperHalfPlane : stdEdgeTube ϖ ⊆ upperHalfPlane K₀ K := fun _ h => h.1

def vertexTube (g : PGL(2, K₀)) : Set K :=
  {z | z ∈ upperHalfPlane K₀ K ∧ pmoebius K₀ g⁻¹ z ∈ affinoid ϖ 0}

def edgeTube (g : PGL(2, K₀)) : Set K :=
  {z | z ∈ upperHalfPlane K₀ K ∧ pmoebius K₀ g⁻¹ z ∈ stdEdgeTube ϖ}

theorem mem_vertexTube_iff (g : PGL(2, K₀)) (z : K) :
    z ∈ vertexTube ϖ g ↔ z ∈ upperHalfPlane K₀ K ∧ pmoebius K₀ g⁻¹ z ∈ affinoid ϖ 0 := Iff.rfl

theorem mem_edgeTube_iff (g : PGL(2, K₀)) (z : K) :
    z ∈ edgeTube ϖ g ↔ z ∈ upperHalfPlane K₀ K ∧ pmoebius K₀ g⁻¹ z ∈ stdEdgeTube ϖ := Iff.rfl

theorem vertexTube_subset_upperHalfPlane (g : PGL(2, K₀)) : vertexTube ϖ g ⊆ upperHalfPlane K₀ K := fun _ h => h.1

theorem edgeTube_subset_upperHalfPlane (g : PGL(2, K₀)) : edgeTube ϖ g ⊆ upperHalfPlane K₀ K := fun _ h => h.1

theorem vertexTube_one : vertexTube ϖ (1 : PGL(2, K₀)) = affinoid ϖ 0 := by
  ext z
  simp only [mem_vertexTube_iff, inv_one, pmoebius_one]
  exact ⟨fun h => h.2, fun h => ⟨affinoid_subset_upperHalfPlane ϖ 0 h, h⟩⟩

theorem edgeTube_one : edgeTube ϖ (1 : PGL(2, K₀)) = stdEdgeTube ϖ := by
  ext z
  simp only [mem_edgeTube_iff, inv_one, pmoebius_one]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

namespace IsometricAut

omit [DecidableEq K] in

theorem mapsTo_stdEdgeTube (s : IsometricAut K₀ K) : Set.MapsTo s.toRingEquiv (stdEdgeTube ϖ) (stdEdgeTube ϖ) := by
  rintro z ⟨hz, h1, h2⟩
  refine ⟨s.mapsTo_upperHalfPlane hz, ?_, ?_⟩
  · rw [s.isometry]; exact h1
  · rw [s.isometry]; exact h2

theorem mapsTo_vertexTube (s : IsometricAut K₀ K) (g : PGL(2, K₀)) :
    Set.MapsTo s.toRingEquiv (vertexTube ϖ g) (vertexTube ϖ g) := by
  rintro z ⟨hz, hg⟩
  refine ⟨s.mapsTo_upperHalfPlane hz, ?_⟩
  rw [← s.comm_pmoebius g⁻¹ hz]
  exact s.mapsTo_affinoid ϖ 0 hg

theorem mapsTo_edgeTube (s : IsometricAut K₀ K) (g : PGL(2, K₀)) :
    Set.MapsTo s.toRingEquiv (edgeTube ϖ g) (edgeTube ϖ g) := by
  rintro z ⟨hz, hg⟩
  refine ⟨s.mapsTo_upperHalfPlane hz, ?_⟩
  rw [← s.comm_pmoebius g⁻¹ hz]
  exact s.mapsTo_stdEdgeTube ϖ hg

theorem mem_vertexTube_iff_mem (s : IsometricAut K₀ K) (g : PGL(2, K₀)) (z : K) :
    s.toRingEquiv z ∈ vertexTube ϖ g ↔ z ∈ vertexTube ϖ g := by
  refine ⟨fun h => ?_, fun h => s.mapsTo_vertexTube ϖ g h⟩
  have := (s⁻¹).mapsTo_vertexTube ϖ g h
  simpa [inv_toRingEquiv] using this

theorem mem_edgeTube_iff_mem (s : IsometricAut K₀ K) (g : PGL(2, K₀)) (z : K) :
    s.toRingEquiv z ∈ edgeTube ϖ g ↔ z ∈ edgeTube ϖ g := by
  refine ⟨fun h => ?_, fun h => s.mapsTo_edgeTube ϖ g h⟩
  have := (s⁻¹).mapsTo_edgeTube ϖ g h
  simpa [inv_toRingEquiv] using this

end IsometricAut

end CerednikDrinfeld.Omega

end


