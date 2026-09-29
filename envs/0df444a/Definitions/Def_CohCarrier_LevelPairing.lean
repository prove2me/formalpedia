-- Prove2me | Definitions.Def_CohCarrier_LevelPairing
-- name    : CohCarrier_LevelPairing
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/bd920423-f31c-5300-89ba-b69eeec13076
-- title:
--   Corner data, degeneracy descents and leg data
-- statement:
--   Throughout, $\mathcal{O}$ is a commutative ring, $\mathbb{T}$ a commutative $\mathcal{O}$-algebra and $V$ an $\mathcal{O}$-module with a compatible $\mathbb{T}$-action. A `CornerData` on $(\mathbb{T},V)$ consists of three pieces: an `IdempotentSplitting` of $\mathbb{T}$, i.e. a finite family of idempotents $e_0,\dots,e_{n-1}$ forming a complete orthogonal system together with maximal ideals $\mathfrak{m}_i$ exhausting all maximal ideals of $\mathbb{T}$ and satisfying $e_i \in \mathfrak{m}_j \iff i \neq j$; a chosen index `idx`; and a `LevelPairing` over the corner ring $e_{\mathrm{idx}}\mathbb{T}e_{\mathrm{idx}}$ on the corner submodule $e_{\mathrm{idx}} \cdot V$, that is an $\mathcal{O}$-bilinear form $B$ with values in $\mathcal{O}$ which is self-adjoint for the corner-ring action and perfect in the sense that $m \mapsto B(m,-)$ is bijective. The abbreviations `cornerRing` and `cornerModule` name the corner ring and corner submodule attached to the chosen index.
--
--   Given corner data $cd$ on $(\mathbb{T},V)$ and $cd'$ on $(\mathbb{T}',V')$, a `DegeneracyDescent` of length $n$ is a pair of families of $\mathcal{O}$-linear maps $\mathrm{iRaw}_k : V \to V'$ and $\mathrm{jRaw}_k : V' \to V$, $k \in \mathrm{Fin}\,n$, each carrying the chosen corner submodule into the chosen corner submodule; `iLeg` and `jLeg` are the resulting maps between the corner modules, with the evident compatibility of underlying elements recorded. The map `toLegDatum` converts such a descent, together with a table $\mathbb{T}$-valued matrix $(t_{k,k'})$ in the corner ring, a proof that each $\mathrm{jLeg}_k$ is adjoint to $\mathrm{iLeg}_k$ for the two pairings, and a proof that $\mathrm{jLeg}_k \circ \mathrm{iLeg}_{k'} = t_{k,k'}\cdot(-)$, into a `RungAssembly.LegDatum` between the two level pairings; three lemmas identify its components with the given data.
--
--   Finally `H1CornerData` specialises `CornerData` to $V =$ the $\mathcal{O}$-module $\mathrm{Hom}(\Gamma_H(M)^{\mathrm{ab,add}}, A)$ of additive characters of $\Gamma_H(M)$, the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of matrices in $\Gamma_0(M)$ whose lower-right entry reduces into $H \leq (\mathbb{Z}/M)^\times$.
--
--   **Relation to Mathlib.** The structures `CornerData`, `DegeneracyDescent` and the target `LegDatum` are the project's own; they are built on Mathlib's `CompleteOrthogonalIdempotents` and corner ring `IsIdempotentElem.Corner`, and on Mathlib's congruence subgroups $\Gamma_0(M)$, $\Gamma(M)$.
--
--   **Where it is used.** Corner data localise a Hecke algebra at a maximal ideal and equip the corresponding direct summand of degree-one group cohomology with a perfect self-adjoint pairing; degeneracy descents record the level-changing maps between two such summands. Feeding a descent through `toLegDatum` and then through the rung assembly produces the `RungDatum` whose Ihara and eta clauses are the inputs to the level-changing step of the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CohCarrier_LevelPairing.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_HeckeModule_IharaRungDatum
import Definitions.Def_HeckeModule_IharaDataAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace IharaTower

open IharaLemma

variable {𝒪 : Type} [CommRing 𝒪]

structure CornerData (𝕋 : Type) [CommRing 𝕋] [Algebra 𝒪 𝕋]
    (V : Type) [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V] : Type where
  split : IdempotentSplitting 𝕋
  idx : Fin split.n
  pairing : LevelPairing (𝒪 := 𝒪) (split.CornerRing idx)
    ↥(cornerSubmodule (M := V) (split.e idx))

namespace CornerData

variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]

abbrev cornerRing (cd : CornerData (𝒪 := 𝒪) 𝕋 V) : Type := cd.split.CornerRing cd.idx

abbrev cornerModule (cd : CornerData (𝒪 := 𝒪) 𝕋 V) : Type :=
  ↥(cornerSubmodule (M := V) (cd.split.e cd.idx))

end CornerData

variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
variable {𝕋' : Type} [CommRing 𝕋'] [Algebra 𝒪 𝕋']
variable {V' : Type} [AddCommGroup V'] [Module 𝒪 V'] [Module 𝕋' V'] [IsScalarTower 𝒪 𝕋' V']

structure DegeneracyDescent (cd : CornerData (𝒪 := 𝒪) 𝕋 V)
    (cd' : CornerData (𝒪 := 𝒪) 𝕋' V') (n : ℕ) : Type where
  iRaw : Fin n → V →ₗ[𝒪] V'
  jRaw : Fin n → V' →ₗ[𝒪] V
  corner_i : ∀ (k : Fin n) (v : V), v ∈ cornerSubmodule (M := V) (cd.split.e cd.idx) →
    iRaw k v ∈ cornerSubmodule (M := V') (cd'.split.e cd'.idx)
  corner_j : ∀ (k : Fin n) (v' : V'), v' ∈ cornerSubmodule (M := V') (cd'.split.e cd'.idx) →
    jRaw k v' ∈ cornerSubmodule (M := V) (cd.split.e cd.idx)

namespace DegeneracyDescent

variable {cd : CornerData (𝒪 := 𝒪) 𝕋 V} {cd' : CornerData (𝒪 := 𝒪) 𝕋' V'} {n : ℕ}

noncomputable def iLeg (D : DegeneracyDescent cd cd' n) (k : Fin n) :
    cd.cornerModule →ₗ[𝒪] cd'.cornerModule where
  toFun v := ⟨D.iRaw k v, D.corner_i k v v.2⟩
  map_add' := by intro a b; apply Subtype.ext; simp
  map_smul' := by intro r a; apply Subtype.ext; simp

noncomputable def jLeg (D : DegeneracyDescent cd cd' n) (k : Fin n) :
    cd'.cornerModule →ₗ[𝒪] cd.cornerModule where
  toFun v' := ⟨D.jRaw k v', D.corner_j k v' v'.2⟩
  map_add' := by intro a b; apply Subtype.ext; simp
  map_smul' := by intro r a; apply Subtype.ext; simp

@[simp] theorem iLeg_apply (D : DegeneracyDescent cd cd' n) (k : Fin n)
    (v : cd.cornerModule) : (↑(D.iLeg k v) : V') = D.iRaw k ↑v := rfl

@[simp] theorem jLeg_apply (D : DegeneracyDescent cd cd' n) (k : Fin n)
    (v' : cd'.cornerModule) : (↑(D.jLeg k v') : V) = D.jRaw k ↑v' := rfl

noncomputable def toLegDatum (D : DegeneracyDescent cd cd' n)
    (table : Fin n → Fin n → cd.cornerRing)
    (adjoint_leg : ∀ (k : Fin n) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B (D.jLeg k m') m = cd'.pairing.B m' (D.iLeg k m))
    (htable : ∀ (k k' : Fin n) (m : cd.cornerModule),
      D.jLeg k (D.iLeg k' m) = table k k' • m) :
    RungAssembly.LegDatum (𝒪 := 𝒪) cd.pairing cd'.pairing n :=
  ⟨D.iLeg, D.jLeg, adjoint_leg, table, htable⟩

theorem toLegDatum_iLeg (D : DegeneracyDescent cd cd' n) (table : Fin n → Fin n → cd.cornerRing)
    (adjoint_leg : ∀ (k : Fin n) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B (D.jLeg k m') m = cd'.pairing.B m' (D.iLeg k m))
    (htable : ∀ (k k' : Fin n) (m : cd.cornerModule),
      D.jLeg k (D.iLeg k' m) = table k k' • m) :
    (D.toLegDatum table adjoint_leg htable).iLeg = D.iLeg := rfl

theorem toLegDatum_jLeg (D : DegeneracyDescent cd cd' n) (table : Fin n → Fin n → cd.cornerRing)
    (adjoint_leg : ∀ (k : Fin n) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B (D.jLeg k m') m = cd'.pairing.B m' (D.iLeg k m))
    (htable : ∀ (k k' : Fin n) (m : cd.cornerModule),
      D.jLeg k (D.iLeg k' m) = table k k' • m) :
    (D.toLegDatum table adjoint_leg htable).jLeg = D.jLeg := rfl

theorem toLegDatum_table (D : DegeneracyDescent cd cd' n) (table : Fin n → Fin n → cd.cornerRing)
    (adjoint_leg : ∀ (k : Fin n) (m' : cd'.cornerModule) (m : cd.cornerModule),
      cd.pairing.B (D.jLeg k m') m = cd'.pairing.B m' (D.iLeg k m))
    (htable : ∀ (k k' : Fin n) (m : cd.cornerModule),
      D.jLeg k (D.iLeg k' m) = table k k' • m) :
    (D.toLegDatum table adjoint_leg htable).table = table := rfl

end DegeneracyDescent

open CohCarrier in

abbrev H1CornerData (M : ℕ) (H : Subgroup (ZMod M)ˣ) (A : Type) [AddCommGroup A] [Module 𝒪 A]
    (𝕋 : Type) [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M H A)]
    [IsScalarTower 𝒪 𝕋 (H1 M H A)] : Type :=
  CornerData (𝒪 := 𝒪) 𝕋 (H1 M H A)

end IharaTower


