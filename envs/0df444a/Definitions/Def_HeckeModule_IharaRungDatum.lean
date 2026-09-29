-- Prove2me | Definitions.Def_HeckeModule_IharaRungDatum
-- name    : HeckeModule_IharaRungDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/74373ae9-bea7-529e-9249-1bb1caf1f750
-- title:
--   Level pairings, rung data and leg-assembled degeneracy maps
-- statement:
--   Over a commutative base ring $\mathcal{O}$, a `LevelPairing` on an $\mathcal{O}$-algebra $T$ acting on an $\mathcal{O}$-module $M$ (with the scalar actions compatible) is a structure carrying an $\mathcal{O}$-bilinear form $B : M \times M \to \mathcal{O}$, presented as an iterated linear map, together with two fields asserted as axioms: self-adjointness of every Hecke scalar, $B(t\cdot m, n) = B(m, t\cdot n)$ for $t \in T$, and perfectness in the strong sense that the induced map $M \to \operatorname{Hom}_{\mathcal{O}}(M,\mathcal{O})$ is bijective.
--
--   A `RungDatum` relates two such paired levels $(T,M,P)$ and $(T',M',P')$. Its data are an $\mathcal{O}$-algebra map $\mathrm{res} : T' \to T$, $\mathcal{O}$-linear maps $i : M \to M'$ and $j : M' \to M$, and an element $\Delta \in T$, subject to two axioms: $i$ and $j$ are adjoint for the two pairings, $P.B(j m', m) = P'.B(m', i m)$, and $j \circ i$ is multiplication by $\Delta$ on $M$. No axiom of the structure links $\mathrm{res}$ to $i$, $j$ or $\Delta$.
--
--   Two predicates are attached to a datum and $\mathcal{O}$-algebra points. `IharaClauseAt` $(\pi_T, \pi_{T'})$ says that $i$ carries the $\mathcal{O}$-submodule of $M$ annihilated by $\ker \pi_T$ exactly onto the submodule of $M'$ annihilated by $\ker \pi_{T'}$. `EtaClauseAt` $(\pi_T, c)$ says that $\pi_T(\Delta)$ and $c$ generate the same principal ideal of $\mathcal{O}$.
--
--   The assembly part fixes $n$ degeneracy legs: a `LegDatum` consists of families $i_k : M \to M'$, $j_k : M' \to M$ with per-leg adjointness and a table $t_{k,k'} \in T$ with $j_k \circ i_{k'} = t_{k,k'}\cdot \mathrm{id}$. For a coefficient vector $c : \mathrm{Fin}\,n \to T$ one forms $i_c = \sum_k i_k \circ c_k$, $j_c = \sum_k c_k \circ j_k$ and $\Delta_c = \sum_{k,k'} c_k t_{k,k'} c_{k'}$, the quadratic form of the table; `rungDatumOfLegs` packages these, together with a chosen $\mathrm{res}$, into a `RungDatum`. A helper turns multiplication by $t \in T$ into an $\mathcal{O}$-linear endomorphism of $M$.
--
--   **Relation to Mathlib.** The structures `LevelPairing`, `RungDatum` and `LegDatum`, and the two clauses, are the project's own; Mathlib has no notion of Hecke level pairing or degeneracy datum. The torsion submodules in `IharaClauseAt` are Mathlib's `Submodule.torsionBySet` (elements killed by every member of a given set of scalars), with scalars restricted to $\mathcal{O}$, and perfectness is phrased as bijectivity of the induced map into the $\mathcal{O}$-dual rather than through Mathlib's perfect-pairing predicates.
--
--   **Where it is used.** These data axiomatise the formal input of the level-raising and congruence-ideal arguments: degeneracy maps between Hecke modules at two levels, adjoint for perfect Hecke-equivariant pairings, with the composite $j \circ i$ given by a Hecke element whose image at a point controls the $\eta$-invariant. The `IharaClauseAt` and `EtaClauseAt` predicates are the two conclusions a rung of the tower is required to supply in the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_HeckeModule_IharaRungDatum.lean

import Mathlib.Algebra.Module.Torsion.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace IharaTower

variable {𝒪 : Type} [CommRing 𝒪]

structure LevelPairing (T : Type) [CommRing T] [Algebra 𝒪 T]
    (M : Type) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M] where
  B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪
  selfAdjoint : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n)
  perfect : Function.Bijective B

structure RungDatum (T : Type) [CommRing T] [Algebra 𝒪 T]
    (T' : Type) [CommRing T'] [Algebra 𝒪 T']
    (M : Type) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    (M' : Type) [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
    (P : LevelPairing (𝒪 := 𝒪) T M) (P' : LevelPairing (𝒪 := 𝒪) T' M') where
  res : T' →ₐ[𝒪] T
  i : M →ₗ[𝒪] M'
  j : M' →ₗ[𝒪] M
  Δ : T
  adjoint : ∀ (m' : M') (m : M), P.B (j m') m = P'.B m' (i m)
  comp_eq_smul : ∀ m : M, j (i m) = Δ • m

section Clauses

variable {T : Type} [CommRing T] [Algebra 𝒪 T]
  {T' : Type} [CommRing T'] [Algebra 𝒪 T']
  {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
  {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}

def IharaClauseAt (D : RungDatum T T' M M' P P')
    (πT : T →ₐ[𝒪] 𝒪) (πT' : T' →ₐ[𝒪] 𝒪) : Prop :=
  Submodule.map D.i ((Submodule.torsionBySet T M ↑(RingHom.ker πT)).restrictScalars 𝒪) =
    (Submodule.torsionBySet T' M' ↑(RingHom.ker πT')).restrictScalars 𝒪

def EtaClauseAt (D : RungDatum T T' M M' P P') (πT : T →ₐ[𝒪] 𝒪) (c : 𝒪) : Prop :=
  Ideal.span {πT D.Δ} = Ideal.span {c}

end Clauses

namespace RungAssembly

variable {T : Type} [CommRing T] [Algebra 𝒪 T]
  {T' : Type} [CommRing T'] [Algebra 𝒪 T']
  {M : Type} [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
  {M' : Type} [AddCommGroup M'] [Module T' M'] [Module 𝒪 M'] [IsScalarTower 𝒪 T' M']
  {P : LevelPairing (𝒪 := 𝒪) T M} {P' : LevelPairing (𝒪 := 𝒪) T' M'}

def smulLinear (t : T) : M →ₗ[𝒪] M where
  toFun m := t • m
  map_add' := smul_add t
  map_smul' a m := by
    simp only [RingHom.id_apply]
    rw [← algebraMap_smul (A := T) (M := M) a m, ← algebraMap_smul (A := T) (M := M) a (t • m),
      smul_smul, smul_smul, mul_comm]

@[simp] lemma smulLinear_apply (t : T) (m : M) : smulLinear (𝒪 := 𝒪) t m = t • m := rfl

variable (P P') in

structure LegDatum (n : ℕ) where
  iLeg : Fin n → (M →ₗ[𝒪] M')
  jLeg : Fin n → (M' →ₗ[𝒪] M)
  adjoint_leg : ∀ (k : Fin n) (m' : M') (m : M), P.B (jLeg k m') m = P'.B m' (iLeg k m)
  table : Fin n → Fin n → T
  htable : ∀ (k k' : Fin n) (m : M), jLeg k (iLeg k' m) = table k k' • m

variable {n : ℕ}

def iComb (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T) : M →ₗ[𝒪] M' :=
  ∑ k, (L.iLeg k).comp (smulLinear (c k))

def jComb (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T) : M' →ₗ[𝒪] M :=
  ∑ k, (smulLinear (c k)).comp (L.jLeg k)

def deltaComb (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T) : T :=
  ∑ k, ∑ k', c k * L.table k k' * c k'

def rungDatumOfLegs (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) : RungDatum (𝒪 := 𝒪) T T' M M' P P' where
  res := res
  i := iComb L c
  j := jComb L c
  Δ := deltaComb L c
  adjoint := by
    intro m' m
    simp only [iComb, jComb, LinearMap.sum_apply, LinearMap.comp_apply, smulLinear_apply,
      map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [P.selfAdjoint, L.adjoint_leg]
  comp_eq_smul := by
    intro m
    simp only [iComb, jComb, LinearMap.sum_apply, LinearMap.comp_apply, smulLinear_apply,
      map_sum, deltaComb, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [L.htable, smul_smul, smul_smul]

@[simp] lemma rungDatumOfLegs_res (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) : (rungDatumOfLegs L c res).res = res := rfl

@[simp] lemma rungDatumOfLegs_i (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) : (rungDatumOfLegs L c res).i = iComb L c := rfl

@[simp] lemma rungDatumOfLegs_j (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) : (rungDatumOfLegs L c res).j = jComb L c := rfl

@[simp] lemma rungDatumOfLegs_Δ (L : LegDatum (𝒪 := 𝒪) P P' n) (c : Fin n → T)
    (res : T' →ₐ[𝒪] T) : (rungDatumOfLegs L c res).Δ = deltaComb L c := rfl

end RungAssembly

end IharaTower


