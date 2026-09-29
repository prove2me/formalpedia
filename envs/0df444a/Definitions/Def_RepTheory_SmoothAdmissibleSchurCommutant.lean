-- Prove2me | Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
-- name    : RepTheory_SmoothAdmissibleSchurCommutant
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/d1545173-3e9c-5f13-859b-63cbe29a02f3
-- title:
--   Smooth admissible representations and a Schur-type commutant theorem
-- statement:
--   The setting is a field $k$, a group $G$, a $k$-vector space $V$ and a monoid homomorphism $\pi : G \to \mathrm{End}_k(V)$ (the same data as a representation of $G$ on $V$). For a subgroup $K \le G$, `fixedVectors` is the $k$-submodule $\{v \in V : \pi(u)v = v \text{ for all } u \in K\}$; for a vector $v$, `repStabilizer` is the subgroup $\{g \in G : \pi(g)v = v\}$. Three predicates are introduced. `IsIrreducibleRep` asserts that $V$ contains a non-zero vector and that every $k$-submodule $W$ with $\pi(g)W \subseteq W$ for all $g$ is $\bot$ or $\top$. With a topology on $G$, `IsSmoothRep` asserts that the stabiliser of every vector of $V$ is open as a subset of $G$, and `IsAdmissibleRep` asserts that for every subgroup $K$ whose underlying set is both compact and open, the space of $K$-fixed vectors is finite-dimensional over $k$. Note that smoothness and admissibility are formulated purely through these conditions on subgroups of $G$, with no topology on $V$.
--
--   The accompanying results form a Schur-type statement. An endomorphism $T$ commuting with every $\pi(g)$ preserves $K$-fixed vectors. If $k$ is algebraically closed, $\pi$ is irreducible, $T$ commutes with the image of $\pi$, and some non-zero vector is fixed by a subgroup $K$ with finite-dimensional space of $K$-fixed vectors, then $T = c \cdot \mathrm{id}$ for some $c \in k$; the scalar is unique as soon as $V \neq 0$. Under separate continuity of multiplication on $G$, existence of one compact open subgroup, and smoothness, admissibility and irreducibility of $\pi$, the same conclusion follows for all commuting $T$, the set of such $T$ is exactly the set of scalar operators, and the centraliser of the range of $\pi$ inside the $k$-algebra $\mathrm{End}_k(V)$ is $\bot$, i.e. the image of $k$.
--
--   **Relation to Mathlib.** Mathlib has no notions of smooth or admissible representation, nor of this irreducibility predicate (which is stated directly in terms of $\pi$-stable submodules rather than via `IsSimpleModule`); these are the project's own. The representation itself is taken in the shape `G →* Module.End k V` used by Mathlib's representations, and the finite-dimensionality, compactness and openness conditions are Mathlib's.
--
--   **Where it is used.** These definitions supply the Schur-type input needed for the representation-theoretic side of the argument, where endomorphisms commuting with a smooth admissible irreducible representation of a locally profinite group (such as $\mathrm{GL}_2$ over a local field, or an adelic group) must be scalars.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_RepTheory_SmoothAdmissibleSchurCommutant.lean

import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Prod
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace FLT.SmoothAdmissibleSchurCommutant

section FixedVectors

universe u v w

variable {k : Type u} [Field k] {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

variable (π : G →* Module.End k V)

def fixedVectors (K : Subgroup G) : Submodule k V where
  carrier := {v : V | ∀ u ∈ K, π u v = v}
  add_mem' := by
    intro a b ha hb u hu
    rw [map_add, ha u hu, hb u hu]
  zero_mem' := by
    intro u hu
    rw [map_zero]
  smul_mem' := by
    intro c v hv u hu
    rw [map_smul, hv u hu]

@[simp] theorem mem_fixedVectors {K : Subgroup G} {v : V} :
    v ∈ fixedVectors π K ↔ ∀ u ∈ K, π u v = v := Iff.rfl

theorem apply_mem_fixedVectors_of_commute {T : Module.End k V}
    (hT : ∀ g : G, π g * T = T * π g) {K : Subgroup G} {x : V}
    (hx : x ∈ fixedVectors π K) : T x ∈ fixedVectors π K := by
  intro u hu
  have h1 : π u (T x) = T (π u x) := by
    have h := congrArg (fun S : Module.End k V => S x) (hT u)
    simpa [Module.End.mul_apply] using h
  rw [h1, hx u hu]

def repStabilizer (v : V) : Subgroup G where
  carrier := {g : G | π g v = v}
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha]
    _ = π (a⁻¹ * a) v := by rw [map_mul, Module.End.mul_apply]
    _ = v := by rw [inv_mul_cancel, map_one, Module.End.one_apply]

@[simp] theorem mem_repStabilizer {v : V} {g : G} :
    g ∈ repStabilizer π v ↔ π g v = v := Iff.rfl

end FixedVectors

section Predicates

universe u v w

variable {k : Type u} [Field k] {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

variable (π : G →* Module.End k V)

def IsIrreducibleRep : Prop :=
  (∃ v : V, v ≠ 0) ∧
    ∀ W : Submodule k V,
      (∀ (g : G) (v : V), v ∈ W → π g v ∈ W) → W = ⊥ ∨ W = ⊤

variable [TopologicalSpace G]

def IsSmoothRep : Prop :=
  ∀ v : V, IsOpen ((repStabilizer π v : Subgroup G) : Set G)

def IsAdmissibleRep : Prop :=
  ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
    FiniteDimensional k (fixedVectors π K)

end Predicates

section Master

universe u v w

variable {k : Type u} [Field k] {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

variable (π : G →* Module.End k V)

theorem exists_forall_eq_smul_of_commute_of_fixed [IsAlgClosed k]
    (hirr : IsIrreducibleRep π) {T : Module.End k V}
    (hcomm : ∀ g : G, π g * T = T * π g)
    {K : Subgroup G} {v : V} (hv : v ≠ 0) (hvK : ∀ u ∈ K, π u v = v)
    (hfd : FiniteDimensional k (fixedVectors π K)) :
    ∃ c : k, ∀ x : V, T x = c • x := by
  classical
  haveI : FiniteDimensional k (fixedVectors π K) := hfd

  have hvmem : v ∈ fixedVectors π K := hvK
  haveI : Nontrivial (fixedVectors π K) := by
    refine nontrivial_of_ne ⟨v, hvmem⟩ 0 ?_
    intro h
    exact hv (by simpa using congrArg Subtype.val h)

  have hres : ∀ x ∈ fixedVectors π K, T x ∈ fixedVectors π K := fun x hx =>
    apply_mem_fixedVectors_of_commute π hcomm hx

  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hres)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw_ne : w ≠ 0 := hw.2
  have hw_eq : (T.restrict hres) w = c • w := hw.apply_eq_smul

  have hwV : T (w : V) = c • (w : V) := by
    have h := congrArg Subtype.val hw_eq
    rw [LinearMap.coe_restrict_apply] at h
    simpa using h
  have hwV_ne : (w : V) ≠ 0 := by
    intro h
    exact hw_ne (Subtype.ext (by simpa using h))

  refine ⟨c, ?_⟩
  set E : Submodule k V := LinearMap.ker (T - c • (1 : Module.End k V)) with hE
  have hmemE : ∀ x : V, x ∈ E ↔ T x = c • x := by
    intro x
    rw [hE, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Module.End.one_apply, sub_eq_zero]
  have hEinv : ∀ (g : G) (x : V), x ∈ E → π g x ∈ E := by
    intro g x hx
    rw [hmemE] at hx ⊢
    have h1 : T (π g x) = π g (T x) := by
      have h := congrArg (fun S : Module.End k V => S x) (hcomm g)
      simpa [Module.End.mul_apply] using h.symm
    rw [h1, hx, map_smul]
  have hEne : E ≠ ⊥ := by
    intro h
    have hwE : (w : V) ∈ E := (hmemE _).mpr hwV
    rw [h, Submodule.mem_bot] at hwE
    exact hwV_ne hwE
  have hEtop : E = ⊤ := (hirr.2 E hEinv).resolve_left hEne
  intro x
  exact (hmemE x).mp (hEtop ▸ Submodule.mem_top)

theorem exists_eq_smul_one_of_commute_of_fixed [IsAlgClosed k]
    (hirr : IsIrreducibleRep π) {T : Module.End k V}
    (hcomm : ∀ g : G, π g * T = T * π g)
    {K : Subgroup G} {v : V} (hv : v ≠ 0) (hvK : ∀ u ∈ K, π u v = v)
    (hfd : FiniteDimensional k (fixedVectors π K)) :
    ∃ c : k, T = c • (1 : Module.End k V) := by
  obtain ⟨c, hc⟩ := exists_forall_eq_smul_of_commute_of_fixed π hirr hcomm hv hvK hfd
  refine ⟨c, ?_⟩
  ext x
  simpa [LinearMap.smul_apply, Module.End.one_apply] using hc x

theorem smul_one_injective_of_exists_ne_zero (hV : ∃ v : V, v ≠ 0) {a b : k}
    (h : a • (1 : Module.End k V) = b • (1 : Module.End k V)) : a = b := by
  obtain ⟨v, hv⟩ := hV
  have h1 : a • v = b • v := by
    have := congrArg (fun S : Module.End k V => S v) h
    simpa [LinearMap.smul_apply, Module.End.one_apply] using this
  have h2 : (a - b) • v = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 hv

end Master

section Topological

universe u v w

variable {k : Type u} [Field k] {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

variable (π : G →* Module.End k V)

variable [TopologicalSpace G]

theorem exists_eq_smul_one_of_forall_isCompactOpen_fixed [IsAlgClosed k]
    (hsm : ∀ v : V, v ≠ 0 → ∃ K : Subgroup G,
      IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ ∀ u ∈ K, π u v = v)
    (hadm : IsAdmissibleRep π) (hirr : IsIrreducibleRep π)
    {T : Module.End k V} (hcomm : ∀ g : G, π g * T = T * π g) :
    ∃ c : k, T = c • (1 : Module.End k V) := by
  obtain ⟨v, hv⟩ := hirr.1
  obtain ⟨K, hKc, hKo, hKfix⟩ := hsm v hv
  exact exists_eq_smul_one_of_commute_of_fixed π hirr hcomm hv hKfix (hadm K hKc hKo)

theorem exists_eq_smul_one_of_smooth_admissible [IsAlgClosed k] [SeparatelyContinuousMul G]
    (hK₀ : ∃ K₀ : Subgroup G, IsCompact (K₀ : Set G) ∧ IsOpen (K₀ : Set G))
    (hsm : IsSmoothRep π) (hadm : IsAdmissibleRep π) (hirr : IsIrreducibleRep π)
    {T : Module.End k V} (hcomm : ∀ g : G, π g * T = T * π g) :
    ∃ c : k, T = c • (1 : Module.End k V) := by
  refine exists_eq_smul_one_of_forall_isCompactOpen_fixed π ?_ hadm hirr hcomm
  intro v _
  obtain ⟨K₀, hK₀c, hK₀o⟩ := hK₀
  refine ⟨K₀ ⊓ repStabilizer π v, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    exact hK₀c.inter_right ((repStabilizer π v).isClosed_of_isOpen (hsm v))
  · rw [Subgroup.coe_inf]
    exact hK₀o.inter (hsm v)
  · intro u hu
    exact (Subgroup.mem_inf.mp hu).2

theorem exists_forall_eq_smul_of_smooth_admissible [IsAlgClosed k] [SeparatelyContinuousMul G]
    (hK₀ : ∃ K₀ : Subgroup G, IsCompact (K₀ : Set G) ∧ IsOpen (K₀ : Set G))
    (hsm : IsSmoothRep π) (hadm : IsAdmissibleRep π) (hirr : IsIrreducibleRep π)
    {T : Module.End k V} (hcomm : ∀ g : G, π g * T = T * π g) :
    ∃ c : k, ∀ x : V, T x = c • x := by
  obtain ⟨c, hc⟩ :=
    exists_eq_smul_one_of_smooth_admissible π hK₀ hsm hadm hirr hcomm
  exact ⟨c, fun x => by
    rw [hc]
    simp [LinearMap.smul_apply, Module.End.one_apply]⟩

theorem commutant_setOf_eq_range_smul_one [IsAlgClosed k] [SeparatelyContinuousMul G]
    (hK₀ : ∃ K₀ : Subgroup G, IsCompact (K₀ : Set G) ∧ IsOpen (K₀ : Set G))
    (hsm : IsSmoothRep π) (hadm : IsAdmissibleRep π) (hirr : IsIrreducibleRep π) :
    {T : Module.End k V | ∀ g : G, π g * T = T * π g} =
      Set.range (fun c : k => c • (1 : Module.End k V)) := by
  ext T
  constructor
  · intro hT
    obtain ⟨c, hc⟩ := exists_eq_smul_one_of_smooth_admissible π hK₀ hsm hadm hirr hT
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, rfl⟩ g
    simp

theorem centralizer_range_eq_bot [IsAlgClosed k] [SeparatelyContinuousMul G]
    (hK₀ : ∃ K₀ : Subgroup G, IsCompact (K₀ : Set G) ∧ IsOpen (K₀ : Set G))
    (hsm : IsSmoothRep π) (hadm : IsAdmissibleRep π) (hirr : IsIrreducibleRep π) :
    Subalgebra.centralizer k (Set.range fun g : G => (π g : Module.End k V)) = ⊥ := by
  apply le_antisymm
  · intro T hT
    rw [Subalgebra.mem_centralizer_iff] at hT
    have hcomm : ∀ g : G, π g * T = T * π g := fun g => hT (π g) ⟨g, rfl⟩
    obtain ⟨c, hc⟩ := exists_eq_smul_one_of_smooth_admissible π hK₀ hsm hadm hirr hcomm
    rw [Algebra.mem_bot]
    refine ⟨c, ?_⟩
    rw [Module.algebraMap_end_eq_smul_id, hc]
    rfl
  · exact bot_le

end Topological

end FLT.SmoothAdmissibleSchurCommutant


