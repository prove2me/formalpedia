-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumCongruence
-- name    : OddOrder_GroupTheory_RepresentationTheory_ClassSumCongruence
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:49:28.834191+00:00
-- url     : https://prove2.me/theorems/63b1f14b-c81c-4f0d-a05c-97c30898bf03
-- title:
--   Class-sum congruences and central characters (Peterfalvi (6.7.1)–(6.7.2))
-- statement:
--   Develops the central character $\omega_\rho:Z(\mathbb{C}[G])\to\mathbb{C}$ of an irreducible complex representation and the congruences between class sums used in Peterfalvi (6.7): the fixed-point-free hypothesis (6.7.1) in the Sylow/TI set-up, and the product rule modulo $|P|$ (6.7.2), including its geometric form for a TI-subset. Also shown are algebraic integrality of central-character values (Isaacs (3.7)) and constancy of central-character values under TI hypotheses.
--
--   Main definitions: `centralCharacterOfRep` (the central character attached to an irreducible representation) and `nonidentityZClassCoeffSum` (the nonidentity part of the class-sum product coefficient over classes meeting $Z$).
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ClassSumCongruence.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ClassSumCongruence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_TISubset
import Definitions.Def_OddOrder_Algebra_AlgInt
import Definitions.Def_OddOrder_GroupTheory_FreeActionOrbitCount
import Definitions.Def_OddOrder_GroupTheory_ConjClassSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_AbsolutelyIrreducible
import Definitions.Def_OddOrder_GroupTheory_ConjClassCardinality
import Definitions.Def_OddOrder_Mathlib_Sylow
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumSections
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.RationalRoot

namespace OddOrder.RepresentationTheory

open scoped MonoidAlgebra

open OddOrder.GroupTheory.CenterClassSum

open Module (finrank)

open Representation

variable {G : Type*} [Group G]

section FixedPointFree

open OddOrder.GroupTheory

/-- **Peterfalvi (6.7.1)** (fixed-point-free hypothesis).  Setup of (6.7): `P` a Sylow `p`-subgroup
of the finite group `G`, `L = N_G(P)`, `P^# = P ∖ {1}` a TI-subset of `G` (with normalizer-bound
`L`), and `Z ≤ P` a subgroup that is *normal in* `L`.  Suppose the conjugacy classes satisfy
`C_i ∩ Z^# ≠ ∅`, `C_j ∩ Z^# ≠ ∅`, and `C_s ∩ Z = ∅`.

Then `P` acts *fixed-point-freely* by conjugation on `Ω = {(u,v) ∈ C_i × C_j ∣ u·v ∈ C_s}`:
no `x ∈ P` with `x ≠ 1` fixes a pair of `Ω`.

The argument is Peterfalvi's: if `x ∈ P^#` fixes `(u, v)`, then `x` centralizes both `u` and `v`,
so `u, v ∈ C_G(x) ⊆ L` (because `P^#` is TI and `x ∈ P^#` is centralized, so any centralizing
element conjugates `x ∈ P^#` to itself, landing in `L`).  Each of `u, v` is a `p`-element (it is
`G`-conjugate to a nontrivial element of `Z ≤ P`, a `p`-group), hence lies in `P`
(`mem_sylow_of_mem_normalizer_of_isPGroup`).  The same conjugacy carries `u` (resp. `v`) into `Z^#`
by an element of `L` (TI again), and `Z ⊴ L` forces `u, v ∈ Z`; then `u·v ∈ Z`, contradicting
`C_s ∩ Z = ∅`. -/
theorem fixedPointFree_classPair_of_isTISubset {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {Z : Subgroup G} (hZP : Z ≤ (P : Subgroup G))
    (hZnormal : (Z.subgroupOf (Subgroup.normalizer (P : Subgroup G))).Normal)
    (hti : OddOrder.GroupTheory.IsTISubset ((P : Set G) \ {1})
      (Subgroup.normalizer (P : Subgroup G)))
    {Ci Cj Cs : ConjClasses G}
    (hCi : ∃ z : G, z ∈ Z ∧ z ≠ 1 ∧ ConjClasses.mk z = Ci)
    (hCj : ∃ z : G, z ∈ Z ∧ z ≠ 1 ∧ ConjClasses.mk z = Cj)
    (hCs : ∀ w : G, ConjClasses.mk w = Cs → w ∉ Z) :
    ∀ x : (P : Subgroup G), (x : G) ≠ 1 → ∀ q : ClassPair Ci Cj Cs, x • q ≠ q := by
  classical
  -- `Z ≤ P ≤ L`, so `Z` sits inside `L = N_G(P)`.
  have hZL : ∀ a : G, a ∈ Z → a ∈ Subgroup.normalizer (P : Subgroup G) := by
    intro a ha
    exact (P : Subgroup G).le_normalizer (hZP ha)
  -- `Z ⊴ L`, read at the level of `G`: `L` conjugates `Z` to itself.
  have hZconj : ∀ c : G, c ∈ Subgroup.normalizer (P : Subgroup G) →
      ∀ a : G, a ∈ Z → c * a * c⁻¹ ∈ Z := by
    intro c hc a ha
    have haL : a ∈ Subgroup.normalizer (P : Subgroup G) := hZL a ha
    have := hZnormal.conj_mem ⟨a, haL⟩ ha ⟨c, hc⟩
    simpa [Subgroup.mem_subgroupOf] using this
  -- `z ∈ P` has `p`-power order, so does anything `G`-conjugate to it: `⟨w⟩` is a `p`-group.
  have hp_of_conj : ∀ {w z : G}, z ∈ (P : Subgroup G) → IsConj z w →
      IsPGroup p (Subgroup.zpowers w) := by
    intro w z hzP hconj
    -- `orderOf z = p ^ k` (it lies in the `p`-group `P`), and conjugation preserves order.
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.2) ⟨z, hzP⟩
    rw [Subgroup.orderOf_mk] at hk
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hsc : SemiconjBy c z w := mul_inv_eq_iff_eq_mul.mp hc
    have hordw : orderOf w = p ^ k := (SemiconjBy.orderOf_eq c hsc).symm.trans hk
    -- A cyclic group of `p`-power order is a `p`-group.
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hordw])
  -- `x ∈ P^#` fixing `(u,v)` centralizes `u`, `v`; TI puts that centralizer inside `L`.
  intro x hx q hfix
  obtain ⟨⟨u, v⟩, hq⟩ := q
  obtain ⟨hqi, hqj, hqs⟩ := hq
  -- Work with the underlying group element `xg = ↑x` to keep inverses on the `G` side.
  set xg : G := (x : G) with hxg
  -- Unfold `x • (u,v) = (u,v)` into `xg u xg⁻¹ = u` and `xg v xg⁻¹ = v`.
  have hcoe := congrArg (Subtype.val) hfix
  rw [classPairSMul_coe] at hcoe
  simp only [Prod.mk.injEq] at hcoe
  obtain ⟨hxu, hxv⟩ := hcoe
  -- `xg ∈ P^# = P ∖ {1}`.
  have hxP : xg ∈ ((P : Set G) \ {1}) := ⟨x.2, by simpa [hxg] using hx⟩
  -- Any `y` commuting with `xg` lands in `L`: it conjugates `xg ∈ P^#` to `xg ∈ P^#`.
  have hcent_le : ∀ y : G, xg * y * xg⁻¹ = y →
      y ∈ Subgroup.normalizer (P : Subgroup G) := by
    intro y hy
    -- `xg y xg⁻¹ = y` says `xg, y` commute; hence `y xg y⁻¹ = xg`, overlapping `P^#`.
    have hcomm : xg * y = y * xg := mul_inv_eq_iff_eq_mul.mp hy
    have hyx : y * xg * y⁻¹ = xg := by
      rw [← hcomm]; group
    exact hti y ⟨xg, hxP, by rw [hyx]; exact hxP⟩
  -- The core sub-step applied to a member `y ∈ {u, v}`: `y ∈ Z`.
  have hmem_Z : ∀ {y z : G}, xg * y * xg⁻¹ = y → z ∈ Z → z ≠ 1 → IsConj z y →
      y ∈ Z := by
    intro y z hxy hzZ _ hconj
    -- `y ∈ L` (it commutes with `xg ∈ P^#`).
    have hyL : y ∈ Subgroup.normalizer (P : Subgroup G) := hcent_le y hxy
    -- `y` is a `p`-element (conjugate to `z ∈ Z ≤ P`), hence `y ∈ P`.
    have hyP : y ∈ (P : Subgroup G) :=
      mem_sylow_of_mem_normalizer_of_isPGroup P hyL (hp_of_conj (hZP hzZ) hconj)
    -- `c z c⁻¹ = y` for some `c`; so `c⁻¹` conjugates `y ∈ P^#` into `Z^# ⊆ P^#`.
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hyne : y ≠ 1 := by
      rintro rfl
      -- `c z c⁻¹ = 1` forces `z = 1`, contradicting `z ≠ 1`.
      apply ‹z ≠ 1›
      have : c * z * c⁻¹ = 1 := hc
      simpa [mul_eq_one_iff_eq_inv] using this
    have hyP' : y ∈ ((P : Set G) \ {1}) :=
      ⟨SetLike.mem_coe.mpr hyP, by simpa using hyne⟩
    have hzP' : z ∈ ((P : Set G) \ {1}) :=
      ⟨SetLike.mem_coe.mpr (hZP hzZ), by simpa using ‹z ≠ 1›⟩
    -- TI applied to `c⁻¹` (sending `y ∈ P^#` to `c⁻¹ y c = z ∈ P^#`) gives `c⁻¹ ∈ L`.
    have hcinv_conj : c⁻¹ * y * (c⁻¹)⁻¹ = z := by rw [← hc]; group
    have hcinvL : c⁻¹ ∈ Subgroup.normalizer (P : Subgroup G) :=
      hti c⁻¹ ⟨y, hyP', by rw [hcinv_conj]; exact hzP'⟩
    -- So `c ∈ L`, and `y = c z c⁻¹` with `Z ⊴ L`, `z ∈ Z` give `y ∈ Z`.
    have hcL : c ∈ Subgroup.normalizer (P : Subgroup G) := by
      simpa using inv_mem hcinvL
    have := hZconj c hcL z hzZ
    rwa [hc] at this
  -- Apply the sub-step to `u` and `v` via their class memberships, then derive `u·v ∈ Z`.
  obtain ⟨zi, hziZ, hzine, hzic⟩ := hCi
  obtain ⟨zj, hzjZ, hzjne, hzjc⟩ := hCj
  -- `u ∈ C_i` and `zi ∈ C_i ∩ Z^#` are conjugate, similarly `v`, `zj`.
  have huconj : IsConj zi u :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (hzic.trans hqi.symm)
  have hvconj : IsConj zj v :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (hzjc.trans hqj.symm)
  have huZ : u ∈ Z := hmem_Z hxu hziZ hzine huconj
  have hvZ : v ∈ Z := hmem_Z hxv hzjZ hzjne hvconj
  -- `u·v ∈ Z` contradicts `C_s ∩ Z = ∅` (here `u·v ∈ C_s`).
  exact hCs (u * v) hqs (Z.mul_mem huZ hvZ)

end FixedPointFree

section CentralCharacter

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **Schur's lemma for central elements of `ℂ[G]`.** A central element `x` of the group algebra
acts on a finite-dimensional irreducible complex representation `ρ` as a scalar: there is `c : ℂ`
with `ρ.asAlgebraHom x = c • LinearMap.id`.  (Isaacs (1.5)/§3.) -/
theorem exists_central_scalar_asAlgebraHom (ρ : Representation ℂ G V) [IsIrreducible ρ]
    {x : ℂ[G]} (hx : x ∈ Subalgebra.center ℂ (ℂ[G])) :
    ∃ c : ℂ, ρ.asAlgebraHom x = c • LinearMap.id := by
  -- `asAlgebraHom ρ x` is an intertwiner: it commutes with every `ρ g`.
  have hcomm : ∀ (g : G) (v : V), ρ.asAlgebraHom x (ρ g v) = ρ g (ρ.asAlgebraHom x v) := by
    intro g v
    have hgx : MonoidAlgebra.of ℂ G g * x = x * MonoidAlgebra.of ℂ G g :=
      (Subalgebra.mem_center_iff (R := ℂ)).mp hx _
    have h1 : ρ.asAlgebraHom (MonoidAlgebra.of ℂ G g * x)
        = ρ.asAlgebraHom (x * MonoidAlgebra.of ℂ G g) := by rw [hgx]
    simp only [map_mul, asAlgebraHom_of] at h1
    have := LinearMap.congr_fun h1 v
    simpa only [Module.End.mul_apply] using this.symm
  let f : IntertwiningMap ρ ρ :=
    (ρ.asAlgebraHom x).intertwiningMap_of_isIntertwiningMap ρ ρ hcomm
  obtain ⟨c, hc⟩ :=
    (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := ρ)).surjective f
  refine ⟨c, ?_⟩
  have hlin := congrArg IntertwiningMap.toLinearMap hc
  rw [IntertwiningMap.algebraMap_apply, IntertwiningMap.toLinearMap_smul,
    show (1 : IntertwiningMap ρ ρ).toLinearMap = LinearMap.id from rfl] at hlin
  exact hlin.symm

/-- The unique scalar `c` with `ρ.asAlgebraHom x = c • id` is the normalized trace
`trace(ρ.asAlgebraHom x) / finrank ℂ V`. -/
theorem centralScalar_eq (ρ : Representation ℂ G V) [IsIrreducible ρ]
    {x : ℂ[G]} {c : ℂ} (hc : ρ.asAlgebraHom x = c • LinearMap.id) :
    c = LinearMap.trace ℂ V (ρ.asAlgebraHom x) / (finrank ℂ V : ℂ) := by
  have := nontrivial_of_isIrreducible ρ
  have hfr : (finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul, mul_div_assoc, div_self hfr, mul_one]

/-- **The central character `ω_ρ : Z(ℂ[G]) →ₐ[ℂ] ℂ`** attached to a finite-dimensional irreducible
complex representation `ρ` of `G`.  A central element `x` acts on `V` as the scalar `ω_ρ(x)`, and
`x ↦ ω_ρ(x)` is a `ℂ`-algebra homomorphism.  This is the homomorphism `ω` of Isaacs §3 (p. 35),
invoked in Peterfalvi (6.7.2).

The value `ω_ρ(x)` is `trace(ρ.asAlgebraHom x) / finrank ℂ V`; the algebra-hom axioms hold because
`ρ.asAlgebraHom` is multiplicative and each `ρ.asAlgebraHom x` (for central `x`) is a scalar matrix,
whose normalized trace is exactly its scalar. -/
noncomputable def centralCharacterOfRep (ρ : Representation ℂ G V) [IsIrreducible ρ] :
    Subalgebra.center ℂ (ℂ[G]) →ₐ[ℂ] ℂ where
  toFun x := LinearMap.trace ℂ V (ρ.asAlgebraHom x.val) / (finrank ℂ V : ℂ)
  map_one' := by
    have hfr : (finrank ℂ V : ℂ) ≠ 0 := by
      have := nontrivial_of_isIrreducible ρ
      exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    change LinearMap.trace ℂ V (ρ.asAlgebraHom (1 : ℂ[G])) / (finrank ℂ V : ℂ) = 1
    rw [map_one, LinearMap.trace_one, div_self hfr]
  map_mul' x y := by
    have hfr : (finrank ℂ V : ℂ) ≠ 0 := by
      have := nontrivial_of_isIrreducible ρ
      exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    obtain ⟨cx, hcx⟩ := exists_central_scalar_asAlgebraHom ρ x.property
    obtain ⟨cy, hcy⟩ := exists_central_scalar_asAlgebraHom ρ y.property
    have hxy : (x * y : Subalgebra.center ℂ (ℂ[G])).val = x.val * y.val := rfl
    change LinearMap.trace ℂ V (ρ.asAlgebraHom (x * y).val) / (finrank ℂ V : ℂ)
        = (LinearMap.trace ℂ V (ρ.asAlgebraHom x.val) / (finrank ℂ V : ℂ))
          * (LinearMap.trace ℂ V (ρ.asAlgebraHom y.val) / (finrank ℂ V : ℂ))
    -- RHS: each normalized trace is the corresponding scalar.
    rw [← centralScalar_eq ρ hcx, ← centralScalar_eq ρ hcy]
    -- LHS: `asAlgebraHom (x*y) = (cx•id)*(cy•id) = (cx*cy)•id`, normalized trace is `cx*cy`.
    rw [hxy, map_mul, hcx, hcy, smul_mul_smul_comm, Module.End.mul_eq_comp, LinearMap.id_comp,
      map_smul, LinearMap.trace_id, smul_eq_mul, mul_div_assoc, div_self hfr, mul_one]
  map_zero' := by
    change LinearMap.trace ℂ V (ρ.asAlgebraHom (0 : ℂ[G])) / (finrank ℂ V : ℂ) = 0
    rw [map_zero, map_zero, zero_div]
  map_add' x y := by
    change LinearMap.trace ℂ V (ρ.asAlgebraHom (x + y).val) / (finrank ℂ V : ℂ)
        = LinearMap.trace ℂ V (ρ.asAlgebraHom x.val) / (finrank ℂ V : ℂ)
          + LinearMap.trace ℂ V (ρ.asAlgebraHom y.val) / (finrank ℂ V : ℂ)
    have hadd : (x + y : Subalgebra.center ℂ (ℂ[G])).val = x.val + y.val := rfl
    rw [hadd, map_add, map_add, add_div]
  commutes' r := by
    have hfr : (finrank ℂ V : ℂ) ≠ 0 := by
      have := nontrivial_of_isIrreducible ρ
      exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    change LinearMap.trace ℂ V (ρ.asAlgebraHom ((algebraMap ℂ (Subalgebra.center ℂ (ℂ[G])) r)).val)
        / (finrank ℂ V : ℂ) = r
    rw [Subalgebra.coe_algebraMap, AlgHom.commutes, Module.algebraMap_end_eq_smul_id,
      map_smul, LinearMap.trace_id, smul_eq_mul, mul_div_assoc, div_self hfr, mul_one]

@[simp] theorem centralCharacterOfRep_apply (ρ : Representation ℂ G V) [IsIrreducible ρ]
    (x : Subalgebra.center ℂ (ℂ[G])) :
    centralCharacterOfRep ρ x = LinearMap.trace ℂ V (ρ.asAlgebraHom x.val) / (finrank ℂ V : ℂ) :=
  rfl

end CentralCharacter

section Evaluation

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

variable [Fintype G] [DecidableEq (ConjClasses G)]

omit [FiniteDimensional ℂ V] in
/-- The image of a class sum under the representation algebra map is `∑_{g ∈ C} ρ g`. -/
theorem asAlgebraHom_classSum (ρ : Representation ℂ G V) (C : ConjClasses G) :
    ρ.asAlgebraHom (classSum C) =
      ∑ g : G, if ConjClasses.mk g = C then ρ g else 0 := by
  rw [classSum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases h : ConjClasses.mk g = C
  · simp only [h, if_true, asAlgebraHom_of]
  · simp [h]

omit [FiniteDimensional ℂ V] in
/-- The trace of `ρ.asAlgebraHom (classSum C)` is `∑_{g ∈ C} χ_ρ(g)`, i.e. `|C| · χ_ρ(g)` for any
`g ∈ C` (since `χ_ρ` is a class function). -/
theorem trace_asAlgebraHom_classSum (ρ : Representation ℂ G V) (C : ConjClasses G) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum C)) =
      ∑ g : G, if ConjClasses.mk g = C then ρ.character g else 0 := by
  rw [asAlgebraHom_classSum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  by_cases h : ConjClasses.mk g = C
  · simp only [h, if_true]; rfl
  · simp [h]

/-- **Evaluation of the central character on a class sum** (Isaacs (3.6); Peterfalvi (6.7.2)):
`ω_ρ(C) = (∑_{g ∈ C} χ_ρ(g)) / χ_ρ(1)`.  Since `χ_ρ` is constant on `C`, the numerator equals
`|C| · χ_ρ(g)` for any representative `g ∈ C`. -/
theorem centralCharacterOfRep_classSum (ρ : Representation ℂ G V) [IsIrreducible ρ]
    (C : ConjClasses G) :
    centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩ =
      (∑ g : G, if ConjClasses.mk g = C then ρ.character g else 0) / (finrank ℂ V : ℂ) := by
  rw [centralCharacterOfRep_apply, trace_asAlgebraHom_classSum]

omit [FiniteDimensional ℂ V] in
/-- The numerator `∑_{g ∈ C} χ_ρ(g)` equals `|C| · χ_ρ(g)` for any `g ∈ C`: the character is
constant on the class, and `|C|` is the number of group elements lying in `C`. -/
theorem sum_character_eq_card_mul (ρ : Representation ℂ G V) (C : ConjClasses G) {g : G}
    (hg : ConjClasses.mk g = C) :
    (∑ g : G, if ConjClasses.mk g = C then ρ.character g else 0)
      = (Nat.card { x : G // ConjClasses.mk x = C } : ℂ) * ρ.character g := by
  classical
  -- The character is constant on the class: replace `χ g'` by `χ g` under the guard.
  have hbody : ∀ g' : G, (if ConjClasses.mk g' = C then ρ.character g' else 0)
      = (if ConjClasses.mk g' = C then ρ.character g else 0) := by
    intro g'
    by_cases hg' : ConjClasses.mk g' = C
    · have hconj : IsConj g g' := ConjClasses.mk_eq_mk_iff_isConj.mp (hg.trans hg'.symm)
      obtain ⟨u, rfl⟩ := isConj_iff.mp hconj
      rw [char_conj]
    · simp [hg']
  rw [Finset.sum_congr rfl (fun g' _ => hbody g')]
  -- Now sum a constant over the class: `∑ g', (if mk g' = C then χ g else 0) = |C| · χ g`.
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **The central character is `1` on the identity class** (`ω_ρ(C₀) = 1`), the value Peterfalvi
uses for the `⟦1⟧` term when collapsing the (6.7.2) right-hand sum to `ψ(1)(a_{ij0} + a_{ij}α)`.
The identity class is the singleton `{1}`, so `ω_ρ(⟦1⟧) = (1 · χ_ρ(1)) / χ_ρ(1) = 1`. -/
theorem centralCharacterOfRep_one (ρ : Representation ℂ G V) [IsIrreducible ρ] :
    centralCharacterOfRep ρ ⟨classSum 1, classSum_mem_center 1⟩ = 1 := by
  classical
  have := nontrivial_of_isIrreducible ρ
  have hfr : (finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hmk : ConjClasses.mk (1 : G) = (1 : ConjClasses G) := (ConjClasses.one_eq_mk_one).symm
  rw [centralCharacterOfRep_classSum, sum_character_eq_card_mul ρ (1 : ConjClasses G) hmk]
  -- The identity class is the singleton `{1}` (`mk x = 1 ↔ x = 1`), so its size is `1`.
  have hcard : Nat.card { x : G // ConjClasses.mk x = (1 : ConjClasses G) } = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, hmk⟩⟩⟩
    have ha : (a : G) = 1 := mk_eq_one_iff_eq_one.mp a.2
    have hb : (b : G) = 1 := mk_eq_one_iff_eq_one.mp b.2
    rw [ha, hb]
  -- `ω(⟦1⟧) = (1 · χ(1)) / χ(1) = 1`.
  rw [hcard, ρ.char_one, Nat.cast_one, one_mul, div_self hfr]

end Evaluation

section Integrality

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

variable [Fintype G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]

/-- Shorthand for the central-character value `ω_ρ(C_s)` on a class sum. -/
local notation3 "ω" ρ:max C:max => centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩

/-- **The product rule for central-character values.** Because `ω_ρ` is a `ℂ`-algebra hom and
`C_i · C_j = ∑_s m_s · C_s` (`classSum_mul`), the value `ω_ρ(C_i) · ω_ρ(C_j)` is a linear
combination of the values `ω_ρ(C_s)` whose coefficients
`(classSum Ci * classSum Cj : ℂ[G]).coeff C_s.out` are
*natural numbers* (factorization counts), the key fact making the generated `ℤ`-subalgebra closed
under multiplication. -/
theorem centralCharacterOfRep_classSum_mul (ρ : Representation ℂ G V) [IsIrreducible ρ]
    (Ci Cj : ConjClasses G) :
    (ω ρ Ci) * (ω ρ Cj) =
      ∑ Cs : ConjClasses G, ((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) • (ω ρ Cs) := by
  classical
  -- `ω` is multiplicative, and the product of the two class sums is the stated combination.
  have hcenter : (⟨classSum Ci, classSum_mem_center Ci⟩ : Subalgebra.center ℂ (ℂ[G]))
        * ⟨classSum Cj, classSum_mem_center Cj⟩
      = ∑ Cs : ConjClasses G,
          ((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) •
            (⟨classSum Cs, classSum_mem_center Cs⟩ : Subalgebra.center ℂ (ℂ[G])) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, AddSubmonoidClass.coe_finsetSum]
    simp only [SetLike.val_smul]
    exact classSum_mul Ci Cj
  calc (ω ρ Ci) * (ω ρ Cj)
      = centralCharacterOfRep ρ
          (⟨classSum Ci, classSum_mem_center Ci⟩ * ⟨classSum Cj, classSum_mem_center Cj⟩) := by
        rw [map_mul]
    _ = centralCharacterOfRep ρ
          (∑ Cs : ConjClasses G, ((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) •
            (⟨classSum Cs, classSum_mem_center Cs⟩ : Subalgebra.center ℂ (ℂ[G]))) := by
        rw [hcenter]
    _ = ∑ Cs : ConjClasses G,
          ((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) • (ω ρ Cs) := by
        rw [map_sum]; exact Finset.sum_congr rfl fun Cs _ => map_smul _ _ _

omit [Fintype (ConjClasses G)] [DecidableEq (ConjClasses G)] [FiniteDimensional ℂ V] [Fintype G] in
/-- **The centralizer of a TI-subset element lies in the TI normalizer.**

If `A` is a TI-subset of `G` with normalizer-bound `L` and `x ∈ A`, then `C_G(x) ≤ L`: any `g`
centralizing `x` fixes `x ∈ A` under conjugation (`g x g⁻¹ = x ∈ A`), so the TI condition forces
`g ∈ L`.  This is the group-theoretic fact behind Peterfalvi (6.7)'s `|C_G(z)| = |C_L(z)|` for
`z ∈ Z^# ⊆ P^#`: with `C_G(z) ⊆ L = N_G(P)`, the centralizer in `G` equals the centralizer in `L`,
so the hypothesis `|C_L(z)|` constant on `Z^#` makes `|⟦z⟧| = [G : C_G(z)]` constant, feeding the
class-size hypothesis of `centralCharacterOfRep_eq_of_card_eq_of_character_eq`. -/
theorem centralizer_le_of_mem_isTISubset {A : Set G} {L : Subgroup G}
    (hA : OddOrder.GroupTheory.IsTISubset A L) {x : G} (hx : x ∈ A) :
    Subgroup.centralizer ({x} : Set G) ≤ L := by
  intro g hg
  refine hA g ⟨x, hx, ?_⟩
  have hcomm : x * g = g * x := (Subgroup.mem_centralizer_iff.mp hg) x (Set.mem_singleton x)
  have hfix : g * x * g⁻¹ = x := by rw [← hcomm]; group
  rw [hfix]; exact hx

omit [Fintype (ConjClasses G)] in
/-- **The central-character value `ω_ρ(⟦z⟧)` depends only on `χ_ρ(z)` and the class size `|⟦z⟧|`.**

`ω_ρ(⟦z⟧) = |⟦z⟧| · χ_ρ(z) / χ_ρ(1)` (`centralCharacterOfRep_classSum` +
`sum_character_eq_card_mul`),
so if `z, z'` have equal class size (`|⟦z⟧| = |⟦z'⟧|`) and equal character value
(`χ_ρ(z) = χ_ρ(z')`) then `ω_ρ(⟦z⟧) = ω_ρ(⟦z'⟧)`.

This is the constancy Peterfalvi (6.7) uses ("`α` does not depend on `s`", mmd 04.8 L102): on `Z^#`
both `ψ(z)` (`ψ` constant on `Z^#`, a hypothesis) and `|⟦z⟧| = [G : C_G(z)]` are independent of `z`
— the latter because `|C_G(z)| = |C_L(z)|` (`C_G(z) ⊆ L` from the `P^#`-TI-subset,
`centralizer_le_normalizer_of_mem_tiSubset`) is constant by hypothesis.  This lemma isolates the
*character-theoretic* constancy; the *group-theoretic* class-size constancy (`hcard`) is supplied by
the caller from the TI-subset / `|C_L(z)|`-constancy data. -/
theorem centralCharacterOfRep_eq_of_card_eq_of_character_eq (ρ : Representation ℂ G V)
    [IsIrreducible ρ] {z z' : G}
    (hcard : Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z }
      = Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z' })
    (hchar : ρ.character z = ρ.character z') :
    ω ρ (ConjClasses.mk z) = ω ρ (ConjClasses.mk z') := by
  rw [centralCharacterOfRep_classSum ρ (ConjClasses.mk z),
    centralCharacterOfRep_classSum ρ (ConjClasses.mk z'),
    sum_character_eq_card_mul ρ (ConjClasses.mk z) (g := z) rfl,
    sum_character_eq_card_mul ρ (ConjClasses.mk z') (g := z') rfl, hcard, hchar]

omit [Fintype G] in
omit [Fintype (ConjClasses G)] in
omit [DecidableEq (ConjClasses G)] in
/-- **Class-size constancy from centralizer constancy inside a subgroup.**  If the ambient
centralizers `C_G(z)` and `C_G(z')` both lie in `L`, then equality of the `L`-centralizer sizes
`|L ∩ C_G(z)| = |L ∩ C_G(z')|` forces equality of the ambient conjugacy-class sizes
`|⟦z⟧| = |⟦z'⟧|`.

This is the group-theoretic bridge used in Peterfalvi (6.7): the TI condition puts
`C_G(x) ≤ L` for `x ∈ P^#`, so a hypothesis that `|C_L(x)|` is constant on `Z^#` can be read as
constancy of the ambient class size. -/
theorem card_class_eq_of_inf_centralizer_card_eq [Finite G] (L : Subgroup G) {z z' : G}
    (hz : Subgroup.centralizer ({z} : Set G) ≤ L)
    (hz' : Subgroup.centralizer ({z'} : Set G) ≤ L)
    (hcard : Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set G))
      = Nat.card ↥(L ⊓ Subgroup.centralizer ({z'} : Set G))) :
    Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z }
      = Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z' } := by
  have hLz : L ⊓ Subgroup.centralizer ({z} : Set G)
      = Subgroup.centralizer ({z} : Set G) := by
    exact le_antisymm inf_le_right (le_inf hz le_rfl)
  have hLz' : L ⊓ Subgroup.centralizer ({z'} : Set G)
      = Subgroup.centralizer ({z'} : Set G) := by
    exact le_antisymm inf_le_right (le_inf hz' le_rfl)
  have hcent : Nat.card (Subgroup.centralizer ({z} : Set G))
      = Nat.card (Subgroup.centralizer ({z'} : Set G)) := by
    simpa [hLz, hLz'] using hcard
  rw [card_class_eq_index_centralizer z, card_class_eq_index_centralizer z']
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Subgroup.centralizer ({z'} : Set G)))
  calc
    (Subgroup.centralizer ({z} : Set G)).index
        * Nat.card (Subgroup.centralizer ({z'} : Set G))
        = (Subgroup.centralizer ({z} : Set G)).index
            * Nat.card (Subgroup.centralizer ({z} : Set G)) := by rw [hcent]
    _ = Nat.card G := (Subgroup.centralizer ({z} : Set G)).index_mul_card
    _ = (Subgroup.centralizer ({z'} : Set G)).index
        * Nat.card (Subgroup.centralizer ({z'} : Set G)) :=
      (Subgroup.centralizer ({z'} : Set G)).index_mul_card.symm

omit [Fintype (ConjClasses G)] in
/-- **Central-character constancy from TI, `L`-centralizer constancy, and character-value
constancy.**  For elements `z, z'` in a TI-subset `A`, the TI condition gives
`C_G(z), C_G(z') ≤ L`.  If the corresponding `L`-centralizer sizes agree and
`χ_ρ(z) = χ_ρ(z')`, then the central-character values on their conjugacy classes agree.

This packages the `(iii)` bridge in Peterfalvi (6.7): `ω(C_s)=α` on classes meeting `Z^#` follows
from constancy of `ψ` and of `|C_L(-)|` on `Z^#`. -/
theorem centralCharacterOfRep_eq_of_tiSubset_card_eq_of_character_eq
    (ρ : Representation ℂ G V) [IsIrreducible ρ] {A : Set G} {L : Subgroup G}
    (hA : OddOrder.GroupTheory.IsTISubset A L) {z z' : G} (hz : z ∈ A) (hz' : z' ∈ A)
    (hcard : Nat.card ↥(L ⊓ Subgroup.centralizer ({z} : Set G))
      = Nat.card ↥(L ⊓ Subgroup.centralizer ({z'} : Set G)))
    (hchar : ρ.character z = ρ.character z') :
    ω ρ (ConjClasses.mk z) = ω ρ (ConjClasses.mk z') :=
  centralCharacterOfRep_eq_of_card_eq_of_character_eq ρ
    (card_class_eq_of_inf_centralizer_card_eq L
      (centralizer_le_of_mem_isTISubset hA hz)
      (centralizer_le_of_mem_isTISubset hA hz') hcard)
    hchar

omit [Fintype (ConjClasses G)] in
/-- **Central-character substitution at a representative.**  For an irreducible representation,
`χ(1) · ω(⟦z⟧) = |⟦z⟧| · χ(z)`.

This is the equation `ψ(1)α = |C₁|ψ(z)` used in Peterfalvi (6.7.3), obtained directly from the
central-character formula on a class sum. -/
theorem character_one_mul_centralCharacterOfRep_mk (ρ : Representation ℂ G V)
    [IsIrreducible ρ] (z : G) :
    ρ.character 1 * (ω ρ (ConjClasses.mk z))
      = (Nat.card { x : G // ConjClasses.mk x = ConjClasses.mk z } : ℂ) * ρ.character z := by
  rw [centralCharacterOfRep_classSum ρ (ConjClasses.mk z),
    sum_character_eq_card_mul ρ (ConjClasses.mk z) (g := z) rfl, ρ.char_one]
  have := nontrivial_of_isIrreducible ρ
  have hd : (finrank ℂ V : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  field_simp [hd]

omit [Fintype (ConjClasses G)] in
/-- **Algebraic integrality of the central-character value `ω_ρ(C)`** (Isaacs (3.7); the
structure-constant integrality used in Peterfalvi (6.7.3)).  For an irreducible representation `ρ`
of a finite group `G` and a conjugacy class `C`, the value `ω_ρ(C) = |C| · χ_ρ(g) / χ_ρ(1)` is an
**algebraic integer**.

The proof realizes the standard structure-constant argument inside `ℂ` directly: the `ℤ`-submodule
`N ⊆ ℂ` spanned by `{1} ∪ {ω_ρ(C_s) : C_s}` is finitely generated (the spanning set is finite, as
`ConjClasses G` is finite) and closed under multiplication — the latter because `ω_ρ` is a
`ℂ`-algebra hom and `classSum_mul` expresses `C_i · C_j` with integer structure coefficients, so
`ω_ρ(C_i) · ω_ρ(C_j) = ∑_s m_s · ω_ρ(C_s) ∈ N` (`centralCharacterOfRep_classSum_mul`).  Thus `N` is
a `ℤ`-subalgebra of `ℂ` that is module-finite, and every element of a module-finite subalgebra is
integral (`IsIntegral.of_mem_of_fg`). -/
theorem centralCharacterOfRep_classSum_isIntegral (ρ : Representation ℂ G V) [IsIrreducible ρ]
    (C : ConjClasses G) :
    IsIntegral ℤ (ω ρ C) := by
  classical
  have : Finite (ConjClasses G) := Finite.of_surjective _ ConjClasses.mk_surjective
  have : Fintype (ConjClasses G) := Fintype.ofFinite _
  -- The finite spanning set: `{1}` together with all central-character values.
  set s : Set ℂ := insert 1 (Set.range (fun Cs : ConjClasses G => ω ρ Cs)) with hs
  have hsfin : s.Finite := (Set.finite_range _).insert 1
  -- The `ℤ`-submodule generated by `s`.
  set N : Submodule ℤ ℂ := Submodule.span ℤ s with hN
  -- Membership of `1` and every generator.
  have h1_mem : (1 : ℂ) ∈ N := Submodule.subset_span (Set.mem_insert _ _)
  have hgen_mem : ∀ Cs : ConjClasses G, (ω ρ Cs) ∈ N := fun Cs =>
    Submodule.subset_span (Set.mem_insert_of_mem _ ⟨Cs, rfl⟩)
  -- A factorization-count coefficient times a generator lands in `N` (`ℕ`-smul of a member).
  have hcoeff_smul : ∀ (Ci Cj Cs : ConjClasses G),
      ((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) • (ω ρ Cs) ∈ N := by
    intro Ci Cj Cs
    rw [classSum_mul_apply, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem (hgen_mem Cs) _
  -- Closure under multiplication: it suffices to check products of generators.
  have hmul : ∀ x y : ℂ, x ∈ N → y ∈ N → x * y ∈ N := by
    have hgen : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ N := by
      intro a ha b hb
      rcases ha with rfl | ⟨Ci, rfl⟩
      · rw [one_mul]; exact Submodule.subset_span hb
      · rcases hb with rfl | ⟨Cj, rfl⟩
        · rw [mul_one]; exact hgen_mem Ci
        · rw [centralCharacterOfRep_classSum_mul]
          exact Submodule.sum_mem _ fun Cs _ => hcoeff_smul Ci Cj Cs
    -- Lift generator-closure to all of `N` by span induction (bilinearly).
    intro x y hx hy
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro a ha
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · intro b hb; exact hgen a ha b hb
      · rw [mul_zero]; exact N.zero_mem
      · intro b c _ _ hb hc; rw [mul_add]; exact N.add_mem hb hc
      · intro r b _ hb; rw [mul_smul_comm]; exact N.smul_mem r hb
    · rw [zero_mul]; exact N.zero_mem
    · intro a c _ _ ha hc; rw [add_mul]; exact N.add_mem ha hc
    · intro r a _ ha; rw [smul_mul_assoc]; exact N.smul_mem r ha
  -- Package `N` as a `ℤ`-subalgebra of `ℂ`.
  let S : Subalgebra ℤ ℂ := N.toSubalgebra h1_mem hmul
  have hSfg : S.toSubmodule.FG := by
    rw [Submodule.toSubalgebra_toSubmodule]; exact Submodule.fg_span hsfin
  -- `ω ρ C ∈ S`, and every element of a module-finite subalgebra is integral.
  exact IsIntegral.of_mem_of_fg S hSfg _ (hgen_mem C)

end Integrality

section CharacterIntegrality

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Finite G]

/-- **`|C| · χ_ρ(g) / χ_ρ(1)` is an algebraic integer** (Isaacs (3.7); the integrality input to
Peterfalvi (6.7.3)).  For an irreducible representation `ρ` of a finite group `G`, a conjugacy class
`C`, and any representative `g ∈ C`, the value `|C| · χ_ρ(g) / χ_ρ(1)` is an algebraic integer over
`ℤ`.

This is the explicit character-value form of `centralCharacterOfRep_classSum_isIntegral`: that
theorem states `ω_ρ(C)` is integral, and `centralCharacterOfRep_classSum` together with
`sum_character_eq_card_mul` identify `ω_ρ(C)` with `|C| · χ_ρ(g) / χ_ρ(1)` (using `char_one` for
`χ_ρ(1) = finrank ℂ V`).  This is the form most arguments consume (e.g. the `mod |P|` congruence of
(6.7.3), and the classical proof that `χ_ρ(1) ∣ |G|`). -/
theorem isIntegral_card_mul_character_div (ρ : Representation ℂ G V) [IsIrreducible ρ]
    (C : ConjClasses G) {g : G} (hg : ConjClasses.mk g = C) :
    IsIntegral ℤ
      ((Nat.card { x : G // ConjClasses.mk x = C } : ℂ) * ρ.character g / ρ.character 1) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hval :
      (Nat.card { x : G // ConjClasses.mk x = C } : ℂ) * ρ.character g / ρ.character 1 =
        centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩ := by
    rw [centralCharacterOfRep_classSum, sum_character_eq_card_mul ρ C hg, ρ.char_one]
  rw [hval]
  exact centralCharacterOfRep_classSum_isIntegral ρ C

end CharacterIntegrality

section CharacterValuesIntegral

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **Eigenvalues of a finite-order endomorphism are roots of unity.** If `f : End ℂ V` satisfies
`f ^ n = 1` and `μ` is a root of the characteristic polynomial of `f` (equivalently an eigenvalue),
then `μ ^ n = 1`. -/
theorem pow_eq_one_of_isRoot_charpoly_of_pow_eq_one {f : Module.End ℂ V} {n : ℕ}
    (hf : f ^ n = 1) {μ : ℂ} (hμ : f.charpoly.IsRoot μ) : μ ^ n = 1 := by
  -- `μ` is a root of the charpoly, hence an eigenvalue, so it has a nonzero eigenvector.
  have hev : f.HasEigenvalue μ := (Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mpr hμ
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  -- Acting by `f ^ n` scales `v` by `μ ^ n`; but `f ^ n = 1`, so `μ ^ n • v = v`.
  have hpow : (f ^ n) v = μ ^ n • v := hv.pow_apply n
  rw [hf, Module.End.one_apply] at hpow
  -- `hpow : v = μ ^ n • v`; hence `(μ ^ n - 1) • v = 0` with `v ≠ 0` over `ℂ` forces `μ ^ n = 1`.
  have hsub : (μ ^ n - 1) • v = 0 := by rw [sub_smul, one_smul, ← hpow, sub_self]
  rcases smul_eq_zero.mp hsub with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv.2

/-- **Character values are algebraic integers** (Isaacs (3.7) preamble / standard).  For any
finite-dimensional complex representation `ρ` of a finite group `G` and any `g : G`, the character
value `χ_ρ(g) = trace(ρ g)` is an algebraic integer over `ℤ`.

Standard proof: `ρ g` has finite order `n = |G|` (since `g ^ |G| = 1` and `ρ` is a homomorphism),
so `(ρ g) ^ n = 1`.  Over `ℂ` the characteristic polynomial of `ρ g` splits, so the trace is the
sum of its roots (eigenvalues); each eigenvalue `μ` satisfies `μ ^ n = 1`, hence is a root of unity
and so integral over `ℤ` (`isIntegral_of_pow_eq_one`).  A sum of algebraic integers is an algebraic
integer. -/
theorem character_isIntegral (ρ : Representation ℂ G V) [Finite G] (g : G) :
    IsIntegral ℤ (ρ.character g) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set n : ℕ := Nat.card G with hn_def
  have hn : n ≠ 0 := Nat.card_pos.ne'
  -- `(ρ g) ^ n = ρ (g ^ n) = ρ 1 = 1`, using `g ^ |G| = 1`.
  have hgn : g ^ n = 1 := pow_card_eq_one'
  have hfn : (ρ g) ^ n = 1 := by
    rw [← map_pow, hgn, map_one]
  -- The trace is the sum of the roots of the (splitting) characteristic polynomial.
  have hsplits : (ρ g).charpoly.Splits := IsAlgClosed.splits _
  have htrace : ρ.character g = (ρ g).charpoly.roots.sum := by
    rw [Representation.character]
    exact Module.End.trace_eq_sum_roots_charpoly_of_splits hsplits
  rw [htrace]
  -- A finite sum (over a multiset) of algebraic integers is an algebraic integer; each root is one.
  refine IsIntegral.multiset_sum ?_
  intro μ hμ
  have hroot : (ρ g).charpoly.IsRoot μ :=
    (Polynomial.mem_roots ((ρ g).charpoly_monic).ne_zero).mp hμ
  exact isIntegral_of_pow_eq_one hn (pow_eq_one_of_isRoot_charpoly_of_pow_eq_one hfn hroot)

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- **Diagonalization keystone: character value equals degree forces the identity operator.**
For a finite-dimensional complex representation `ρ` of a finite group `G` and `g : G`, if the
character value at `g` equals the degree, `ρ.character g = ρ.character 1` (`= finrank ℂ V`), then
the operator `ρ g` is the identity.

This is the unique shared gate for Peterfalvi (6.6) G2.2 and G2.5: it provides
(a) inflation surjectivity / quotient-representation well-definedness (`ρ` factors through
`G ⧸ ⟨⟨ker χ⟩⟩` when `χ(g) = χ(1)`), and (b) the constituent-inherits-kernel fact.

Proof.  `g` has finite order `n = |G|`, so `(ρ g) ^ n = 1` and `ρ g` is annihilated by the
squarefree polynomial `X ^ n - 1`, hence **semisimple** (`isSemisimple_of_squarefree_aeval_eq_zero`)
and **diagonalizable**: its eigenspaces span `V` (`IsSemisimple.iSup_eigenspace_eq_top`).  The trace
`character g = (ρ g).charpoly.roots.sum` is the sum of the eigenvalues (with multiplicity), each a
root of unity (`‖μ‖ = 1`), and equals `character 1 = finrank ℂ V = roots.card`.  The equality case
of the triangle inequality (`all_eq_one_of_norm_eq_one_of_sum_eq_card`) forces every root, hence
every eigenvalue, to be `1`.  A semisimple operator whose only eigenvalue is `1` has
`eigenspace 1 = ⊤`, i.e. `ρ g - 1 = 0`. -/
theorem rep_eq_id_of_character_eq_one (ρ : Representation ℂ G V) [Finite G] {g : G}
    (h : ρ.character g = ρ.character 1) :
    ρ g = LinearMap.id := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set n : ℕ := Nat.card G with hn_def
  have hn : n ≠ 0 := Nat.card_pos.ne'
  -- `(ρ g) ^ n = 1` since `g ^ |G| = 1`.
  have hfn : (ρ g) ^ n = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  -- `ρ g` is a root of the squarefree polynomial `X ^ n - C 1`, hence semisimple.
  have hsq : Squarefree (Polynomial.X ^ n - Polynomial.C (1 : ℂ)) :=
    (Polynomial.separable_X_pow_sub_C 1 (by exact_mod_cast hn) one_ne_zero).squarefree
  have haeval : (Polynomial.aeval (ρ g)) (Polynomial.X ^ n - Polynomial.C (1 : ℂ)) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hfn]
    simp
  have hss : Module.End.IsSemisimple (ρ g) :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq haeval
  -- The trace is the sum of the (splitting) charpoly roots; the degree is their count.
  have hsplits : (ρ g).charpoly.Splits := IsAlgClosed.splits _
  have htrace : ρ.character g = (ρ g).charpoly.roots.sum :=
    Module.End.trace_eq_sum_roots_charpoly_of_splits hsplits
  have hcard : Multiset.card (ρ g).charpoly.roots = Module.finrank ℂ V := by
    rw [hsplits.natDegree_eq_card_roots.symm, (ρ g).charpoly_natDegree]
  -- Each root is a root of unity, so has unit modulus.
  have hroot_norm : ∀ μ ∈ (ρ g).charpoly.roots, ‖μ‖ = 1 := by
    intro μ hμ
    have hroot : (ρ g).charpoly.IsRoot μ :=
      (Polynomial.mem_roots ((ρ g).charpoly_monic).ne_zero).mp hμ
    exact Complex.norm_eq_one_of_pow_eq_one
      (pow_eq_one_of_isRoot_charpoly_of_pow_eq_one hfn hroot) hn
  -- The hypothesis `character g = character 1 = finrank` says `roots.sum = roots.card`.
  have hsum : (ρ g).charpoly.roots.sum = (Multiset.card (ρ g).charpoly.roots : ℂ) := by
    rw [← htrace, h, ρ.char_one, hcard]
  -- Triangle-inequality equality case: every root equals `1`.
  have hroot_one : ∀ μ ∈ (ρ g).charpoly.roots, μ = 1 :=
    all_eq_one_of_norm_eq_one_of_sum_eq_card hroot_norm hsum
  -- Hence the only eigenvalue of `ρ g` is `1`.
  have heig_one : ∀ μ : ℂ, Module.End.HasEigenvalue (ρ g) μ → μ = 1 := by
    intro μ hμ
    exact hroot_one μ ((Polynomial.mem_roots ((ρ g).charpoly_monic).ne_zero).mpr
      ((Module.End.hasEigenvalue_iff_isRoot_charpoly (ρ g) μ).mp hμ))
  -- A semisimple operator whose eigenvalues are all `1`: its eigenspaces (spanning `V`) collapse to
  -- the `μ = 1` eigenspace, so `eigenspace 1 = ⊤`, i.e. `ρ g - 1 = 0`.
  have htop : Module.End.eigenspace (ρ g) 1 = ⊤ := by
    rw [← hss.iSup_eigenspace_eq_top]
    refine le_antisymm (le_iSup _ 1) (iSup_le fun μ => ?_)
    rcases eq_or_ne μ 1 with rfl | hμ
    · exact le_refl _
    · have : Module.End.eigenspace (ρ g) μ = ⊥ := by
        by_contra hne
        exact hμ (heig_one μ hne)
      simp [this]
  -- `eigenspace 1 = ker (ρ g - 1) = ⊤` gives `ρ g - 1 = 0`, i.e. `ρ g = id`.
  rw [Module.End.eigenspace_def, one_smul, LinearMap.ker_eq_top, sub_eq_zero] at htop
  exact htop

/-- **Character values are bounded by the degree** (the general `|χ(g)| ≤ χ(1)` bound; Isaacs
*Character Theory*, the inequality underlying Lemma 2.27 and the equality case of (2.21)/(2.27)).
For a finite-dimensional complex representation `ρ` of a finite group `G` and `g : G`,
`‖ρ.character g‖ ≤ ρ.character 1 = finrank ℂ V`.

Proof.  `g` has finite order, so `(ρ g) ^ |G| = 1` and the (splitting) charpoly roots — the
eigenvalues with multiplicity — are roots of unity (`‖μ‖ = 1`).  The trace is their sum, and the
triangle inequality gives `‖∑ μ‖ ≤ ∑ ‖μ‖ = roots.card = finrank ℂ V`.

This is the general-`g` companion of the central Schur equality `‖χ(z)‖² = χ(1)²`; the equality case
`‖χ(g)‖ = χ(1)` together with positivity of the trace at the kernel is what
`rep_eq_id_of_character_eq_one` (the keystone) sharpens to `ρ g = id`. -/
theorem norm_character_le_finrank (ρ : Representation ℂ G V) [Finite G] (g : G) :
    ‖ρ.character g‖ ≤ (Module.finrank ℂ V : ℝ) := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set n : ℕ := Nat.card G with hn_def
  have hn : n ≠ 0 := Nat.card_pos.ne'
  have hfn : (ρ g) ^ n = 1 := by rw [← map_pow, pow_card_eq_one', map_one]
  -- `character g = roots.sum`, with `roots.card = finrank`.
  have hsplits : (ρ g).charpoly.Splits := IsAlgClosed.splits _
  have htrace : ρ.character g = (ρ g).charpoly.roots.sum :=
    Module.End.trace_eq_sum_roots_charpoly_of_splits hsplits
  have hcard : Multiset.card (ρ g).charpoly.roots = Module.finrank ℂ V := by
    rw [hsplits.natDegree_eq_card_roots.symm, (ρ g).charpoly_natDegree]
  -- Each root is a root of unity: `‖μ‖ = 1`.
  have hroot_norm : ∀ μ ∈ (ρ g).charpoly.roots, ‖μ‖ = 1 := by
    intro μ hμ
    have hroot : (ρ g).charpoly.IsRoot μ :=
      (Polynomial.mem_roots ((ρ g).charpoly_monic).ne_zero).mp hμ
    exact Complex.norm_eq_one_of_pow_eq_one
      (pow_eq_one_of_isRoot_charpoly_of_pow_eq_one hfn hroot) hn
  -- Triangle inequality: `‖∑ μ‖ ≤ ∑ ‖μ‖ = ∑ 1 = card = finrank`.
  rw [htrace]
  refine (norm_multiset_sum_le _).trans ?_
  have hmap : ((ρ g).charpoly.roots.map fun μ => ‖μ‖) = (ρ g).charpoly.roots.map fun _ => (1 : ℝ) :=
    Multiset.map_congr rfl hroot_norm
  rw [hmap, Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul, mul_one]

end CharacterValuesIntegral

section ClassCongruence

open OddOrder.AlgInt

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

variable [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]

/-- Shorthand for the central-character value `ω_ρ(C_s)` on a class sum (matching the notation of
the `Integrality` section). -/
local notation3 "ω" ρ:max C:max => centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩

omit [DecidableEq G] [Fintype (ConjClasses G)] in
/-- **The per-element factorization count times the class size is the pair count** (cast to `ℂ`).
The structure coefficient `a_{ijs} = (classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out`
(constant on the class)
times `|C_s|` equals the pair-count `classSumCoeff Ci Cj Cs = a_{ijs}|C_s|`.  This reconciles the
*class-sum* coefficient of `classSum_mul` with Peterfalvi's pair-count `a_{ijs}|{\cal C}_s|` of
(6.7.1). -/
theorem coeff_mul_card_eq_classSumCoeff (Ci Cj Cs : ConjClasses G) :
    (classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out *
        (Nat.card { x : G // ConjClasses.mk x = Cs } : ℂ) = (classSumCoeff Ci Cj Cs : ℂ) := by
  classical
  -- `classSumCoeff` counts pairs; fiber the pair set over the class of the product `u·v`.
  have hsum : (classSumCoeff Ci Cj Cs : ℂ)
      = ∑ w ∈ Finset.univ.filter (fun w : G => ConjClasses.mk w = Cs),
          (classSum Ci * classSum Cj : ℂ[G]).coeff w := by
    rw [classSumCoeff]
    -- The pair set with `mk (u·v) = Cs` is the disjoint union over `w ∈ Cs` of `{u·v = w}` sets.
    have hcard : (Finset.univ.filter (fun p : G × G =>
          ConjClasses.mk p.1 = Ci ∧ ConjClasses.mk p.2 = Cj ∧
            ConjClasses.mk (p.1 * p.2) = Cs)).card
        = ∑ w ∈ Finset.univ.filter (fun w : G => ConjClasses.mk w = Cs),
            (Finset.univ.filter (fun p : G × G =>
              ConjClasses.mk p.1 = Ci ∧ ConjClasses.mk p.2 = Cj ∧ p.1 * p.2 = w)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
        constructor
        · rintro ⟨hi, hj, hs⟩; exact ⟨p.1 * p.2, hs, hi, hj, rfl⟩
        · rintro ⟨w, hw, hi, hj, hp⟩; exact ⟨hi, hj, hp ▸ hw⟩
      · intro w₁ _ w₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        rintro p hp1 hp2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
        exact hne (hp1.2.2 ▸ hp2.2.2)
    rw [hcard, Nat.cast_sum]
    exact Finset.sum_congr rfl fun w _ => (classSum_mul_apply Ci Cj w).symm
  rw [hsum]
  -- Each summand is the constant value `(classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out`.
  have hconst : ∀ w ∈ Finset.univ.filter (fun w : G => ConjClasses.mk w = Cs),
      (classSum Ci * classSum Cj : ℂ[G]).coeff w
        = (classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out := by
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [classSum_mul_apply_out, hw.2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [DecidableEq G] [Fintype (ConjClasses G)] in
/-- **Identity-class class-sum coefficient.**  The per-element coefficient of `1` in
`classSum Ci * classSum Cj` is the identity-class pair count `classSumCoeff Ci Cj 1`, since the
identity conjugacy class has one element. -/
theorem classSum_mul_apply_one_eq_classSumCoeff_one (Ci Cj : ConjClasses G) :
    (classSum Ci * classSum Cj : ℂ[G]).coeff (1 : G) = (classSumCoeff Ci Cj 1 : ℂ) := by
  classical
  have hcard : Nat.card { x : G // ConjClasses.mk x = (1 : ConjClasses G) } = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, (ConjClasses.one_eq_mk_one).symm⟩⟩⟩
    have ha : (a : G) = 1 := mk_eq_one_iff_eq_one.mp a.2
    have hb : (b : G) = 1 := mk_eq_one_iff_eq_one.mp b.2
    rw [ha, hb]
  have hout : (classSum Ci * classSum Cj : ℂ[G]).coeff (1 : ConjClasses G).out
      = (classSum Ci * classSum Cj : ℂ[G]).coeff (1 : G) := by
    simpa [ConjClasses.one_eq_mk_one] using (classSum_mul_apply_out Ci Cj (1 : G)).symm
  have h := coeff_mul_card_eq_classSumCoeff Ci Cj (1 : ConjClasses G)
  rw [hcard, Nat.cast_one, mul_one, hout] at h
  exact h

omit [DecidableEq G] [Fintype (ConjClasses G)] in
/-- The sum of per-element class-sum coefficients over any finite family of conjugacy classes is an
algebraic integer. -/
theorem isIntegral_sum_classSum_mul_coeff (Ci Cj : ConjClasses G) (s : Finset (ConjClasses G)) :
    IsIntegral ℤ (∑ Cs ∈ s, (classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) := by
  classical
  refine IsIntegral.sum _ fun Cs _ => ?_
  rw [classSum_mul_apply]
  exact isIntegral_algebraMap

/-- The nonidentity part of the class-sum product coefficient over the classes meeting `Z`.

This is Peterfalvi's `a_{ij}` after the `(6.7.2)` RHS has been collapsed: it sums the per-element
coefficients over the classes that meet `Z^#`. -/
noncomputable def nonidentityZClassCoeffSum (Z : Subgroup G) (Ci Cj : ConjClasses G) : ℂ := by
  classical
  exact ∑ Cs ∈ Finset.univ.filter
      (fun Cs : ConjClasses G => ∃ w : G, ConjClasses.mk w = Cs ∧ w ∈ Z ∧ w ≠ 1),
    (classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out

/-- The nonidentity `Z`-class coefficient sum is an algebraic integer. -/
theorem nonidentityZClassCoeffSum_isIntegral (Z : Subgroup G) (Ci Cj : ConjClasses G) :
    IsIntegral ℤ (nonidentityZClassCoeffSum Z Ci Cj) := by
  classical
  exact isIntegral_sum_classSum_mul_coeff Ci Cj _

omit [DecidableEq G] [Fintype (ConjClasses G)] in
set_option backward.isDefEq.respectTransparency false in
/-- **The term `ψ(1)·a_{ijs}·ω(C_s)` evaluated** (Peterfalvi (6.7.2), per-class term).  For an
irreducible representation `ρ` with character `ψ = χ_ρ`, the contribution of class `C_s` to
`ψ(1)·ω(C_i)·ω(C_j)` is `χ_ρ(1)·a_{ijs}·ω_ρ(C_s) = (a_{ijs}|C_s|)·χ_ρ(C_s.out)`, where
`a_{ijs}|C_s| = classSumCoeff Ci Cj Cs` is the pair count.  (Here `a_{ijs}` is the per-element
factorization count `(classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out`.) -/
theorem character_one_mul_coeff_mul_centralChar (ρ : Representation ℂ G V) [IsIrreducible ρ]
    (Ci Cj Cs : ConjClasses G) :
    ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * (ω ρ Cs))
      = (classSumCoeff Ci Cj Cs : ℂ) * ρ.character Cs.out := by
  classical
  have := nontrivial_of_isIrreducible ρ
  have hd : ρ.character 1 ≠ 0 := by
    rw [ρ.char_one]; exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hmkout : ConjClasses.mk Cs.out = Cs := by
    rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
  -- `ω(C_s) = (|C_s|·χ(C_s.out)) / χ(1)` (class-constancy of `χ` over `C_s`).
  have homega : (ω ρ Cs)
      = ((Nat.card { x : G // ConjClasses.mk x = Cs } : ℂ) * ρ.character Cs.out) / ρ.character 1 :=
    by rw [centralCharacterOfRep_classSum, sum_character_eq_card_mul ρ Cs hmkout, ρ.char_one]
  rw [homega]
  -- `a_{ijs}·|C_s| = classSumCoeff` (cast to `ℂ`).
  have hcoeff := coeff_mul_card_eq_classSumCoeff Ci Cj Cs
  -- `χ(1) * (m_s * (|C_s|·χ(out)/χ(1))) = m_s·|C_s|·χ(out) = classSumCoeff·χ(out)`.
  rw [show ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ)
        * ((Nat.card { x : G // ConjClasses.mk x = Cs } : ℂ) * ρ.character Cs.out / ρ.character 1))
      = (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ)
          * (Nat.card { x : G // ConjClasses.mk x = Cs } : ℂ) * ρ.character Cs.out)
          * (ρ.character 1 / ρ.character 1) by ring, div_self hd, mul_one, hcoeff]

omit [DecidableEq G] [Fintype (ConjClasses G)] in
/-- **A `C_s ∩ Z = ∅` term vanishes mod `|P|`** (Peterfalvi (6.7.1) ⟹ the per-class term of
(6.7.2)).  If the modulus `m` divides the pair-count `a_{ijs}|C_s| = classSumCoeff Ci Cj Cs` (which
(6.7.1) supplies via `card_dvd_classSumCoeff_of_fixedPointFree` for classes disjoint from `Z`), then
the term `ψ(1)·a_{ijs}·ω_ρ(C_s)` is `≡ 0 (mod m)`: it equals `(a_{ijs}|C_s|)·χ_ρ(C_s.out)`, an
algebraic-integer multiple of `m`. -/
theorem character_one_mul_coeff_mul_centralChar_cong_zero (ρ : Representation ℂ G V)
    [IsIrreducible ρ] [Finite G] {m : ℤ} (Ci Cj Cs : ConjClasses G)
    (hdvd : m ∣ (classSumCoeff Ci Cj Cs : ℤ)) (hm : (m : ℂ) ≠ 0) :
    ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * (ω ρ Cs))
      ≡ 0 [ALGMOD m] := by
  rw [character_one_mul_coeff_mul_centralChar]
  -- `classSumCoeff = m · k` (as integers); the term is `m · (k · χ(out))`, integral over `ℤ`.
  obtain ⟨k, hk⟩ := hdvd
  refine cong_of_exists_isIntegral hm (c := (k : ℂ) * ρ.character Cs.out) ?_ ?_
  · exact (isIntegral_algebraMap (x := k)).mul (character_isIntegral ρ Cs.out)
  · rw [sub_zero]
    have : ((classSumCoeff Ci Cj Cs : ℤ) : ℂ) = (m : ℂ) * (k : ℂ) := by rw [hk]; push_cast; ring
    push_cast at this ⊢
    rw [this]; ring

omit [DecidableEq G] in
/-- **Peterfalvi (6.7.2)** (product rule mod `|P|`).  For an irreducible representation `ρ` with
character `ψ = χ_ρ`, and a (decidable) predicate `inZ` selecting the conjugacy classes meeting `Z`
(Peterfalvi's `C_s ∩ Z^# ≠ ∅`), suppose the modulus `m` divides the pair-count
`classSumCoeff Ci Cj Cs` for every class `C_s` *disjoint* from `Z` (`¬ inZ C_s`) — exactly the
content of (6.7.1).  Then
`ψ(1)·ω(C_i)·ω(C_j) ≡ ∑_{s : C_s∩Z≠∅} ψ(1)·a_{ijs}·ω(C_s) (mod m)`,
i.e. the classes disjoint from `Z` drop out of `ψ(1)·ω(C_i)·ω(C_j)` modulo `m`.

This is Peterfalvi's identity `ψ(1)α² ≡ ψ(1)(a_{ij0} + a_{ij}α) (mod |P|)`: once `ω(C_s)` is the
constant `α` on the classes meeting `Z^#` and `ω(C_0) = 1`, the right-hand sum collapses to
`ψ(1)(a_{ij0} + a_{ij}α)`. -/
theorem centralCharacterOfRep_classSum_mul_cong [Finite G] (ρ : Representation ℂ G V)
    [IsIrreducible ρ] {m : ℤ} (Ci Cj : ConjClasses G) (inZ : ConjClasses G → Prop)
    [DecidablePred inZ]
    (hdvd : ∀ Cs : ConjClasses G, ¬ inZ Cs → m ∣ (classSumCoeff Ci Cj Cs : ℤ))
    (hm : (m : ℂ) ≠ 0) :
    ρ.character 1 * ((ω ρ Ci) * (ω ρ Cj))
      ≡ ∑ Cs ∈ Finset.univ.filter inZ,
          ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * (ω ρ Cs))
            [ALGMOD m] := by
  classical
  -- Expand `ψ(1)·ω(Ci)·ω(Cj)` as `∑_s ψ(1)·m_s·ω(C_s)` (product rule × ψ(1)).
  have hexpand : ρ.character 1 * ((ω ρ Ci) * (ω ρ Cj))
      = ∑ Cs : ConjClasses G,
          ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * (ω ρ Cs)) := by
    rw [centralCharacterOfRep_classSum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun Cs _ => ?_
    rw [smul_eq_mul]
  rw [hexpand]
  -- Split the full sum into the `inZ` and `¬ inZ` parts; the latter vanishes mod `m`.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ inZ]
  -- Reduce `(A + B) ≡ A` to `B ≡ 0`, then sum the per-class vanishing.
  have hsplit := (Cong.refl m (∑ Cs ∈ Finset.univ.filter inZ,
      ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * (ω ρ Cs)))).add
    (show (∑ Cs ∈ Finset.univ.filter (fun Cs => ¬ inZ Cs),
        ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * (ω ρ Cs)))
      ≡ 0 [ALGMOD m] from ?_)
  · simpa using hsplit
  · -- `∑_{¬inZ} term ≡ 0` by the per-class vanishing (sum of `≡0` terms is `≡0`).
    refine Finset.sum_induction _ (· ≡ 0 [ALGMOD m]) ?_ (Cong.refl m 0) ?_
    · intro a b ha hb; simpa using ha.add hb
    · intro Cs hCs
      rw [Finset.mem_filter] at hCs
      exact character_one_mul_coeff_mul_centralChar_cong_zero ρ Ci Cj Cs (hdvd Cs hCs.2) hm

omit [DecidableEq G] in
open OddOrder.GroupTheory Classical in
/-- **Peterfalvi (6.7.2)** (geometric form, modulus `|P|`).  This specializes
`centralCharacterOfRep_classSum_mul_cong` to the actual setup of (6.7): a Sylow `p`-subgroup
`P ≤ G`, a subgroup `Z ≤ P` that is *normal in* `L = N_G(P)`, and `P^# = P ∖ {1}` a TI-subset of `G`
with normalizer-bound `L`.  With the class-membership predicate `inZ Cs := ∃ w, ⟦w⟧ = Cs ∧ w ∈ Z`
(the classes meeting `Z`) and the two source classes `C_i`, `C_j` each meeting `Z^#`, one gets
`ψ(1)·ω(C_i)·ω(C_j) ≡ ∑_{C_s meets Z} ψ(1)·a_{ijs}·ω(C_s) (mod |P|)`.

The abstract divisibility hypothesis `hdvd` of `centralCharacterOfRep_classSum_mul_cong` is here
*discharged*: for a class `C_s` disjoint from `Z` (`¬ inZ C_s`), Peterfalvi (6.7.1) says `P` acts
fixed-point-freely by conjugation on `Ω = {(u,v) ∈ C_i × C_j ∣ uv ∈ C_s}`
(`fixedPointFree_classPair_of_isTISubset`), whence `|P| ∣ a_{ijs}|C_s|`
(`card_dvd_classSumCoeff_of_fixedPointFree`).  Thus the classes disjoint from `Z` drop out of
`ψ(1)·ω(C_i)·ω(C_j)` modulo `|P|`, the content Peterfalvi uses to pass to `(6.7.3)`. -/
theorem centralCharacterOfRep_classSum_mul_cong_of_isTISubset [Finite G]
    (ρ : Representation ℂ G V) [IsIrreducible ρ] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {Z : Subgroup G} (hZP : Z ≤ (P : Subgroup G))
    (hZnormal : (Z.subgroupOf (Subgroup.normalizer (P : Subgroup G))).Normal)
    (hti : OddOrder.GroupTheory.IsTISubset ((P : Set G) \ {1})
      (Subgroup.normalizer (P : Subgroup G)))
    {Ci Cj : ConjClasses G}
    (hCi : ∃ z : G, z ∈ Z ∧ z ≠ 1 ∧ ConjClasses.mk z = Ci)
    (hCj : ∃ z : G, z ∈ Z ∧ z ≠ 1 ∧ ConjClasses.mk z = Cj) :
    ρ.character 1 * ((ω ρ Ci) * (ω ρ Cj))
      ≡ ∑ Cs ∈ Finset.univ.filter (fun Cs => ∃ w : G, ConjClasses.mk w = Cs ∧ w ∈ Z),
          ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * (ω ρ Cs))
        [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
  classical
  -- The modulus `|P|` is a nonzero complex number (`P` is a finite group, hence nonempty).
  have hm : ((Nat.card (P : Subgroup G) : ℤ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℕ) < Nat.card (P : Subgroup G) := Nat.card_pos
    exact_mod_cast (Nat.cast_ne_zero (R := ℂ)).mpr hpos.ne'
  -- For every class `C_s` disjoint from `Z`, `(6.7.1)` gives `|P| ∣ a_{ijs}|C_s|`.
  refine centralCharacterOfRep_classSum_mul_cong ρ Ci Cj _ ?_ hm
  intro Cs hCs
  -- `¬ ∃ w, ⟦w⟧ = Cs ∧ w ∈ Z` is exactly the `(6.7.1)` hypothesis `∀ w, ⟦w⟧ = Cs → w ∉ Z`.
  have hCsZ : ∀ w : G, ConjClasses.mk w = Cs → w ∉ Z := by
    intro w hw hwZ; exact hCs ⟨w, hw, hwZ⟩
  -- The fixed-point-free hypothesis from `(6.7.1)`, then the counting divisibility.
  have hfree := fixedPointFree_classPair_of_isTISubset P hZP hZnormal hti hCi hCj hCsZ
  have hdvd : Nat.card (P : Subgroup G) ∣ classSumCoeff Ci Cj Cs :=
    card_dvd_classSumCoeff_of_fixedPointFree (P : Subgroup G) Ci Cj Cs hfree
  exact_mod_cast hdvd

open Classical in
/-- **Collapse of the `(6.7.2)` RHS over `Z`.**  If the central-character value is constant with
value `α` on every class meeting `Z^#`, then the sum over classes meeting `Z` splits into the
identity-class term plus `α` times the nonidentity `Z`-class coefficient sum.

This is the algebraic part of Peterfalvi's passage from the sum form of (6.7.2) to
`ψ(1)(a_{ij0}+a_{ij}α)`. -/
theorem centralCharacterOfRep_sum_inZ_eq_identity_add_nonidentity
    (ρ : Representation ℂ G V) [IsIrreducible ρ] (Z : Subgroup G)
    (Ci Cj : ConjClasses G) {α : ℂ}
    (hα : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 → ω ρ(ConjClasses.mk w) = α) :
    (∑ Cs ∈ Finset.univ.filter (fun Cs => ∃ w : G, ConjClasses.mk w = Cs ∧ w ∈ Z),
        ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * (ω ρ Cs)))
      = ρ.character 1 *
          (((classSum Ci * classSum Cj : ℂ[G]).coeff (1 : G) : ℂ)
            + nonidentityZClassCoeffSum Z Ci Cj * α) := by
  classical
  let inZ : ConjClasses G → Prop := fun Cs => ∃ w : G, ConjClasses.mk w = Cs ∧ w ∈ Z
  let inZsharp : ConjClasses G → Prop :=
    fun Cs => ∃ w : G, ConjClasses.mk w = Cs ∧ w ∈ Z ∧ w ≠ 1
  let term : ConjClasses G → ℂ := fun Cs =>
    ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * (ω ρ Cs))
  have hfilters :
      (Finset.univ.filter inZ).filter (fun Cs : ConjClasses G => Cs ≠ 1)
        = Finset.univ.filter inZsharp := by
    ext Cs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨w, hwCs, hwZ⟩, hCs1⟩
      refine ⟨w, hwCs, hwZ, ?_⟩
      intro hw1
      exact hCs1 (by simpa [hw1, ConjClasses.one_eq_mk_one] using hwCs.symm)
    · rintro ⟨w, hwCs, hwZ, hw1⟩
      refine ⟨⟨w, hwCs, hwZ⟩, ?_⟩
      intro hCs1
      exact hw1 (mk_eq_one_iff_eq_one.mp (by simpa [hCs1] using hwCs))
  have hid :
      (∑ Cs ∈ (Finset.univ.filter inZ).filter (fun Cs : ConjClasses G => Cs = 1), term Cs)
        = ρ.character 1 * ((classSum Ci * classSum Cj : ℂ[G]).coeff (1 : G)) := by
    rw [Finset.sum_eq_single (1 : ConjClasses G)]
    · have hout : (classSum Ci * classSum Cj : ℂ[G]).coeff (1 : ConjClasses G).out
          = (classSum Ci * classSum Cj : ℂ[G]).coeff (1 : G) := by
        simpa [ConjClasses.one_eq_mk_one] using (classSum_mul_apply_out Ci Cj (1 : G)).symm
      change ρ.character 1 *
          (((classSum Ci * classSum Cj : ℂ[G]).coeff (1 : ConjClasses G).out : ℂ)
            * (ω ρ (1 : ConjClasses G)))
        = ρ.character 1 * ((classSum Ci * classSum Cj : ℂ[G]).coeff (1 : G))
      rw [hout, centralCharacterOfRep_one]
      ring
    · intro Cs hCs hne
      rw [Finset.mem_filter] at hCs
      exact (hne hCs.2).elim
    · intro hnot
      exfalso
      exact hnot (by
        rw [Finset.mem_filter]
        exact ⟨by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, ⟨1, (ConjClasses.one_eq_mk_one).symm, Z.one_mem⟩⟩, rfl⟩)
  have hnon :
      (∑ Cs ∈ (Finset.univ.filter inZ).filter (fun Cs : ConjClasses G => Cs ≠ 1), term Cs)
        = ρ.character 1 * (nonidentityZClassCoeffSum Z Ci Cj * α) := by
    rw [hfilters, nonidentityZClassCoeffSum]
    have hterm : ∀ Cs ∈ Finset.univ.filter inZsharp,
        term Cs = ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * α) := by
      intro Cs hCs
      rw [Finset.mem_filter] at hCs
      obtain ⟨w, hwCs, hwZ, hw1⟩ := hCs.2
      have hω : ω ρ Cs = α := by
        simpa [hwCs] using hα hwZ hw1
      change ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * (ω ρ Cs))
        = ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * α)
      rw [hω]
    calc
      (∑ Cs ∈ Finset.univ.filter inZsharp, term Cs)
          = ∑ Cs ∈ Finset.univ.filter inZsharp,
              ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * α) :=
        Finset.sum_congr rfl hterm
      _ = ρ.character 1 *
          ((∑ Cs ∈ Finset.univ.filter inZsharp,
            (classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out) * α) := by
        rw [Finset.sum_mul, Finset.mul_sum]
  calc
    (∑ Cs ∈ Finset.univ.filter (fun Cs => ∃ w : G, ConjClasses.mk w = Cs ∧ w ∈ Z),
        ρ.character 1 * (((classSum Ci * classSum Cj : ℂ[G]).coeff Cs.out : ℂ) * (ω ρ Cs)))
        = ∑ Cs ∈ Finset.univ.filter inZ, term Cs := rfl
    _ = (∑ Cs ∈ (Finset.univ.filter inZ).filter (fun Cs : ConjClasses G => Cs = 1), term Cs)
        + ∑ Cs ∈ (Finset.univ.filter inZ).filter (fun Cs : ConjClasses G => Cs ≠ 1),
            term Cs := by
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter inZ)
            (fun Cs : ConjClasses G => Cs = 1)]
    _ = ρ.character 1 * ((classSum Ci * classSum Cj : ℂ[G]).coeff (1 : G))
        + ρ.character 1 * (nonidentityZClassCoeffSum Z Ci Cj * α) := by rw [hid, hnon]
    _ = ρ.character 1 *
          (((classSum Ci * classSum Cj : ℂ[G]).coeff (1 : G) : ℂ)
            + nonidentityZClassCoeffSum Z Ci Cj * α) := by ring

/-- **Peterfalvi (6.7.2), collapsed geometric form.**  This combines the geometric product-rule
congruence with the RHS collapse over the classes meeting `Z`: if `ω` is constant with value `α` on
classes meeting `Z^#`, then
`ψ(1)ω(C_i)ω(C_j) ≡ ψ(1)(a_{ij0}+a_{ij}α) (mod |P|)`, where `a_{ij0}` is the identity coefficient
and `a_{ij}` is `nonidentityZClassCoeffSum`.

The sole remaining mathematical input here is the constancy of `ω` on `Z^#`; the divisibility of
the classes disjoint from `Z` has already been discharged from the TI/Sylow setup. -/
theorem centralCharacterOfRep_classSum_mul_cong_collapse_of_isTISubset [Finite G]
    (ρ : Representation ℂ G V) [IsIrreducible ρ] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    {Z : Subgroup G} (hZP : Z ≤ (P : Subgroup G))
    (hZnormal : (Z.subgroupOf (Subgroup.normalizer (P : Subgroup G))).Normal)
    (hti : OddOrder.GroupTheory.IsTISubset ((P : Set G) \ {1})
      (Subgroup.normalizer (P : Subgroup G)))
    {Ci Cj : ConjClasses G}
    (hCi : ∃ z : G, z ∈ Z ∧ z ≠ 1 ∧ ConjClasses.mk z = Ci)
    (hCj : ∃ z : G, z ∈ Z ∧ z ≠ 1 ∧ ConjClasses.mk z = Cj)
    {α : ℂ} (hα : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 → ω ρ(ConjClasses.mk w) = α) :
    ρ.character 1 * ((ω ρ Ci) * (ω ρ Cj))
      ≡ ρ.character 1 *
          (((classSum Ci * classSum Cj : ℂ[G]).coeff (1 : G) : ℂ)
            + nonidentityZClassCoeffSum Z Ci Cj * α)
        [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
  classical
  have hsum :=
    centralCharacterOfRep_classSum_mul_cong_of_isTISubset ρ P hZP hZnormal hti hCi hCj
  convert hsum using 1
  exact (centralCharacterOfRep_sum_inZ_eq_identity_add_nonidentity ρ Z Ci Cj hα).symm

end ClassCongruence

end OddOrder.RepresentationTheory


