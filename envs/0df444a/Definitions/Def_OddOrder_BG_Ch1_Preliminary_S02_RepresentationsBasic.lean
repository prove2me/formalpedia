-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_RepresentationsBasic
-- name    : OddOrder_BG_Ch1_Preliminary_S02_RepresentationsBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:31:47.639234+00:00
-- url     : https://prove2.me/theorems/0c935319-b233-4f41-bd5f-ce551c947106
-- title:
--   Bender–Glauberman §2: basics of representations
-- statement:
--   A part of the Bender–Glauberman §2 formalization (representations), covering one-dimensional representations, conjugation of subrepresentations, and the subgroup acting trivially on a submodule and on its quotient.
--
--   Main definitions: `scalarMonoidHomOfFinrankEqOne` and `scalarCharacterOfFinrankEqOne` (the scalar character of a representation on a one-dimensional module), `finrank_eq_one_of_simple_submodule_of_commutative_group` (simple submodules for abelian groups have dimension one), `conjugateSubrepresentationOfNormal` (conjugating a subrepresentation by an ambient element), and `fixedOnSubmoduleAndQuotientSubgroup` (the subgroup acting trivially on $W$ and on $V/W$).
--
--   The bundle also proves 30 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S02_RepresentationsBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S02_RepresentationsBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_IsExtraspecial
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_EigenspaceUnderCyclicAction
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_PGroupFixedVector
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BaseChange
import Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Main
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Main
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Submodule
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

namespace OddOrder.BG.Ch1.S02

open scoped Pointwise

open OddOrder.RepresentationTheory (baseChangeRepresentation baseChangeRepresentation_apply_tmul
  baseChangeRepresentation_faithful)

/-- In characteristic `p`, a field element whose `p^n`-th power is `1` is `1`.

This is the scalar calculation used in BG Thm 2.6, q = p: the multiplicative
group of a characteristic-`p` field has no nontrivial `p`-power torsion. -/
private theorem eq_one_of_pow_prime_pow_eq_one
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    (x : F) {n : ℕ} (hx : x ^ p ^ n = 1) : x = 1 := by
  have hsub : (x - 1) ^ p ^ n = 0 := by
    rw [sub_pow_char_pow_of_commute p n (Commute.one_right x), hx, one_pow, sub_self]
  have hxsub : x - 1 = 0 := eq_zero_of_pow_eq_zero hsub
  exact sub_eq_zero.mp hxsub

/-- Unit-valued version of `eq_one_of_pow_prime_pow_eq_one`. -/
private theorem unit_eq_one_of_pow_prime_pow_eq_one
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    (u : Fˣ) {n : ℕ} (hu : u ^ p ^ n = 1) : u = 1 := by
  ext
  exact eq_one_of_pow_prime_pow_eq_one (p := p) (u : F) (by
    simpa using congrArg Units.val hu)

/-- A p-group has no nontrivial scalar characters over a characteristic-`p` field. -/
private theorem monoidHom_units_eq_one_of_isPGroup_charP
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    (hG : IsPGroup p G) {F : Type*} [Field F] [CharP F p]
    (φ : G →* Fˣ) : φ = 1 := by
  ext g
  obtain ⟨n, hg⟩ := hG g
  exact congrArg Units.val <|
    unit_eq_one_of_pow_prime_pow_eq_one (p := p) (φ g) (n := n) (by
      rw [← map_pow, hg, map_one])

/-- A nonzero proper submodule of a two-dimensional vector space has dimension one,
and so does its quotient. -/
theorem rank_one_subquotients_of_finrank_two
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) (hdim : Module.finrank F V = 2)
    (hW_ne_bot : W ≠ ⊥) (hW_ne_top : W ≠ ⊤) :
    Module.finrank F W = 1 ∧ Module.finrank F (V ⧸ W) = 1 := by
  have hW_pos : 1 ≤ Module.finrank F W := by
    rw [Submodule.one_le_finrank_iff]
    exact hW_ne_bot
  have hW_lt : Module.finrank F W < 2 := by
    have hlt : Module.finrank F W < Module.finrank F V :=
      Submodule.finrank_lt hW_ne_top
    simpa [hdim] using hlt
  have hdimW : Module.finrank F W = 1 := by
    omega
  have hsum : Module.finrank F (V ⧸ W) + Module.finrank F W = 2 := by
    simpa [hdim] using W.finrank_quotient_add_finrank
  refine ⟨hdimW, ?_⟩
  omega

/-- If a rank-one submodule has a complement in a two-dimensional space, then
the complementary submodule and its quotient are rank one as well. -/
private theorem complement_rank_one_right_subquotients_of_finrank_two
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W U : Submodule F V) (hdim : Module.finrank F V = 2)
    (hcompl : IsCompl W U) (hWdim : Module.finrank F W = 1) :
    Module.finrank F U = 1 ∧ Module.finrank F (V ⧸ U) = 1 := by
  have hsum : Module.finrank F W + Module.finrank F U = Module.finrank F V := by
    simpa using Submodule.finrank_add_eq_of_isCompl hcompl
  have hUdim : Module.finrank F U = 1 := by
    omega
  have hU_ne_bot : U ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff]
    omega
  have hU_ne_top : U ≠ ⊤ := by
    intro hU_top
    have h12 : (1 : ℕ) = 2 := by
      calc
        1 = Module.finrank F U := hUdim.symm
        _ = Module.finrank F (⊤ : Submodule F V) := by rw [hU_top]
        _ = Module.finrank F V := finrank_top F V
        _ = 2 := hdim
    omega
  exact ⟨hUdim,
    (rank_one_subquotients_of_finrank_two U hdim hU_ne_bot hU_ne_top).2⟩

/-- Two rank-one submodules with nonzero intersection are equal. -/
private theorem eq_of_rank_one_submodules_inf_ne_bot
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    {W U : Submodule F V}
    (hWdim : Module.finrank F W = 1) (hUdim : Module.finrank F U = 1)
    (hinf : W ⊓ U ≠ ⊥) :
    W = U := by
  have hinf_pos : 1 ≤ Module.finrank F (W ⊓ U : Submodule F V) := by
    rw [Submodule.one_le_finrank_iff]
    exact hinf
  have hinf_le_W :
      Module.finrank F (W ⊓ U : Submodule F V) ≤ Module.finrank F W :=
    Submodule.finrank_mono inf_le_left
  have hinf_le_U :
      Module.finrank F (W ⊓ U : Submodule F V) ≤ Module.finrank F U :=
    Submodule.finrank_mono inf_le_right
  have hinf_dim_W :
      Module.finrank F (W ⊓ U : Submodule F V) = Module.finrank F W := by
    omega
  have hinf_dim_U :
      Module.finrank F (W ⊓ U : Submodule F V) = Module.finrank F U := by
    omega
  have hW : W ⊓ U = W :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left hinf_dim_W
  have hU : W ⊓ U = U :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right hinf_dim_U
  exact hW.symm.trans hU

/-- A rank-one invariant submodule of a two-line diagonal action lies on one
of the two eigenspaces.

This is the linear-algebra core of the BG Thm 2.6 q≠p sentence that, after
choosing `x ∈ K#` with distinct eigenvalues on the two Maschke lines, those
two lines are the only one-dimensional `K`-submodules. -/
theorem rank_one_invariant_submodule_eq_left_or_right_of_distinct_scalars
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W U L : Submodule F V) (f : Module.End F V)
    (hcompl : IsCompl W U)
    (hWdim : Module.finrank F W = 1) (hUdim : Module.finrank F U = 1)
    (hLdim : Module.finrank F L = 1)
    (hLstable : L ≤ L.comap f)
    (a b : F) (hab : a ≠ b)
    (hWscalar : ∀ w ∈ W, f w = a • w)
    (hUscalar : ∀ u ∈ U, f u = b • u) :
    L = W ∨ L = U := by
  have hL_ne_bot : L ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff]
    omega
  rcases Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hL_ne_bot) with
    ⟨l, hl_ne_zero⟩
  let v : V := l
  have hvL : v ∈ L := l.2
  obtain ⟨w, u, hv, _huniq⟩ := Submodule.existsUnique_add_of_isCompl hcompl v
  have hab_sub : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hba_sub : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hw_mem_L : (w : V) ∈ L := by
    have hdiff_mem : f v - b • v ∈ L :=
      L.sub_mem (hLstable hvL) (L.smul_mem b hvL)
    have hdiff_eq : f v - b • v = (a - b) • (w : V) := by
      rw [← hv, map_add, hWscalar (w : V) w.2, hUscalar (u : V) u.2]
      module
    have hscaled : (a - b) • (w : V) ∈ L := by
      simpa [hdiff_eq] using hdiff_mem
    exact (L.smul_mem_iff hab_sub).mp hscaled
  have hu_mem_L : (u : V) ∈ L := by
    have hdiff_mem : f v - a • v ∈ L :=
      L.sub_mem (hLstable hvL) (L.smul_mem a hvL)
    have hdiff_eq : f v - a • v = (b - a) • (u : V) := by
      rw [← hv, map_add, hWscalar (w : V) w.2, hUscalar (u : V) u.2]
      module
    have hscaled : (b - a) • (u : V) ∈ L := by
      simpa [hdiff_eq] using hdiff_mem
    exact (L.smul_mem_iff hba_sub).mp hscaled
  by_cases hw_zero : (w : V) = 0
  · right
    have hvU : v ∈ U := by
      rw [← hv, hw_zero, zero_add]
      exact u.2
    apply eq_of_rank_one_submodules_inf_ne_bot hLdim hUdim
    intro hbot
    have hv_inf : v ∈ L ⊓ U := ⟨hvL, hvU⟩
    have hv_zero : v = 0 := by
      have : v ∈ (⊥ : Submodule F V) := by simpa [hbot] using hv_inf
      simpa using this
    exact hl_ne_zero (Subtype.ext hv_zero)
  by_cases hu_zero : (u : V) = 0
  · left
    have hvW : v ∈ W := by
      rw [← hv, hu_zero, add_zero]
      exact w.2
    apply eq_of_rank_one_submodules_inf_ne_bot hLdim hWdim
    intro hbot
    have hv_inf : v ∈ L ⊓ W := ⟨hvL, hvW⟩
    have hv_zero : v = 0 := by
      have : v ∈ (⊥ : Submodule F V) := by simpa [hbot] using hv_inf
      simpa using this
    exact hl_ne_zero (Subtype.ext hv_zero)
  · have hLW : L = W := by
      apply eq_of_rank_one_submodules_inf_ne_bot hLdim hWdim
      intro hbot
      have hw_inf : (w : V) ∈ L ⊓ W := ⟨hw_mem_L, w.2⟩
      have hw_bot : (w : V) ∈ (⊥ : Submodule F V) := by
        simpa [hbot] using hw_inf
      exact hw_zero (by simpa using hw_bot)
    have hLU : L = U := by
      apply eq_of_rank_one_submodules_inf_ne_bot hLdim hUdim
      intro hbot
      have hu_inf : (u : V) ∈ L ⊓ U := ⟨hu_mem_L, u.2⟩
      have hu_bot : (u : V) ∈ (⊥ : Submodule F V) := by
        simpa [hbot] using hu_inf
      exact hu_zero (by simpa using hu_bot)
    have hWU : W = U := hLW.symm.trans hLU
    have hW_ne_bot : W ≠ ⊥ := by
      rw [← Submodule.one_le_finrank_iff]
      omega
    have hW_eq_bot : W = ⊥ := by
      have hWinf : W ⊓ U = W := by rw [hWU, inf_idem]
      simpa [hcompl.inf_eq_bot] using hWinf.symm
    exact False.elim (hW_ne_bot hW_eq_bot)

/-- A representation on a one-dimensional module has a scalar monoid character. -/
private noncomputable def scalarMonoidHomOfFinrankEqOne
    {F : Type*} [Field F] {G : Type*} [Monoid G]
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (ρ : Representation F G M) : G →* F where
  toFun g := (LinearEquiv.smul_id_of_finrank_eq_one hdim).symm (ρ g)
  map_one' := by
    let e := LinearEquiv.smul_id_of_finrank_eq_one hdim
    apply e.injective
    ext m
    simp [e]
  map_mul' g h := by
    let e := LinearEquiv.smul_id_of_finrank_eq_one hdim
    let cg : F := e.symm (ρ g)
    let ch : F := e.symm (ρ h)
    have hg_apply : ∀ m : M, ρ g m = cg • m := by
      intro m
      have hg_eq : e cg = ρ g := by simp [cg]
      simpa [e] using congrArg (fun u : Module.End F M => u m) hg_eq.symm
    have hh_apply : ∀ m : M, ρ h m = ch • m := by
      intro m
      have hh_eq : e ch = ρ h := by simp [ch]
      simpa [e] using congrArg (fun u : Module.End F M => u m) hh_eq.symm
    apply e.injective
    change e (e.symm (ρ (g * h))) = e (cg * ch)
    rw [e.apply_symm_apply]
    ext m
    change ρ (g * h) m = (cg * ch) • m
    rw [map_mul]
    change ρ g (ρ h m) = (cg * ch) • m
    rw [hh_apply, hg_apply]
    exact (mul_smul cg ch m).symm

/-- The scalar monoid character indeed describes the representation action. -/
private theorem scalarMonoidHomOfFinrankEqOne_apply_smul
    {F : Type*} [Field F] {G : Type*} [Monoid G]
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (ρ : Representation F G M) (g : G) (m : M) :
    ρ g m = (scalarMonoidHomOfFinrankEqOne hdim ρ g : F) • m := by
  let e := LinearEquiv.smul_id_of_finrank_eq_one hdim
  change ρ g m = e (e.symm (ρ g)) m
  rw [e.apply_symm_apply]

/-- The scalar monoid character of a group representation on a one-dimensional module
lands in units. -/
noncomputable def scalarCharacterOfFinrankEqOne
    {F : Type*} [Field F] {G : Type*} [Group G]
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (ρ : Representation F G M) : G →* Fˣ :=
  let ψ := scalarMonoidHomOfFinrankEqOne hdim ρ
  { toFun := fun g =>
      { val := ψ g
        inv := ψ g⁻¹
        val_inv := by
          have h := map_mul ψ g g⁻¹
          simpa using h.symm
        inv_val := by
          have h := map_mul ψ g⁻¹ g
          simpa using h.symm }
    map_one' := by
      ext
      simp [ψ]
    map_mul' := by
      intro g h
      ext
      exact map_mul ψ g h }

/-- The unit-valued scalar character describes the representation action. -/
theorem scalarCharacterOfFinrankEqOne_apply_smul
    {F : Type*} [Field F] {G : Type*} [Group G]
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (ρ : Representation F G M) (g : G) (m : M) :
    ρ g m = (scalarCharacterOfFinrankEqOne hdim ρ g : F) • m :=
  scalarMonoidHomOfFinrankEqOne_apply_smul hdim ρ g m

/-- A scalar endomorphism of a one-dimensional module has that scalar as determinant. -/
theorem det_eq_scalar_of_finrank_eq_one
    {F : Type*} [Field F]
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (f : Module.End F M) (c : F)
    (hf : ∀ m : M, f m = c • m) :
    LinearMap.det f = c := by
  have hf_eq : f = c • (LinearMap.id : Module.End F M) := by
    ext m
    simpa using hf m
  calc
    LinearMap.det f = LinearMap.det (c • (LinearMap.id : Module.End F M)) := by
      rw [hf_eq]
    _ = c := by
      simp [hdim]

/-- Characteristic-away bridge for Maschke in the BG Thm 2.6 q≠p branch.

If `K` is a finite q-group and the field has characteristic `p ≠ q`, then
`|K|` is nonzero in the field.  This is the exact typeclass premise needed by
mathlib's Maschke theorem. -/
private theorem neZero_nat_card_cast_of_isPGroup_ne_char
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {F : Type*} [Field F] [CharP F p]
    {K : Type*} [Group K] [Finite K]
    (hK : IsPGroup q K) (hq_ne_p : q ≠ p) :
    NeZero (Nat.card K : F) := by
  refine ⟨?_⟩
  intro hzero
  have hp_dvd_card : p ∣ Nat.card K :=
    (CharP.cast_eq_zero_iff F p (Nat.card K)).mp hzero
  rcases (IsPGroup.iff_card (p := q) (G := K)).mp hK with ⟨n, hcard⟩
  rw [hcard] at hp_dvd_card
  have hp_prime : p.Prime := Fact.out
  have hq_prime : q.Prime := Fact.out
  have hp_dvd_q : p ∣ q := hp_prime.dvd_of_dvd_pow hp_dvd_card
  exact hq_ne_p ((Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hp_dvd_q).symm

/-- Maschke cardinality bridge from a theorem-level characteristic-away
hypothesis.

If no prime divisor of `|K|` is the characteristic of `F`, then `|K|` is
nonzero in `F`.  This is the exact bridge from BG Thm 2.6(a)'s hypothesis to
Maschke's typeclass premise. -/
private theorem neZero_nat_card_cast_of_forall_prime_not_char
    {F : Type*} [Field F] {K : Type*} [Group K] [Finite K]
    (hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card K → ¬ CharP F q) :
    NeZero (Nat.card K : F) := by
  rcases CharP.exists' F with hzero | hpos
  · have : CharZero F := hzero
    refine ⟨?_⟩
    intro hcast
    exact (Nat.card_pos (α := K)).ne' (Nat.cast_eq_zero.mp hcast)
  · rcases hpos with ⟨p, hp_prime, hp_char⟩
    have : CharP F p := hp_char
    refine NeZero.of_not_dvd (R := F) (p := p) (n := Nat.card K) ?_
    intro hp_dvd
    exact (hchar p hp_prime.out hp_dvd) hp_char

/-- Subgroup form of `neZero_nat_card_cast_of_forall_prime_not_char`.

The theorem-level hypothesis in BG Thm 2.6(a) is stated for `G`; Maschke is
applied to normal q-subgroups `K ≤ G`. -/
theorem neZero_nat_card_cast_of_subgroup_forall_prime_not_char
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → ¬ CharP F q)
    (K : Subgroup G) :
    NeZero (Nat.card K : F) := by
  exact neZero_nat_card_cast_of_forall_prime_not_char
    (F := F) (K := K)
    (fun q hq_prime hq_dvd =>
      hchar q hq_prime (hq_dvd.trans (Subgroup.card_subgroup_dvd_card K)))

/-- Maschke simple-constituent extraction from the exact cardinality premise.

This is the Maschke core needed in BG Thm 2.6: if `|K|` is nonzero in the
field, then the group-algebra module attached to a nonzero representation has
a simple submodule.  Characteristic-specific lemmas below only have to supply
this `NeZero` instance. -/
private theorem exists_simple_submodule_of_neZero_card
    {F : Type*} [Field F]
    {K : Type*} [Group K] [Finite K]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V]
    [NeZero (Nat.card K : F)]
    (σ : Representation F K V) :
    ∃ N : Submodule (MonoidAlgebra F K) σ.asModule,
      IsSimpleModule (MonoidAlgebra F K) N := by
  let : AddCommGroup σ.asModule := Representation.instAddCommGroupAsModule σ
  let : Module F σ.asModule := Representation.instModuleAsModule σ
  let : Module (MonoidAlgebra F K) σ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule σ
  let : IsScalarTower F (MonoidAlgebra F K) σ.asModule := inferInstance
  have hnontriv : Nontrivial σ.asModule := by
    change Nontrivial V
    infer_instance
  have hsemi :
      @IsSemisimpleModule (MonoidAlgebra F K) inferInstance σ.asModule
        (Representation.instAddCommGroupAsModule σ)
        (Representation.instModuleMonoidAlgebraAsModule σ) := by
    infer_instance
  exact @IsSemisimpleModule.exists_simple_submodule
      (MonoidAlgebra F K) inferInstance σ.asModule
      (Representation.instAddCommGroupAsModule σ)
      (Representation.instModuleMonoidAlgebraAsModule σ) hsemi hnontriv

open scoped IsMulCommutative in
/-- Scalar-instance bridge for a simple group-algebra submodule of an abelian group.

The simple object naturally lives as a `MonoidAlgebra F K`-submodule of
`σ.asModule`, whereas the BG line argument needs its underlying
`F`-subrepresentation.  This lemma performs that transport and applies the
commutative Schur finrank-one result at the group-algebra level. -/
private theorem finrank_eq_one_of_simple_submodule_of_commutative_group
    {F : Type*} [Field F] [IsAlgClosed F] {K : Type*} [Group K]
    (hKcomm : Std.Commutative (· * · : K → K → K))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (σ : Representation F K V)
    (N : Submodule (MonoidAlgebra F K) σ.asModule)
    (hNsimple : IsSimpleModule (MonoidAlgebra F K) N) :
    Module.finrank F (Subrepresentation.ofSubmodule' N).toSubmodule = 1 := by
  have : IsSimpleModule (MonoidAlgebra F K) N := hNsimple
  let : Module F N :=
    @Submodule.module' F (MonoidAlgebra F K) σ.asModule
      inferInstance inferInstance
      (Representation.instModuleMonoidAlgebraAsModule σ)
      N inferInstance inferInstance (Representation.instModuleAsModule σ) inferInstance
  let : IsScalarTower F (MonoidAlgebra F K) N :=
    @Submodule.isScalarTower F (MonoidAlgebra F K) σ.asModule
      inferInstance inferInstance (Representation.instModuleMonoidAlgebraAsModule σ)
      N inferInstance inferInstance inferInstance
  have hfiniteN : Module.Finite F N := by
    let NF : Submodule F σ.asModule :=
      @Submodule.restrictScalars F (MonoidAlgebra F K) σ.asModule
        inferInstance inferInstance inferInstance
        (Representation.instModuleAsModule σ)
        (Representation.instModuleMonoidAlgebraAsModule σ)
        inferInstance inferInstance N
    have hfiniteAs : Module.Finite F σ.asModule := .equiv σ.asModuleEquiv.symm
    have hfiniteTop : Module.Finite F (⊤ : Submodule F σ.asModule) :=
      @Module.Finite.top F σ.asModule inferInstance inferInstance
        (Representation.instModuleAsModule σ) hfiniteAs
    have hfiniteNF : Module.Finite F NF :=
      @Submodule.finiteDimensional_of_le F σ.asModule
        inferInstance inferInstance (Representation.instModuleAsModule σ)
        NF ⊤ hfiniteTop le_top
    exact hfiniteNF.equiv
      ((Submodule.restrictScalarsEquiv F (MonoidAlgebra F K) σ.asModule N).restrictScalars F)
  have : IsMulCommutative K := ⟨hKcomm⟩
  have : IsMulCommutative (MonoidAlgebra F K) := inferInstance
  have hNdim : Module.finrank F N = 1 :=
    @IsSimpleModule.finrank_eq_one_of_isMulCommutative
      (MonoidAlgebra F K) N F
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance hfiniteN inferInstance inferInstance
  let W : Subrepresentation σ := Subrepresentation.ofSubmodule' N
  change Module.finrank F W.toSubmodule = 1
  let eW : W.toSubmodule ≃ₗ[F] N :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [eW.finrank_eq]
  exact hNdim

/-- Maschke complement extraction from the exact cardinality premise.

For a two-dimensional representation of an abelian finite group whose order is
nonzero in the field, Maschke gives an invariant complement to a simple
rank-one constituent.  This is the characteristic-free core behind both the
q≠p branch and the characteristic-away branch of BG Thm 2.6(a). -/
private theorem exists_rank_one_complement_subrepresentations_of_commutative_of_neZero_card
    {F : Type*} [Field F] [IsAlgClosed F]
    {K : Type*} [Group K] [Finite K]
    (hKcomm : Std.Commutative (· * · : K → K → K))
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] [Nontrivial V]
    [NeZero (Nat.card K : F)]
    (σ : Representation F K V) (hdim : Module.finrank F V = 2) :
    ∃ W U : Subrepresentation σ,
      W ≠ ⊥ ∧ IsCompl W.toSubmodule U.toSubmodule ∧
        Module.finrank F W.toSubmodule = 1 ∧
        Module.finrank F (V ⧸ W.toSubmodule) = 1 := by
  let : AddCommGroup σ.asModule := Representation.instAddCommGroupAsModule σ
  let : Module F σ.asModule := Representation.instModuleAsModule σ
  let : Module (MonoidAlgebra F K) σ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule σ
  let : IsScalarTower F (MonoidAlgebra F K) σ.asModule := inferInstance
  rcases exists_simple_submodule_of_neZero_card (K := K) σ with
    ⟨N, hNsimple⟩
  rcases (@MonoidAlgebra.Submodule.exists_isCompl F inferInstance K inferInstance
      inferInstance inferInstance σ.asModule (Representation.instAddCommGroupAsModule σ)
      (Representation.instModuleMonoidAlgebraAsModule σ) N) with
    ⟨Q, hNQ⟩
  let W : Subrepresentation σ := Subrepresentation.ofSubmodule' N
  let U : Subrepresentation σ := Subrepresentation.ofSubmodule' Q
  have hWdim :
      Module.finrank F W.toSubmodule = 1 :=
    finrank_eq_one_of_simple_submodule_of_commutative_group hKcomm σ N hNsimple
  have hsubrep_compl : IsCompl W U :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := σ)).symm.isCompl hNQ
  have hcompl : IsCompl W.toSubmodule U.toSubmodule := by
    refine IsCompl.of_eq ?_ ?_
    · have h := congrArg Subrepresentation.toSubmodule hsubrep_compl.inf_eq_bot
      rw [Subrepresentation.toSubmodule_inf] at h
      exact h
    · have h := congrArg Subrepresentation.toSubmodule hsubrep_compl.sup_eq_top
      rw [Subrepresentation.toSubmodule_sup] at h
      exact h
  have : IsSimpleModule (MonoidAlgebra F K) N := hNsimple
  have hW_ne_bot_sub : W.toSubmodule ≠ ⊥ := by
    have hN_nontrivial : Nontrivial N :=
      IsSimpleModule.nontrivial (MonoidAlgebra F K) N
    have hW_nontrivial : Nontrivial W.toSubmodule := by
      change Nontrivial N
      exact hN_nontrivial
    exact W.toSubmodule.nontrivial_iff_ne_bot.mp hW_nontrivial
  have hW_ne_bot : W ≠ ⊥ := by
    intro hW_bot
    exact hW_ne_bot_sub (congrArg Subrepresentation.toSubmodule hW_bot)
  have hW_ne_top_sub : W.toSubmodule ≠ ⊤ := by
    intro hW_top
    have h12 : (1 : ℕ) = 2 := by
      calc
        1 = Module.finrank F W.toSubmodule := hWdim.symm
        _ = Module.finrank F (⊤ : Submodule F V) := by rw [hW_top]
        _ = Module.finrank F V := finrank_top F V
        _ = 2 := hdim
    omega
  have hQdim :
      Module.finrank F (V ⧸ W.toSubmodule) = 1 :=
    (rank_one_subquotients_of_finrank_two W.toSubmodule hdim hW_ne_bot_sub
      hW_ne_top_sub).2
  exact ⟨W, U, hW_ne_bot, hcompl, hWdim, hQdim⟩

/-- Maschke complement extraction packaged in the theorem-facing data shape.

This is the cardinality-premise version of the rank-one data bridge.  It
keeps the linear-algebra input aligned with Maschke's actual hypothesis,
allowing theorem-level characteristic-away assumptions to supply `NeZero`
without manufacturing a separate characteristic prime. -/
theorem exists_rank_one_KSubmodule_data_of_commutative_of_neZero_card
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hdim : Module.finrank F V = 2)
    (K : Subgroup G) [NeZero (Nat.card K : F)]
    (hKcomm : Std.Commutative (· * · : K → K → K)) :
    ∃ W : Subrepresentation (ρ.comp K.subtype),
    ∃ U : Subrepresentation (ρ.comp K.subtype),
      Nonempty (Module.Free F W.toSubmodule) ∧
      Nonempty (Module.Free F U.toSubmodule) ∧
      Nonempty (Module.Finite F W.toSubmodule) ∧
      Nonempty (Module.Finite F U.toSubmodule) ∧
      Nonempty (Module.Free F (V ⧸ W.toSubmodule)) ∧
      Nonempty (Module.Free F (V ⧸ U.toSubmodule)) ∧
      IsCompl W.toSubmodule U.toSubmodule ∧
      Module.finrank F W.toSubmodule = 1 ∧
      Module.finrank F U.toSubmodule = 1 ∧
      Module.finrank F (V ⧸ W.toSubmodule) = 1 ∧
      Module.finrank F (V ⧸ U.toSubmodule) = 1 := by
  have hVpos : 0 < Module.finrank F V := by
    rw [hdim]
    norm_num
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (M := V) hVpos
  rcases exists_rank_one_complement_subrepresentations_of_commutative_of_neZero_card
      (F := F) (K := K) hKcomm (ρ.comp K.subtype) hdim with
    ⟨W, U, _hW_ne_bot, hcompl, hdimW, hdimQW⟩
  rcases complement_rank_one_right_subquotients_of_finrank_two
      W.toSubmodule U.toSubmodule hdim hcompl hdimW with
    ⟨hdimU, hdimQU⟩
  exact ⟨W, U, ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩,
    ⟨inferInstance⟩, ⟨inferInstance⟩, ⟨inferInstance⟩, hcompl, hdimW,
    hdimU, hdimQW, hdimQU⟩

/-- q≠p Maschke complement extraction packaged in the theorem-facing data shape.

This strengthens `exists_rank_one_complement_subrepresentations_of_commutative_isPGroup_ne_char`
by also supplying the symmetric rank-one data for the complementary line and
the local `Free`/`Finite` evidence needed by the determinant-kernel uniqueness
bridges.  It is the exact input shape consumed by
`commutative_of_determinantKernel_opCore_ne_bot_of_rankOneKSubmodules`. -/
theorem exists_rank_one_KSubmodule_data_of_commutative_isPGroup_ne_char
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hdim : Module.finrank F V = 2)
    (K : Subgroup G) (hKq : IsPGroup q K) (hq_ne_p : q ≠ p)
    (hKcomm : Std.Commutative (· * · : K → K → K)) :
    ∃ W : Subrepresentation (ρ.comp K.subtype),
    ∃ U : Subrepresentation (ρ.comp K.subtype),
      Nonempty (Module.Free F W.toSubmodule) ∧
      Nonempty (Module.Free F U.toSubmodule) ∧
      Nonempty (Module.Finite F W.toSubmodule) ∧
      Nonempty (Module.Finite F U.toSubmodule) ∧
      Nonempty (Module.Free F (V ⧸ W.toSubmodule)) ∧
      Nonempty (Module.Free F (V ⧸ U.toSubmodule)) ∧
      IsCompl W.toSubmodule U.toSubmodule ∧
      Module.finrank F W.toSubmodule = 1 ∧
      Module.finrank F U.toSubmodule = 1 ∧
      Module.finrank F (V ⧸ W.toSubmodule) = 1 ∧
      Module.finrank F (V ⧸ U.toSubmodule) = 1 := by
  have : NeZero (Nat.card K : F) :=
    neZero_nat_card_cast_of_isPGroup_ne_char (F := F) (K := K) hKq hq_ne_p
  exact exists_rank_one_KSubmodule_data_of_commutative_of_neZero_card
    ρ hdim K hKcomm

/-- Conjugating a `K`-subrepresentation by an ambient element of `G`.

This is the normality bridge in the q≠p branch of BG Thm 2.6: if `K ⊴ G`,
then the image of a `K`-stable line under any `g : G` is again `K`-stable.
The next step is to combine this with uniqueness of the two rank-one
`K`-submodules. -/
def conjugateSubrepresentationOfNormal
    {F : Type*} [Field F] {G : Type*} [Group G]
    (K : Subgroup G) (hKnormal : K.Normal)
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (W : Subrepresentation (ρ.comp K.subtype)) (g : G) :
    Subrepresentation (ρ.comp K.subtype) where
  toSubmodule := W.toSubmodule.map (ρ g)
  apply_mem_toSubmodule k {v} hv := by
    rcases Submodule.mem_map.mp hv with ⟨w, hw, rfl⟩
    let kg : K := ⟨g⁻¹ * (k : G) * g, hKnormal.conj_mem' (k : G) k.2 g⟩
    refine Submodule.mem_map.mpr ⟨ρ (kg : G) w, W.apply_mem_toSubmodule kg hw, ?_⟩
    have hmul : g * (kg : G) = (k : G) * g := by
      dsimp [kg]
      group
    calc
      ρ g (ρ (kg : G) w) = ρ (g * (kg : G)) w := by
        simp [← Module.End.mul_apply, ← map_mul]
      _ = ρ ((k : G) * g) w := by rw [hmul]
      _ = ρ (k : G) (ρ g w) := by
        simp [← Module.End.mul_apply, ← map_mul]

/-- Conjugating a subrepresentation by a group element preserves finrank. -/
private theorem finrank_conjugateSubrepresentationOfNormal
    {F : Type*} [Field F] {G : Type*} [Group G]
    (K : Subgroup G) (hKnormal : K.Normal)
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (W : Subrepresentation (ρ.comp K.subtype)) (g : G) :
    Module.finrank F (conjugateSubrepresentationOfNormal K hKnormal ρ W g).toSubmodule =
      Module.finrank F W.toSubmodule := by
  let e : V ≃ₗ[F] V := LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)
  have hcoe : (e : V →ₗ[F] V) = ρ g := LinearMap.ext fun x => by simp [e]
  have h := LinearEquiv.finrank_map_eq e W.toSubmodule
  rw [hcoe] at h
  exact h

/-- Conjugating complementary `K`-subrepresentations by an ambient element
preserves complementarity. -/
theorem isCompl_conjugateSubrepresentationOfNormal
    {F : Type*} [Field F] {G : Type*} [Group G]
    (K : Subgroup G) (hKnormal : K.Normal)
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (W U : Subrepresentation (ρ.comp K.subtype)) (g : G)
    (hcompl : IsCompl W.toSubmodule U.toSubmodule) :
    IsCompl
      (conjugateSubrepresentationOfNormal K hKnormal ρ W g).toSubmodule
      (conjugateSubrepresentationOfNormal K hKnormal ρ U g).toSubmodule := by
  have hinj : Function.Injective (ρ g) := (ρ.apply_bijective g).1
  have hsurj : Function.Surjective (ρ g) := (ρ.apply_bijective g).2
  refine IsCompl.of_eq ?_ ?_
  · change W.toSubmodule.map (ρ g) ⊓ U.toSubmodule.map (ρ g) =
      (⊥ : Submodule F V)
    rw [← Submodule.map_inf (ρ g) hinj, hcompl.inf_eq_bot, Submodule.map_bot]
  · change W.toSubmodule.map (ρ g) ⊔ U.toSubmodule.map (ρ g) =
      (⊤ : Submodule F V)
    rw [← (Submodule.map_sup (p := W.toSubmodule) (p' := U.toSubmodule) (f := ρ g)),
      hcompl.sup_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr hsurj

/-- If the rank-one `K`-subrepresentations are exhausted by a pair `W, U`,
then every conjugate of `W` is one of that pair. -/
theorem conjugateSubrepresentation_eq_left_or_right_of_rank_one_unique
    {F : Type*} [Field F] {G : Type*} [Group G]
    (K : Subgroup G) (hKnormal : K.Normal)
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V)
    (W U : Subrepresentation (ρ.comp K.subtype))
    (hWdim : Module.finrank F W.toSubmodule = 1)
    (hunique : ∀ L : Subrepresentation (ρ.comp K.subtype),
      Module.finrank F L.toSubmodule = 1 → L = W ∨ L = U)
    (g : G) :
    conjugateSubrepresentationOfNormal K hKnormal ρ W g = W ∨
      conjugateSubrepresentationOfNormal K hKnormal ρ W g = U := by
  apply hunique
  exact (finrank_conjugateSubrepresentationOfNormal K hKnormal ρ W g).trans hWdim

/-- Equality of a conjugate line with a target line gives the `comap` form used
by `RankOneLinePairData.permutes`. -/
theorem le_comap_of_conjugateSubrepresentation_eq
    {F : Type*} [Field F] {G : Type*} [Group G]
    (K : Subgroup G) (hKnormal : K.Normal)
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (W T : Subrepresentation (ρ.comp K.subtype)) {g : G}
    (hconj : conjugateSubrepresentationOfNormal K hKnormal ρ W g = T) :
    W.toSubmodule ≤ T.toSubmodule.comap (ρ g) := by
  intro w hw
  have hmem :
      ρ g w ∈ (conjugateSubrepresentationOfNormal K hKnormal ρ W g).toSubmodule :=
    Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  have hsub :=
    congrArg Subrepresentation.toSubmodule hconj
  simpa [hsub] using hmem

/-- In characteristic `p`, a p-group acts trivially on every one-dimensional representation. -/
private theorem isPGroup_rank_one_representation_trivial_of_charP
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] (hG : IsPGroup p G)
    {M : Type*} [AddCommGroup M] [Module F M] [Module.Free F M]
    (hdim : Module.finrank F M = 1) (ρ : Representation F G M) :
    ∀ g : G, ∀ m : M, ρ g m = m := by
  let φ := scalarCharacterOfFinrankEqOne hdim ρ
  have hφ : φ = 1 := monoidHom_units_eq_one_of_isPGroup_charP hG φ
  intro g m
  calc
    ρ g m = (φ g : F) • m := scalarCharacterOfFinrankEqOne_apply_smul hdim ρ g m
    _ = m := by simp [hφ]

/-- Submodule form of `isPGroup_rank_one_representation_trivial_of_charP`. -/
theorem isPGroup_rank_one_submodule_action_trivial_of_charP
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] (hG : IsPGroup p G)
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) [Module.Free F W] (hdimW : Module.finrank F W = 1)
    (ρ : Representation F G V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ∀ g : G, ∀ w ∈ W, ρ g w = w := by
  have htriv := isPGroup_rank_one_representation_trivial_of_charP hG hdimW
    (ρ.subrepresentation W hW)
  intro g w hw
  have hsub := htriv g ⟨w, hw⟩
  exact congrArg Subtype.val hsub

/-- Quotient form of `isPGroup_rank_one_representation_trivial_of_charP`. -/
theorem isPGroup_rank_one_quotient_action_trivial_of_charP
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] (hG : IsPGroup p G)
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) [Module.Free F (V ⧸ W)]
    (hdimQ : Module.finrank F (V ⧸ W) = 1)
    (ρ : Representation F G V) (hW : ∀ g, W ≤ W.comap (ρ g)) :
    ∀ g : G, ∀ v : V, ρ g v - v ∈ W := by
  have htriv := isPGroup_rank_one_representation_trivial_of_charP hG hdimQ
    (ρ.quotient W hW)
  intro g v
  have hq := htriv g (Submodule.Quotient.mk v : V ⧸ W)
  change Submodule.Quotient.mk (ρ g v) = Submodule.Quotient.mk v at hq
  simpa [Submodule.Quotient.eq] using hq

/-- If two endomorphisms are trivial on a submodule and on the quotient by it,
then they commute.

This is the linear-algebra core of BG Thm 2.6, q = p: the subgroup
`C_G(W) ∩ C_G(V/W)` acts by maps `1 + n` where `n` kills `W` and has image in
`W`; products of two such nilpotent parts vanish. -/
private theorem end_commute_of_fixed_on_submodule_and_quotient
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (f g : Module.End F V)
    (hfW : ∀ w ∈ W, f w = w) (hfQ : ∀ v, f v - v ∈ W)
    (hgW : ∀ w ∈ W, g w = w) (hgQ : ∀ v, g v - v ∈ W) :
    f * g = g * f := by
  ext v
  calc
    (f * g) v = f (g v) := rfl
    _ = f (v + (g v - v)) := by congr 1; abel
    _ = f v + (g v - v) := by rw [map_add, hfW (g v - v) (hgQ v)]
    _ = g v + (f v - v) := by abel
    _ = g (v + (f v - v)) := by rw [map_add, hgW (f v - v) (hfQ v)]
    _ = g (f v) := by congr 1; abel
    _ = (g * f) v := rfl

/-- Submonoid-level wrapper for
`end_commute_of_fixed_on_submodule_and_quotient`. -/
private theorem submonoid_commutative_of_fixed_on_submodule_and_quotient
    {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (S : Submonoid (Module.End F V))
    (hS : ∀ f ∈ S, (∀ w ∈ W, f w = w) ∧ (∀ v, f v - v ∈ W)) :
    Std.Commutative (· * · : S → S → S) := by
  constructor
  intro f g
  apply Subtype.ext
  exact end_commute_of_fixed_on_submodule_and_quotient W (f : Module.End F V)
    (g : Module.End F V) (hS f f.2).1 (hS f f.2).2 (hS g g.2).1 (hS g g.2).2

/-- Representation-range wrapper for
`submonoid_commutative_of_fixed_on_submodule_and_quotient`.

For monoid homs into `Module.End`, mathlib's range object is
`MonoidHom.mrange` (a `Submonoid`). -/
private theorem representation_mrange_commutative_of_fixed_on_submodule_and_quotient
    {F : Type*} [Field F] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (ρ : Representation F G V)
    (hρ : ∀ g : G, (∀ w ∈ W, ρ g w = w) ∧ (∀ v, ρ g v - v ∈ W)) :
    Std.Commutative
      (· * · : MonoidHom.mrange ρ → MonoidHom.mrange ρ → MonoidHom.mrange ρ) := by
  apply submonoid_commutative_of_fixed_on_submodule_and_quotient W (MonoidHom.mrange ρ)
  intro f hf
  obtain ⟨g, rfl⟩ := MonoidHom.mem_mrange.mp hf
  exact hρ g

/-- A faithful representation reflects commutativity from its endomorphism image. -/
private theorem commutative_of_injective_representation_mrange_commutative
    {F : Type*} [Field F] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hrange : Std.Commutative
      (· * · : MonoidHom.mrange ρ → MonoidHom.mrange ρ → MonoidHom.mrange ρ)) :
    Std.Commutative (· * · : G → G → G) := by
  constructor
  intro x y
  apply hfaithful
  have hcomm := hrange.comm
    (⟨ρ x, MonoidHom.mem_mrange.mpr ⟨x, rfl⟩⟩ : MonoidHom.mrange ρ)
    (⟨ρ y, MonoidHom.mem_mrange.mpr ⟨y, rfl⟩⟩ : MonoidHom.mrange ρ)
  calc
    ρ (x * y) = ρ x * ρ y := map_mul ρ x y
    _ = ρ y * ρ x := congrArg Subtype.val hcomm
    _ = ρ (y * x) := (map_mul ρ y x).symm

/-- Faithful-representation form of the `C_G(W) ∩ C_G(V/W)` commutativity
calculation used in BG Thm 2.6, q = p. -/
private theorem commutative_of_faithful_representation_fixed_on_submodule_and_quotient
    {F : Type*} [Field F] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hρ : ∀ g : G, (∀ w ∈ W, ρ g w = w) ∧ (∀ v, ρ g v - v ∈ W)) :
    Std.Commutative (· * · : G → G → G) :=
  commutative_of_injective_representation_mrange_commutative ρ hfaithful
    (representation_mrange_commutative_of_fixed_on_submodule_and_quotient W ρ hρ)

/-- Subgroup-restriction form of
`commutative_of_faithful_representation_fixed_on_submodule_and_quotient`.

This is the shape needed for BG Thm 2.6, q = p, where
`H = C_G(W) ∩ C_G(V/W)`. -/
theorem subgroup_commutative_of_faithful_representation_fixed_on_submodule_and_quotient
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (H : Subgroup G) (W : Submodule F V) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hH : ∀ h : H, (∀ w ∈ W, ρ h w = w) ∧ (∀ v, ρ h v - v ∈ W)) :
    Std.Commutative (· * · : H → H → H) := by
  apply commutative_of_faithful_representation_fixed_on_submodule_and_quotient W
    (ρ.comp H.subtype)
  · intro x y hxy
    apply Subtype.ext
    exact hfaithful hxy
  · exact hH

/-- The subgroup acting trivially on `W` and on `V/W`.

This is the Lean version of the `C_G(W) ∩ C_G(V/W)` subgroup appearing in
BG Thm 2.6, q = p.  The quotient condition is written without choosing a
quotient representation: `ρ g v - v ∈ W` for every `v`. -/
def fixedOnSubmoduleAndQuotientSubgroup
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (ρ : Representation F G V) : Subgroup G where
  carrier := {g | (∀ w ∈ W, ρ g w = w) ∧ (∀ v, ρ g v - v ∈ W)}
  one_mem' := by
    constructor
    · intro w _hw
      simp
    · intro v
      simp
  mul_mem' := by
    intro a b ha hb
    constructor
    · intro w hw
      simpa [map_mul, hb.1 w hw] using ha.1 w hw
    · intro v
      have haW : ρ a (ρ b v) - ρ b v ∈ W := ha.2 (ρ b v)
      have hbW : ρ b v - v ∈ W := hb.2 v
      have hsum : (ρ a (ρ b v) - ρ b v) + (ρ b v - v) ∈ W := W.add_mem haW hbW
      have htarget :
          ρ (a * b) v - v = (ρ a (ρ b v) - ρ b v) + (ρ b v - v) := by
        rw [map_mul]
        change ρ a (ρ b v) - v = (ρ a (ρ b v) - ρ b v) + (ρ b v - v)
        abel
      rwa [htarget]
  inv_mem' := by
    intro a ha
    constructor
    · intro w hw
      have hdiff : w - ρ a⁻¹ w ∈ W := by
        simpa [map_mul] using ha.2 (ρ a⁻¹ w)
      have hinvW : ρ a⁻¹ w ∈ W := by
        have htmp : w - (w - ρ a⁻¹ w) ∈ W := W.sub_mem hw hdiff
        convert htmp using 1
        abel
      have hleft : ρ a (ρ a⁻¹ w) = w := by
        calc
          ρ a (ρ a⁻¹ w) = ((ρ a) * (ρ a⁻¹)) w := rfl
          _ = ρ (a * a⁻¹) w := by rw [map_mul]
          _ = w := by simp
      have hfix := ha.1 (ρ a⁻¹ w) hinvW
      rw [hleft] at hfix
      exact hfix.symm
    · intro v
      have hdiff : v - ρ a⁻¹ v ∈ W := by
        simpa [map_mul] using ha.2 (ρ a⁻¹ v)
      simpa [sub_eq_add_neg, add_comm] using W.neg_mem hdiff

end OddOrder.BG.Ch1.S02


