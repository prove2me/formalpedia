-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtraspecialSinger
-- name    : OddOrder_GroupTheory_RepresentationTheory_ExtraspecialSinger
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:30:42.070035+00:00
-- url     : https://prove2.me/theorems/c049a107-3545-4da0-a5a3-b061e7bc770c
-- title:
--   Singer / symplectic divisibility for extraspecial actions (BG §15.7(e), route B)
-- statement:
--   Provides the route-B divisibility $|K|\mid p+1$ for a cyclic $p'$-group $K$ acting on an extraspecial group $P$ of order $p^3$, used by Theorem 15.7(e) disjunct 3 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem* (the type-V Singer / $SL_2(p)$ case). It builds the alternating form from the commutator bihomomorphism and shows that a map preserving a nonzero top-degree alternating form has determinant $1$.
--
--   Main declarations: `bilinToAlt`; `commMulEquiv` (The multiplicative identification `Z(P) ≅ (𝔽_p, +)` (both have prime order `p`)); `commBihomP`; `commBihom1` (The commutator bihom with the second argument descended: `P →* (P/Z) →* Multiplicative 𝔽_p`); and 12 more.
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ExtraspecialSinger.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ExtraspecialSinger.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_IsExtraspecial
import Definitions.Def_OddOrder_GroupTheory_PRank
import Definitions.Def_OddOrder_GroupTheory_FrattiniPGroup
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LineScalarCharacter
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.RepresentationTheory.Irreducible

namespace OddOrder.GroupTheory

open Module

open scoped commutatorElement

section PureLinearAlgebra

variable {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- **A map preserving a nonzero top-degree alternating form has determinant `1`.**

If `ω : M [⋀^ι]→ₗ[R] R` is a nonzero alternating form indexed by a basis `e : Basis ι R M`, and
`f : M →ₗ[R] M` preserves it (`ω ∘ fⁱ = ω`), then `det f = 1`.  This is the abstract content of
"`K` preserves the symplectic commutator form ⟹ `K ⊆ Sp = SL₂` ⟹ `det = 1`": any alternating
top-form is `ω(e) • e.det`, and `e.det (f ∘ e) = det f · e.det e = det f`. -/
theorem det_eq_one_of_compLinearMap_alternating [Finite ι]
    (e : Basis ι R M) (ω : M [⋀^ι]→ₗ[R] R)
    (hω : ω ≠ 0) {f : M →ₗ[R] M} (hf : ω.compLinearMap f = ω) :
    LinearMap.det f = 1 := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hbasis : ω e ≠ 0 := (ω.map_basis_ne_zero_iff e).mpr hω
  -- `ω (f ∘ e) = ω e` (preservation) and `= ω e * det f` (top-form scaling).
  have h2 : ω (⇑f ∘ ⇑e) = ω ⇑e := by
    have hfe := DFunLike.congr_fun hf ⇑e
    rwa [AlternatingMap.compLinearMap_apply] at hfe
  have h3 : ω (⇑f ∘ ⇑e) = ω ⇑e * LinearMap.det f := by
    nth_rewrite 1 [ω.eq_smul_basis_det e]
    rw [AlternatingMap.smul_apply, e.det_comp, e.det_self, mul_one, smul_eq_mul]
  rw [h2] at h3
  have h4 : ω ⇑e * 1 = ω ⇑e * LinearMap.det f := by rw [mul_one]; exact h3
  exact (mul_left_cancel₀ hbasis h4).symm

/-- A bilinear form `β` that is **alternating** (`β x x = 0`) packaged as a degree-`2`
alternating map `V [⋀^Fin 2]→ₗ[R] R`, `v ↦ β (v 0) (v 1)`. -/
def bilinToAlt {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (β : M →ₗ[R] M →ₗ[R] R) (halt : ∀ x : M, β x x = 0) : M [⋀^Fin 2]→ₗ[R] R where
  toFun v := β (v 0) (v 1)
  map_update_add' m i x y := by
    fin_cases i <;>
      simp only [Function.update, Fin.isValue, dite_eq_ite] <;>
      norm_num
  map_update_smul' m i c x := by
    fin_cases i <;>
      simp only [Function.update, Fin.isValue, dite_eq_ite,
        smul_eq_mul] <;>
      norm_num
  map_eq_zero_of_eq' v i j hvij hij := by
    have h01 : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | simp_all
    simp only [h01, halt]

@[simp] theorem bilinToAlt_apply {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (β : M →ₗ[R] M →ₗ[R] R) (halt : ∀ x : M, β x x = 0) (v : Fin 2 → M) :
    bilinToAlt β halt v = β (v 0) (v 1) := rfl

end PureLinearAlgebra

section ClassTwoCommutator

variable {G : Type*} [Group G]

/-- `⁅x, y⁆ ∈ commutator G` for all `x y`. -/
theorem commutatorElement_mem_commutator_top (x y : G) : ⁅x, y⁆ ∈ commutator G := by
  rw [commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)

/-- In class `≤ 2` (`commutator G ≤ Z(G)`), `⁅·, z⁆` is multiplicative on the left:
`⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆`. -/
theorem commutatorElement_mul_left_of_le_center
    (hC : commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have h_yz : ⁅y, z⁆ ∈ Subgroup.center G := hC (commutatorElement_mem_commutator_top y z)
  have h_xz : ⁅x, z⁆ ∈ Subgroup.center G := hC (commutatorElement_mem_commutator_top x z)
  have hgen : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
    simp only [commutatorElement_def]; group
  rw [hgen, show x * ⁅y, z⁆ = ⁅y, z⁆ * x from Subgroup.mem_center_iff.mp h_yz x,
    mul_inv_cancel_right]
  exact Subgroup.mem_center_iff.mp h_xz ⁅y, z⁆

/-- In class `≤ 2`, `⁅x, ·⁆` is multiplicative on the right: `⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆`. -/
theorem commutatorElement_mul_right_of_le_center
    (hC : commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have h_xy : ⁅x, y⁆ ∈ Subgroup.center G := hC (commutatorElement_mem_commutator_top x y)
  have h_xz : ⁅x, z⁆ ∈ Subgroup.center G := hC (commutatorElement_mem_commutator_top x z)
  have hgen : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [hgen, show y * ⁅x, z⁆ = ⁅x, z⁆ * y from Subgroup.mem_center_iff.mp h_xz y,
    mul_inv_cancel_right]

end ClassTwoCommutator

section CommutatorForm

variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]

/-- Abbreviation for the symplectic space `V = P / Z(P)` of an extraspecial `p`-group. -/
local notation3 "V[" P "]" => Additive (P ⧸ commutator P)

variable (hP : IsExtraspecial p P)

/-- The multiplicative identification `Z(P) ≅ (𝔽_p, +)` (both have prime order `p`). -/
noncomputable def commMulEquiv : ↥(commutator P) ≃* Multiplicative (ZMod p) :=
  haveI : NeZero p := ⟨Fact.out (p := p.Prime).ne_zero⟩
  mulEquivOfPrimeCardEq hP.commutator_card
    (show Nat.card (Multiplicative (ZMod p)) = p by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])

/-- The commutator bihomomorphism `P →* P →* Multiplicative 𝔽_p`, `(x, y) ↦ ζ ⁅x, y⁆`
(class `≤ 2`, so multiplicative in each slot). -/
private noncomputable def commBihomP : P →* P →* Multiplicative (ZMod p) where
  toFun x :=
    { toFun := fun y => commMulEquiv hP ⟨⁅x, y⁆, commutatorElement_mem_commutator_top x y⟩
      map_one' := by simp [commutatorElement_one_right]
      map_mul' := fun y y' => by
        rw [← map_mul]
        exact congrArg (commMulEquiv hP)
          (Subtype.ext (commutatorElement_mul_right_of_le_center hP.commutator_eq_center.le x y y'))
              }
  map_one' := by
    ext y
    simp [commutatorElement_one_left]
  map_mul' x x' := by
    ext y
    simp only [MonoidHom.mul_apply, MonoidHom.coe_mk, OneHom.coe_mk, ← map_mul]
    exact congrArg (commMulEquiv hP)
      (Subtype.ext (commutatorElement_mul_left_of_le_center hP.commutator_eq_center.le x x' y))

omit [Finite P] in
/-- `ζ ⁅x, z⁆ = 1` when `z ∈ commutator P` (central, right slot). -/
private theorem commBihomP_central_right (x : P) {z : P} (hz : z ∈ commutator P) :
    commBihomP hP x z = 1 := by
  have hz1 : (⟨⁅x, z⁆, commutatorElement_mem_commutator_top x z⟩ : ↥(commutator P)) = 1 :=
    Subtype.ext (commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp (hP.commutator_eq_center.le hz) x))
  simp only [commBihomP, MonoidHom.coe_mk, OneHom.coe_mk, hz1, map_one]

omit [Finite P] in
/-- `ζ ⁅z, y⁆ = 1` when `z ∈ commutator P` (central, left slot). -/
private theorem commBihomP_central_left {z : P} (hz : z ∈ commutator P) (y : P) :
    commBihomP hP z y = 1 := by
  have hz1 : (⟨⁅z, y⁆, commutatorElement_mem_commutator_top z y⟩ : ↥(commutator P)) = 1 :=
    Subtype.ext (commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_center_iff.mp (hP.commutator_eq_center.le hz) y).symm)
  simp only [commBihomP, MonoidHom.coe_mk, OneHom.coe_mk, hz1, map_one]

/-- The commutator bihom with the **second** argument descended: `P →* (P/Z) →* Multiplicative 𝔽_p`.
-/
private noncomputable def commBihom1 : P →* (P ⧸ commutator P) →* Multiplicative (ZMod p) where
  toFun x := QuotientGroup.lift (commutator P) (commBihomP hP x)
    (fun y hy => MonoidHom.mem_ker.mpr (commBihomP_central_right hP x hy))
  map_one' := by
    ext q
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.lift_mk',
      MonoidHom.one_apply, map_one]
  map_mul' x x' := by
    ext q
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, QuotientGroup.mk'_apply,
      QuotientGroup.lift_mk', map_mul]

/-- The fully descended commutator pairing `(P/Z) →* (P/Z) →* Multiplicative 𝔽_p`. -/
private noncomputable def commBihom2 :
    (P ⧸ commutator P) →* (P ⧸ commutator P) →* Multiplicative (ZMod p) :=
  QuotientGroup.lift (commutator P) (commBihom1 hP)
    (fun x hx => MonoidHom.mem_ker.mpr (by
      ext q
      simp only [commBihom1, MonoidHom.coe_mk, OneHom.coe_mk]
      exact commBihomP_central_left hP hx q))

/-- The **symplectic commutator form** on `V = P / Z(P)`, valued in `𝔽_p`: the bi-additive
pairing `(v, w) ↦ toAdd (ζ ⁅x, y⁆)` for representatives `x, y`.  Alternating and (for non-abelian
`P`) non-degenerate; preserved by every automorphism centralizing `Z(P)`. -/
noncomputable def commPairing : V[P] →+ V[P] →+ ZMod p :=
  AddMonoidHom.mk'
    (fun v => AddMonoidHom.mk'
      (fun w => Multiplicative.toAdd (commBihom2 hP (Additive.toMul v) (Additive.toMul w)))
      (fun w w' => by
        rw [show Additive.toMul (w + w') = Additive.toMul w * Additive.toMul w' from rfl,
          map_mul, toAdd_mul]))
    (fun v v' => by
      refine AddMonoidHom.ext fun w => ?_
      change Multiplicative.toAdd (commBihom2 hP (Additive.toMul (v + v')) (Additive.toMul w)) =
        Multiplicative.toAdd (commBihom2 hP (Additive.toMul v) (Additive.toMul w)) +
        Multiplicative.toAdd (commBihom2 hP (Additive.toMul v') (Additive.toMul w))
      rw [show Additive.toMul (v + v') = Additive.toMul v * Additive.toMul v' from rfl,
        map_mul, MonoidHom.mul_apply, toAdd_mul])

omit [Finite P] in
@[simp] theorem commPairing_mk (x y : P) :
    commPairing hP (Additive.ofMul (QuotientGroup.mk x)) (Additive.ofMul (QuotientGroup.mk y)) =
      Multiplicative.toAdd (commBihom2 hP (QuotientGroup.mk x) (QuotientGroup.mk y)) := rfl

omit [Finite P] in
private theorem commBihom2_mk (x y : P) :
    commBihom2 hP (QuotientGroup.mk x) (QuotientGroup.mk y) =
      commMulEquiv hP ⟨⁅x, y⁆, commutatorElement_mem_commutator_top x y⟩ := by
  simp only [commBihom2, commBihom1, QuotientGroup.lift_mk', MonoidHom.coe_mk, OneHom.coe_mk]
  rfl

omit [Finite P] in
/-- Value of the commutator form on representatives: `b(x̄, ȳ) = toAdd (ζ ⁅x, y⁆)`. -/
theorem commPairing_ofMul (x y : P) :
    commPairing hP (Additive.ofMul (QuotientGroup.mk x)) (Additive.ofMul (QuotientGroup.mk y)) =
      Multiplicative.toAdd (commMulEquiv hP ⟨⁅x, y⁆, commutatorElement_mem_commutator_top x y⟩) :=
          by
  rw [commPairing_mk, commBihom2_mk]

omit [Finite P] in
/-- The commutator form is **alternating**: `b(v, v) = 0`. -/
theorem commPairing_self (v : Additive (P ⧸ commutator P)) : commPairing hP v v = 0 := by
  obtain ⟨q, rfl⟩ := Additive.ofMul.surjective v
  refine QuotientGroup.induction_on q fun x => ?_
  rw [commPairing_ofMul,
    show (⟨⁅x, x⁆, commutatorElement_mem_commutator_top x x⟩ : ↥(commutator P)) = 1 from
      Subtype.ext (commutatorElement_self x), map_one, toAdd_one]

omit [Finite P] in
/-- The commutator form is **non-degenerate** when `P` is non-abelian: some value is nonzero. -/
theorem commPairing_ne (hnonab : ¬ ∀ a b : P, a * b = b * a) :
    ∃ v w, commPairing hP v w ≠ 0 := by
  obtain ⟨x, y, hxy⟩ : ∃ x y : P, ⁅x, y⁆ ≠ 1 := by
    by_contra h
    push Not at h
    exact hnonab fun a b => commutatorElement_eq_one_iff_mul_comm.mp (h a b)
  refine ⟨Additive.ofMul (QuotientGroup.mk x), Additive.ofMul (QuotientGroup.mk y), ?_⟩
  rw [commPairing_ofMul]
  intro hzero
  apply hxy
  have h1 : commMulEquiv hP ⟨⁅x, y⁆, commutatorElement_mem_commutator_top x y⟩ = 1 :=
    Multiplicative.toAdd.injective (by rw [hzero, toAdd_one])
  have h2 : (⟨⁅x, y⁆, commutatorElement_mem_commutator_top x y⟩ : ↥(commutator P)) = 1 :=
    (commMulEquiv hP).injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

end CommutatorForm

section RouteB

universe u

variable {p : ℕ} [Fact p.Prime] {K P : Type u} [Group K] [Finite K] [Group P] [Finite P]

omit [Finite K] in
/-- **`|K| ∣ n` from a Singer embedding `μ : K ↪ C` into a finite cyclic group whose images are
`n`-th roots of unity.**  The final arithmetic step of route B (here `C = 𝔽_{p²}ˣ`, `n = p+1`). -/
private theorem card_dvd_of_injective_to_cyclic_forall_pow {C : Type*}
    [Group C] [Finite C] [IsCyclic C] (μ : K →* C) (hμ : Function.Injective μ)
    {n : ℕ} (h : ∀ k : K, μ k ^ n = 1) : Nat.card K ∣ n := by
  have hKn : ∀ k : K, k ^ n = 1 := fun k => hμ (by rw [map_pow, h k, map_one])
  have : IsCyclic K := isCyclic_of_surjective (MonoidHom.ofInjective hμ).symm.toMonoidHom
    (MonoidHom.ofInjective hμ).symm.surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  rw [(orderOf_eq_card_of_forall_mem_zpowers hg).symm]
  exact orderOf_dvd_of_pow_eq_one (hKn g)

open OddOrder.BG.Ch1_Preliminary

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom quotientMulAutHom_apply)

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped IsMulCommutative in
/-- **Route B (BG Theorem 15.7(e), disjunct 3): `|K| ∣ p + 1`.**

A cyclic `p'`-group `K` (`p` odd) acting on an extraspecial group `P` of order `p³` with the
prime action `C_P(k) ⊆ Z(P)` for `k ≠ 1` (`hfpf`), `K` centralizing `Z(P)` (`hcentZ`), and
`¬ |K| ∣ p - 1`, has `|K| ∣ p + 1`.  (`hfpf` is `C_P(k) ⊆ Z(P)` at the `P`-level; coprimality
lifts it to fixed-point-freeness on `V = P/Z(P)` internally.)

`V` is a `2`-dimensional `𝔽_p`-space, the action is fixed-point-free hence faithful, and
irreducible (else the split-torus / line case gives `|K| ∣ p - 1`).  Singer realizes
`V ≅ 𝔽_{p²}` with `μ : K ↪ 𝔽_{p²}ˣ`.  `K` preserves the commutator symplectic form, so
`det ρ(k) = 1`; but `det ρ(k) = N(μ k) = μ(k)^{p+1}`, whence `|K| ∣ p + 1`. -/
theorem card_dvd_succ_of_primeAction_extraspecial (_hodd : Odd p)
    (hP : IsExtraspecial p P) (hPcard : Nat.card P = p ^ 3) (φ : K →* MulAut P)
    (hfpf : ∀ k : K, k ≠ 1 → ∀ x : P, (φ k) x = x → x ∈ commutator P)
    (hcentZ : ∀ k : K, ∀ z : P, z ∈ commutator P → (φ k) z = z)
    (hKcyc : IsCyclic K) (hKp' : ¬ p ∣ Nat.card K) (hndvd : ¬ Nat.card K ∣ p - 1) :
    Nat.card K ∣ p + 1 := by
  classical
  have : NeZero p := ⟨Fact.out (p := p.Prime).ne_zero⟩
  -- `V = P / Z(P)` is an elementary abelian `𝔽_p`-space.
  have hEA : IsElementaryAbelian p (P ⧸ commutator P) :=
    IsElementaryAbelian.of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hP.commutator_eq_frattini).symm
      (IsPGroup.quotient_frattini_isElementaryAbelian hP.isPGroup)
  have hVcomm : IsMulCommutative (P ⧸ commutator P) := ⟨⟨hEA.comm⟩⟩
  have hVmod : Module (ZMod p) (Additive (P ⧸ commutator P)) :=
    AddCommGroup.zmodModule (n := p) (fun x => by
      apply Additive.toMul.injective
      rw [toMul_nsmul, toMul_zero]
      exact hEA.pow_eq_one (Additive.toMul x))
  -- The descended conjugation representation `ρ : K → GL(V)`.
  have hinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (commutator P) :=
    OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic _
  let qhom : K →* MulAut (P ⧸ commutator P) := quotientMulAutHom hinv
  let ρ : Representation (ZMod p) K (Additive (P ⧸ commutator P)) :=
    (mulAutToEnd (P ⧸ commutator P) p).comp qhom
  have hρmk : ∀ (k : K) (x : P),
      ρ k (Additive.ofMul (QuotientGroup.mk x)) = Additive.ofMul (QuotientGroup.mk ((φ k) x)) :=
    fun k x => rfl
  -- `|V| = p²`, so `dim V = 2`.
  have hVcard : Nat.card (Additive (P ⧸ commutator P)) = p ^ 2 := by
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator P)
    rw [hPcard, hP.commutator_card] at hq
    have : Nat.card (P ⧸ commutator P) = p ^ 2 := by
      have hp1 : 0 < p := Fact.out (p := p.Prime).pos
      have : Nat.card (P ⧸ commutator P) * p = p ^ 2 * p := by rw [← hq]; ring
      exact Nat.eq_of_mul_eq_mul_right hp1 this
    exact (Nat.card_congr Additive.toMul).trans this
  have hdim : Module.finrank (ZMod p) (Additive (P ⧸ commutator P)) = 2 := by
    have := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive (P ⧸ commutator P))
    rw [hVcard, Nat.card_eq_fintype_card (α := ZMod p), ZMod.card] at this
    exact (Nat.pow_right_injective (Fact.out (p := p.Prime)).two_le this.symm)
  -- Fixed-point-freeness of `ρ` on `V` (the prime action `hfpf` is `C_P(k) ⊆ Z(P)`; coprimality
  -- of `⟨k⟩` on the `p`-group `P` lifts it to `C_{P/Z}(k) = 0` via Isaacs Cor 3.28).
  have hfpfρ : ∀ k : K, k ≠ 1 → ∀ v : Additive (P ⧸ commutator P), ρ k v = v → v = 0 := by
    intro k hk v hv
    obtain ⟨q, rfl⟩ := Additive.ofMul.surjective v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hρmk] at hv
    have heqmk : (QuotientGroup.mk ((φ k) x) : P ⧸ commutator P) = QuotientGroup.mk x :=
      Additive.ofMul.injective hv
    have hxZ : x ∈ commutator P := by
      set A := Subgroup.zpowers k with hAdef
      let φ' : ↥A →* MulAut P := φ.comp A.subtype
      have hAinv : OddOrder.Isaacs.Ch03.IsAInvariant φ' (commutator P) :=
        OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic _
      have hKp : ¬ p ∣ orderOf k := fun h => hKp' (h.trans (orderOf_dvd_natCard k))
      have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card P) := by
        rw [hPcard, hAdef, Nat.card_zpowers]
        exact Nat.Coprime.pow_right 3
          ((Nat.coprime_comm.mp ((Fact.out (p := p.Prime)).coprime_iff_not_dvd.mpr hKp)))
      -- `mk x` is fixed by `qhom k`, hence by every `(qhom k)^j`.
      have hfixq : qhom k (QuotientGroup.mk x) = QuotientGroup.mk x := heqmk
      have hfixqinv : (qhom k)⁻¹ (QuotientGroup.mk x) = QuotientGroup.mk x := by
        conv_lhs => rw [← hfixq]
        simp
      have hfixj : ∀ j : ℤ, ((qhom k) ^ j) (QuotientGroup.mk x) = QuotientGroup.mk x := by
        intro j
        refine Int.induction_on j ?_ (fun n ih => ?_) (fun n ih => ?_)
        · simp
        · rw [zpow_add_one, MulAut.mul_apply, hfixq]; exact ih
        · rw [zpow_sub_one, MulAut.mul_apply, hfixqinv]; exact ih
      have hgfix : ∀ a : ↥A, ∃ n ∈ commutator P, φ' a x = x * n := by
        rintro ⟨a, ha⟩
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        have h2 : (QuotientGroup.mk ((φ (k ^ j)) x) : P ⧸ commutator P) = QuotientGroup.mk x := by
          have h3 : qhom (k ^ j) (QuotientGroup.mk x) = QuotientGroup.mk x := by
            rw [map_zpow]; exact hfixj j
          exact h3
        rw [QuotientGroup.eq] at h2
        refine ⟨x⁻¹ * (φ (k ^ j)) x, by simpa [mul_inv_rev] using (commutator P).inv_mem h2, ?_⟩
        change φ (k ^ j) x = x * (x⁻¹ * (φ (k ^ j)) x)
        group
      obtain ⟨c, hc, n, hn, hcn⟩ :=
        OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient hcop
          (Or.inr (haveI : Group.IsNilpotent P := hP.isPGroup.isNilpotent; inferInstance))
          hAinv hgfix
      have hck : (φ k) c = c := hc ⟨k, Subgroup.mem_zpowers k⟩
      have hcZ : c ∈ commutator P := hfpf k hk c hck
      have hxc : x = c * n⁻¹ := by rw [hcn]; group
      rw [hxc]
      exact (commutator P).mul_mem hcZ ((commutator P).inv_mem hn)
    change Additive.ofMul (QuotientGroup.mk x) = 0
    rw [show (QuotientGroup.mk x : P ⧸ commutator P) = 1 from
      (QuotientGroup.eq_one_iff x).mpr hxZ]
    rfl
  -- `ρ` is faithful.
  have hVnt : Nontrivial (Additive (P ⧸ commutator P)) :=
    Module.nontrivial_of_finrank_eq_succ (n := 1) (by rw [hdim])
  have hfaith : Function.Injective ρ := by
    intro a b hab
    by_contra hne
    have hba : b⁻¹ * a ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
    obtain ⟨v, hv⟩ := exists_ne (0 : Additive (P ⧸ commutator P))
    refine hv (hfpfρ (b⁻¹ * a) hba v ?_)
    rw [map_mul, Module.End.mul_apply, hab, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  -- `P` is non-abelian (`|Z(P)| = p < p³ = |P|`).
  have hnonab : ¬ ∀ a b : P, a * b = b * a := by
    intro hcomm
    have htop : Subgroup.center P = ⊤ := by
      rw [Subgroup.eq_top_iff']
      exact fun x => Subgroup.mem_center_iff.mpr fun y => hcomm y x
    have h1 : Nat.card (Subgroup.center P) = Nat.card P :=
      Nat.card_congr (htop ▸ (Subgroup.topEquiv (G := P)).toEquiv)
    rw [hP.center_card, hPcard] at h1
    have h2 := (Fact.out (p := p.Prime)).one_lt
    nlinarith [pow_lt_pow_right₀ h2 (by norm_num : 1 < 3), h1]
  -- The symplectic commutator form `β` and its alternating packaging `ω`.
  let β : Additive (P ⧸ commutator P) →ₗ[ZMod p] Additive (P ⧸ commutator P) →ₗ[ZMod p] ZMod p :=
    (AddMonoidHom.mk' (fun v => (commPairing hP v).toZModLinearMap p)
      (fun v v' => by ext w; simp [map_add])).toZModLinearMap p
  have hβ : ∀ a b, β a b = commPairing hP a b := fun a b => rfl
  let ω := bilinToAlt β (fun v => by rw [hβ]; exact commPairing_self hP v)
  have hωne : ω ≠ 0 := by
    obtain ⟨v, w, hvw⟩ := commPairing_ne hP hnonab
    intro h0
    exact hvw (by simpa [ω, bilinToAlt_apply, hβ] using DFunLike.congr_fun h0 ![v, w])
  -- `K` preserves `β` (it centralizes `Z(P)`, so `ζ ⁅k·x, k·y⁆ = ζ ⁅x, y⁆`).
  have hpres : ∀ (k : K) (a b : Additive (P ⧸ commutator P)),
      commPairing hP (ρ k a) (ρ k b) = commPairing hP a b := by
    intro k a b
    obtain ⟨qa, rfl⟩ := Additive.ofMul.surjective a
    obtain ⟨xa, rfl⟩ := QuotientGroup.mk_surjective qa
    obtain ⟨qb, rfl⟩ := Additive.ofMul.surjective b
    obtain ⟨xb, rfl⟩ := QuotientGroup.mk_surjective qb
    have hval : ⁅(φ k) xa, (φ k) xb⁆ = ⁅xa, xb⁆ := by
      rw [← map_commutatorElement (φ k) xa xb]
      exact hcentZ k ⁅xa, xb⁆ (commutatorElement_mem_commutator_top xa xb)
    have hcomm_eq : (⟨⁅(φ k) xa, (φ k) xb⁆, commutatorElement_mem_commutator_top _ _⟩ :
        ↥(commutator P)) = ⟨⁅xa, xb⁆, commutatorElement_mem_commutator_top xa xb⟩ :=
      Subtype.ext hval
    rw [hρmk, hρmk, commPairing_ofMul, commPairing_ofMul, hcomm_eq]
  have hdet1 : ∀ k : K, LinearMap.det (ρ k) = 1 := fun k =>
    det_eq_one_of_compLinearMap_alternating
      ((Module.finBasis (ZMod p) _).reindex (finCongr hdim)) ω hωne (by
        ext vv
        rw [AlternatingMap.compLinearMap_apply, bilinToAlt_apply, bilinToAlt_apply, hβ, hβ]
        exact hpres k (vv 0) (vv 1))
  -- `ρ` is irreducible: a proper invariant line would give `|K| ∣ p - 1`.
  have hirr : Representation.IsIrreducible ρ := by
    have hbnt : (⊥ : Subrepresentation ρ) ≠ ⊤ := fun h =>
      bot_ne_top (congrArg Subrepresentation.toSubmodule h)
    have : Nontrivial (Subrepresentation ρ) := ⟨⊥, ⊤, hbnt⟩
    refine ⟨fun W => ?_⟩
    by_contra hW
    push Not at hW
    obtain ⟨hWbot, hWtop⟩ := hW
    have hWsub_bot : W.toSubmodule ≠ ⊥ := fun h =>
      hWbot (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
    have hWsub_top : W.toSubmodule ≠ ⊤ := fun h =>
      hWtop (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
    have : Module.Finite (ZMod p) ↥W.toSubmodule := Module.Finite.of_finite
    have hpos : 0 < Module.finrank (ZMod p) ↥W.toSubmodule := by
      have := Submodule.finrank_lt_finrank_of_lt (s := (⊥ : Submodule (ZMod p) _))
        (t := W.toSubmodule) (lt_of_le_of_ne bot_le (Ne.symm hWsub_bot))
      simpa using this
    have hlt : Module.finrank (ZMod p) ↥W.toSubmodule <
        Module.finrank (ZMod p) (Additive (P ⧸ commutator P)) := Submodule.finrank_lt hWsub_top
    have hWdim : Module.finrank (ZMod p) ↥W.toSubmodule = 1 := by rw [hdim] at hlt; omega
    have hfaithW : Function.Injective W.toRepresentation := by
      intro a b hab
      by_contra hne
      have hba : b⁻¹ * a ≠ 1 := fun h => hne (inv_mul_eq_one.mp h).symm
      apply hWsub_bot
      rw [Submodule.eq_bot_iff]
      intro w hw
      have hfix : W.toRepresentation (b⁻¹ * a) ⟨w, hw⟩ = ⟨w, hw⟩ := by
        rw [map_mul, Module.End.mul_apply, hab, ← Module.End.mul_apply, ← map_mul,
          inv_mul_cancel, map_one, Module.End.one_apply]
      have hfixV : ρ (b⁻¹ * a) w = w := by
        have := congrArg Subtype.val hfix
        simpa [Subrepresentation.toRepresentation, LinearMap.coe_restrict_apply] using this
      exact hfpfρ (b⁻¹ * a) hba w hfixV
    exact hndvd (OddOrder.RepresentationTheory.card_dvd_sub_one_of_faithful_line
      W.toRepresentation hWdim hfaithW)
  -- Singer realization: `V ≅ 𝔽_{p²}` with `μ : K ↪ 𝔽_{p²}ˣ`.
  have hcommK : ∀ a b : K, a * b = b * a :=
    ((MonoidHom.id K).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [MonoidHom.ker_id]; exact bot_le)).is_comm.comm
  let : Module (MonoidAlgebra (ZMod p) K) (Additive (P ⧸ commutator P)) :=
    Module.compHom (Additive (P ⧸ commutator P)) (ρ.asAlgebraHom).toRingHom
  have hsmul : ∀ (k : K) (x : Additive (P ⧸ commutator P)),
      MonoidAlgebra.of (ZMod p) K k • x = ρ k x := fun k x => by
    change (ρ.asAlgebraHom (MonoidAlgebra.of (ZMod p) K k)) x = ρ k x
    rw [Representation.asAlgebraHom_of]
  have : IsSimpleModule (MonoidAlgebra (ZMod p) K) (Additive (P ⧸ commutator P)) :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hirr
  -- Realize the Singer field `Kf = 𝔽_p[K]/I ≅ 𝔽_{p²}` with `μ : K ↪ Kfˣ` (no `CommGroup K`
  -- instance: the commutative `𝔽_p[K]` is built from the commutativity *proof*).
  let : CommRing (MonoidAlgebra (ZMod p) K) :=
    { (inferInstance : Ring (MonoidAlgebra (ZMod p) K)) with
      mul_comm := OddOrder.RepresentationTheory.mul_comm_monoidAlgebra_of_comm hcommK }
  obtain ⟨I, hImax, ⟨lequiv⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := MonoidAlgebra (ZMod p) K)
      (M := Additive (P ⧸ commutator P))).mp ‹_›
  have : I.IsMaximal := hImax
  let : Field (MonoidAlgebra (ZMod p) K ⧸ I) := Ideal.Quotient.field I
  have : Finite (MonoidAlgebra (ZMod p) K ⧸ I) := Finite.of_equiv _ lequiv.toEquiv
  have : (I : Ideal (MonoidAlgebra (ZMod p) K)).IsTwoSided := inferInstance
  let Kf := MonoidAlgebra (ZMod p) K ⧸ I
  let μ : K →* Kfˣ :=
    (Units.map (Ideal.Quotient.mk I : MonoidAlgebra (ZMod p) K →+* Kf).toMonoidHom).comp
      (MonoidAlgebra.of (ZMod p) K).toHomUnits
  have hcompat : ∀ (k : K) (m : Additive (P ⧸ commutator P)),
      lequiv (MonoidAlgebra.of (ZMod p) K k • m) = (↑(μ k) : Kf) * lequiv m := fun k m => by
    rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]; rfl
  let eL : Additive (P ⧸ commutator P) ≃ₗ[ZMod p] Kf :=
    { lequiv.toAddEquiv with
      map_smul' := fun c x => ZMod.map_smul lequiv.toAddEquiv.toAddMonoidHom c x }
  have heL : ∀ x, eL x = lequiv x := fun _ => rfl
  have hKfcard : Nat.card Kf = p ^ 2 := by rw [← Nat.card_congr lequiv.toEquiv, hVcard]
  -- `det ρ(k) = N(μ k)` (the action is multiplication by `μ k` in the field).
  have hdetnorm : ∀ k : K, LinearMap.det (ρ k) = Algebra.norm (ZMod p) (↑(μ k) : Kf) := by
    intro k
    have hmaps : ((eL : Additive (P ⧸ commutator P) →ₗ[ZMod p] Kf) ∘ₗ ρ k ∘ₗ
        (eL.symm : Kf →ₗ[ZMod p] Additive (P ⧸ commutator P))) =
        Algebra.lmul (ZMod p) Kf ↑(μ k) := by
      ext y
      change eL (ρ k (eL.symm y)) = ↑(μ k) * y
      rw [heL, ← hsmul k (eL.symm y), hcompat]
      congr 1
      rw [← heL, eL.apply_symm_apply]
    rw [Algebra.norm_apply, ← LinearMap.det_conj (ρ k) eL, hmaps]
  -- `(p²-1)/(p-1) = p+1`.
  have hexp : (Nat.card Kf - 1) / (Nat.card (ZMod p) - 1) = p + 1 := by
    rw [hKfcard, Nat.card_eq_fintype_card (α := ZMod p), ZMod.card,
      ← Nat.geomSum_eq (Fact.out (p := p.Prime)).two_le 2, Finset.sum_range_succ,
      Finset.sum_range_one, pow_zero, pow_one, add_comm]
  -- `μ(k)^{p+1} = 1`.
  have hμpow : ∀ k : K, (↑(μ k) : Kf) ^ (p + 1) = 1 := by
    intro k
    have hN1 : Algebra.norm (ZMod p) (↑(μ k) : Kf) = 1 := by rw [← hdetnorm k, hdet1 k]
    have hpow := FiniteField.algebraMap_norm_eq_pow (K := ZMod p) (K' := Kf) (x := (↑(μ k) : Kf))
    rw [hN1, map_one, hexp] at hpow
    exact hpow.symm
  -- `μ` injective (faithfulness) ⟹ `|K| ∣ p + 1`.
  have hμinj : Function.Injective μ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    refine hfaith (DFunLike.ext _ _ fun m => ?_)
    rw [map_one, Module.End.one_apply, ← hsmul k m]
    exact lequiv.injective (by rw [hcompat, hk, Units.val_one, one_mul])
  refine card_dvd_of_injective_to_cyclic_forall_pow μ hμinj (fun k => Units.ext ?_)
  rw [Units.val_pow_eq_pow_val, hμpow k, Units.val_one]

end RouteB

end OddOrder.GroupTheory


