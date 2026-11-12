-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_FixedQuotientMachinery
-- name    : OddOrder_BG_Ch1_Preliminary_S02_FixedQuotientMachinery
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:34:13.021076+00:00
-- url     : https://prove2.me/theorems/767bc5fb-ecee-433e-b07f-c629abb8cd35
-- title:
--   Bender–Glauberman §2F: fixed submodules and quotients (main layer)
-- statement:
--   The main layer of the machinery behind the proof of Bender–Glauberman Theorem 2.6, built on `fixedOnSubmoduleAndQuotientSubgroup`: scalar characters, determinant-kernel line analysis, the stay-or-swap dichotomy, and the commutator bounds, up to but excluding the final assembly layer.
--
--   Main definitions: `representationToGeneralLinearGroup` (a representation as a homomorphism into $GL(V)$), `determinantCharacterOfRepresentation` (the determinant character) and `determinantKernelSubgroup` (the determinant-kernel subgroup $G^*$ of BG Thm 2.6).
--
--   The bundle also proves 40 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S02_FixedQuotientMachinery.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S02_FixedQuotientMachinery.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_RepresentationsBasic

namespace OddOrder.BG.Ch1.S02

open scoped Pointwise

open OddOrder.RepresentationTheory (baseChangeRepresentation baseChangeRepresentation_apply_tmul
  baseChangeRepresentation_faithful)

private theorem mem_fixedOnSubmoduleAndQuotientSubgroup
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    {W : Submodule F V} {ρ : Representation F G V} {g : G} :
    g ∈ fixedOnSubmoduleAndQuotientSubgroup W ρ ↔
      (∀ w ∈ W, ρ g w = w) ∧ (∀ v, ρ g v - v ∈ W) :=
  Iff.rfl

/-- If `g` acts trivially on `W` and on `V/W`, then `ρ g - 1` squares to zero.

This is the unipotent calculation behind BG Thm 2.6(b), q = p. -/
private theorem fixedOnSubmoduleAndQuotientSubgroup_sub_pow_two_eq_zero
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) (ρ : Representation F G V)
    {g : G} (hg : g ∈ fixedOnSubmoduleAndQuotientSubgroup W ρ) :
    (((ρ g : Module.End F V) - 1) ^ 2 : Module.End F V) = 0 := by
  rw [pow_two]
  ext v
  rw [Module.End.mul_apply]
  change ρ g (ρ g v - v) - (ρ g v - v) = 0
  have hmem := (mem_fixedOnSubmoduleAndQuotientSubgroup.mp hg).2 v
  have hfix := (mem_fixedOnSubmoduleAndQuotientSubgroup.mp hg).1 (ρ g v - v) hmem
  rw [hfix, sub_self]

/-- In characteristic `p`, every element of `C_G(W) ∩ C_G(V/W)` acts with
p-th power identity under the representation. -/
private theorem fixedOnSubmoduleAndQuotientSubgroup_rep_pow_prime_eq_one
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    [Nontrivial V]
    (W : Submodule F V) (ρ : Representation F G V)
    {g : G} (hg : g ∈ fixedOnSubmoduleAndQuotientSubgroup W ρ) :
    (ρ g : Module.End F V) ^ p = 1 := by
  have : CharP (Module.End F V) p := IsPGroup.charP_End_of_field
  have hsq :
      (((ρ g : Module.End F V) - 1) ^ 2 : Module.End F V) = 0 :=
    fixedOnSubmoduleAndQuotientSubgroup_sub_pow_two_eq_zero W ρ hg
  have hpow_zero :
      (((ρ g : Module.End F V) - 1) ^ p : Module.End F V) = 0 :=
    pow_eq_zero_of_le (Nat.Prime.two_le (Fact.out : p.Prime)) hsq
  have hsub :
      (((ρ g : Module.End F V) - 1) ^ p : Module.End F V) =
        (ρ g : Module.End F V) ^ p - 1 := by
    rw [sub_pow_char_of_commute p (Commute.one_right (ρ g : Module.End F V)), one_pow]
  exact sub_eq_zero.mp (hsub ▸ hpow_zero)

/-- Faithfulness turns the previous representation-level p-torsion into
group-level p-torsion. -/
private theorem fixedOnSubmoduleAndQuotientSubgroup_pow_prime_eq_one
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    [Nontrivial V]
    (W : Submodule F V) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    {g : G} (hg : g ∈ fixedOnSubmoduleAndQuotientSubgroup W ρ) :
    g ^ p = 1 := by
  apply hfaithful
  simpa [map_pow] using
    (fixedOnSubmoduleAndQuotientSubgroup_rep_pow_prime_eq_one
      (p := p) W ρ hg)

/-- In a faithful representation over characteristic `p`, the subgroup acting
trivially on a submodule and on the quotient is a p-subgroup. -/
private theorem fixedOnSubmoduleAndQuotientSubgroup_isPGroup_of_faithful
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    [Nontrivial V]
    (W : Submodule F V) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) :
    IsPGroup p (fixedOnSubmoduleAndQuotientSubgroup W ρ) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa using
    (fixedOnSubmoduleAndQuotientSubgroup_pow_prime_eq_one
      (p := p) W ρ hfaithful g.property)

/-- If a p-subgroup acts on a rank-one invariant submodule and rank-one quotient,
then it lies in `C_G(W) ∩ C_G(V/W)`. -/
private theorem subgroup_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    (H : Subgroup G) (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hH : IsPGroup p H)
    (hW : ∀ h : H, W ≤ W.comap (ρ h))
    (hdimW : Module.finrank F W = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1) :
    H ≤ fixedOnSubmoduleAndQuotientSubgroup W ρ := by
  intro g hg
  rw [mem_fixedOnSubmoduleAndQuotientSubgroup]
  let h : H := ⟨g, hg⟩
  constructor
  · exact isPGroup_rank_one_submodule_action_trivial_of_charP hH W hdimW (ρ.comp H.subtype)
      hW h
  · exact isPGroup_rank_one_quotient_action_trivial_of_charP hH W hdimQ
      (ρ.comp H.subtype) hW h

/-- Commutativity consequence of
`subgroup_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients`. -/
private theorem subgroup_commutative_of_rank_one_subquotients
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    (H : Subgroup G) (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ) (hH : IsPGroup p H)
    (hW : ∀ h : H, W ≤ W.comap (ρ h))
    (hdimW : Module.finrank F W = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1) :
    Std.Commutative (· * · : H → H → H) := by
  apply subgroup_commutative_of_faithful_representation_fixed_on_submodule_and_quotient
    H W ρ hfaithful
  intro h
  exact mem_fixedOnSubmoduleAndQuotientSubgroup.mp
    (subgroup_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients
      H W ρ hH hW hdimW hdimQ h.property)

/-- A scalar character into a field's unit group kills the commutator subgroup. -/
private theorem commutator_le_ker_of_units_character
    {F : Type*} [Field F] {G : Type*} [Group G] (φ : G →* Fˣ) :
    commutator G ≤ φ.ker := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro x _hx y _hy
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm (φ x) (φ y))

/-- A representation as a group homomorphism into `GL(V)`.

This is the determinant-facing form of a `Representation`; the inverse of
`ρ g` is supplied by `ρ g⁻¹`. -/
def representationToGeneralLinearGroup
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) : G →* LinearMap.GeneralLinearGroup F V where
  toFun g :=
    { val := ρ g
      inv := ρ g⁻¹
      val_inv := by
        rw [← map_mul, mul_inv_cancel, map_one]
      inv_val := by
        rw [← map_mul, inv_mul_cancel, map_one] }
  map_one' := by
    apply Units.ext
    ext v
    simp
  map_mul' g h := by
    apply Units.ext
    ext v
    simp [map_mul]

/-- The determinant character attached to a representation.  BG writes its
kernel as `G* = G ∩ SL(V, F)`. -/
noncomputable def determinantCharacterOfRepresentation
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) : G →* Fˣ :=
  (LinearEquiv.det : (V ≃ₗ[F] V) →* Fˣ).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv F V).toMonoidHom.comp
      (representationToGeneralLinearGroup ρ))

/-- Determinant-kernel subgroup `G*` from BG Thm 2.6. -/
noncomputable def determinantKernelSubgroup
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) : Subgroup G :=
  (determinantCharacterOfRepresentation ρ).ker

theorem mem_determinantKernelSubgroup
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    {ρ : Representation F G V} {g : G} :
    g ∈ determinantKernelSubgroup ρ ↔
      determinantCharacterOfRepresentation ρ g = 1 :=
  Iff.rfl

theorem determinantKernelSubgroup_normal
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) :
    (determinantKernelSubgroup ρ).Normal := by
  dsimp [determinantKernelSubgroup]
  infer_instance

/-- On an invariant rank-one submodule and rank-one quotient, the determinant
character is the product of the two scalar characters. -/
private theorem determinantCharacter_eq_scalarCharacter_mul_quotient
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hdimW : Module.finrank F W = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1)
    (g : G) :
    determinantCharacterOfRepresentation ρ g =
      scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW) g *
        scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW) g := by
  ext
  have hdet :
      LinearMap.det (ρ g) =
        LinearMap.det ((ρ g).restrict (hW g)) *
          LinearMap.det (W.mapQ W (ρ g) (hW g)) :=
    LinearMap.det_eq_det_mul_det W (ρ g) (hW g)
  have hdetW :
      LinearMap.det ((ρ g).restrict (hW g)) =
        (scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW) g : F) := by
    apply det_eq_scalar_of_finrank_eq_one hdimW
    intro w
    simpa [Representation.subrepresentation] using
      scalarCharacterOfFinrankEqOne_apply_smul hdimW
        (ρ.subrepresentation W hW) g w
  have hdetQ :
      LinearMap.det (W.mapQ W (ρ g) (hW g)) =
        (scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW) g : F) := by
    apply det_eq_scalar_of_finrank_eq_one hdimQ
    intro v
    simpa [Representation.quotient] using
      scalarCharacterOfFinrankEqOne_apply_smul hdimQ (ρ.quotient W hW) g v
  calc
    (determinantCharacterOfRepresentation ρ g : F) = LinearMap.det (ρ g) := by
      simp [determinantCharacterOfRepresentation, representationToGeneralLinearGroup]
    _ = LinearMap.det ((ρ g).restrict (hW g)) *
        LinearMap.det (W.mapQ W (ρ g) (hW g)) := hdet
    _ = (scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW) g : F) *
        (scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW) g : F) := by
      rw [hdetW, hdetQ]

/-- Membership in the determinant kernel forces the two rank-one scalar
characters to have product one. -/
private theorem scalarCharacters_mul_eq_one_of_mem_determinantKernel
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hdimW : Module.finrank F W = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1)
    {g : G} (hg : g ∈ determinantKernelSubgroup ρ) :
    scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW) g *
        scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW) g = 1 := by
  have hdet :=
    determinantCharacter_eq_scalarCharacter_mul_quotient W ρ hW hdimW hdimQ g
  have hgdet : determinantCharacterOfRepresentation ρ g = 1 :=
    mem_determinantKernelSubgroup.mp hg
  simpa [hdet] using hgdet

/-- On a preserved complement, the scalar character of the quotient `V/W`
is the same as the scalar character on the complementary line.

This is the bridge needed in BG Thm 2.6 q ≠ p to replace the determinant
formula's quotient scalar by the actual scalar on the second Maschke line. -/
private theorem scalarCharacter_quotient_eq_complement_of_isCompl
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W U : Submodule F V) [Module.Free F U] [Module.Finite F U]
    [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V)
    (hcompl : IsCompl W U)
    (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hU : ∀ g : G, U ≤ U.comap (ρ g))
    (hdimU : Module.finrank F U = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1)
    (g : G) :
    scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW) g =
      scalarCharacterOfFinrankEqOne hdimU (ρ.subrepresentation U hU) g := by
  let φQ : G →* Fˣ := scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW)
  let φU : G →* Fˣ := scalarCharacterOfFinrankEqOne hdimU (ρ.subrepresentation U hU)
  have hU_ne_bot : U ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff]
    omega
  rcases Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hU_ne_bot) with
    ⟨u, hu_ne_zero⟩
  have hmk_ne_zero :
      (Submodule.Quotient.mk (u : V) : V ⧸ W) ≠ 0 := by
    intro hmk
    have huW : (u : V) ∈ W := by
      simpa [Submodule.Quotient.mk_eq_zero] using hmk
    have huInf : (u : V) ∈ W ⊓ U := ⟨huW, u.2⟩
    have huBot : (u : V) ∈ (⊥ : Submodule F V) := by
      simpa [hcompl.inf_eq_bot] using huInf
    exact hu_ne_zero (Subtype.ext (by simpa using huBot))
  have hquot :=
    scalarCharacterOfFinrankEqOne_apply_smul hdimQ (ρ.quotient W hW) g
      (Submodule.Quotient.mk (u : V) : V ⧸ W)
  change
      (Submodule.Quotient.mk (ρ g (u : V)) : V ⧸ W) =
        (φQ g : F) • (Submodule.Quotient.mk (u : V) : V ⧸ W) at hquot
  have hsub :=
    scalarCharacterOfFinrankEqOne_apply_smul hdimU (ρ.subrepresentation U hU) g u
  have hsubV : ρ g (u : V) = (φU g : F) • (u : V) :=
    congrArg Subtype.val hsub
  have hscalar :
      (φU g : F) • (Submodule.Quotient.mk (u : V) : V ⧸ W) =
        (φQ g : F) • (Submodule.Quotient.mk (u : V) : V ⧸ W) := by
    simpa [hsubV] using hquot
  ext
  have hdiff :
      ((φU g : F) - (φQ g : F)) •
          (Submodule.Quotient.mk (u : V) : V ⧸ W) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hscalar
  have hcoeff : (φU g : F) - (φQ g : F) = 0 := by
    exact (smul_eq_zero.mp hdiff).resolve_right hmk_ne_zero
  exact (sub_eq_zero.mp hcoeff).symm

/-- Determinant-kernel elements have inverse scalar characters on two preserved
complementary rank-one lines. -/
private theorem scalarCharacters_complement_mul_eq_one_of_mem_determinantKernel
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W U : Submodule F V) [Module.Free F W] [Module.Free F U] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V)
    (hcompl : IsCompl W U)
    (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hU : ∀ g : G, U ≤ U.comap (ρ g))
    (hdimW : Module.finrank F W = 1)
    (hdimU : Module.finrank F U = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1)
    {g : G} (hg : g ∈ determinantKernelSubgroup ρ) :
    scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW) g *
        scalarCharacterOfFinrankEqOne hdimU (ρ.subrepresentation U hU) g = 1 := by
  have hprod :=
    scalarCharacters_mul_eq_one_of_mem_determinantKernel W ρ hW hdimW hdimQ hg
  have hquot_eq :=
    scalarCharacter_quotient_eq_complement_of_isCompl W U ρ hcompl hW hU
      hdimU hdimQ g
  simpa [hquot_eq] using hprod

/-- A nontrivial odd-order determinant-kernel element has distinct scalars on
two preserved complementary rank-one lines.

This is the BG Thm 2.6 q ≠ p eigenvalue step: if the two scalars were equal,
their determinant product would make the common scalar square to one; odd order
then forces both scalars to be one, and faithfulness makes the element trivial. -/
private theorem scalarCharacters_ne_of_mem_determinantKernel_of_ne_one
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W U : Submodule F V) [Module.Free F W] [Module.Free F U]
    [Module.Finite F U] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (hcompl : IsCompl W U)
    (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hU : ∀ g : G, U ≤ U.comap (ρ g))
    (hdimW : Module.finrank F W = 1)
    (hdimU : Module.finrank F U = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1)
    {g : G} (hgdet : g ∈ determinantKernelSubgroup ρ)
    (hoddg : Odd (orderOf g)) (hg_ne_one : g ≠ 1) :
    scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW) g ≠
      scalarCharacterOfFinrankEqOne hdimU (ρ.subrepresentation U hU) g := by
  let φW : G →* Fˣ := scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW)
  let φU : G →* Fˣ := scalarCharacterOfFinrankEqOne hdimU (ρ.subrepresentation U hU)
  intro hsame
  have hprod :
      φW g * φU g = 1 :=
    scalarCharacters_complement_mul_eq_one_of_mem_determinantKernel
      W U ρ hcompl hW hU hdimW hdimU hdimQ hgdet
  have hsq : (φW g) ^ 2 = 1 := by
    simpa [φW, φU, pow_two, hsame] using hprod
  have hpow_order : (φW g) ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have horder_dvd_two : orderOf (φW g) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one]
    exact hsq
  have horder_dvd_g : orderOf (φW g) ∣ orderOf g :=
    orderOf_dvd_of_pow_eq_one hpow_order
  have hodd_scalar : Odd (orderOf (φW g)) :=
    hoddg.of_dvd_nat horder_dvd_g
  have horder_pos : 0 < orderOf (φW g) := Odd.pos hodd_scalar
  have horder_le_two : orderOf (φW g) ≤ 2 :=
    Nat.le_of_dvd (by decide) horder_dvd_two
  have horder_ne_two : orderOf (φW g) ≠ 2 := by
    intro htwo
    rw [htwo] at hodd_scalar
    exact (by norm_num : ¬ Odd (2 : ℕ)) hodd_scalar
  have horder_one : orderOf (φW g) = 1 := by omega
  have hφW_one : φW g = 1 := orderOf_eq_one_iff.mp horder_one
  have hφU_one : φU g = 1 := by
    simpa [φW, φU, hsame] using hφW_one
  have hg_one : g = 1 := by
    apply hfaithful
    ext v
    obtain ⟨w, u, hv, _huniq⟩ := Submodule.existsUnique_add_of_isCompl hcompl v
    have hw_fix : ρ g (w : V) = (w : V) := by
      have hw_scalar :=
        scalarCharacterOfFinrankEqOne_apply_smul hdimW
          (ρ.subrepresentation W hW) g w
      calc
        ρ g (w : V) = (φW g : F) • (w : V) := congrArg Subtype.val hw_scalar
        _ = (w : V) := by simp [hφW_one]
    have hu_fix : ρ g (u : V) = (u : V) := by
      have hu_scalar :=
        scalarCharacterOfFinrankEqOne_apply_smul hdimU
          (ρ.subrepresentation U hU) g u
      calc
        ρ g (u : V) = (φU g : F) • (u : V) := congrArg Subtype.val hu_scalar
        _ = (u : V) := by simp [hφU_one]
    calc
      ρ g v = ρ g ((w : V) + (u : V)) := by rw [hv]
      _ = ρ g (w : V) + ρ g (u : V) := map_add (ρ g) (w : V) (u : V)
      _ = (w : V) + (u : V) := by rw [hw_fix, hu_fix]
      _ = v := hv
      _ = (ρ 1) v := by simp
  exact hg_ne_one hg_one

/-- A nontrivial odd-order determinant-kernel element with two complementary
rank-one eigenspaces exhausts the rank-one subrepresentations.

This packages the BG Thm 2.6 q ≠ p step that the distinct eigenvalues of
`x ∈ K#` make the two Maschke lines the only one-dimensional `K`-submodules. -/
private theorem rank_one_subrepresentation_eq_left_or_right_of_determinantKernel_element
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ)
    (W U : Subrepresentation ρ)
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F U.toSubmodule] [Module.Free F (V ⧸ W.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQ : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    {x : G} (hxdet : x ∈ determinantKernelSubgroup ρ)
    (hoddx : Odd (orderOf x)) (hx_ne_one : x ≠ 1) :
    ∀ L : Subrepresentation ρ,
      Module.finrank F L.toSubmodule = 1 → L = W ∨ L = U := by
  have hW : ∀ g : G, W.toSubmodule ≤ W.toSubmodule.comap (ρ g) := by
    intro g v hv
    exact W.apply_mem_toSubmodule g hv
  have hU : ∀ g : G, U.toSubmodule ≤ U.toSubmodule.comap (ρ g) := by
    intro g v hv
    exact U.apply_mem_toSubmodule g hv
  let φW : G →* Fˣ :=
    scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W.toSubmodule hW)
  let φU : G →* Fˣ :=
    scalarCharacterOfFinrankEqOne hdimU (ρ.subrepresentation U.toSubmodule hU)
  have hdistinct_units : φW x ≠ φU x :=
    scalarCharacters_ne_of_mem_determinantKernel_of_ne_one
      W.toSubmodule U.toSubmodule ρ hfaithful hcompl hW hU hdimW hdimU hdimQ
      hxdet hoddx hx_ne_one
  have hdistinct : (φW x : F) ≠ (φU x : F) := by
    intro hval
    exact hdistinct_units (Units.ext hval)
  intro L hLdim
  have hLstable : L.toSubmodule ≤ L.toSubmodule.comap (ρ x) := by
    intro v hv
    exact L.apply_mem_toSubmodule x hv
  have hWscalar : ∀ w ∈ W.toSubmodule, ρ x w = (φW x : F) • w := by
    intro w hw
    have hw_scalar :=
      scalarCharacterOfFinrankEqOne_apply_smul hdimW
        (ρ.subrepresentation W.toSubmodule hW) x ⟨w, hw⟩
    exact congrArg Subtype.val hw_scalar
  have hUscalar : ∀ u ∈ U.toSubmodule, ρ x u = (φU x : F) • u := by
    intro u hu
    have hu_scalar :=
      scalarCharacterOfFinrankEqOne_apply_smul hdimU
        (ρ.subrepresentation U.toSubmodule hU) x ⟨u, hu⟩
    exact congrArg Subtype.val hu_scalar
  rcases rank_one_invariant_submodule_eq_left_or_right_of_distinct_scalars
      W.toSubmodule U.toSubmodule L.toSubmodule (ρ x)
      hcompl hdimW hdimU hLdim hLstable (φW x : F) (φU x : F)
      hdistinct hWscalar hUscalar with hLW | hLU
  · left
    exact Subrepresentation.toSubmodule_injective hLW
  · right
    exact Subrepresentation.toSubmodule_injective hLU

/-- Ambient form of
`rank_one_subrepresentation_eq_left_or_right_of_determinantKernel_element`.

If `K ≤ G*` and `G` has odd order, a nontrivial element of `K` supplies the
distinct-scalar witness for the restricted `K`-representation.  This is the
form needed before applying the normal-conjugate line bridge. -/
private theorem rank_one_subrepresentation_eq_left_or_right_of_determinantKernel_subgroup
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (K : Subgroup G) (hKle : K ≤ determinantKernelSubgroup ρ)
    (W U : Subrepresentation (ρ.comp K.subtype))
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F U.toSubmodule] [Module.Free F (V ⧸ W.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQ : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    {x : K} (hx_ne_one : x ≠ 1) :
    ∀ L : Subrepresentation (ρ.comp K.subtype),
      Module.finrank F L.toSubmodule = 1 → L = W ∨ L = U := by
  have hρK_faithful : Function.Injective (ρ.comp K.subtype) := by
    intro a b hab
    apply Subtype.ext
    exact hfaithful (by simpa using hab)
  have hxdet : x ∈ determinantKernelSubgroup (ρ.comp K.subtype) := by
    have hxdetG : (x : G) ∈ determinantKernelSubgroup ρ := hKle x.2
    rw [mem_determinantKernelSubgroup] at hxdetG ⊢
    simpa [determinantCharacterOfRepresentation, representationToGeneralLinearGroup] using hxdetG
  have hoddxG : Odd (orderOf (x : G)) :=
    hodd.of_dvd_nat (orderOf_dvd_natCard (x : G))
  have hoddx : Odd (orderOf x) := by
    simpa [Subgroup.orderOf_coe x] using hoddxG
  exact rank_one_subrepresentation_eq_left_or_right_of_determinantKernel_element
    (ρ.comp K.subtype) hρK_faithful W U hcompl hdimW hdimU hdimQ
    hxdet hoddx hx_ne_one

/-- Determinant-kernel uniqueness forces every ambient conjugate of one Maschke
line to be one of the two Maschke lines.

This is the next BG Thm 2.6 q ≠ p bridge after choosing a nontrivial
`x : K`: normality makes the conjugate a `K`-subrepresentation, and the
distinct-scalar uniqueness pins it to `W` or `U`. -/
private theorem conjugateSubrepresentation_eq_left_or_right_of_determinantKernel_subgroup
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (K : Subgroup G) (hKnormal : K.Normal) (hKle : K ≤ determinantKernelSubgroup ρ)
    (W U : Subrepresentation (ρ.comp K.subtype))
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F U.toSubmodule] [Module.Free F (V ⧸ W.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQ : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    {x : K} (hx_ne_one : x ≠ 1) (g : G) :
    conjugateSubrepresentationOfNormal K hKnormal ρ W g = W ∨
      conjugateSubrepresentationOfNormal K hKnormal ρ W g = U := by
  exact conjugateSubrepresentation_eq_left_or_right_of_rank_one_unique
    K hKnormal ρ W U hdimW
    (rank_one_subrepresentation_eq_left_or_right_of_determinantKernel_subgroup
      ρ hfaithful hodd K hKle W U hcompl hdimW hdimU hdimQ hx_ne_one)
    g

/-- The two conjugate-line alternatives are coherent: an ambient element either
preserves both Maschke lines or swaps them.

The impossible mixed cases would make the two conjugate complementary lines
land on the same nonzero rank-one line. -/
private theorem conjugateSubrepresentations_stay_or_swap_of_determinantKernel_subgroup
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (K : Subgroup G) (hKnormal : K.Normal) (hKle : K ≤ determinantKernelSubgroup ρ)
    (W U : Subrepresentation (ρ.comp K.subtype))
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F W.toSubmodule] [Module.Finite F U.toSubmodule]
    [Module.Free F (V ⧸ W.toSubmodule)] [Module.Free F (V ⧸ U.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQW : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    (hdimQU : Module.finrank F (V ⧸ U.toSubmodule) = 1)
    {x : K} (hx_ne_one : x ≠ 1) (g : G) :
    (conjugateSubrepresentationOfNormal K hKnormal ρ W g = W ∧
      conjugateSubrepresentationOfNormal K hKnormal ρ U g = U) ∨
    (conjugateSubrepresentationOfNormal K hKnormal ρ W g = U ∧
      conjugateSubrepresentationOfNormal K hKnormal ρ U g = W) := by
  have hW_ne_bot : W.toSubmodule ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff]
    omega
  have hU_ne_bot : U.toSubmodule ≠ ⊥ := by
    rw [← Submodule.one_le_finrank_iff]
    omega
  have hcomplg :
      IsCompl
        (conjugateSubrepresentationOfNormal K hKnormal ρ W g).toSubmodule
        (conjugateSubrepresentationOfNormal K hKnormal ρ U g).toSubmodule :=
    isCompl_conjugateSubrepresentationOfNormal K hKnormal ρ W U g hcompl
  rcases conjugateSubrepresentation_eq_left_or_right_of_determinantKernel_subgroup
      ρ hfaithful hodd K hKnormal hKle W U hcompl hdimW hdimU hdimQW
      hx_ne_one g with hWW | hWU
  · rcases conjugateSubrepresentation_eq_left_or_right_of_determinantKernel_subgroup
        ρ hfaithful hodd K hKnormal hKle U W hcompl.symm hdimU hdimW hdimQU
        hx_ne_one g with hUU | hUW
    · exact Or.inl ⟨hWW, hUU⟩
    · exfalso
      have hW_bot : W.toSubmodule = ⊥ := by
        have hleft := congrArg Subrepresentation.toSubmodule hWW
        have hright := congrArg Subrepresentation.toSubmodule hUW
        simpa [hleft, hright] using hcomplg.inf_eq_bot
      exact hW_ne_bot hW_bot
  · rcases conjugateSubrepresentation_eq_left_or_right_of_determinantKernel_subgroup
        ρ hfaithful hodd K hKnormal hKle U W hcompl.symm hdimU hdimW hdimQU
        hx_ne_one g with hUU | hUW
    · exfalso
      have hU_bot : U.toSubmodule = ⊥ := by
        have hleft := congrArg Subrepresentation.toSubmodule hWU
        have hright := congrArg Subrepresentation.toSubmodule hUU
        simpa [hleft, hright] using hcomplg.inf_eq_bot
      exact hU_ne_bot hU_bot
    · exact Or.inr ⟨hWU, hUW⟩

/-- Coherent `comap` form of the two-line alternatives: each ambient element
either preserves both lines or swaps them. -/
private theorem both_lines_le_comap_stay_or_swap_of_determinantKernel_subgroup
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (K : Subgroup G) (hKnormal : K.Normal) (hKle : K ≤ determinantKernelSubgroup ρ)
    (W U : Subrepresentation (ρ.comp K.subtype))
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F W.toSubmodule] [Module.Finite F U.toSubmodule]
    [Module.Free F (V ⧸ W.toSubmodule)] [Module.Free F (V ⧸ U.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQW : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    (hdimQU : Module.finrank F (V ⧸ U.toSubmodule) = 1)
    {x : K} (hx_ne_one : x ≠ 1) (g : G) :
    (W.toSubmodule ≤ W.toSubmodule.comap (ρ g) ∧
      U.toSubmodule ≤ U.toSubmodule.comap (ρ g)) ∨
    (W.toSubmodule ≤ U.toSubmodule.comap (ρ g) ∧
      U.toSubmodule ≤ W.toSubmodule.comap (ρ g)) := by
  rcases conjugateSubrepresentations_stay_or_swap_of_determinantKernel_subgroup
      ρ hfaithful hodd K hKnormal hKle W U hcompl hdimW hdimU hdimQW hdimQU
      hx_ne_one g with hstay | hswap
  · exact Or.inl
      ⟨le_comap_of_conjugateSubrepresentation_eq K hKnormal ρ W W hstay.1,
        le_comap_of_conjugateSubrepresentation_eq K hKnormal ρ U U hstay.2⟩
  · exact Or.inr
      ⟨le_comap_of_conjugateSubrepresentation_eq K hKnormal ρ W U hswap.1,
        le_comap_of_conjugateSubrepresentation_eq K hKnormal ρ U W hswap.2⟩

/-- An injective character into `Fˣ` forces the source group to be abelian. -/
private theorem commutative_of_injective_units_character
    {F : Type*} [Field F] {G : Type*} [Group G] (φ : G →* Fˣ)
    (hφ : Function.Injective φ) :
    Std.Commutative (· * · : G → G → G) := by
  constructor
  intro x y
  apply hφ
  calc
    φ (x * y) = φ x * φ y := map_mul φ x y
    _ = φ y * φ x := by rw [mul_comm]
    _ = φ (y * x) := (map_mul φ y x).symm

private theorem determinantCharacter_injective_of_kernel_eq_bot
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (hker : determinantKernelSubgroup ρ = ⊥) :
    Function.Injective (determinantCharacterOfRepresentation ρ) :=
  (MonoidHom.ker_eq_bot_iff _).mp (by
    simpa [determinantKernelSubgroup] using hker)

/-- BG Thm 2.6 determinant endpoint: if `G* = ker(det ∘ ρ)` is trivial, then
the determinant character embeds `G` into the abelian group `Fˣ`. -/
theorem commutative_of_determinantKernel_eq_bot
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (hker : determinantKernelSubgroup ρ = ⊥) :
    Std.Commutative (· * · : G → G → G) :=
  commutative_of_injective_units_character (determinantCharacterOfRepresentation ρ)
    (determinantCharacter_injective_of_kernel_eq_bot ρ hker)

/-- If `G` preserves a rank-one submodule and rank-one quotient, then `G'`
acts trivially on both.

This is the `G' ≤ C_G(W) ∩ C_G(V/W)` half of BG Thm 2.6, q = p.  Unlike the
p-subgroup bridge above, it does not use characteristic `p`: scalar characters
to `Fˣ` kill commutators because `Fˣ` is abelian. -/
private theorem commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hdimW : Module.finrank F W = 1) (hdimQ : Module.finrank F (V ⧸ W) = 1) :
    commutator G ≤ fixedOnSubmoduleAndQuotientSubgroup W ρ := by
  let φW : G →* Fˣ :=
    scalarCharacterOfFinrankEqOne hdimW (ρ.subrepresentation W hW)
  let φQ : G →* Fˣ :=
    scalarCharacterOfFinrankEqOne hdimQ (ρ.quotient W hW)
  have hkerW : commutator G ≤ φW.ker :=
    commutator_le_ker_of_units_character φW
  have hkerQ : commutator G ≤ φQ.ker :=
    commutator_le_ker_of_units_character φQ
  intro g hg
  rw [mem_fixedOnSubmoduleAndQuotientSubgroup]
  constructor
  · intro w hw
    have hφW : φW g = 1 := MonoidHom.mem_ker.mp (hkerW hg)
    have hsub :=
      scalarCharacterOfFinrankEqOne_apply_smul hdimW
        (ρ.subrepresentation W hW) g ⟨w, hw⟩
    calc
      ρ g w = (φW g : F) • w := congrArg Subtype.val hsub
      _ = w := by simp [hφW]
  · intro v
    have hφQ : φQ g = 1 := MonoidHom.mem_ker.mp (hkerQ hg)
    have hq :=
      scalarCharacterOfFinrankEqOne_apply_smul hdimQ (ρ.quotient W hW) g
        (Submodule.Quotient.mk v : V ⧸ W)
    change Submodule.Quotient.mk (ρ g v) =
      (φQ g : F) • (Submodule.Quotient.mk v : V ⧸ W) at hq
    have hq_one :
        (Submodule.Quotient.mk (ρ g v) : V ⧸ W) =
          (Submodule.Quotient.mk v : V ⧸ W) := by
      simpa [hφQ] using hq
    simpa [Submodule.Quotient.eq] using hq_one

/-- An element acting trivially on a submodule and on the quotient is the identity
if it also preserves a complementary submodule.

This is the diagonal-form bridge for BG Thm 2.6, q ≠ p: once the two
one-dimensional `K`-submodules are both `G`-invariant, a commutator that is
trivial on one line and on the quotient is trivial on the complementary line
as well. -/
private theorem eq_one_of_mem_fixedOnSubmoduleAndQuotientSubgroup_of_preserves_complement
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W U : Submodule F V) (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hcompl : IsCompl W U)
    (hU : ∀ g : G, U ≤ U.comap (ρ g))
    {g : G} (hg : g ∈ fixedOnSubmoduleAndQuotientSubgroup W ρ) :
    g = 1 := by
  apply hfaithful
  ext v
  obtain ⟨w, u, hv, _huniq⟩ := Submodule.existsUnique_add_of_isCompl hcompl v
  have hgW : ∀ w ∈ W, ρ g w = w :=
    (mem_fixedOnSubmoduleAndQuotientSubgroup.mp hg).1
  have hgQ : ∀ v, ρ g v - v ∈ W :=
    (mem_fixedOnSubmoduleAndQuotientSubgroup.mp hg).2
  have hfixU : ρ g (u : V) = (u : V) := by
    have hdiffW : ρ g (u : V) - (u : V) ∈ W := hgQ u
    have hdiffU : ρ g (u : V) - (u : V) ∈ U :=
      U.sub_mem (hU g u.2) u.2
    have hdiff_bot : ρ g (u : V) - (u : V) ∈ (⊥ : Submodule F V) := by
      simpa [hcompl.inf_eq_bot] using (show ρ g (u : V) - (u : V) ∈ W ⊓ U from
        ⟨hdiffW, hdiffU⟩)
    exact sub_eq_zero.mp (by simpa using hdiff_bot)
  calc
    ρ g v = ρ g ((w : V) + (u : V)) := by rw [hv]
    _ = ρ g (w : V) + ρ g (u : V) := map_add (ρ g) (w : V) (u : V)
    _ = (w : V) + (u : V) := by rw [hgW (w : V) w.2, hfixU]
    _ = v := hv
    _ = (ρ 1) v := by simp

/-- If a faithful representation preserves complementary one-dimensional
submodules, then the group is abelian.

In the q≠p branch of BG Thm 2.6, Maschke and algebraic closedness give
`V = W₁ ⊕ W₂` with both lines `G`-invariant.  The two rank-one scalar
characters kill commutators on `W₁` and on `V/W₁`; the complement prevents any
remaining unipotent shear. -/
private theorem commutative_of_faithful_representation_preserves_rank_one_complement
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W U : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hcompl : IsCompl W U) (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hU : ∀ g : G, U ≤ U.comap (ρ g))
    (hdimW : Module.finrank F W = 1)
    (hdimQ : Module.finrank F (V ⧸ W) = 1) :
    Std.Commutative (· * · : G → G → G) := by
  constructor
  intro x y
  rw [← commutatorElement_eq_one_iff_mul_comm]
  apply eq_one_of_mem_fixedOnSubmoduleAndQuotientSubgroup_of_preserves_complement
    W U ρ hfaithful hcompl hU
  exact commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients
    W ρ hW hdimW hdimQ
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))

/-- Odd order turns a stay/swap dichotomy for two complementary lines into
actual preservation of both lines.

This is the line-permutation step in BG Thm 2.6, q ≠ p, stated without
choosing an explicit `Fin 2` action.  If an element swapped the two lines, then
its square would preserve them; since the element has odd order, the element
itself is a power of its square, contradiction with the nonzero first line and
the direct-sum decomposition. -/
private theorem preserves_of_stay_or_swap_rank_one_complement_of_odd
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W U : Submodule F V) [Module.Finite F W]
    (ρ : Representation F G V)
    (hodd : Odd (Nat.card G)) (hcompl : IsCompl W U)
    (hstay_swap : ∀ g : G,
      (W ≤ W.comap (ρ g) ∧ U ≤ U.comap (ρ g)) ∨
      (W ≤ U.comap (ρ g) ∧ U ≤ W.comap (ρ g)))
    (hdimW : Module.finrank F W = 1) :
    ∀ g : G, W ≤ W.comap (ρ g) ∧ U ≤ U.comap (ρ g) := by
  intro g
  rcases hstay_swap g with hstay | hswap
  · exact hstay
  · exfalso
    have hW_ne_bot : W ≠ ⊥ := by
      rw [← Submodule.one_le_finrank_iff]
      omega
    have hg2W : W ≤ W.comap (ρ (g ^ 2)) := by
      intro w hw
      rw [pow_two, map_mul]
      exact hswap.2 (hswap.1 hw)
    have hpowW : ∀ n : ℕ, W ≤ W.comap (ρ ((g ^ 2) ^ n)) := by
      intro n
      induction n with
      | zero =>
          intro w hw
          simpa using hw
      | succ n ih =>
          intro w hw
          rw [pow_succ, map_mul]
          exact ih (hg2W hw)
    have hoddg : Odd (orderOf g) := hodd.of_dvd_nat (orderOf_dvd_natCard g)
    rcases hoddg with ⟨k, hk⟩
    have hg_pow_square : g = (g ^ 2) ^ (k + 1) := by
      calc
        g = g ^ (orderOf g + 1) := by
          rw [pow_succ, pow_orderOf_eq_one, one_mul]
        _ = g ^ (2 * (k + 1)) := by
          congr 1
          omega
        _ = (g ^ 2) ^ (k + 1) := by
          rw [pow_mul]
    have hgW : W ≤ W.comap (ρ g) := by
      rw [hg_pow_square]
      exact hpowW (k + 1)
    rcases Submodule.exists_mem_ne_zero_of_ne_bot hW_ne_bot with ⟨w, hwW, hw_ne_zero⟩
    have hρgw_bot : ρ g w ∈ (⊥ : Submodule F V) := by
      have hρgw_inf : ρ g w ∈ W ⊓ U := ⟨hgW hwW, hswap.1 hwW⟩
      simpa [hcompl.inf_eq_bot] using hρgw_inf
    have hρgw_zero : ρ g w = 0 := by
      simpa using hρgw_bot
    have hw_zero : w = 0 := by
      have hleft : ρ g⁻¹ (ρ g w) = w := by
        calc
          ρ g⁻¹ (ρ g w) = ((ρ g⁻¹) * (ρ g)) w := rfl
          _ = ρ (g⁻¹ * g) w := by rw [map_mul]
          _ = w := by simp
      simpa [hleft] using congrArg (ρ g⁻¹) hρgw_zero
    exact hw_ne_zero hw_zero

/-- Stay/swap form of the odd-order two-line bridge.

This avoids building a separate `Fin 2` action when the proof has already
produced the concrete dichotomy that every element preserves both lines or
swaps them. -/
private theorem commutative_of_faithful_representation_stay_or_swap_rank_one_complement_of_odd
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (W U : Submodule F V) [Module.Free F W] [Module.Finite F W]
    [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hcompl : IsCompl W U)
    (hstay_swap : ∀ g : G,
      (W ≤ W.comap (ρ g) ∧ U ≤ U.comap (ρ g)) ∨
      (W ≤ U.comap (ρ g) ∧ U ≤ W.comap (ρ g)))
    (hdimW : Module.finrank F W = 1)
    (hdimQ : Module.finrank F (V ⧸ W) = 1) :
    Std.Commutative (· * · : G → G → G) := by
  have hpreserve :=
    preserves_of_stay_or_swap_rank_one_complement_of_odd
      W U ρ hodd hcompl hstay_swap hdimW
  exact commutative_of_faithful_representation_preserves_rank_one_complement
    W U ρ hfaithful hcompl
    (fun g => (hpreserve g).1) (fun g => (hpreserve g).2) hdimW hdimQ

/-- Determinant-kernel line-pair bridge for the q≠p branch.

Once Maschke has produced two complementary rank-one `K`-submodules and a
nontrivial element of the normal subgroup `K ≤ G*`, the determinant-kernel
uniqueness argument gives a stay/swap dichotomy for every ambient group
element.  Odd order removes the swap case, so the faithful diagonal bridge
makes `G` abelian. -/
theorem commutative_of_determinantKernel_subgroup_rank_one_complement
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (K : Subgroup G) (hKnormal : K.Normal) (hKle : K ≤ determinantKernelSubgroup ρ)
    (W U : Subrepresentation (ρ.comp K.subtype))
    [Module.Free F W.toSubmodule] [Module.Free F U.toSubmodule]
    [Module.Finite F W.toSubmodule] [Module.Finite F U.toSubmodule]
    [Module.Free F (V ⧸ W.toSubmodule)] [Module.Free F (V ⧸ U.toSubmodule)]
    (hcompl : IsCompl W.toSubmodule U.toSubmodule)
    (hdimW : Module.finrank F W.toSubmodule = 1)
    (hdimU : Module.finrank F U.toSubmodule = 1)
    (hdimQW : Module.finrank F (V ⧸ W.toSubmodule) = 1)
    (hdimQU : Module.finrank F (V ⧸ U.toSubmodule) = 1)
    {x : K} (hx_ne_one : x ≠ 1) :
    Std.Commutative (· * · : G → G → G) := by
  exact
    commutative_of_faithful_representation_stay_or_swap_rank_one_complement_of_odd
      W.toSubmodule U.toSubmodule ρ hfaithful hodd hcompl
      (fun g =>
        both_lines_le_comap_stay_or_swap_of_determinantKernel_subgroup
          ρ hfaithful hodd K hKnormal hKle W U hcompl hdimW hdimU hdimQW hdimQU
          hx_ne_one g)
      hdimW hdimQW

/-- Two-dimensional form of
`commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients`. -/
private theorem commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_finrank_two
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hW : ∀ g : G, W ≤ W.comap (ρ g))
    (hdim : Module.finrank F V = 2) (hW_ne_bot : W ≠ ⊥) (hW_ne_top : W ≠ ⊤) :
    commutator G ≤ fixedOnSubmoduleAndQuotientSubgroup W ρ := by
  rcases rank_one_subquotients_of_finrank_two W hdim hW_ne_bot hW_ne_top with
    ⟨hdimW, hdimQ⟩
  exact commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_rank_one_subquotients
    W ρ hW hdimW hdimQ

/-- A normal p-subgroup is contained in every Sylow p-subgroup.

This is the Sylow-conjugacy bridge used in BG Thm 2.6(b) after a normal
p-subgroup containing `G'` has been constructed. -/
private theorem normal_pSubgroup_le_sylow
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite (Sylow p G)]
    (N : Subgroup G) (hNnormal : N.Normal) (hN : IsPGroup p N) (P : Sylow p G) :
    N ≤ (P : Subgroup G) := by
  have : N.Normal := hNnormal
  obtain ⟨Q, hNQ⟩ := hN.exists_le_sylow
  obtain ⟨g, hgQ⟩ := MulAction.exists_smul_eq G Q P
  calc (N : Subgroup G)
      = MulAut.conj g • N := (Subgroup.Normal.conj_smul_eq_self g N).symm
    _ ≤ MulAut.conj g • (Q : Subgroup G) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hNQ
    _ = ↑(g • Q) := Sylow.coe_subgroup_smul.symm
    _ = ↑P := by rw [hgQ]

/-- If `G'` lies in a normal p-subgroup, then `G'` lies in every Sylow
p-subgroup. -/
private theorem commutator_le_sylow_of_le_normal_pSubgroup
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite (Sylow p G)]
    (N : Subgroup G) (hNnormal : N.Normal) (hN : IsPGroup p N)
    (hcomm : commutator G ≤ N) (P : Sylow p G) :
    commutator G ≤ (P : Subgroup G) :=
  hcomm.trans (normal_pSubgroup_le_sylow N hNnormal hN P)

/-- Two-dimensional wrapper for
`subgroup_commutative_of_rank_one_subquotients`.

This is the form needed in BG Thm 2.6, q = p, after constructing a nonzero
proper invariant fixed-space `W = C_V(K)`. -/
private theorem subgroup_commutative_of_finrank_two_invariant_submodule
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V]
    (H : Subgroup G) (W : Submodule F V) [Module.Free F W] [Module.Free F (V ⧸ W)]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ) (hH : IsPGroup p H)
    (hW : ∀ h : H, W ≤ W.comap (ρ h))
    (hdim : Module.finrank F V = 2) (hW_ne_bot : W ≠ ⊥) (hW_ne_top : W ≠ ⊤) :
    Std.Commutative (· * · : H → H → H) := by
  rcases rank_one_subquotients_of_finrank_two W hdim hW_ne_bot hW_ne_top with
    ⟨hdimW, hdimQ⟩
  exact subgroup_commutative_of_rank_one_subquotients
    H W ρ hfaithful hH hW hdimW hdimQ

/-- If a normal p-subgroup has a proper fixed space in a faithful two-dimensional
representation over characteristic `p`, then every p-subgroup preserving that
fixed space is abelian.

In BG Thm 2.6, q = p, this is applied to
`K = Ω₁(Z(O_p(G^*)))` and `W = C_V(K)`.  Nontriviality of `W` is supplied by
`IsPGroup.invariants_ne_bot`; normality of `K` supplies `G`-invariance. -/
private theorem subgroup_commutative_of_normal_p_fixed_space_proper
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V]
    (K H : Subgroup G) [K.Normal] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hK : IsPGroup p K) (hH : IsPGroup p H)
    (hdim : Module.finrank F V = 2)
    (hfixed_ne_top : Representation.invariants (ρ.comp K.subtype) ≠ ⊤) :
    Std.Commutative (· * · : H → H → H) := by
  let W : Submodule F V := Representation.invariants (ρ.comp K.subtype)
  have hV_ne_bot : (⊤ : Submodule F V) ≠ ⊥ := by
    intro hbot
    have htop : Module.finrank F (⊤ : Submodule F V) = 2 := by
      simp [hdim]
    have hzero : Module.finrank F (⊤ : Submodule F V) = 0 := by
      rw [hbot, finrank_bot]
    omega
  have hW_ne_bot : W ≠ ⊥ := by
    simpa [W] using hK.invariants_ne_bot (ρ.comp K.subtype) hV_ne_bot
  have hW_ne_top : W ≠ ⊤ := by
    simpa [W] using hfixed_ne_top
  have hW_invariant : ∀ h : H, W ≤ W.comap (ρ h) := by
    intro h
    exact Representation.le_comap_invariants ρ K h
  exact subgroup_commutative_of_finrank_two_invariant_submodule
    H W ρ hfaithful hH hW_invariant hdim hW_ne_bot hW_ne_top

/-- In a faithful representation, a nontrivial subgroup cannot fix the whole
space pointwise. -/
private theorem invariants_ne_top_of_faithful_subgroup_ne_bot
    {F : Type*} [Field F] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (K : Subgroup G) (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hK_ne_bot : K ≠ ⊥) :
    Representation.invariants (ρ.comp K.subtype) ≠ ⊤ := by
  intro htop
  apply hK_ne_bot
  ext g
  constructor
  · intro hg
    let k : K := ⟨g, hg⟩
    have hk_fixed : ∀ v : V, ρ g v = v := by
      intro v
      have hv : v ∈ Representation.invariants (ρ.comp K.subtype) := by
        rw [htop]
        exact Submodule.mem_top
      simpa [k] using (Representation.mem_invariants (ρ.comp K.subtype) v).mp hv k
    have hρg : ρ g = 1 := by
      ext v
      exact hk_fixed v
    have hg_one : g = 1 := by
      apply hfaithful
      simp [hρg]
    simp [hg_one]
  · intro hg
    have hg_one : g = 1 := by
      simpa using hg
    simp [hg_one]

/-- Nontrivial-normal-subgroup version of
`subgroup_commutative_of_normal_p_fixed_space_proper`.

This is the closest current Lean entrypoint to BG Thm 2.6, q = p: once the
nontrivial normal p-subgroup `K` is constructed, faithful two-dimensionality
forces its fixed space to be nonzero and proper, hence every p-subgroup is
abelian. -/
private theorem subgroup_commutative_of_nontrivial_normal_p_fixed_space
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V]
    (K H : Subgroup G) [K.Normal] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hK : IsPGroup p K) (hH : IsPGroup p H)
    (hdim : Module.finrank F V = 2) (hK_ne_bot : K ≠ ⊥) :
    Std.Commutative (· * · : H → H → H) :=
  subgroup_commutative_of_normal_p_fixed_space_proper K H ρ hfaithful hK hH hdim
    (invariants_ne_top_of_faithful_subgroup_ne_bot K ρ hfaithful hK_ne_bot)

/-- Nontrivial-normal-p-subgroup form of
`commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_finrank_two`.

This packages the `G' ≤ C_G(W) ∩ C_G(V/W)` bridge for the same
`W = C_V(K)` used in BG Thm 2.6, q = p. -/
private theorem
    commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_nontrivial_normal_p_fixed_space
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V]
    (K : Subgroup G) [K.Normal] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hK : IsPGroup p K)
    (hdim : Module.finrank F V = 2) (hK_ne_bot : K ≠ ⊥) :
    commutator G ≤
      fixedOnSubmoduleAndQuotientSubgroup
        (Representation.invariants (ρ.comp K.subtype)) ρ := by
  let W : Submodule F V := Representation.invariants (ρ.comp K.subtype)
  have hV_ne_bot : (⊤ : Submodule F V) ≠ ⊥ := by
    intro hbot
    have htop : Module.finrank F (⊤ : Submodule F V) = 2 := by
      simp [hdim]
    have hzero : Module.finrank F (⊤ : Submodule F V) = 0 := by
      rw [hbot, finrank_bot]
    omega
  have hW_ne_bot : W ≠ ⊥ := by
    simpa [W] using hK.invariants_ne_bot (ρ.comp K.subtype) hV_ne_bot
  have hW_ne_top : W ≠ ⊤ := by
    simpa [W] using invariants_ne_top_of_faithful_subgroup_ne_bot K ρ hfaithful hK_ne_bot
  have hW_invariant : ∀ g : G, W ≤ W.comap (ρ g) := by
    intro g
    exact Representation.le_comap_invariants ρ K g
  exact commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_finrank_two
    W ρ hW_invariant hdim hW_ne_bot hW_ne_top

/-- Nontrivial-normal-p-subgroup normality form for the same
`W = C_V(K)` used in BG Thm 2.6, q = p. -/
private theorem
    fixedOnSubmoduleAndQuotientSubgroup_normal_of_nontrivial_normal_p_fixed_space
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] {V : Type*} [AddCommGroup V] [Module F V]
    [Module.Finite F V]
    (K : Subgroup G) [K.Normal] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hK : IsPGroup p K)
    (hdim : Module.finrank F V = 2) (hK_ne_bot : K ≠ ⊥) :
    (fixedOnSubmoduleAndQuotientSubgroup
      (Representation.invariants (ρ.comp K.subtype)) ρ).Normal :=
  Subgroup.Normal.of_commutator_le
    (G := G)
    (H := fixedOnSubmoduleAndQuotientSubgroup
      (Representation.invariants (ρ.comp K.subtype)) ρ)
    (commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_nontrivial_normal_p_fixed_space
      K ρ hfaithful hK hdim hK_ne_bot)

/-- Nontrivial-normal-p-subgroup route to the Sylow containment `G' ≤ P`.

This is the current q = p endpoint: after constructing a nontrivial normal
p-subgroup `K`, its fixed space supplies the invariant submodule `W = C_V(K)`,
and the fixed-subquotient subgroup carries `G'` into every Sylow p-subgroup. -/
private theorem commutator_le_sylow_of_nontrivial_normal_p_fixed_space
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (K : Subgroup G) [K.Normal] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hK : IsPGroup p K)
    (hdim : Module.finrank F V = 2) (hK_ne_bot : K ≠ ⊥)
    (P : Sylow p G) :
    commutator G ≤ (P : Subgroup G) := by
  let W : Submodule F V := Representation.invariants (ρ.comp K.subtype)
  have hVpos : 0 < Module.finrank F V := by
    rw [hdim]
    norm_num
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := F) (M := V) hVpos
  exact commutator_le_sylow_of_le_normal_pSubgroup
    (fixedOnSubmoduleAndQuotientSubgroup W ρ)
    (by
      simpa [W] using
        (fixedOnSubmoduleAndQuotientSubgroup_normal_of_nontrivial_normal_p_fixed_space
          K ρ hfaithful hK hdim hK_ne_bot))
    (fixedOnSubmoduleAndQuotientSubgroup_isPGroup_of_faithful
      (p := p) W ρ hfaithful)
    (by
      simpa [W] using
        (commutator_le_fixedOnSubmoduleAndQuotientSubgroup_of_nontrivial_normal_p_fixed_space
          K ρ hfaithful hK hdim hK_ne_bot))
    P

/-- q = p endpoint for BG Thm 2.6(b), conditional on the construction of a
nontrivial normal p-subgroup `K`.

The remaining theorem-level task is to construct the `K` supplied by the BG
argument; once it exists, this lemma gives exactly the Sylow conclusion. -/
theorem sylow_commutative_and_commutator_le_of_nontrivial_normal_p_fixed_space
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (K : Subgroup G) [K.Normal] (ρ : Representation F G V)
    (hfaithful : Function.Injective ρ) (hK : IsPGroup p K)
    (hdim : Module.finrank F V = 2) (hK_ne_bot : K ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  constructor
  · exact subgroup_commutative_of_nontrivial_normal_p_fixed_space
      K (P : Subgroup G) ρ hfaithful hK P.2 hdim hK_ne_bot
  · exact commutator_le_sylow_of_nontrivial_normal_p_fixed_space
      K ρ hfaithful hK hdim hK_ne_bot P

end OddOrder.BG.Ch1.S02


