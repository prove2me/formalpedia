-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordConjugateChar
-- name    : OddOrder_GroupTheory_RepresentationTheory_CliffordConjugateChar
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:52:28.281193+00:00
-- url     : https://prove2.me/theorems/e7fc359d-0ff0-4ecd-b793-e51998b18341
-- title:
--   Conjugate characters of the constituents of a restriction (toward BG Prop 2.2(a))
-- statement:
--   For a representation $\rho$ of $G$, a normal subgroup $H\trianglelefteq G$ and a $k[H]$-submodule $W$ of the restriction, conjugation by $g$ (realised by the linear automorphism $\rho(g)$) carries the subrepresentation on $W$ to the subrepresentation on the conjugate $\rho(g)(W)$.
--
--   Main definitions include `repEquiv` ($\rho(g)$ as a linear automorphism), `equivAsModule` and `equivOfAsModuleEquiv` (isomorphisms of representations versus $k[J]$-linear isomorphisms of their modules) and `conjSubEquiv` (the restricted equivalence between a constituent and its conjugate).
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CliffordConjugateChar.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CliffordConjugateChar.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordMultiplicityOne
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtraspecialFaithful
import Definitions.Def_OddOrder_GroupTheory_IsExtraspecial
import Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Main
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

namespace OddOrder.RepresentationTheory

open Representation

open scoped MonoidAlgebra

variable {G : Type*} [Group G]

variable {k : Type*} [Field k]

variable {V : Type*} [AddCommGroup V] [Module k V]

variable (ρ : Representation k G V)

/-- `ρ g` as a `k`-linear automorphism of `V`. -/
noncomputable def repEquiv (g : G) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id])
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id])

@[simp] theorem repEquiv_apply (g : G) (v : V) : repEquiv ρ g v = ρ g v := rfl

/-- Global conjugation identity: `ρ h ∘ ρ g = ρ g ∘ ρ (g⁻¹ h g)`. -/
theorem repEquiv_conj (g : G) (h : G) :
    (ρ h) ∘ₗ (repEquiv ρ g).toLinearMap
      = (repEquiv ρ g).toLinearMap ∘ₗ (ρ (g⁻¹ * h * g)) := by
  ext v
  simp only [LinearMap.comp_apply, repEquiv_apply, LinearEquiv.coe_coe]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 2
  group

/-- A group automorphism preserves the centre: `e h` is central iff `h` is. -/
theorem mulEquiv_mem_center_iff {Γ : Type*} [Group Γ] (e : Γ ≃* Γ) (h : Γ) :
    e h ∈ Subgroup.center Γ ↔ h ∈ Subgroup.center Γ := by
  simp only [Subgroup.mem_center_iff]
  refine ⟨fun H z => e.injective ?_, fun H y => ?_⟩
  · rw [map_mul, map_mul, H (e z)]
  · rw [← e.apply_symm_apply y, ← map_mul, ← map_mul, H (e.symm y)]

/-- **`G = ⟨P, x⟩` centralises `Z(P)`** when `x` does (the `hgc` group input).  Every `z ∈ Z(P)` is
fixed by conjugation by any `g ∈ G`: the centraliser of `z` in `G` contains `P` (`z` is central in
`P`) and `x` (hypothesis `hxZ`), hence contains `⟨P, x⟩ = ⊤`. -/
theorem conjNormalMulAut_center_eq_of_closure {P : Subgroup G} [P.Normal] (x : G)
    (hxZ : ∀ z : ↥P, z ∈ Subgroup.center ↥P → conjNormalMulAut P x z = z)
    (hgen : Subgroup.closure ((P : Set G) ∪ {x}) = ⊤)
    (g : G) {z : ↥P} (hz : z ∈ Subgroup.center ↥P) :
    conjNormalMulAut P g z = z := by
  apply Subtype.ext
  rw [conjNormalMulAut_apply_coe]
  have hle : Subgroup.closure ((P : Set G) ∪ {x}) ≤ Subgroup.centralizer {(z : G)} := by
    rw [Subgroup.closure_le]
    rintro s (hsP | hsx)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro y rfl
      have hc := Subgroup.mem_center_iff.mp hz ⟨s, hsP⟩
      exact congrArg (Subtype.val) hc.symm
    · rw [Set.mem_singleton_iff] at hsx; subst hsx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro y rfl
      have hx := congrArg (Subtype.val) (hxZ z hz)
      rw [conjNormalMulAut_apply_coe, mul_inv_eq_iff_eq_mul] at hx
      exact hx.symm
  have hmem := hle (hgen ▸ Subgroup.mem_top g)
  rw [Subgroup.mem_centralizer_iff] at hmem
  rw [show g * (z : G) = (z : G) * g from (hmem (z : G) rfl).symm, mul_assoc,
    mul_inv_cancel, mul_one]

section SubrepAsModule

variable {J : Type*} [Monoid J] {M : Type*} [AddCommGroup M] [Module k M]

variable (σ : Representation k J M)

set_option backward.isDefEq.respectTransparency false in
/-- The `k[J]`-action on the `asModule` of a subrepresentation `ofSubmodule' N` is the ambient
action restricted. -/
theorem subRep_coe_smul (N : Submodule k[J] σ.asModule) (c : k[J])
    (v : (Subrepresentation.ofSubmodule' N).toRepresentation.asModule) :
    ((c • v).1 : σ.asModule) = c • (show σ.asModule from v.1) := by
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [add_smul, add_smul, AddSubmonoid.coe_add, hx, hy]
  | single g a => rw [Representation.single_smul, Representation.single_smul]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- A `k[J]`-submodule `N` of `σ.asModule`, viewed as `ofSubmodule' N`, has its `asModule`
`k[J]`-linearly isomorphic to `N` (identity on the shared carrier). -/
noncomputable def subRepAsModuleEquiv (N : Submodule k[J] σ.asModule) :
    (↥N) ≃ₗ[k[J]] (Subrepresentation.ofSubmodule' N).toRepresentation.asModule where
  toFun v := v
  invFun w := w
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c v := by
    apply Subtype.ext
    rw [RingHom.id_apply, Submodule.coe_smul]
    exact (subRep_coe_smul σ N c v).symm

set_option backward.isDefEq.respectTransparency false in
/-- For a simple `k[J]`-submodule `N`, the subrepresentation `ofSubmodule' N` is irreducible. -/
theorem subRep_isIrreducible (N : Submodule k[J] σ.asModule) [IsSimpleModule k[J] (↥N)] :
    Representation.IsIrreducible (Subrepresentation.ofSubmodule' N).toRepresentation := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact (subRepAsModuleEquiv σ N).isSimpleModule_iff.mp inferInstance

/-- An isomorphism of representations is a `k[J]`-linear isomorphism of the `asModule`s. -/
noncomputable def equivAsModule {N : Type*} [AddCommGroup N] [Module k N]
    {ρ₁ : Representation k J M} {ρ₂ : Representation k J N} (φ : ρ₁.Equiv ρ₂) :
    ρ₁.asModule ≃ₗ[k[J]] ρ₂.asModule :=
  LinearEquiv.ofBijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ₁ ρ₂ φ.toIntertwiningMap)
    φ.toLinearEquiv.bijective

open Representation.IntertwiningMap in
/-- **Reverse of `equivAsModule`**: a `k[J]`-linear isomorphism of `asModule`s is an isomorphism of
representations.  Its `J`-equivariance comes from the intertwining map underlying
`equivLinearMapAsModule.symm e.toLinearMap` (the reduction `IM.toLinearMap v = e v` goes through
`apply_symm_apply`, since the `.symm`-built map does not definitionally compute). -/
noncomputable def equivOfAsModuleEquiv {N : Type*} [AddCommGroup N] [Module k N]
    {ρ₁ : Representation k J M} {ρ₂ : Representation k J N}
    (e : ρ₁.asModule ≃ₗ[k[J]] ρ₂.asModule) : ρ₁.Equiv ρ₂ :=
  Representation.Equiv.mk (e.restrictScalars k) (by
    have hIM : ∀ v, ((equivLinearMapAsModule ρ₁ ρ₂).symm e.toLinearMap).toLinearMap v = e v := by
      intro v
      have key := (equivLinearMapAsModule ρ₁ ρ₂).apply_symm_apply e.toLinearMap
      have h2 : (equivLinearMapAsModule ρ₁ ρ₂ ((equivLinearMapAsModule ρ₁ ρ₂).symm e.toLinearMap)) v
          = ((equivLinearMapAsModule ρ₁ ρ₂).symm e.toLinearMap).toLinearMap v := rfl
      rw [← h2, key]; rfl
    intro g
    ext v
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    change e (ρ₁ g v) = ρ₂ g (e v)
    rw [← hIM (ρ₁ g v), ← hIM v]
    exact LinearMap.congr_fun
      (((equivLinearMapAsModule ρ₁ ρ₂).symm e.toLinearMap).isIntertwining' g) v)

end SubrepAsModule

section ConjChar

variable {H : Subgroup G} [hH : H.Normal]

variable (W : Submodule k[↥H] (resRep ρ H).asModule)

/-- The underlying `k`-submodule of the conjugate `(ρ g)(W)` equals the `repEquiv ρ g`-image of the
underlying `k`-submodule of `W`. -/
theorem ofSubmodule'_map_toSubmodule (g : G) :
    (Subrepresentation.ofSubmodule' (W.map (conjSemilinearEnd (H := H) ρ g))).toSubmodule
      = (Subrepresentation.ofSubmodule' W).toSubmodule.map (repEquiv ρ g).toLinearMap := by
  apply Submodule.ext
  intro v
  simp only [Submodule.mem_map, repEquiv_apply, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩

/-- The restricted `k`-linear equivalence between the constituent on `W` and the constituent on the
conjugate `(ρ g)(W)`, induced by `repEquiv ρ g`. -/
noncomputable def conjSubEquiv (g : G) :
    (Subrepresentation.ofSubmodule' W).toSubmodule ≃ₗ[k]
      (Subrepresentation.ofSubmodule' (W.map (conjSemilinearEnd (H := H) ρ g))).toSubmodule :=
  (Submodule.equivMapOfInjective (repEquiv ρ g).toLinearMap (repEquiv ρ g).injective _).trans
    (LinearEquiv.ofEq _ _ (ofSubmodule'_map_toSubmodule ρ W g).symm)

@[simp] theorem conjSubEquiv_coe (g : G)
    (w : (Subrepresentation.ofSubmodule' W).toSubmodule) :
    (conjSubEquiv ρ W g w : V) = ρ g (w : V) := by
  simp only [conjSubEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    Submodule.coe_equivMapOfInjective_apply, LinearEquiv.coe_coe, repEquiv_apply]

omit hH in
/-- Coe of the subrepresentation action: `(σ.toRepresentation h) w = ρ h w` in `V`. -/
theorem coe_toRepresentation_apply (σ : Subrepresentation (resRep ρ H)) (h : ↥H)
    (w : σ.toSubmodule) :
    ((σ.toRepresentation h) w : V) = ρ (h : G) (w : V) := rfl

/-- **Conjugate character** (the bridge for BG Prop 2.2(a)'s `hconj`).  The character of the
conjugate constituent `(ρ g)(W)` at `h` equals the character of `W` at `g⁻¹ h g`.  Proof: `repEquiv`
realises an isomorphism of representations between `(ρ g)(W)` and `W` precomposed with the
conjugation automorphism `h ↦ g⁻¹ h g`, so `Representation.char_iso` equates their characters. -/
theorem character_subRep_conj [FiniteDimensional k V] (g : G) (h : ↥H) :
    ((Subrepresentation.ofSubmodule'
        (W.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation).character h
      = ((Subrepresentation.ofSubmodule' W).toRepresentation).character
          (conjNormalMulAut H g⁻¹ h) := by
  have hequiv : Representation.Equiv
      (((Subrepresentation.ofSubmodule' W).toRepresentation).comp
        (conjNormalMulAut H g⁻¹).toMonoidHom)
      ((Subrepresentation.ofSubmodule'
        (W.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation) :=
    Representation.Equiv.mk (conjSubEquiv ρ W g) (by
      intro h'
      ext w
      have hconj := LinearMap.congr_fun (repEquiv_conj ρ g (h' : G)) (w : V)
      simp only [LinearMap.comp_apply, repEquiv_apply, LinearEquiv.coe_coe] at hconj
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, conjSubEquiv_coe,
        MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, coe_toRepresentation_apply,
        conjNormalMulAut_apply_coe, inv_inv]
      exact hconj.symm)
  exact (congrFun (Representation.char_iso hequiv) h).symm

/-- **The conjugate constituent has the same character** when `W` is a faithful irreducible
constituent (nilpotency class `≤ 2`) and `g` centralises `Z(H)`.  Combines the conjugate-character
identity with the vanishing of the character off the centre (`character_eq_zero_of_notMem_center`,
Gor 5.5.5): on the centre the conjugation `h ↦ g⁻¹ h g` is the identity, and off the centre both
characters vanish (the centre is automorphism-invariant). -/
theorem character_subRep_conj_eq [IsAlgClosed k] [FiniteDimensional k V] [IsSimpleModule k[↥H] ↥W]
    (hf : Function.Injective ((Subrepresentation.ofSubmodule' W).toRepresentation))
    (hcl : commutator ↥H ≤ Subgroup.center ↥H) (g : G)
    (hgc : ∀ z : ↥H, z ∈ Subgroup.center ↥H → conjNormalMulAut H g⁻¹ z = z) :
    ((Subrepresentation.ofSubmodule'
        (W.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation).character
      = ((Subrepresentation.ofSubmodule' W).toRepresentation).character := by
  have := subRep_isIrreducible (resRep ρ H) W
  have : FiniteDimensional k ↥((Subrepresentation.ofSubmodule' W).toSubmodule) := inferInstance
  funext h
  rw [character_subRep_conj]
  by_cases hmem : h ∈ Subgroup.center ↥H
  · rw [hgc h hmem]
  · rw [character_eq_zero_of_notMem_center _ hf hcl
        (fun hc => hmem ((mulEquiv_mem_center_iff (conjNormalMulAut H g⁻¹) h).mp hc)),
      character_eq_zero_of_notMem_center _ hf hcl hmem]

/-- **From equal characters to an isomorphism of constituents.**  If the simple constituent `W` and
its conjugate `(ρ g)(W)` have the same character (as `H`-representations), then they are isomorphic
as `k[H]`-modules.  Over an algebraically closed field with `char k ∤ |H|`, this is Schur
orthogonality (`Representation.char_orthonormal`): equal characters force the inner product
`⟨χ_W, χ_W⟩ = 1` to coincide with `⟦W ≅ (ρ g)(W)⟧`, so the latter is nonzero, i.e.
`W ≅ (ρ g)(W)`. -/
theorem submodule_iso_of_character_eq [IsAlgClosed k] [FiniteDimensional k V] [Finite ↥H]
    [Invertible (Nat.card ↥H : k)] [IsSimpleModule k[↥H] ↥W] (g : G)
    (hchar : ((Subrepresentation.ofSubmodule'
          (W.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation).character
        = ((Subrepresentation.ofSubmodule' W).toRepresentation).character) :
    Nonempty (↥W ≃ₗ[k[↥H]] ↥(W.map (conjSemilinearEnd (H := H) ρ g))) := by
  have : Fintype ↥H := Fintype.ofFinite _
  have : IsSimpleModule k[↥H] ↥(W.map (conjSemilinearEnd (H := H) ρ g)) :=
    isSimpleModule_map_conjSemilinearEnd ρ g W
  have := subRep_isIrreducible (resRep ρ H) W
  have := subRep_isIrreducible (resRep ρ H) (W.map (conjSemilinearEnd (H := H) ρ g))
  have h2 : (Nat.card ↥H : k)⁻¹ * ∑ h : ↥H,
      ((Subrepresentation.ofSubmodule' W).toRepresentation).character h
        * ((Subrepresentation.ofSubmodule' W).toRepresentation).character h⁻¹ = 1 := by
    rw [Representation.char_orthonormal, if_pos ⟨Representation.Equiv.refl _⟩]
  have key := Representation.char_orthonormal
    ((Subrepresentation.ofSubmodule' (W.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation)
    ((Subrepresentation.ofSubmodule' W).toRepresentation)
  rw [hchar, h2] at key
  have hne : Nonempty (((Subrepresentation.ofSubmodule' W).toRepresentation).Equiv
      ((Subrepresentation.ofSubmodule'
        (W.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation)) := by
    by_contra hc
    rw [if_neg hc] at key
    exact one_ne_zero key
  obtain ⟨φ⟩ := hne
  exact ⟨(subRepAsModuleEquiv (resRep ρ H) W).trans ((equivAsModule φ).trans
    (subRepAsModuleEquiv (resRep ρ H) (W.map (conjSemilinearEnd (H := H) ρ g))).symm)⟩

/-- **The conjugate `M ≅ M^g` for a faithful irreducible constituent** (BG Prop 2.2(a)'s `hconj`,
the char_orthonormal route).  If `W` is a faithful simple constituent of nilpotency class `≤ 2` over
an algebraically closed field with `char k ∤ |H|`, and `g` centralises `Z(H)`, then `W` is
isomorphic to its conjugate `(ρ g)(W)`.  This is exactly the per-`g` input
(`conjSemilinearEnd`-conjugate form) consumed by `restriction_isIrreducible` /
`isIsotypicOfType_of_conjugates`, obtained from Gorenstein 5.5.5 (character vanishing) plus Schur
orthogonality rather than a from-scratch Gorenstein 5.5.4. -/
theorem conjugate_submodule_iso [IsAlgClosed k] [FiniteDimensional k V] [Finite ↥H]
    [Invertible (Nat.card ↥H : k)] [IsSimpleModule k[↥H] ↥W]
    (hf : Function.Injective ((Subrepresentation.ofSubmodule' W).toRepresentation))
    (hcl : commutator ↥H ≤ Subgroup.center ↥H) (g : G)
    (hgc : ∀ z : ↥H, z ∈ Subgroup.center ↥H → conjNormalMulAut H g⁻¹ z = z) :
    Nonempty (↥W ≃ₗ[k[↥H]] ↥(W.map (conjSemilinearEnd (H := H) ρ g))) :=
  submodule_iso_of_character_eq ρ W g (character_subRep_conj_eq ρ W hf hcl g hgc)

end ConjChar

section UniqueMinimalNormal

/-- **`Z(P)` is the unique minimal normal subgroup of an extraspecial group**: every nontrivial
normal subgroup contains the centre.  Since `N ⊓ Z(P)` is nontrivial
(`normal_inf_center_nontrivial`, `N ⊴ P` nontrivial in a finite `p`-group) and `|Z(P)| = p` is
prime, the corresponding subgroup of
`↥Z(P)` is `⊥` or `⊤`; nontriviality forces `⊤`, i.e. `Z(P) ≤ N`. -/
theorem extraspecial_center_le_of_normal_ne_bot {p : ℕ} [Fact p.Prime] {P : Type*} [Group P]
    [Finite P] (h : OddOrder.GroupTheory.IsExtraspecial p P) {N : Subgroup P} [N.Normal]
    (hN : N ≠ ⊥) : Subgroup.center P ≤ N := by
  have hNnt : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  have hinf : Nontrivial ↥(N ⊓ Subgroup.center P) :=
    OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial h.isPGroup hNnt
  have : Fact (Nat.card ↥(Subgroup.center P)).Prime := ⟨h.center_card.symm ▸ Fact.out⟩
  rcases (N.subgroupOf (Subgroup.center P)).eq_bot_or_eq_top_of_prime_card with hbot | htop
  · exfalso
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff] at hbot
    exact (Subgroup.nontrivial_iff_ne_bot _).mp hinf hbot
  · rwa [Subgroup.subgroupOf_eq_top] at htop

end UniqueMinimalNormal

section Materialize

variable {H : Subgroup G} [hH : H.Normal]

set_option backward.isDefEq.respectTransparency false in
/-- **BG 2.10: every simple constituent of a faithful irreducible is faithful** (over an
extraspecial `H`).  If `ρ` is irreducible and faithful and `H` is extraspecial, then any nonzero
simple `k[H]`-submodule `W` of the restriction carries a faithful representation of `H`.  Proof: the
kernel of the constituent is normal; if nonzero it contains `Z(H)` (unique minimal normal,
`extraspecial_center_le_of_normal_ne_bot`); then a central `z₀ ≠ 1` acts trivially on `W`, hence on
every conjugate `(ρ g)(W)` (the conjugate of `z₀` is again central, so also acts trivially), hence
on their span `⊤ = V`; thus `z₀ ∈ ker ρ = 1`, contradicting `|Z(H)| = p`. -/
theorem extraspecial_constituent_faithful {p : ℕ} [Fact p.Prime] [ρ.IsIrreducible]
    (hρf : Function.Injective ρ) (hPe : OddOrder.GroupTheory.IsExtraspecial p ↥H) [Finite ↥H]
    (W : Submodule k[↥H] (resRep ρ H).asModule) (hWne : W ≠ ⊥) [IsSimpleModule k[↥H] ↥W] :
    Function.Injective ((Subrepresentation.ofSubmodule' W).toRepresentation) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  have hZker : Subgroup.center ↥H ≤ (Subrepresentation.ofSubmodule' W).toRepresentation.ker :=
    extraspecial_center_le_of_normal_ne_bot hPe hne
  have : Nontrivial ↥(Subgroup.center ↥H) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hPe.center_card]; exact (Fact.out : p.Prime).one_lt
  obtain ⟨c, hc⟩ := exists_ne (1 : ↥(Subgroup.center ↥H))
  set z₀ : ↥H := (c : ↥H) with hz₀def
  have hz₀mem : z₀ ∈ Subgroup.center ↥H := c.2
  have hz₀ne : z₀ ≠ 1 := fun h => hc (Subtype.ext h)
  have hVtriv : ∀ v : (resRep ρ H).asModule, ρ ((z₀ : G)) v = v := by
    intro v
    have hv : v ∈ ⨆ g : G, W.map (conjSemilinearEnd (H := H) ρ g) := by
      rw [iSup_map_conjSemilinearEnd_eq_top ρ W hWne]; exact Submodule.mem_top
    refine Submodule.iSup_induction
      (motive := fun u => ρ ((z₀ : G)) u = u)
      (fun g : G => W.map (conjSemilinearEnd (H := H) ρ g)) hv ?_ ?_ ?_
    · intro g y hy
      rw [mem_map_conjSemilinearEnd] at hy
      obtain ⟨w, hwW, rfl⟩ := hy
      have hz''mem : conjNormalMulAut H g⁻¹ z₀ ∈ Subgroup.center ↥H :=
        (mulEquiv_mem_center_iff (conjNormalMulAut H g⁻¹) z₀).mpr hz₀mem
      have hz''W : ρ ((conjNormalMulAut H g⁻¹ z₀ : ↥H) : G) w = w := by
        have hker := MonoidHom.mem_ker.mp (hZker hz''mem)
        have hwmem : w ∈ (Subrepresentation.ofSubmodule' W).toSubmodule := hwW
        have h2 : (Subrepresentation.ofSubmodule' W).toRepresentation
            (conjNormalMulAut H g⁻¹ z₀) ⟨w, hwmem⟩ = ⟨w, hwmem⟩ := by rw [hker]; rfl
        simpa [coe_toRepresentation_apply] using Subtype.ext_iff.mp h2
      have hcoe : ((conjNormalMulAut H g⁻¹ z₀ : ↥H) : G) = g⁻¹ * (z₀ : G) * g := by
        rw [conjNormalMulAut_apply_coe, inv_inv]
      change ρ ((z₀ : G)) (ρ g w) = ρ g w
      rw [← Module.End.mul_apply, ← map_mul,
        show (z₀ : G) * g = g * ((conjNormalMulAut H g⁻¹ z₀ : ↥H) : G) by rw [hcoe]; group,
        map_mul, Module.End.mul_apply, hz''W]
    · exact map_zero _
    · intro a b ha hb; rw [map_add, ha, hb]
  have hVtriv' : ρ ((z₀ : G)) = 1 := by
    ext v; rw [Module.End.one_apply]; exact hVtriv v
  have hz1 : (z₀ : G) = 1 := hρf (show ρ ((z₀ : G)) = ρ 1 by rw [hVtriv', map_one])
  exact hz₀ne (OneMemClass.coe_eq_one.mp hz1)

set_option backward.isDefEq.respectTransparency false in
/-- **BG Prop 2.2(a), materialised** (the `hVP` input to the group-level Theorem 2.5).  If `ρ` is a
faithful-type irreducible representation over an algebraically closed field with `char k ∤ |H|`,
`G = ⟨H, x⟩`, `H` has nilpotency class `≤ 2`, `x` centralises `Z(H)`, and *every* nonzero simple
`k[H]`-constituent of the restriction is faithful (BG 2.10), then the restriction `Res^G_H ρ` is
irreducible.  Assembles: a simple constituent `W` exists (`exists_simple_submodule`); each conjugate
is isomorphic to it (`conjugate_submodule_iso`, with `hgc` from
`conjNormalMulAut_center_eq_of_closure`); so `restriction_isIrreducible` applies. -/
theorem restriction_isIrreducible_of_faithful_constituents [ρ.IsIrreducible] [IsAlgClosed k]
    [Module.Finite k V] [Nontrivial V] [Finite ↥H] [Invertible (Nat.card ↥H : k)]
    (x : G) (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hcl : commutator ↥H ≤ Subgroup.center ↥H)
    (hxZ : ∀ z : ↥H, z ∈ Subgroup.center ↥H → conjNormalMulAut H x z = z)
    (hf : ∀ W : Submodule k[↥H] (resRep ρ H).asModule, W ≠ ⊥ → IsSimpleModule k[↥H] ↥W →
        Function.Injective ((Subrepresentation.ofSubmodule' W).toRepresentation)) :
    (resRep ρ H).IsIrreducible := by
  have : NeZero (Nat.card ↥H : k) := inferInstance
  have : Module.Finite k (resRep ρ H).asModule := inferInstance
  have : Module.Finite k[↥H] (resRep ρ H).asModule :=
    Module.Finite.of_restrictScalars_finite k k[↥H] (resRep ρ H).asModule
  have : IsSemisimpleModule k[↥H] (resRep ρ H).asModule := by
    rw [← isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]; infer_instance
  have : Nontrivial (resRep ρ H).asModule := ‹Nontrivial V›
  obtain ⟨W, hWs⟩ := IsSemisimpleModule.exists_simple_submodule k[↥H] (resRep ρ H).asModule
  have := hWs
  have hWne : W ≠ ⊥ := by
    rintro rfl
    have : Nontrivial ↥(⊥ : Submodule k[↥H] (resRep ρ H).asModule) :=
      IsSimpleModule.nontrivial k[↥H] _
    exact false_of_nontrivial_of_subsingleton ↥(⊥ : Submodule k[↥H] (resRep ρ H).asModule)
  exact restriction_isIrreducible ρ x hgen W hWne (fun g =>
    conjugate_submodule_iso ρ W (hf W hWne hWs) hcl g
      (fun z hz => conjNormalMulAut_center_eq_of_closure x hxZ hgen g⁻¹ hz))

set_option backward.isDefEq.respectTransparency false in
/-- **BG Theorem 2.5's `hVP`, fully materialised for an extraspecial `H`.**  If `ρ` is faithful and
irreducible over an algebraically closed field with `char k ∤ |H|`, `G = ⟨H, x⟩`, `H` is
extraspecial of prime-order centre, and `x` centralises `Z(H)`, then the restriction `Res^G_H ρ` is
irreducible.
Combines `restriction_isIrreducible_of_faithful_constituents` with the constituent faithfulness
`extraspecial_constituent_faithful` (BG 2.10), so no faithfulness hypothesis on the constituents
remains.  The class-`≤2` condition is automatic (`commutator H = Z(H)` for extraspecial `H`). -/
theorem restriction_isIrreducible_of_extraspecial {p : ℕ} [Fact p.Prime] [ρ.IsIrreducible]
    [IsAlgClosed k] [Module.Finite k V] [Nontrivial V] [Finite ↥H] [Invertible (Nat.card ↥H : k)]
    (hρf : Function.Injective ρ) (hPe : OddOrder.GroupTheory.IsExtraspecial p ↥H)
    (x : G) (hgen : Subgroup.closure ((H : Set G) ∪ {x}) = ⊤)
    (hxZ : ∀ z : ↥H, z ∈ Subgroup.center ↥H → conjNormalMulAut H x z = z) :
    (resRep ρ H).IsIrreducible :=
  restriction_isIrreducible_of_faithful_constituents ρ x hgen hPe.commutator_eq_center.le hxZ
    (fun W hWne hWs => by
      have := hWs; exact extraspecial_constituent_faithful ρ hρf hPe W hWne)

end Materialize

end OddOrder.RepresentationTheory


