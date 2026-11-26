-- Prove2me | Definitions.Def_ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_Product
-- name    : ProEtale_Mathlib_Algebra_Homology_DerivedCategory_Ext_Product
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:56:48.334229+00:00
-- url     : https://prove2.me/theorems/1b148e4c-7774-4a0e-8323-fab3c4194b9d
-- title:
--   Dimension shifting for Ext: vanishing from short exact sequences, connecting isomorphisms, and comparing $\operatorname{Ext}^1$ across categories
-- statement:
--   Let $\mathcal C$ be an abelian category with Ext groups. Let $0 \to X_1 \to X_2 \xrightarrow{g} X_3 \to 0$ be a short exact sequence and $Z$ an object. The file records consequences of the covariant long exact sequence of $\operatorname{Ext}(Z,-)$.
--
--   Principal results:
--   1. Suppose every morphism $Z \to X_3$ lifts through $g$, and $\operatorname{Ext}^q(Z,X_2) = \operatorname{Ext}^q(Z,X_3) = 0$ for all $q>0$. Then $\operatorname{Ext}^q(Z,X_1) = 0$ for all $q > 0$.
--   2. The degree-zero connecting homomorphism $\delta_0 : \operatorname{Hom}(Z,X_3) \to \operatorname{Ext}^1(Z,X_1)$ sends $s$ to $s$ composed with the extension class. We have $\delta_0(s) = 0$ if and only if $s$ lifts through $g$, and $\delta_0$ is surjective when $\operatorname{Ext}^1(Z,X_2) = 0$.
--   3. If $\operatorname{Ext}^{n+1}(Z,X_2) = \operatorname{Ext}^{n+2}(Z,X_2) = 0$, the connecting map is an additive isomorphism
--   $$\operatorname{Ext}^{n+1}(Z,X_3) \;\cong\; \operatorname{Ext}^{n+2}(Z,X_1).$$
--   4. Let $\mathcal C'$ be a second abelian category with a short exact sequence $0\to X_1'\to X_2'\to X_3'\to 0$ and an object $Z'$. Suppose there are additive equivalences $\operatorname{Hom}(Z,X_2)\cong\operatorname{Hom}(Z',X_2')$ and $\operatorname{Hom}(Z,X_3)\cong\operatorname{Hom}(Z',X_3')$ that commute with composition by $g$, $g'$. If $\operatorname{Ext}^1(Z,X_2)=0=\operatorname{Ext}^1(Z',X_2')$, then $\operatorname{Ext}^1(Z,X_1)\cong\operatorname{Ext}^1(Z',X_1')$. Both sides are identified with the cokernel of $\operatorname{Hom}(Z,X_2)\to\operatorname{Hom}(Z,X_3)$.
--
--   These are the dimension-shifting tools used in the comparison of étale and pro-étale Ext groups and in the study of Ext out of inverse systems.
--
--   **Formalization Note** The declarations are in `CategoryTheory.Abelian.Ext`: `subsingleton_x₁_of_shortExact`, `deltaZero` (an `AddMonoidHom`), `deltaZero_apply`, `deltaZero_surjective`, `deltaZero_apply_eq_zero_iff`, `connectingEquiv` and `oneEquivOfHomEquiv`. Vanishing is expressed as `Subsingleton (Ext Z X q)`. The module docstring also announces `subsingleton_pi` (vanishing of Ext into exact products), but this file only contains a private auxiliary lemma `pi_comp_zero` for it. The statement itself is not included.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/Algebra/Homology/DerivedCategory/Ext/Product.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Vanishing of `Ext` into products and dimension shifting

Let `C` be an abelian category with `HasExt`. We record elementary consequences of the
covariant long exact `Ext`-sequence:

- `CategoryTheory.Abelian.Ext.subsingleton_x₁_of_shortExact`: if `0 → X₁ → X₂ → X₃ → 0` is
  exact, `Hom(Z, X₂) → Hom(Z, X₃)` is surjective and the positive `Ext`-groups from `Z` to
  `X₂` and `X₃` vanish, then the positive `Ext`-groups from `Z` to `X₁` vanish.
- `CategoryTheory.Abelian.Ext.subsingleton_pi`: if products indexed by `ι` are exact
  (levelwise epimorphisms induce an epimorphism on products), then vanishing of the
  positive `Ext`-groups `Ext Z (G i)` implies vanishing of `Ext Z (∏ᶜ G)`.
  This is the product analogue of `CategoryTheory.subsingleton_ext_coproduct` and is proved
  by the same dimension shifting argument.
- `CategoryTheory.Abelian.Ext.connectingEquiv`: the connecting isomorphism
  `Ext Z X₃ (n+1) ≃+ Ext Z X₁ (n+2)` when the adjacent `Ext`-groups of `X₂` vanish.
- `CategoryTheory.Abelian.Ext.oneEquivOfHomEquiv`: a comparison of `Ext¹`-groups across two
  ambient abelian categories, given short exact sequences with vanishing `Ext¹` of the
  middle objects and compatible additive equivalences on `Hom`-level.
-/

universe w w' t v v' u u'

open CategoryTheory Limits Opposite

namespace CategoryTheory
namespace Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

namespace Ext

section ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) (Z : C)

include hS in
/-- If `0 → X₁ → X₂ → X₃ → 0` is a short exact sequence, every morphism `Z ⟶ X₃` lifts to
`X₂` and the positive `Ext`-groups from `Z` to `X₂` and to `X₃` vanish, then the positive
`Ext`-groups from `Z` to `X₁` vanish. -/
lemma subsingleton_x₁_of_shortExact
    (hsurj : ∀ s : Z ⟶ S.X₃, ∃ t : Z ⟶ S.X₂, t ≫ S.g = s)
    (h₂ : ∀ q, 0 < q → Subsingleton (Ext Z S.X₂ q))
    (h₃ : ∀ q, 0 < q → Subsingleton (Ext Z S.X₃ q)) :
    ∀ q, 0 < q → Subsingleton (Ext Z S.X₁ q) := by
  -- Let `ξ : Ext Z S.X₁ (m + 1)`. Its image in `Ext Z S.X₂ (m + 1)` vanishes by `h₂`,
  -- so by `Ext.covariant_sequence_exact₁` it is of the form `x₃.comp hS.extClass` with
  -- `x₃ : Ext Z S.X₃ m`. If `m > 0`, then `x₃ = 0` by `h₃`, so `ξ = 0`.
  -- If `m = 0`, write `x₃ = Ext.mk₀ s` (using `Ext.mk₀_homEquiv₀_apply`) and lift
  -- `s = t ≫ S.g` by `hsurj`; then
  -- `ξ = (mk₀ (t ≫ S.g)).comp hS.extClass = (mk₀ t).comp ((mk₀ S.g).comp hS.extClass) = 0`
  -- by `ShortComplex.ShortExact.comp_extClass` (use `Ext.mk₀_comp_mk₀` and associativity).
  intro q hq
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos hq).symm⟩
  refine subsingleton_of_forall_eq 0 fun ξ ↦ ?_
  obtain ⟨x₃, hx₃⟩ := covariant_sequence_exact₁ Z hS ξ
    ((h₂ (m + 1) m.succ_pos).elim _ _) rfl
  obtain rfl | hm := Nat.eq_zero_or_pos m
  · obtain ⟨s, rfl⟩ : ∃ s, Ext.mk₀ s = x₃ := ⟨_, Ext.mk₀_homEquiv₀_apply x₃⟩
    obtain ⟨t, rfl⟩ := hsurj s
    rw [← hx₃, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
      Ext.comp_zero]
  · rw [← hx₃, (h₃ m hm).elim x₃ 0, Ext.zero_comp]

/-- The degree-zero connecting homomorphism `(Z ⟶ S.X₃) →+ Ext Z S.X₁ 1` of the covariant
long exact sequence, sending `s` to `(Ext.mk₀ s).comp hS.extClass`. -/
noncomputable def deltaZero : (Z ⟶ S.X₃) →+ Ext Z S.X₁ 1 :=
  (hS.extClass.postcomp Z (zero_add 1)).comp Ext.addEquiv₀.symm.toAddMonoidHom

@[simp]
lemma deltaZero_apply (s : Z ⟶ S.X₃) :
    deltaZero hS Z s = (Ext.mk₀ s).comp hS.extClass (zero_add 1) := by
  have h : (Ext.addEquiv₀.symm s : Ext Z S.X₃ 0) = Ext.mk₀ s := by
    have h0 := Ext.mk₀_addEquiv₀_apply ((Ext.addEquiv₀ (X := Z) (Y := S.X₃)).symm s)
    rw [AddEquiv.apply_symm_apply] at h0
    exact h0.symm
  exact congrArg (fun t : Ext Z S.X₃ 0 ↦ t.comp hS.extClass (zero_add 1)) h

include hS in
lemma deltaZero_surjective (h₂ : Subsingleton (Ext Z S.X₂ 1)) :
    Function.Surjective (deltaZero hS Z) := by
  -- For `ξ : Ext Z S.X₁ 1`, the image in `Ext Z S.X₂ 1` vanishes, so
  -- `Ext.covariant_sequence_exact₁` provides `x₃ : Ext Z S.X₃ 0` with
  -- `x₃.comp hS.extClass = ξ`; conclude with `Ext.mk₀_homEquiv₀_apply`.
  intro ξ
  obtain ⟨x₃, hx₃⟩ := covariant_sequence_exact₁ Z hS ξ (h₂.elim _ _) (zero_add 1)
  obtain ⟨s, rfl⟩ : ∃ s, Ext.mk₀ s = x₃ := ⟨_, Ext.mk₀_homEquiv₀_apply x₃⟩
  exact ⟨s, by rw [deltaZero_apply]; exact hx₃⟩

include hS in
lemma deltaZero_apply_eq_zero_iff (s : Z ⟶ S.X₃) :
    deltaZero hS Z s = 0 ↔ ∃ t : Z ⟶ S.X₂, t ≫ S.g = s := by
  -- `←`: `(mk₀ (t ≫ g)).comp extClass = (mk₀ t).comp ((mk₀ g).comp extClass) = 0` by
  --   `ShortComplex.ShortExact.comp_extClass`.
  -- `→`: by `Ext.covariant_sequence_exact₃` applied to `mk₀ s` (in degree 0), there is
  --   `x₂ : Ext Z S.X₂ 0` with `x₂.comp (mk₀ S.g) = mk₀ s`; write `x₂ = mk₀ t` and use
  --   `Ext.mk₀_comp_mk₀` plus injectivity of `mk₀` (`Ext.mk₀_bijective`).
  rw [deltaZero_apply]
  constructor
  · intro h
    obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ Z hS (Ext.mk₀ s) (zero_add 1) h
    obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective Z S.X₂).2 x₂
    rw [Ext.mk₀_comp_mk₀] at hx₂
    exact ⟨t, (Ext.mk₀_bijective Z S.X₃).1 hx₂⟩
  · rintro ⟨t, rfl⟩
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
      Ext.comp_zero]


/-- The connecting isomorphism `Ext Z S.X₃ (n + 1) ≃+ Ext Z S.X₁ (n + 2)` of the covariant
long exact sequence, when the `Ext`-groups of the middle object in degrees `n + 1` and
`n + 2` vanish. -/
noncomputable def connectingEquiv (n : ℕ)
    (h₂ : Subsingleton (Ext Z S.X₂ (n + 1))) (h₂' : Subsingleton (Ext Z S.X₂ (n + 2))) :
    Ext Z S.X₃ (n + 1) ≃+ Ext Z S.X₁ (n + 2) := by
  -- The map is `hS.extClass.postcomp Z rfl : Ext Z S.X₃ (n+1) →+ Ext Z S.X₁ (n+2)`.
  -- Injectivity: if `x₃.comp hS.extClass = 0`, then by `Ext.covariant_sequence_exact₃`
  -- `x₃ = x₂.comp (mk₀ S.g)` with `x₂ : Ext Z S.X₂ (n+1) = 0`, so `x₃ = 0`.
  -- Surjectivity: for `ξ : Ext Z S.X₁ (n+2)`, its image in `Ext Z S.X₂ (n+2)` vanishes,
  -- so `Ext.covariant_sequence_exact₁` provides a preimage.
  -- Use `AddEquiv.ofBijective`.
  refine AddEquiv.ofBijective (hS.extClass.postcomp Z rfl) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x₃ hx₃
    have hx₃' : x₃.comp hS.extClass rfl = 0 := hx₃
    obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ Z hS x₃ rfl hx₃'
    rw [← hx₂, h₂.elim x₂ 0, Ext.zero_comp]
  · intro ξ
    obtain ⟨x₃, hx₃⟩ := covariant_sequence_exact₁ Z hS ξ (h₂'.elim _ _) rfl
    exact ⟨x₃, hx₃⟩

end ShortExact

section Pi

variable {ι : Type t} [HasProductsOfShape ι C] [EnoughInjectives C]

omit [HasExt.{w} C] in
private lemma pi_comp_zero (B : ι → C) :
    (Limits.Pi.map fun i ↦ Injective.ι (B i)) ≫
      (Limits.Pi.map fun i ↦ cokernel.π (Injective.ι (B i))) = 0 := by
  ext i
  simp


end Pi

section OneEquiv

variable {C' : Type u'} [Category.{v'} C'] [Abelian C'] [HasExt.{w'} C']
variable {S : ShortComplex C} (hS : S.ShortExact) (Z : C)
variable {S' : ShortComplex C'} (hS' : S'.ShortExact) (Z' : C')

/-- Comparison of `Ext¹`-groups across two abelian categories. Given short exact sequences
`S` and `S'` whose middle objects have vanishing `Ext¹` from `Z` resp. `Z'`, and additive
equivalences on `Hom`-level intertwining the maps to the third objects, the `Ext¹`-groups
of the first objects are isomorphic.

Both sides are identified with the cokernel of `Hom(Z, X₂) → Hom(Z, X₃)` via the
degree-zero connecting homomorphism `Ext.deltaZero`. -/
noncomputable def oneEquivOfHomEquiv
    (e₂ : (Z ⟶ S.X₂) ≃+ (Z' ⟶ S'.X₂)) (e₃ : (Z ⟶ S.X₃) ≃+ (Z' ⟶ S'.X₃))
    (hcomm : ∀ t : Z ⟶ S.X₂, e₃ (t ≫ S.g) = e₂ t ≫ S'.g)
    (h₂ : Subsingleton (Ext Z S.X₂ 1)) (h₂' : Subsingleton (Ext Z' S'.X₂ 1)) :
    Ext Z S.X₁ 1 ≃+ Ext Z' S'.X₁ 1 := by
  -- Strategy: both `deltaZero hS Z` and `deltaZero hS' Z'` are surjective with kernels
  -- the images of `Hom(Z, X₂)` resp. `Hom(Z', X₂')` (by `deltaZero_surjective` and
  -- `deltaZero_apply_eq_zero_iff`). Define the forward map by
  -- `ξ ↦ deltaZero hS' Z' (e₃ s)` for any `s` with `deltaZero hS Z s = ξ`:
  -- well-definedness follows since for `s` in the kernel, `s = t ≫ S.g`, and then
  -- `e₃ s = e₂ t ≫ S'.g` lies in the kernel of `deltaZero hS' Z'` by `hcomm`.
  -- Implement either by lifting along the quotient
  -- `(Z ⟶ S.X₃) ⧸ (kernel of deltaZero)` using `QuotientAddGroup.lift` and
  -- `QuotientAddGroup.congr`, or directly via `AddEquiv.ofBijective` on a map defined
  -- with `Classical.choice`; the quotient route is preferred:
  -- 1. `e₁ : (Z ⟶ S.X₃) ⧸ (deltaZero hS Z).ker ≃+ Ext Z S.X₁ 1` from
  --    `QuotientAddGroup.quotientKerEquivOfSurjective`.
  -- 2. `(deltaZero hS Z).ker.map e₃ = (deltaZero hS' Z').ker` from
  --    `deltaZero_apply_eq_zero_iff`, `hcomm` and surjectivity of `e₂` (both inclusions).
  -- 3. Conclude with `QuotientAddGroup.congr`.
  have hker : AddSubgroup.map (e₃ : (Z ⟶ S.X₃) →+ (Z' ⟶ S'.X₃))
      (AddMonoidHom.ker (deltaZero hS Z)) = AddMonoidHom.ker (deltaZero hS' Z') := by
    ext y
    simp only [AddSubgroup.mem_map, AddMonoidHom.mem_ker, AddMonoidHom.coe_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, rfl⟩ := (deltaZero_apply_eq_zero_iff hS Z x).1 hx
      exact (deltaZero_apply_eq_zero_iff hS' Z' _).2 ⟨e₂ t, (hcomm t).symm⟩
    · intro hy
      obtain ⟨t', ht'⟩ := (deltaZero_apply_eq_zero_iff hS' Z' y).1 hy
      obtain ⟨t, rfl⟩ := e₂.surjective t'
      refine ⟨t ≫ S.g, (deltaZero_apply_eq_zero_iff hS Z _).2 ⟨t, rfl⟩, ?_⟩
      rw [hcomm t, ht']
  exact ((QuotientAddGroup.quotientKerEquivOfSurjective _
        (deltaZero_surjective hS Z h₂)).symm.trans
      (QuotientAddGroup.congr (AddMonoidHom.ker (deltaZero hS Z))
        (AddMonoidHom.ker (deltaZero hS' Z')) e₃ hker)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (deltaZero_surjective hS' Z' h₂'))

end OneEquiv

end Ext

end Abelian
end CategoryTheory


