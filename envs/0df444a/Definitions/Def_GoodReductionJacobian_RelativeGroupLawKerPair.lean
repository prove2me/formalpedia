-- Prove2me | Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
-- name    : GoodReductionJacobian_RelativeGroupLawKerPair
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/11664d77-cbe8-5847-9574-4e80048bc095
-- title:
--   Homomorphisms of relative group laws and joint kernels
-- statement:
--   Fix a commutative ring $R$ and $R$-schemes $(A,f)$, $(A',f')$ equipped with relative group laws $G$, $G'$ in the project's sense: a group structure on the set $\mathrm{SchemeHomOver}\,t\,f$ of $A$-valued points over each test structure map $t : T \to \operatorname{Spec} R$, natural in $T$. For $\psi$ a morphism $A \to A'$ over $\operatorname{Spec} R$, `IsHom G G' ψ` asserts that for every $t : T \to \operatorname{Spec} R$ and all $x,y$ in $A(T)_t$ one has $\psi\circ(x\cdot_G y) = (\psi\circ x)\cdot_{G'}(\psi\circ y)$, i.e. postcomposition with $\psi$ is multiplicative on points. The consequences recorded are that such a $\psi$ carries the unit to the unit and inverses to inverses, that identities are homomorphisms, that homomorphisms compose, and that homomorphy is preserved by base change along $\iota : \operatorname{Spec} R' \to \operatorname{Spec} R$, the morphism of base-changed schemes being `fibreRestrictAlong ι f g ψ`.
--
--   Given $G'$ and a pair $\varphi : \mathrm{Fin}\,2 \to \mathrm{Hom}_{\operatorname{Spec} R}(A,A')$, `kerPair G' φ` is the joint kernel, defined as the fibre product over $A$ of the two schemes $\varphi_i^{-1}(e)$, where $e$ is the unit section $\operatorname{Spec} R \to A'$ of $G'$ at the identity test object; concretely it is the pullback of the two first projections of $A \times_{A'} \operatorname{Spec} R$ taken along $\varphi_0$ and $\varphi_1$. It comes with the canonical morphism `kerPairι` to $A$ and structure map `kerPairStr` to $\operatorname{Spec} R$ obtained by composing with $f$, together with the points dictionary `kerPairPointEquiv`: for each $t$, the $t$-points of `kerPairStr` correspond bijectively, via composition with `kerPairι`, to those $x \in A(T)_t$ with $\varphi_i \circ x$ equal to the unit of $G'$ for $i=0,1$; this bijection is natural in $T$, and two points of the joint kernel agreeing after composition with `kerPairι` coincide. When both $\varphi_i$ are homomorphisms, that subset of points is closed under multiplication, the unit and inversion, and `kerPairLaw G G' φ hφ` is the relative group law on `kerPairStr` transported along this bijection; `kerPairι` is then a homomorphism, commutativity of $G$ passes to it, and its iterated multiplication $n\cdot z$ matches that of $G$ on points. Finally, if $f'$ is separated the unit section of $G'$ is a closed immersion, hence `kerPairι` is a closed immersion and `kerPairStr` inherits local finite type, quasi-compactness and separatedness from $f$.
--
--   **Relation to Mathlib.** Mathlib has group objects and group schemes via monoid objects in a cartesian monoidal category; the relative group law used here is the project's own functor-of-points formulation, and the joint kernel of a pair of such morphisms, with its induced law, has no Mathlib counterpart. The pullbacks, closed-immersion and finiteness-property instances are Mathlib's.
--
--   **Where it is used.** The joint kernel supplies the scheme $\mathcal H = \ker(\varphi_0,\varphi_1)$ attached to a pair of degeneracy morphisms on a Néron model of a Jacobian of a modular curve, over the base, over a residue field and compatibly with base change, together with its torsion subschemes; these enter the level-lowering analysis of the mod $\ell$ representation via Ribet's theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_RelativeGroupLawKerPair.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra

namespace GoodReductionJacobian
namespace RelativeGroupLaw

section IsHom

variable {R : Type u} [CommRing R] {A A' A'' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)} {f'' : A'' ⟶ Spec (CommRingCat.of R)}

def IsHom (G : RelativeGroupLaw R f) (G' : RelativeGroupLaw R f') (ψ : SchemeHomOver f f') : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (G.mul t x y) ψ =
      G'.mul t (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ)

namespace IsHom

variable {G : RelativeGroupLaw R f} {G' : RelativeGroupLaw R f'} {G'' : RelativeGroupLaw R f''}

theorem mul {ψ : SchemeHomOver f f'} (h : IsHom G G' ψ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (G.mul t x y) ψ =
      G'.mul t (NeronModelInfra.schemeHomOverComp x ψ) (NeronModelInfra.schemeHomOverComp y ψ) :=
  h t x y

theorem one {ψ : SchemeHomOver f f'} (h : IsHom G G' ψ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    NeronModelInfra.schemeHomOverComp (G.one t) ψ = G'.one t := by
  letI := G'.pointGroup t
  have h2 : NeronModelInfra.schemeHomOverComp (G.one t) ψ * NeronModelInfra.schemeHomOverComp (G.one t) ψ =
      NeronModelInfra.schemeHomOverComp (G.one t) ψ := by
    show G'.mul t _ _ = _
    rw [← h t, G.one_mul]
  exact mul_eq_left.mp h2

theorem inv {ψ : SchemeHomOver f f'} (h : IsHom G G' ψ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp (G.inv t x) ψ = G'.inv t (NeronModelInfra.schemeHomOverComp x ψ) := by
  letI := G'.pointGroup t
  have h2 : NeronModelInfra.schemeHomOverComp (G.inv t x) ψ * NeronModelInfra.schemeHomOverComp x ψ = 1 := by
    show G'.mul t _ _ = G'.one t
    rw [← h t, G.inv_mul_cancel, h.one]
  exact eq_inv_of_mul_eq_one_left h2

theorem id (G : RelativeGroupLaw R f) : IsHom G G (NeronModelInfra.schemeHomOverId f) := by
  intro T t x y
  simp only [NeronModelInfra.schemeHomOverComp_id_right]

theorem comp {ψ : SchemeHomOver f f'} {χ : SchemeHomOver f' f''} (hψ : IsHom G G' ψ) (hχ : IsHom G' G'' χ) :
    IsHom G G'' (NeronModelInfra.schemeHomOverComp ψ χ) := by
  intro T t x y
  rw [← NeronModelInfra.schemeHomOverComp_assoc, hψ t, hχ t, NeronModelInfra.schemeHomOverComp_assoc,
    NeronModelInfra.schemeHomOverComp_assoc]

end IsHom

theorem IsHom.fibreRestrictAlong {R' : Type u} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} {Gg : RelativeGroupLaw R g} {Gf : RelativeGroupLaw R f}
    {ψ : SchemeHomOver g f} (h : IsHom Gg Gf ψ) :
    IsHom (Gg.baseChange ι) (Gf.baseChange ι) (NeronSpecialFibreInfra.fibreRestrictAlong ι f g ψ) := by
  intro T t x y
  apply (baseChangePointEquiv ι (f := f) t).injective
  show baseChangePointToBase ι _ = baseChangePointToBase ι _
  rw [baseChangePointToBase_comp_fibreRestrictAlong, baseChange_mul, baseChange_mul,
    baseChangePointToBase_ofBase, baseChangePointToBase_ofBase, h,
    baseChangePointToBase_comp_fibreRestrictAlong, baseChangePointToBase_comp_fibreRestrictAlong]

end IsHom

section KerPair

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}

abbrev kerPair (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f') : Scheme.{u} :=
  pullback (pullback.fst (φ 0).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1)
    (pullback.fst (φ 1).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1)

abbrev kerPairι (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f') : kerPair G' φ ⟶ A :=
  pullback.fst (pullback.fst (φ 0).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1)
      (pullback.fst (φ 1).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫
    pullback.fst (φ 0).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev kerPairStr (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f') :
    kerPair G' φ ⟶ Spec (CommRingCat.of R) :=
  kerPairι G' φ ≫ f

variable (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f')

theorem kerLeg_snd_eq (i : Fin 2) :
    pullback.snd (φ i).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1 =
      pullback.fst (φ i).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f := by
  have h1 := pullback.condition (f := (φ i).1) (g := (G'.one (𝟙 (Spec (CommRingCat.of R)))).1)
  have h2 := congrArg (· ≫ f') h1
  simp only [Category.assoc, (φ i).2, (G'.one (𝟙 (Spec (CommRingCat.of R)))).2, Category.comp_id] at h2
  exact h2.symm

@[reassoc]
theorem kerPair_snd_fst :
    pullback.snd (pullback.fst (φ 0).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1)
        (pullback.fst (φ 1).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫
      pullback.fst (φ 1).1 (G'.one (𝟙 (Spec (CommRingCat.of R)))).1 = kerPairι G' φ :=
  pullback.condition.symm

theorem kerPairι_comp (i : Fin 2) :
    kerPairι G' φ ≫ (φ i).1 = kerPairStr G' φ ≫ (G'.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  fin_cases i
  · show (pullback.fst _ _ ≫ pullback.fst _ _) ≫ (φ 0).1 = ((pullback.fst _ _ ≫ pullback.fst _ _) ≫ f) ≫ _
    simp only [Category.assoc]
    rw [pullback.condition (f := (φ 0).1), kerLeg_snd_eq G' φ 0, Category.assoc]
  · show kerPairι G' φ ≫ (φ 1).1 = (kerPairι G' φ ≫ f) ≫ _
    rw [← kerPair_snd_fst]
    simp only [Category.assoc]
    rw [pullback.condition (f := (φ 1).1), kerLeg_snd_eq G' φ 1, Category.assoc]

theorem one_coe_eq {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (G'.one t).1 = t ≫ (G'.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h := G'.one_natural (𝟙 _) t t (Category.comp_id t)
  rw [← h, schemeHomOverComp_coe]

theorem kerPairι_mem {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (z : SchemeHomOver t (kerPairStr G' φ))
    (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (⟨z.1 ≫ kerPairι G' φ, by rw [Category.assoc]; exact z.2⟩ : SchemeHomOver t f)
      (φ i) = G'.one t := by
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe, one_coe_eq, Category.assoc, kerPairι_comp, ← Category.assoc, z.2]

def kerPairLift {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f)
    (hx : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one t) : T ⟶ kerPair G' φ :=
  pullback.lift
    (pullback.lift x.1 t (by rw [← one_coe_eq]; exact congrArg Subtype.val (hx 0)))
    (pullback.lift x.1 t (by rw [← one_coe_eq]; exact congrArg Subtype.val (hx 1)))
    (by rw [pullback.lift_fst, pullback.lift_fst])

@[simp]
theorem kerPairLift_ι {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver t f)
    (hx : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one t) :
    kerPairLift G' φ x hx ≫ kerPairι G' φ = x.1 := by
  simp only [kerPairLift, ← Category.assoc, pullback.lift_fst]

def kerPairPointEquiv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver t (kerPairStr G' φ) ≃
      {x : SchemeHomOver t f // ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one t} where
  toFun z := ⟨⟨z.1 ≫ kerPairι G' φ, by rw [Category.assoc]; exact z.2⟩, kerPairι_mem G' φ z⟩
  invFun x := ⟨kerPairLift G' φ x.1 x.2, by
    show _ ≫ kerPairι G' φ ≫ f = t
    rw [← Category.assoc, kerPairLift_ι]; exact x.1.2⟩
  left_inv z := by
    have hz : z.1 ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ f = t := by
      have := z.2; simp only [Category.assoc] at this; exact this
    apply Subtype.ext
    show kerPairLift G' φ ⟨z.1 ≫ kerPairι G' φ, by rw [Category.assoc]; exact z.2⟩ (kerPairι_mem G' φ z) = z.1
    apply pullback.hom_ext
    · rw [kerPairLift, pullback.lift_fst]
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show z.1 ≫ kerPairι G' φ = (z.1 ≫ pullback.fst _ _) ≫ pullback.fst _ _
        rw [Category.assoc]
      · rw [pullback.lift_snd, kerLeg_snd_eq, Category.assoc, hz]
    · rw [kerPairLift, pullback.lift_snd]
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
        show z.1 ≫ kerPairι G' φ = (z.1 ≫ pullback.snd _ _) ≫ pullback.fst _ _
        rw [Category.assoc, kerPair_snd_fst]
      · rw [pullback.lift_snd, kerLeg_snd_eq, Category.assoc, kerPair_snd_fst_assoc, hz]
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact kerPairLift_ι G' φ x.1 x.2

@[simp]
theorem kerPairPointEquiv_apply_coe_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t (kerPairStr G' φ)) :
    ((kerPairPointEquiv G' φ t z).1).1 = z.1 ≫ kerPairι G' φ :=
  rfl

@[simp]
theorem kerPairPointEquiv_symm_apply_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : {x : SchemeHomOver t f // ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one t}) :
    ((kerPairPointEquiv G' φ t).symm x).1 ≫ kerPairι G' φ = x.1.1 :=
  kerPairLift_ι G' φ x.1 x.2

abbrev kerPairιOver : SchemeHomOver (kerPairStr G' φ) f :=
  ⟨kerPairι G' φ, rfl⟩

theorem kerPairPointEquiv_apply_coe {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t (kerPairStr G' φ)) :
    (kerPairPointEquiv G' φ t z).1 = NeronModelInfra.schemeHomOverComp z (kerPairιOver G' φ) :=
  rfl

theorem kerPairPointEquiv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (z : SchemeHomOver t (kerPairStr G' φ)) :
    (kerPairPointEquiv G' φ t' (schemeHomOverComp ψ hψ z)).1 =
      schemeHomOverComp ψ hψ (kerPairPointEquiv G' φ t z).1 :=
  Subtype.ext (Category.assoc _ _ _)

theorem kerPairPoint_ext {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {z w : SchemeHomOver t (kerPairStr G' φ)}
    (h : z.1 ≫ kerPairι G' φ = w.1 ≫ kerPairι G' φ) : z = w :=
  (kerPairPointEquiv G' φ t).injective (Subtype.ext (Subtype.ext h))

end KerPair

section KerPairLaw

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
variable (G : RelativeGroupLaw R f) (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f')
  (hφ : ∀ i, IsHom G G' (φ i))

section

variable {G G' φ}
include hφ

theorem kerPair_mul_mem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {x y : SchemeHomOver t f}
    (hx : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one t)
    (hy : ∀ i, NeronModelInfra.schemeHomOverComp y (φ i) = G'.one t) (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (G.mul t x y) (φ i) = G'.one t := by
  rw [hφ i t, hx i, hy i, G'.one_mul]

theorem kerPair_one_mem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (G.one t) (φ i) = G'.one t :=
  IsHom.one (hφ i) t

theorem kerPair_inv_mem {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) {x : SchemeHomOver t f}
    (hx : ∀ i, NeronModelInfra.schemeHomOverComp x (φ i) = G'.one t) (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (G.inv t x) (φ i) = G'.one t := by
  letI := G'.pointGroup t
  rw [IsHom.inv (hφ i) t, hx i]
  exact inv_one

end

def kerPairLaw : RelativeGroupLaw R (kerPairStr G' φ) where
  mul t z w := (kerPairPointEquiv G' φ t).symm
    ⟨G.mul t (kerPairPointEquiv G' φ t z).1 (kerPairPointEquiv G' φ t w).1,
      kerPair_mul_mem hφ t (kerPairPointEquiv G' φ t z).2 (kerPairPointEquiv G' φ t w).2⟩
  one t := (kerPairPointEquiv G' φ t).symm ⟨G.one t, kerPair_one_mem hφ t⟩
  inv t z := (kerPairPointEquiv G' φ t).symm
    ⟨G.inv t (kerPairPointEquiv G' φ t z).1, kerPair_inv_mem hφ t (kerPairPointEquiv G' φ t z).2⟩
  mul_assoc t x y z := by
    simp only [Equiv.apply_symm_apply, G.mul_assoc]
  one_mul t x := by
    simp only [Equiv.apply_symm_apply, G.one_mul, Subtype.coe_eta, Equiv.symm_apply_apply]
  mul_one t x := by
    simp only [Equiv.apply_symm_apply, G.mul_one, Subtype.coe_eta, Equiv.symm_apply_apply]
  inv_mul_cancel t x := by
    simp only [Equiv.apply_symm_apply, G.inv_mul_cancel]
  mul_natural t t' ψ hψ x y := by
    apply kerPairPoint_ext
    rw [schemeHomOverComp_coe, Category.assoc, kerPairPointEquiv_symm_apply_coe, kerPairPointEquiv_symm_apply_coe]
    have h := congrArg Subtype.val (G.mul_natural t t' ψ hψ (kerPairPointEquiv G' φ t x).1 (kerPairPointEquiv G' φ t y).1)
    rw [schemeHomOverComp_coe] at h
    rw [h, ← kerPairPointEquiv_natural, ← kerPairPointEquiv_natural]

@[simp]
theorem kerPairPointEquiv_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z w : SchemeHomOver t (kerPairStr G' φ)) :
    (kerPairPointEquiv G' φ t ((kerPairLaw G G' φ hφ).mul t z w)).1 =
      G.mul t (kerPairPointEquiv G' φ t z).1 (kerPairPointEquiv G' φ t w).1 := by
  simp only [kerPairLaw, Equiv.apply_symm_apply]

@[simp]
theorem kerPairPointEquiv_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (kerPairPointEquiv G' φ t ((kerPairLaw G G' φ hφ).one t)).1 = G.one t := by
  simp only [kerPairLaw, Equiv.apply_symm_apply]

@[simp]
theorem kerPairPointEquiv_inv {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (z : SchemeHomOver t (kerPairStr G' φ)) :
    (kerPairPointEquiv G' φ t ((kerPairLaw G G' φ hφ).inv t z)).1 =
      G.inv t (kerPairPointEquiv G' φ t z).1 := by
  simp only [kerPairLaw, Equiv.apply_symm_apply]

theorem kerPairι_isHom : IsHom (kerPairLaw G G' φ hφ) G (kerPairιOver G' φ) := by
  intro T t x y
  rw [← kerPairPointEquiv_apply_coe, kerPairPointEquiv_mul, kerPairPointEquiv_apply_coe, kerPairPointEquiv_apply_coe]

theorem IsCommutative.kerPairLaw (hc : G.IsCommutative) : (kerPairLaw G G' φ hφ).IsCommutative := by
  intro T t x y
  apply (kerPairPointEquiv G' φ t).injective
  apply Subtype.ext
  rw [kerPairPointEquiv_mul, kerPairPointEquiv_mul, hc t]

theorem kerPairPointEquiv_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (z : SchemeHomOver t (kerPairStr G' φ)) :
    (kerPairPointEquiv G' φ t ((kerPairLaw G G' φ hφ).nsmul t n z)).1 = G.nsmul t n (kerPairPointEquiv G' φ t z).1 := by
  induction n with
  | zero => simp only [nsmul_zero, kerPairPointEquiv_one]
  | succ n ih => simp only [nsmul_succ, kerPairPointEquiv_mul, ih]

end KerPairLaw

section Properties

variable {R : Type u} [CommRing R] {A A' : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
variable (G' : RelativeGroupLaw R f') (φ : Fin 2 → SchemeHomOver f f')

theorem isClosedImmersion_one [IsSeparated f'] :
    IsClosedImmersion (G'.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have : IsClosedImmersion ((G'.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f') := by
    rw [(G'.one (𝟙 (Spec (CommRingCat.of R)))).2]; infer_instance
  exact .of_comp _ f'

instance kerPairι_isClosedImmersion [IsSeparated f'] : IsClosedImmersion (kerPairι G' φ) := by
  haveI := isClosedImmersion_one G'
  infer_instance

instance kerPairStr_locallyOfFiniteType [IsSeparated f'] [LocallyOfFiniteType f] :
    LocallyOfFiniteType (kerPairStr G' φ) := by
  infer_instance

instance kerPairStr_quasiCompact [IsSeparated f'] [QuasiCompact f] : QuasiCompact (kerPairStr G' φ) := by
  infer_instance

instance kerPairStr_isSeparated [IsSeparated f'] [IsSeparated f] : IsSeparated (kerPairStr G' φ) := by
  infer_instance

end Properties

end RelativeGroupLaw
end GoodReductionJacobian

end


