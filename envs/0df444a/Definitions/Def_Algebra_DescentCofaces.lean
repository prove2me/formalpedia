-- Prove2me | Definitions.Def_Algebra_DescentCofaces
-- name    : Algebra_DescentCofaces
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/c8b782d4-5bfc-55f0-951a-cf5b60ffd618
-- title:
--   Amitsur cofaces, transport and the descent cocycle condition
-- statement:
--   For a commutative ring $A$, a commutative ring $B$ and an $A$-algebra structure on $B$, this module names the first three terms of the Amitsur (Čech) complex of $A \to B$ inside `CommRingCat`, together with the transport of a transition morphism along a coface. The objects are $R_2 = B\otimes_A B$ and $R_3 = B\otimes_A(B\otimes_A B)$. The two maps $B \to R_2$ are $i_1(b)=b\otimes 1$ and $i_2(b)=1\otimes b$, and the three maps $R_2 \to R_3$ are $c_{12}(b\otimes b')=b\otimes(b'\otimes 1)$, $c_{23}(b\otimes b')=1\otimes(b\otimes b')$ and $c_{13}(b\otimes b')=b\otimes(1\otimes b')$; the small `_apply`/`_tmul` lemmas record these formulas. The simplicial identities are recorded as equalities of morphisms in `CommRingCat`: $i_1$ followed by $c_{12}$ equals $i_1$ followed by $c_{13}$; $i_2$ followed by $c_{12}$ equals $i_1$ followed by $c_{23}$; $i_2$ followed by $c_{13}$ equals $i_2$ followed by $c_{23}$. Two further statements record that the structure map $A \to B$ followed by $i_1$ agrees with it followed by $i_2$, as a morphism equality and as an equality of ring homomorphisms.
--
--   On the module side, for a $B$-module $N$, a coface $c : R_2 \to R_3$ and a morphism $\varphi'$ from the extension of scalars of $N$ along $i_1$ to that along $i_2$, `T` is the induced morphism between the extensions of scalars of $N$ along $i_1$ followed by $c$ and along $i_2$ followed by $c$, obtained by transporting $\varphi'$ through the comparison isomorphisms for composed extension of scalars. `Cocycle N φ'` is then the Prop asserting the equality, in modules over $B\otimes_A(B\otimes_A B)$, of the composite of the transports of $\varphi'$ along $c_{12}$ and $c_{23}$ with its transport along $c_{13}$; this is a predicate on the chosen morphism $\varphi'$, not extra data. Finally, for an $A$-module $M$, `canonical` is the comparison morphism between the two extensions of scalars of $B\otimes_A M$ along $i_1$ and $i_2$, assembled from the composition isomorphisms for extension of scalars and the identification coming from the equality of the two composites $A \to B\otimes_A B$.
--
--   **Relation to Mathlib.** The rings and maps are built from Mathlib's `Algebra.TensorProduct` inclusions and from `ModuleCat.extendScalars` together with its compatibility isomorphism `ModuleCat.extendScalarsComp`; the naming of the cofaces, the transport `T` and the `Cocycle` predicate are the project's own packaging of these.
--
--   **Where it is used.** This vocabulary is the common interface between the scheme-theoretic formulation of descent for quasi-coherent modules along $\operatorname{Spec} B \to \operatorname{Spec} A$ and the ring-theoretic statement of effective faithfully flat descent for modules, both of which feed the commutative-algebra infrastructure of the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Algebra_DescentCofaces.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct CategoryTheory

noncomputable section

namespace Algebra.DescentCofaces

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

abbrev R₂ : CommRingCat.{u} := CommRingCat.of (B ⊗[A] B)

abbrev R₃ : CommRingCat.{u} := CommRingCat.of (B ⊗[A] (B ⊗[A] B))

def i₁ : CommRingCat.of B ⟶ R₂ A B := CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom

def i₂ : CommRingCat.of B ⟶ R₂ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom

def c₁₂ : R₂ A B ⟶ R₃ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
    (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := B))).toRingHom

def c₂₃ : R₂ A B ⟶ R₃ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B ⊗[A] B)).toRingHom

def c₁₃ : R₂ A B ⟶ R₃ A B :=
  CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
    (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B))).toRingHom

@[simp] theorem i₁_apply (b : B) : (i₁ A B).hom b = b ⊗ₜ 1 := rfl
@[simp] theorem i₂_apply (b : B) : (i₂ A B).hom b = 1 ⊗ₜ b := rfl
@[simp] theorem c₁₂_tmul (b b' : B) : (c₁₂ A B).hom (b ⊗ₜ b') = b ⊗ₜ (b' ⊗ₜ 1) := rfl
@[simp] theorem c₂₃_tmul (b b' : B) : (c₂₃ A B).hom (b ⊗ₜ b') = 1 ⊗ₜ (b ⊗ₜ b') := rfl
@[simp] theorem c₁₃_tmul (b b' : B) : (c₁₃ A B).hom (b ⊗ₜ b') = b ⊗ₜ (1 ⊗ₜ b') := rfl

theorem i₁_c₁₂ : i₁ A B ≫ c₁₂ A B = i₁ A B ≫ c₁₃ A B := rfl
theorem i₂_c₁₂ : i₂ A B ≫ c₁₂ A B = i₁ A B ≫ c₂₃ A B := rfl
theorem i₂_c₁₃ : i₂ A B ≫ c₁₃ A B = i₂ A B ≫ c₂₃ A B := rfl

theorem algebraMap_i₁_eq_i₂ :
    CommRingCat.ofHom (algebraMap A B) ≫ i₁ A B = CommRingCat.ofHom (algebraMap A B) ≫ i₂ A B := by
  ext a
  change algebraMap A B a ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] algebraMap A B a
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

theorem i₁_comp_algebraMap_eq :
    (i₁ A B).hom.comp (algebraMap A B) = (i₂ A B).hom.comp (algebraMap A B) :=
  congrArg CommRingCat.Hom.hom (algebraMap_i₁_eq_i₂ A B)

def canonical (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (i₁ A B).hom).obj ((ModuleCat.extendScalars (algebraMap A B)).obj M) ⟶
      (ModuleCat.extendScalars (i₂ A B).hom).obj ((ModuleCat.extendScalars (algebraMap A B)).obj M) :=
  (ModuleCat.extendScalarsComp (algebraMap A B) (i₁ A B).hom).inv.app M ≫
    eqToHom (congrArg (fun f : A →+* B ⊗[A] B => (ModuleCat.extendScalars f).obj M)
      (i₁_comp_algebraMap_eq A B)) ≫
    (ModuleCat.extendScalarsComp (algebraMap A B) (i₂ A B).hom).hom.app M

variable {A B} in

def T (N : ModuleCat.{u} B) (c : R₂ A B ⟶ R₃ A B)
    (φ' : (ModuleCat.extendScalars (i₁ A B).hom).obj N ⟶ (ModuleCat.extendScalars (i₂ A B).hom).obj N) :
    (ModuleCat.extendScalars (i₁ A B ≫ c).hom).obj N ⟶ (ModuleCat.extendScalars (i₂ A B ≫ c).hom).obj N :=
  (ModuleCat.extendScalarsComp (i₁ A B).hom c.hom).hom.app N ≫
    (ModuleCat.extendScalars c.hom).map φ' ≫
    (ModuleCat.extendScalarsComp (i₂ A B).hom c.hom).inv.app N

variable {A B} in

def Cocycle (N : ModuleCat.{u} B)
    (φ' : (ModuleCat.extendScalars (i₁ A B).hom).obj N ⟶ (ModuleCat.extendScalars (i₂ A B).hom).obj N) : Prop :=
  T N (c₁₂ A B) φ' ≫ T N (c₂₃ A B) φ' = T N (c₁₃ A B) φ'

end Algebra.DescentCofaces

end


