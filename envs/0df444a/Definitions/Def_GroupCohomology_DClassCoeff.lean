-- Prove2me | Definitions.Def_GroupCohomology_DClassCoeff
-- name    : GroupCohomology_DClassCoeff
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/1b29c7e9-b966-5859-9b65-7b2c28fdd890
-- title:
--   Determinant-class coefficients and transfer Hecke operators for ΓH​(M)
-- statement:
--   Throughout, $k$ is a commutative ring, $M$ a natural number and $H \le (\mathbb{Z}/M)^\times$ a subgroup, and $\Gamma_H(M)$ is the subgroup [`CohCarrier.GammaH M H`](../def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those $\gamma \in \Gamma_0(M)$ whose associated unit lies in $H$. The map `unitsOf` is the homomorphism $\Gamma_H(M) \to (\mathbb{Z}/M)^\times$ obtained by restricting [`CohCarrier.gamma0Units M`](../def/CohCarrier_Level.html#L121); by `val_unitsOf` its value on $\gamma$ is the reduction mod $M$ of the $(1,1)$ entry of $\gamma$ (invertible, with inverse the reduction of the $(0,0)$ entry). Since conjugation by $\mathrm{diag}(1,\ell)$, implemented by [`CohCarrier.conjL`](../def/CohCarrier_Level.html#L228), leaves the $(1,1)$ entry unchanged, `unitsOf_conjL` shows `unitsOf` is invariant under it; `cTop` is the same homomorphism with codomain restricted to the top subgroup of $\Gamma_H(M)$.
--
--   A representation $A$ of $\Gamma_H(M)$ over $k$ satisfies `IsDClass` when there exists a representation $\theta$ of $(\mathbb{Z}/M)^\times$ on the same module with $A.\rho(\gamma) = \theta(\mathrm{unitsOf}(\gamma))$ for all $\gamma$; thus the predicate asserts that the action factors through the $(1,1)$-entry character map, the datum $\theta$ being existentially quantified rather than part of the structure. The model examples are `dTwist`, the pullback of a representation $\theta$ of $(\mathbb{Z}/M)^\times$ along `unitsOf`. The general lemma `isTwist_id_of_comp_eq` says that if $\rho(c\,s) = \rho(s)$ for all $s$, the identity is a twist in the sense of `IsTwist`; applied to `cTop` and a `IsDClass` coefficient system it yields `isTwist_id_of_isDClass`, and hence, for $\ell \neq 0$, the operators `heckeH1D` on $H^1(\Gamma_H(M), A)$ and `heckeInvD` on the invariants, defined as the transfer Hecke operators `heckeH1`, `heckeInv` for $S_1 = \top$, $S_2$ the subgroup [`CohCarrier.GammaHUpper M H ℓ`](../def/CohCarrier_Level.html#L210) of matrices with upper-right entry divisible by $\ell$, $c =$ `cTop` and twist the identity.
--
--   In the second section $\Lambda$ is a commutative ring and $\chi : (\mathbb{Z}/M)^\times \to \Lambda^\times$ a character. For a $\Lambda$-module $N$, `unitRep` is the action of $(\mathbb{Z}/M)^\times$ on $N$ by the scalar $\chi(u)$, and `dMod` its `dTwist`, so $\gamma$ acts on $N$ by multiplication by $\chi(\mathrm{unitsOf}(\gamma))$; this is of determinant class by `isDClass_dMod`. A $\Lambda$-linear map induces a morphism `dMap` of such representations, a pair of composable maps with vanishing composite gives a short complex `dSES` in $\mathrm{Rep}_\Lambda(\Gamma_H(M))$, and `idealSES I` is the short complex attached to the inclusion of an ideal $I \subseteq \Lambda$ followed by the quotient map to $\Lambda/I$.
--
--   **Relation to Mathlib.** Mathlib supplies the congruence subgroups $\Gamma_0$, $\Gamma_1$, $\Gamma$ and low-degree group cohomology ($H^1$, `cocycles₁`), together with `Rep` and `Representation`; the subgroup $\Gamma_H(M)$, the unit map on it, the determinant-class predicate, the twist condition `IsTwist` and the transfer Hecke operators are the project's own notions.
--
--   **Where it is used.** These coefficient systems provide the $\Lambda$-modules with $\Gamma_H(M)$-action through a nebentypus character $\chi$ used to realise modular forms of level $M$ and character $\chi$ in group cohomology, with Hecke operators at $\ell$ given by the transfer construction. The short complexes `dSES` and `idealSES` are the input for the long exact cohomology sequences comparing coefficients $I$, $\Lambda$ and $\Lambda/I$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_DClassCoeff.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_GroupCohomology_TransferHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace HeckeCohomology

open CategoryTheory groupCohomology

open scoped MatrixGroups

section DClass

variable {k : Type} [CommRing k] (M : ℕ) (H : Subgroup (ZMod M)ˣ)

def unitsOf : ↥(CohCarrier.GammaH M H) →* (ZMod M)ˣ :=
  (CohCarrier.gamma0Units M).comp (Subgroup.inclusion (CohCarrier.GammaH_le_Gamma0 H))

theorem val_unitsOf (γ : ↥(CohCarrier.GammaH M H)) :
    (unitsOf M H γ : ZMod M) = (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) := rfl

variable (ℓ : ℕ)

theorem unitsOf_conjL (s : ↥(CohCarrier.GammaHUpper M H ℓ)) :
    unitsOf M H (CohCarrier.conjL M H ℓ s) = unitsOf M H (s : ↥(CohCarrier.GammaH M H)) := by
  apply Units.ext
  rw [val_unitsOf, val_unitsOf]
  show (((CohCarrier.conjUpperMat ℓ ((s : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ))
      (CohCarrier.dvd_of_mem_GammaHUpper M H ℓ s)) 1 1 : ℤ) : ZMod M) =
    ((((s : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)
  rw [CohCarrier.conjUpperMat_apply_11]

noncomputable def cTop : ↥(CohCarrier.GammaHUpper M H ℓ) →* ↥(⊤ : Subgroup ↥(CohCarrier.GammaH M H)) :=
  (CohCarrier.conjL M H ℓ).codRestrict ⊤ fun _ => Subgroup.mem_top _

theorem subtype_comp_cTop :
    (⊤ : Subgroup ↥(CohCarrier.GammaH M H)).subtype.comp (cTop M H ℓ) =
      CohCarrier.conjL M H ℓ :=
  MonoidHom.ext fun _ => rfl

theorem isTwist_id_of_comp_eq {Γ : Type} [Group Γ] (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁)
    (A : Rep k Γ) (h : ∀ s : S₂, A.ρ ((c s : S₁) : Γ) = A.ρ (s : Γ)) :
    IsTwist S₁ S₂ c A LinearMap.id := fun s a => by
  rw [LinearMap.id_apply, LinearMap.id_apply, h]

def IsDClass (A : Rep k ↥(CohCarrier.GammaH M H)) : Prop :=
  ∃ θ : Representation k (ZMod M)ˣ A, ∀ γ, A.ρ γ = θ (unitsOf M H γ)

noncomputable def dTwist {V : Type} [AddCommGroup V] [Module k V]
    (θ : Representation k (ZMod M)ˣ V) : Rep k ↥(CohCarrier.GammaH M H) :=
  Rep.of (θ.comp (unitsOf M H))

theorem dTwist_ρ {V : Type} [AddCommGroup V] [Module k V] (θ : Representation k (ZMod M)ˣ V)
    (γ : ↥(CohCarrier.GammaH M H)) : (dTwist M H θ).ρ γ = θ (unitsOf M H γ) := rfl

theorem isDClass_dTwist {V : Type} [AddCommGroup V] [Module k V]
    (θ : Representation k (ZMod M)ˣ V) : IsDClass M H (dTwist M H θ) := ⟨θ, fun _ => rfl⟩

theorem ρ_cTop_eq (A : Rep k ↥(CohCarrier.GammaH M H)) (hA : IsDClass M H A)
    (s : ↥(CohCarrier.GammaHUpper M H ℓ)) :
    A.ρ ((cTop M H ℓ s : (⊤ : Subgroup ↥(CohCarrier.GammaH M H))) : ↥(CohCarrier.GammaH M H)) =
      A.ρ (s : ↥(CohCarrier.GammaH M H)) := by
  obtain ⟨θ, hθ⟩ := hA
  rw [hθ, hθ]
  show θ (unitsOf M H (CohCarrier.conjL M H ℓ s)) = θ (unitsOf M H s)
  rw [unitsOf_conjL]

theorem isTwist_id_of_isDClass (A : Rep k ↥(CohCarrier.GammaH M H)) (hA : IsDClass M H A) :
    IsTwist ⊤ (CohCarrier.GammaHUpper M H ℓ) (cTop M H ℓ) A LinearMap.id :=
  isTwist_id_of_comp_eq ⊤ _ (cTop M H ℓ) A (ρ_cTop_eq M H ℓ A hA)

variable [NeZero ℓ]

noncomputable def heckeH1D (A : Rep k ↥(CohCarrier.GammaH M H)) (hA : IsDClass M H A) :
    H1 A →ₗ[k] H1 A :=
  heckeH1 ⊤ (CohCarrier.GammaHUpper M H ℓ) (cTop M H ℓ) A LinearMap.id
    (isTwist_id_of_isDClass M H ℓ A hA)

noncomputable def heckeInvD (A : Rep k ↥(CohCarrier.GammaH M H)) (hA : IsDClass M H A) :
    A.ρ.invariants →ₗ[k] A.ρ.invariants :=
  heckeInv ⊤ (CohCarrier.GammaHUpper M H ℓ) (cTop M H ℓ) A LinearMap.id
    (isTwist_id_of_isDClass M H ℓ A hA)

end DClass

section UnitsCharacter

variable {Λ : Type} [CommRing Λ] (M : ℕ) (H : Subgroup (ZMod M)ˣ) (χ : (ZMod M)ˣ →* Λˣ)

def unitRep (N : Type) [AddCommGroup N] [Module Λ N] : Representation Λ (ZMod M)ˣ N :=
  (Module.toModuleEnd Λ N).toMonoidHom.comp ((Units.coeHom Λ).comp χ)

theorem unitRep_apply (N : Type) [AddCommGroup N] [Module Λ N] (u : (ZMod M)ˣ) (n : N) :
    unitRep M χ N u n = ((χ u : Λˣ) : Λ) • n := rfl

noncomputable def dMod (N : Type) [AddCommGroup N] [Module Λ N] :
    Rep Λ ↥(CohCarrier.GammaH M H) :=
  dTwist M H (unitRep M χ N)

theorem isDClass_dMod (N : Type) [AddCommGroup N] [Module Λ N] :
    IsDClass M H (dMod M H χ N) :=
  isDClass_dTwist M H _

noncomputable def dMap {N N' : Type} [AddCommGroup N] [Module Λ N] [AddCommGroup N']
    [Module Λ N'] (f : N →ₗ[Λ] N') : dMod M H χ N ⟶ dMod M H χ N' :=
  Rep.ofHom ⟨f, fun g => by
    ext n
    show f (((χ (unitsOf M H g) : Λˣ) : Λ) • n) = ((χ (unitsOf M H g) : Λˣ) : Λ) • f n
    rw [map_smul]⟩

noncomputable def dSES {N₁ N₂ N₃ : Type} [AddCommGroup N₁] [Module Λ N₁] [AddCommGroup N₂]
    [Module Λ N₂] [AddCommGroup N₃] [Module Λ N₃] (f : N₁ →ₗ[Λ] N₂) (g : N₂ →ₗ[Λ] N₃)
    (hfg : ∀ x, g (f x) = 0) : ShortComplex (Rep Λ ↥(CohCarrier.GammaH M H)) where
  X₁ := dMod M H χ N₁
  X₂ := dMod M H χ N₂
  X₃ := dMod M H χ N₃
  f := dMap M H χ f
  g := dMap M H χ g
  zero := by ext x; exact hfg x

noncomputable def idealSES (I : Ideal Λ) : ShortComplex (Rep Λ ↥(CohCarrier.GammaH M H)) :=
  dSES M H χ I.subtype I.mkQ fun x => (Submodule.Quotient.mk_eq_zero I).2 x.2

end UnitsCharacter

end HeckeCohomology


