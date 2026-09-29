-- Prove2me | Definitions.Def_AlgebraicGeometry_ThetaGroupAction
-- name    : AlgebraicGeometry_ThetaGroupAction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/96b8e816-e354-514a-8558-d7c0b0abdb3c
-- title:
--   Translations, theta points and Schrödinger frames on abelian schemes
-- statement:
--   Throughout, $S$ is a commutative ring, $f : A \to \operatorname{Spec} S$ is a morphism of schemes equipped with a relative group law $L$, and $t : \operatorname{Spec} R \to \operatorname{Spec} S$ is an affine test object; write $A_R = A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ with projections $\mathrm{pr} =$ `pullback.fst f t` and $q =$ `pullback.snd f t`, and $\mathcal L_R = \mathrm{pr}^*\mathcal L$ for $\mathcal L$ an object of `A.Modules`. For a point $x$ of `SchemeHomOver t f` (a morphism $\operatorname{Spec} R \to A$ over $t$), `translate f L t x` is the endomorphism $\tau_x$ of $A_R$ whose first component is the $L$-product, over the base $q \circ t$, of the tautological point $\mathrm{pr}$ with $x$ pulled back along $q$, and whose second component is $q$; `translate_snd` records that $\tau_x$ is a morphism over $\operatorname{Spec} R$.
--
--   A term of `ThetaPt f L 𝓛 t` is a pair consisting of such a point `pt` together with an isomorphism `iso` of modules $\tau_{\mathrm{pt}}^*\mathcal L_R \cong \mathcal L_R$; no further condition (invertibility of $\mathcal L$, membership of the kernel, normalisation) is imposed. For such a $\theta$, `ThetaPt.act θ s` sends a global section $s$ of $\mathcal L_R$ to the image under the forward component of `iso` of the pullback of $s$ along $\tau_{\mathrm{pt}}$, the two relevant open sets $\tau_{\mathrm{pt}}^{-1}(\top)$ and $\top$ being the same. `baseScalar f t r` is the global function on $A_R$ obtained from $r \in R$ through $\Gamma(\operatorname{Spec} R) \cong R$ and $q$.
--
--   Finally, for $\delta : \mathrm{Fin}\,g \to \mathbb N$ with all $\delta_i$ nonzero and $H = \prod_i \mathbb Z/\delta_i$, a `SchrodingerFrame` consists of sections $\sigma_h$ of $\mathcal L_R$ indexed by $h \in H$ such that $c \mapsto \sum_h \mathrm{baseScalar}(c_h)\,\sigma_h$ is a bijection $R^H \to \Gamma(\mathcal L_R,\top)$, together with theta points $\theta_h$ for $h \in H$ and $\eta_\chi$ for each additive character $\chi : H \to R$, subject to the two families of equations $\theta_h \cdot \sigma_{h'} = \sigma_{h+h'}$ and $\eta_\chi \cdot \sigma_h = \chi(h)\,\sigma_h$. Only these identities are required: the assignments $h \mapsto \theta_h$ and $\chi \mapsto \eta_\chi$ are not asked to be homomorphisms, and no group structure on theta points is introduced.
--
--   **Relation to Mathlib.** Mathlib has no theta groups or theta structures for abelian schemes; these definitions are the project's own, formulated on top of Mathlib's sheaves of modules on a scheme and the project's relative group laws and pullbacks of local sections.
--
--   **Where it is used.** These are the vocabulary items for theta rigidifications of polarised abelian schemes of type $\delta$: a Schrödinger frame is exactly a basis of sections of the polarisation bundle on which chosen lifts of the two Lagrangian subgroups of the kernel act by the standard translation and character formulae, which is what the fine moduli statements for polarised abelian schemes of a given type are phrased against.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ThetaGroupAction.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianSchemeOfType
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.Polarisation

variable {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)

def translate {R : Type u} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f) : pullback f t ⟶ pullback f t :=
  pullback.lift
    (L.mul (pullback.snd f t ≫ t) ⟨pullback.fst f t, pullback.condition⟩
        (schemeHomOverComp (pullback.snd f t) rfl x)).1
    (pullback.snd f t)
    (L.mul (pullback.snd f t ≫ t) ⟨pullback.fst f t, pullback.condition⟩
        (schemeHomOverComp (pullback.snd f t) rfl x)).2

theorem translate_snd {R : Type u} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (x : SchemeHomOver t f) : translate f L t x ≫ pullback.snd f t = pullback.snd f t :=
  pullback.lift_snd _ _ _

structure ThetaPt (𝓛 : A.Modules) {R : Type u} [CommRing R]
    (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) where

  pt : SchemeHomOver t f

  iso : (Scheme.Modules.pullback (translate f L t pt)).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
    (Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛

namespace ThetaPt

variable {f} {L} {𝓛 : A.Modules} {R : Type u} [CommRing R] {t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)}

def act (θ : ThetaPt f L 𝓛 t) (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)) :
    Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤) :=

  (θ.iso.hom.app ((translate f L t θ.pt) ⁻¹ᵁ ⊤)
      (Scheme.Modules.pullbackLocalSection (translate f L t θ.pt) s) :
    Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, (translate f L t θ.pt) ⁻¹ᵁ ⊤))

end ThetaPt

def baseScalar {R : Type u} [CommRing R] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) (r : R) :
    Γ(pullback f t, ⊤) :=
  (pullback.snd f t).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)

structure SchrodingerFrame (𝓛 : A.Modules) {R : Type u} [CommRing R]
    (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S)) {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] where

  σ : ((i : Fin g) → ZMod (δ i)) → Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)

  basis : Function.Bijective fun c : ((i : Fin g) → ZMod (δ i)) → R => ∑ h, baseScalar f t (c h) • σ h

  lift : ((i : Fin g) → ZMod (δ i)) → ThetaPt f L 𝓛 t

  dualLift : AddChar ((i : Fin g) → ZMod (δ i)) R → ThetaPt f L 𝓛 t

  lift_act : ∀ h h', (lift h).act (σ h') = σ (h + h')

  dualLift_act : ∀ χ h, (dualLift χ).act (σ h) = baseScalar f t (χ h) • σ h

end AlgebraicGeometry.Polarisation

end


