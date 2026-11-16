-- Prove2me | Definitions.Def_RPLib_S4_EtShGalGen
-- name    : RPLib_S4_EtShGalGen
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:48:45.478806+00:00
-- url     : https://prove2.me/theorems/3894a930-ca9a-470a-b216-5e12934a0d28
-- title:
--   The generic Galois representation of $F_V$ factors through $\pi_1$
-- statement:
--   Let $A$ be a domain with fraction field $K$ and $L \subseteq K_U$ a finite Galois subextension of the maximal extension unramified over $A$, with its Galois cover ($B$ the integral closure of $A$ in $L$, $G = \mathrm{Gal}(L/K)$) and restriction $\pi_1 = \mathrm{Gal}(K_U/K) \to G$. The embedding $K_U \to \kappa(\eta)^{\mathrm{sep}}$ gives a lift of the generic geometric point $\bar\eta$ to $\mathrm{Spec}\,B$, and for it the Galois representation on $(F_V)_{\bar\eta}$ is $\rho \circ \mathrm{res}_L \circ c$, where $c : \mathrm{Gal}(\kappa(\eta)^{\mathrm{sep}}/\kappa(\eta)) \to \pi_1$ is the comparison map: it factors through $\pi_1$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose V, Section 8; J. S. Milne, Etale Cohomology, Princeton University Press (1980), Chapter I, Section 5

import Mathlib
import Definitions.Def_RPLib_S4_EtShGalFV
import Definitions.Def_RPLib_S4_EtShGenBr

/-!
# S4-EtSheaves, part O10d-2(iv-c), generic point: `galFV` is `π₁ ↠ Gal(L/K)` after `genToPi1`

For a finite Galois subextension `L ⊆ K_U` unramified over `A` and its cover `C = coverOf L`
(`B` = integral closure of `A` in `L`, `G = Gal(L/K)`), restriction is a hom `resL : π₁ = Gal(K_U/K) →* G`
(`resL_spec`). The embedding `K_U → κ(η)^sep` of `GenBr` gives a lift `lGen : Spec κ(η)^sep → Spec B` of the
generic geometric point `η̄` (`hlGen`), and for it `galFV = resL ∘ genToPi1` (`galFV_gen`). Hence the Galois
representation on `(F_V)_η̄` is `ρ ∘ resL ∘ genToPi1` (`stalkFVGen_galRep`): it factors through `π₁`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

open GenBr

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal genAlg genAlgSep genTower

theorem galFV_eq_iff {A : Type} [CommRing A] [IsDomain A] {C : GalCover A} (x : SX A)
    (l : Spec (CommRingCat.of (geomPtAt x).Ω) ⟶ SY C) (hl : l ≫ pr C = (geomPtAt x).pt) (σ : Gal x) (g : C.G) :
    galFV x l hl σ = g ↔ galSpec x σ ≫ l = l ≫ act C g :=
  actOfL_eq_iff _ l hl (galSpec x σ) (galSpec_comp x σ) g

variable (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [IsIntegrallyClosed A] [IsNoetherianRing A]
variable (L : IntermediateField K (AlgebraicClosure K)) (hL : L ∈ unramSet A K)

theorem le_maxUnram (hL' : L ∈ unramSet A K) : L ≤ maxUnram A K := by
  rw [maxUnram_eq_sSup]
  exact le_sSup hL'

/-- Restriction `π₁ = Gal(K_U/K) →* Gal(L/K)`, the group of `coverOf L`. -/
def resL : Pi1 A K →* (coverOf A K L hL).G :=
  haveI := hL.2.1
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion (le_maxUnram A K L hL)).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (le_maxUnram A K L hL))
  AlgEquiv.restrictNormalHom L

theorem resL_spec (τ : Pi1 A K) (x : L) :
    IntermediateField.inclusion (le_maxUnram A K L hL) ((show L ≃ₐ[K] L from resL A K L hL τ) x) =
      τ (IntermediateField.inclusion (le_maxUnram A K L hL) x) := by
  haveI := hL.2.1
  letI : Algebra L (maxUnram A K) := (IntermediateField.inclusion (le_maxUnram A K L hL)).toAlgebra
  haveI : IsScalarTower K L (maxUnram A K) :=
    IsScalarTower.of_algHom (IntermediateField.inclusion (le_maxUnram A K L hL))
  exact τ.restrictNormal_commutes L x

/-- `B → K_U → κ(η)^sep`. -/
def gam : (coverOf A K L hL).B →+* SeparableClosure (genField A) :=
  (genEmb A K).comp ((IntermediateField.inclusion (le_maxUnram A K L hL)).toRingHom.comp
    (algebraMap (integralClosure A L) L))

/-- The lift of the generic geometric point `η̄` to `Spec B` given by `gam`. -/
def lGen : Spec (CommRingCat.of (geomPtAt (genPt A)).Ω) ⟶ SY (coverOf A K L hL) :=
  Spec.map (CommRingCat.ofHom (gam A K L hL))

theorem fracIso_algebraMap (a : A) :
    fracIso A K (algebraMap A K a) =
      (Scheme.Spec.residueFieldIso (CommRingCat.of A) (genPt A)).inv.hom (algebraMap A _ a) := by
  show (Scheme.Spec.residueFieldIso (CommRingCat.of A) (genPt A)).inv.hom
    (IsLocalization.algEquiv (nonZeroDivisors A) K (⊥ : Ideal A).ResidueField (algebraMap A K a)) = _
  rw [AlgEquiv.commutes]
  rfl

theorem gam_algebraMap (a : A) :
    IntermediateField.inclusion (le_maxUnram A K L hL) (algebraMap (integralClosure A L) L (algebraMap A _ a)) =
      algebraMap K (maxUnram A K) (algebraMap A K a) := by
  rw [← IsScalarTower.algebraMap_apply A (integralClosure A L) L, IsScalarTower.algebraMap_apply A K L,
    AlgHom.commutes]

theorem hlGen : lGen A K L hL ≫ pr (coverOf A K L hL) = (geomPtAt (genPt A)).pt := by
  change Spec.map (CommRingCat.ofHom (gam A K L hL)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (coverOf A K L hL).B)) =
    Spec.map (CommRingCat.ofHom (algebraMap (genField A) (SeparableClosure (genField A)))) ≫
      (Spec (CommRingCat.of A)).fromSpecResidueField (genPt A)
  refine (Spec.map_comp _ _).symm.trans ?_
  refine Eq.trans ?_ (congrArg (fun φ => Spec.map (CommRingCat.ofHom
    (algebraMap (genField A) (SeparableClosure (genField A)))) ≫ φ)
    (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (CommRingCat.of A) (genPt A)))
  refine Eq.trans ?_ (congrArg (fun φ => Spec.map (CommRingCat.ofHom
    (algebraMap (genField A) (SeparableClosure (genField A)))) ≫ φ) (Spec.map_comp _ _))
  refine Eq.trans ?_ (Spec.map_comp _ _)
  refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
  exact (congrArg (genEmb A K) (gam_algebraMap A K L hL a)).trans ((genEmb_algebraMap A K _).trans
    (congrArg (algebraMap (genField A) (SeparableClosure (genField A))) (fracIso_algebraMap A K a)))

/-- **At the generic point, `galFV = resL ∘ genToPi1`**: the Galois action on `F_V` factors through `π₁`. -/
theorem galFV_gen (σ : Gal (genPt A)) :
    galFV (genPt A) (lGen A K L hL) (hlGen A K L hL) σ = resL A K L hL (genToPi1 A K σ) := by
  refine (galFV_eq_iff _ _ _ σ _).2 ?_
  change Spec.map (CommRingCat.ofHom (σ : SeparableClosure (genField A) →+* SeparableClosure (genField A))) ≫
      Spec.map (CommRingCat.ofHom (gam A K L hL)) =
    Spec.map (CommRingCat.ofHom (gam A K L hL)) ≫
      Spec.map (CommRingCat.ofHom (rh (coverOf A K L hL) (resL A K L hL (genToPi1 A K σ))))
  refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
  refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun b => ?_))
  exact (genEmb_genToPi1 A K σ _).symm.trans (congrArg (genEmb A K) (resL_spec A K L hL _ _).symm)

variable (Λ : Type) [CommRing Λ] {V : Type} [AddCommGroup V] [Module Λ V]
  (ρ : Representation Λ (coverOf A K L hL).G V)

/-- **The Galois representation on `(F_V)_η̄` is `ρ ∘ resL ∘ genToPi1`.** -/
theorem stalkFVGen_galRep (σ : Gal (genPt A)) (w : stalk Λ (FV (coverOf A K L hL) Λ ρ) (genPt A)) :
    (stalkFVAt Λ ρ (geomPtAt (genPt A)) (lGen A K L hL) (hlGen A K L hL)).hom.hom
        (galRep Λ (FV (coverOf A K L hL) Λ ρ) (genPt A) σ w) =
      ρ (resL A K L hL (genToPi1 A K σ))
        ((stalkFVAt Λ ρ (geomPtAt (genPt A)) (lGen A K L hL) (hlGen A K L hL)).hom.hom w) := by
  rw [stalkFVAt_galRep, galFV_gen]

end RamanujanPetersson.EtSheaves.TorSec


