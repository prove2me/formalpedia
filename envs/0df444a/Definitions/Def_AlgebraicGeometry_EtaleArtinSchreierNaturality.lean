-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleArtinSchreierNaturality
-- name    : AlgebraicGeometry_EtaleArtinSchreierNaturality
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-27T04:08:39.751823+00:00
-- url     : https://prove2.me/theorems/edeb412a-9b6f-46b9-b128-582517ad6782
-- title:
--   Naturality of the Artin–Schreier comparison
-- statement:
--   The canonical restriction map on additive étale cohomology is semilinear over the ground field map and commutes with Frobenius and the inclusion of constant coefficients.
-- source:
--   Stacks Project, Lemma 59.63.6, https://stacks.math.columbia.edu/tag/0A3P.

import Definitions.Def_AlgebraicGeometry_EtaleAdditiveArtinSchreierSequence
import Definitions.Def_AlgebraicGeometry_EtaleAdditiveStructureSheaf
import Definitions.Def_AlgebraicGeometry_EtaleArtinSchreierCohomology
import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_EtaleOpenCoefficientComparison

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)
namespace PhilipponEtaleAcyclicCohomology
universe u
private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

/-- The identity chart is terminal in the small étale site. -/
def isTerminal (X : Scheme.{u}) : IsTerminal (terminal X) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

/-- The base change of the terminal chart is the terminal chart. -/
def terminalComparison {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (baseChange f).obj (terminal X) ≅ terminal Y := by
  have : PreservesFiniteLimits (baseChange f) :=
    inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ f))
  exact (IsTerminal.isTerminalObj (baseChange f) _ (isTerminal X)).uniqueUpToIso (isTerminal Y)

end PhilipponEtaleAcyclicCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAdditiveStructureSheaf (sheaf frobenius scalar mulScalar cohomologyModule)
open PhilipponArtinSchreierKernel (inclusion homEquiv_inclusion_apply primeScalar)
open PhilipponEtaleAcyclicCohomology
  (globalSectionsIso pullbackConstantIso terminalComparison)
open PhilipponEtaleBaseChangeComparison (baseChange map_isPullback)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePrimeTorsionComparison (restrict)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponArtinSchreierBaseChange

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private def toPushforward {X Y : Scheme.{u}} (a : Y ⟶ X) :
    sheaf X ⟶ (pushforward a).obj (sheaf Y) where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom (pullback.fst U.unop.hom a).appTop.hom.toAddMonoidHom
      naturality := by
        intro U V f
        apply AddCommGrpCat.ext
        intro x
        change Γ(U.unop.left, ⊤) at x
        let u := pullback.fst U.unop.hom a
        let v := pullback.fst V.unop.hom a
        let t := f.unop.left
        let g : pullback V.unop.hom a ⟶ pullback U.unop.hom a := ((baseChange a).map f.unop).left
        have h : v ≫ t = g ≫ u := (map_isPullback a f.unop).w
        change (t.appTop ≫ v.appTop) x = (u.appTop ≫ g.appTop) x
        rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h] <;> rfl }

/-- Comparison of additive étale structure sheaves along a morphism of schemes. -/
def structureComparison {X Y : Scheme.{u}} (a : Y ⟶ X) :
    (pullbackSheaves a).obj (sheaf X) ⟶ sheaf Y :=
  ((pullbackAdjunction a).homEquiv _ _).symm (toPushforward a)

/-- The structure-sheaf comparison commutes with the Frobenius endomorphisms. -/
theorem structureComparison_frobenius {K E : Type u} [Field K] [Field E]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (r : X ⟶ Spec (.of K)) (s : Y ⟶ Spec (.of E))
    {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0) (hE : (p : E) = 0) :
    (pullbackSheaves a).map (frobenius r hp hK) ≫ structureComparison a =
      structureComparison a ≫ frobenius s hp hE := by
  let adj := pullbackAdjunction a
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    structureComparison, Equiv.apply_symm_apply]
  ext U x
  change Γ(U.unop.left, ⊤) at x
  change (pullback.fst U.unop.hom a).appTop (x ^ p) =
    ((pullback.fst U.unop.hom a).appTop x) ^ p
  exact map_pow (pullback.fst U.unop.hom a).appTop.hom x p

private theorem scalar_baseChange {K E : Type u} [Field K] [Field E]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (r : X ⟶ Spec (.of K)) (s : Y ⟶ Spec (.of E))
    (φ : K →+* E) (h : a ≫ r = s ≫ Spec.map (CommRingCat.ofHom φ)) (U : X.Etale) :
    scalar r U ≫ (pullback.fst U.hom a).appTop =
      CommRingCat.ofHom φ ≫ scalar s ((baseChange a).obj U) := by
  have comm : pullback.fst U.hom a ≫ (U.hom ≫ r) =
      ((baseChange a).obj U).hom ≫ (s ≫ Spec.map (CommRingCat.ofHom φ)) := by
    change _ = pullback.snd U.hom a ≫ _
    rw [← Category.assoc, pullback.condition, Category.assoc, h]
  simp only [scalar, Category.assoc, ← Scheme.Hom.comp_appTop, comm]
  rw [Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality_assoc, ← Scheme.Hom.comp_appTop]
  rw [← Category.assoc ((baseChange a).obj U).hom s, Scheme.Hom.comp_appTop] <;> rfl

/-- Pulling back the additive sheaf along a field extension takes multiplication
by a scalar to multiplication by its image. -/
theorem structureComparison_mulScalar {K E : Type u} [Field K] [Field E]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (r : X ⟶ Spec (.of K)) (s : Y ⟶ Spec (.of E))
    (φ : K →+* E) (h : a ≫ r = s ≫ Spec.map (CommRingCat.ofHom φ)) (k : K) :
    (pullbackSheaves a).map (mulScalar r k) ≫ structureComparison a =
      structureComparison a ≫ mulScalar s (φ k) := by
  let adj := pullbackAdjunction a
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
    structureComparison, Equiv.apply_symm_apply]
  ext U x
  change Γ(U.unop.left, ⊤) at x
  let t : Γ(U.unop.left, ⊤) ⟶ Γ(((baseChange a).obj U.unop).left, ⊤) :=
    (pullback.fst U.unop.hom a).appTop
  change t (scalar r U.unop k * x) = scalar s ((baseChange a).obj U.unop) (φ k) * t x
  have hk := ConcreteCategory.congr_hom (scalar_baseChange a r s φ h U.unop) k
  change t (scalar r U.unop k) = scalar s ((baseChange a).obj U.unop) (φ k) at hk
  rw [map_mul, hk]

/-- The constant prime-field inclusions commute with inverse image along a field extension. -/
theorem inclusion_baseChange {K E : Type u} [Field K] [Field E]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (r : X ⟶ Spec (.of K)) (s : Y ⟶ Spec (.of E))
    (φ : K →+* E) (h : a ≫ r = s ≫ Spec.map (CommRingCat.ofHom φ))
    {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0) (hE : (p : E) = 0) :
    (pullbackSheaves a).map (inclusion r hp hK) ≫ structureComparison a =
      (pullbackConstantIso a).hom.app (AddCommGrpCat.of (ULift.{u} (ZMod p))) ≫ inclusion s hp hE := by
  let TX := Scheme.Etale.mk (𝟙 X)
  let TY := Scheme.Etale.mk (𝟙 Y)
  let tX := PhilipponEtaleAcyclicCohomology.isTerminal X
  let tY := PhilipponEtaleAcyclicCohomology.isTerminal Y
  let cX := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} tX
  let cY := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} tY
  let A := AddCommGrpCat.of (ULift.{u} (ZMod p))
  let adj := pullbackAdjunction a
  let d := (cX.comp adj).ofNatIsoRight (globalSectionsIso a)
  let k := (terminalComparison a).inv
  have hx : d.homEquiv A (sheaf Y) ((pullbackSheaves a).map (inclusion r hp hK) ≫
      structureComparison a) =
      cX.homEquiv A (sheaf X) (inclusion r hp hK) ≫
        (PhilipponEtaleAcyclicCohomology.globalSections X).map (toPushforward a) ≫
          (globalSectionsIso a).hom.app (sheaf Y) := by
    dsimp only [d]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    change cX.homEquiv A _ (adj.homEquiv _ _ _) ≫ (globalSectionsIso a).hom.app _ = _
    rw [adj.homEquiv_naturality_left, structureComparison, Equiv.apply_symm_apply,
      cX.homEquiv_naturality_right, Category.assoc]
  have hy : d.homEquiv A (sheaf Y) ((pullbackConstantIso a).hom.app A ≫ inclusion s hp hE) =
      cY.homEquiv A (sheaf Y) (inclusion s hp hE) := by
    change d.homEquiv A _ ((d.leftAdjointUniq cY).hom.app A ≫ _) = _
    rw [d.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
      ← cY.homEquiv_unit]
  apply (d.homEquiv A (sheaf Y)).injective
  rw [hx, hy]
  apply AddCommGrpCat.ext
  intro x
  change ULift.{u} (ZMod p) at x
  let t : Γ(TX.left, ⊤) ⟶ Γ(((baseChange a).obj TX).left, ⊤) :=
    (pullback.fst TX.hom a).appTop
  change k.left.appTop (t (cX.homEquiv A (sheaf X) (inclusion r hp hK) x)) =
      cY.homEquiv A (sheaf Y) (inclusion s hp hE) x
  rw [homEquiv_inclusion_apply, homEquiv_inclusion_apply]
  have ht : t (scalar r TX (primeScalar hp hK x.down)) =
      scalar s ((baseChange a).obj TX) (φ (primeScalar hp hK x.down)) :=
    ConcreteCategory.congr_hom (scalar_baseChange a r s φ h TX) _
  have hk : scalar s ((baseChange a).obj TX) ≫ k.left.appTop = scalar s TY := by
    rw [scalar, scalar, Category.assoc, ← Scheme.Hom.comp_appTop, ← Category.assoc,
      MorphismProperty.Over.w k]
  have hc : φ (primeScalar hp hK x.down) = primeScalar hp hE x.down :=
    congrArg (fun g : ZMod p →+* E => g x.down) (RingHom.ext_zmod _ _ :
      φ.comp (primeScalar hp hK) = primeScalar hp hE)
  rw [ht, hc]
  exact ConcreteCategory.congr_hom hk _

/-- The canonical map on cohomology with coefficients in the additive sheaf. -/
def structureCohomologyComparison {X Y : Scheme.{u}} (a : Y ⟶ X) (q : ℕ) :
    (sheaf X).H q →+ (sheaf Y).H q :=
  (Sheaf.H.map (structureComparison a) q).comp (restrict a (sheaf X) q)

private theorem structureCohomologyComparison_natural {X Y : Scheme.{u}} (a : Y ⟶ X) (q : ℕ)
    (b : sheaf X ⟶ sheaf X) (c : sheaf Y ⟶ sheaf Y)
    (h : (pullbackSheaves a).map b ≫ structureComparison a = structureComparison a ≫ c)
    (x : (sheaf X).H q) :
    structureCohomologyComparison a q (Sheaf.H.map b q x) =
      Sheaf.H.map c q (structureCohomologyComparison a q x) := by
  let y := restrict a (sheaf X) q x
  have hy : restrict a (sheaf X) q (Sheaf.H.map b q x) =
      Sheaf.H.map ((pullbackSheaves a).map b) q y :=
    PhilipponExtComparison.comparison_post (pullbackSheaves a) _ b q x
  change Sheaf.H.map (structureComparison a) q (restrict a (sheaf X) q (Sheaf.H.map b q x)) =
    Sheaf.H.map c q (Sheaf.H.map (structureComparison a) q y)
  rw [hy, ← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, h]

/-- The additive-sheaf cohomology comparison is semilinear over the field map. -/
theorem structureCohomologyComparison_smul {K E : Type u} [Field K] [Field E]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (r : X ⟶ Spec (.of K)) (s : Y ⟶ Spec (.of E))
    (φ : K →+* E) (h : a ≫ r = s ≫ Spec.map (CommRingCat.ofHom φ)) (q : ℕ)
    (k : K) (x : (sheaf X).H q) :
    structureCohomologyComparison a q ((cohomologyModule r q).smul k x) =
      (cohomologyModule s q).smul (φ k) (structureCohomologyComparison a q x) :=
  structureCohomologyComparison_natural a q _ _ (structureComparison_mulScalar a r s φ h k) x

/-- The additive-sheaf cohomology comparison commutes with Frobenius. -/
theorem structureCohomologyComparison_frobenius {K E : Type u} [Field K] [Field E]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (r : X ⟶ Spec (.of K)) (s : Y ⟶ Spec (.of E))
    {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0) (hE : (p : E) = 0) (q : ℕ)
    (x : (sheaf X).H q) :
    structureCohomologyComparison a q (Sheaf.H.map (frobenius r hp hK) q x) =
      Sheaf.H.map (frobenius s hp hE) q (structureCohomologyComparison a q x) :=
  structureCohomologyComparison_natural a q _ _ (structureComparison_frobenius a r s hp hK hE) x


end PhilipponArtinSchreierBaseChange

end

end


