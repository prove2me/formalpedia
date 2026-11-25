-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LocalFramePowerSections
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_LocalFramePowerSections
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T16:07:34.793209+00:00
-- url     : https://prove2.me/theorems/733a90a6-cb8a-4867-a551-8c000ca0ad6c
-- title:
--   Local Frame Power Sections
-- statement:
--   Definitions and structural lemmas for Local Frame Power Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LocalFramePowerSections.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections
abbrev PowSec {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (N : ℕ) : Type :=
  LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (N : ℤ)))
def BasisAlong {X Y Y' : Scheme.{0}} (L : LB X) (N : ℕ) (φ : Y' ⟶ X) {r : ℕ} (s : Fin r → PowSec L φ N)
    {W : Type} [CommRing W] (p : Y ⟶ Sp W) (ψ : Y ⟶ Y') : Prop :=
  L.IsLB ∧ ∀ t : PowSec L (ψ ≫ φ) N, ∃! a : Fin r → W,
    ∀ (T : Scheme.{0}) (x : T ⟶ Y) (z : T) (J : (T ⟶ X) → L.ι), Good L z J →
      sval t x z J = ∑ k, gs x z ⊤ (Out.scal p (a k)) * sval (s k) (x ≫ ψ) z J
def IsTrait {R₁ W : Type} [CommRing R₁] [IsDomain R₁] [CommRing W] [IsDomain W] [IsLocalRing W] (ρ : R₁ →+* W)
    (κ : FractionRing R₁ →+* FractionRing W) : Prop :=
  GlobalTheory.UU.CDVR W ∧ κ.comp (algebraMap R₁ (FractionRing R₁)) = (algebraMap W (FractionRing W)).comp ρ
section Frames
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G)
def IsModelAt {W : Type} [CommRing W] [IsDomain W] (v₀ : Sp (FractionRing W) ⟶ S) (GW : Over (Sp W)) [GrpObj GW]
    [IsCommMonObj GW] (LW : RigLB GW) (φ : ((Over.pullback (Out.jK W)).obj GW).left ⟶ G.left)
    (w : LB.Iso (LW.L.pull (pullback.fst GW.hom (Out.jK W))) (L.L.pull φ)) : Prop :=
  IsSemiAbelian GW ∧ IsGrpPullback ((Over.pullback (Out.jK W)).obj GW) G v₀ φ ∧ w.IsGen ∧
    ∀ (T : Scheme.{0}) (τ : T ⟶ Sp (FractionRing W)) (x₀ : T ⟶ ((Over.pullback (Out.jK W)).obj GW).left),
      x₀ ≫ pullback.fst GW.hom (Out.jK W) = τ ≫ Out.jK W ≫ eSec GW → x₀ ≫ pullback.snd GW.hom (Out.jK W) = τ →
      ∀ (z : T) (JW : (T ⟶ GW.left) → LW.L.ι) (J : (T ⟶ G.left) → L.L.ι), Good LW.L z JW → Good L.L z J →
        val (L := L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) L.rig (τ ≫ v₀) z J =
          gw w x₀ z (J (x₀ ≫ φ)) (fun _ => JW (x₀ ≫ pullback.fst GW.hom (Out.jK W))) *
            val (L := LW.L) (φ := fun _ : PUnit => eSec GW) (ε := fun _ => 1) LW.rig (τ ≫ Out.jK W) z JW
def IsCombAt {K W : Type} [Field K] [CommRing W] [IsDomain W] (y : Sp K ⟶ S) (κ : K →+* FractionRing W) (N : ℕ) {r : ℕ}
    (s : Fin r → PowSec L.L (pullback.fst G.hom y) N) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (LW : RigLB GW)
    (φ : ((Over.pullback (Out.jK W)).obj GW).left ⟶ G.left)
    (w : LB.Iso (LW.L.pull (pullback.fst GW.hom (Out.jK W))) (L.L.pull φ))
    (σ : PowSec LW.L (𝟙 GW.left) N) (a : Fin r → W) : Prop :=
  ∀ (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (Out.jK W)).obj GW).left) (x' : T ⟶ pullback G.hom y),
    x' ≫ pullback.fst G.hom y = x ≫ φ → x' ≫ pullback.snd G.hom y = x ≫ pullback.snd GW.hom (Out.jK W) ≫ spMap κ →
    ∀ (z : T) (JW : (T ⟶ GW.left) → LW.L.ι) (J : (T ⟶ G.left) → L.L.ι), Good LW.L z JW → Good L.L z J →
      (gw w x z (J (x ≫ φ)) (fun _ => JW (x ≫ pullback.fst GW.hom (Out.jK W)))).val ^ N *
          sval σ (x ≫ pullback.fst GW.hom (Out.jK W)) z JW =
        ∑ k, gs (x ≫ pullback.fst GW.hom (Out.jK W)) z ⊤ (Out.scal GW.hom (a k)) * sval (s k) x' z J
def BasisAtTraits {R₁ : Type} [CommRing R₁] [IsDomain R₁] (y : Sp (FractionRing R₁) ⟶ S) (N : ℕ) {r : ℕ}
    (s : Fin r → PowSec L.L (pullback.fst G.hom y) N) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (ρ : R₁ →+* W) (κ : FractionRing R₁ →+* FractionRing W),
    IsTrait ρ κ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (LW : RigLB GW)
      (φ : ((Over.pullback (Out.jK W)).obj GW).left ⟶ G.left)
      (w : LB.Iso (LW.L.pull (pullback.fst GW.hom (Out.jK W))) (L.L.pull φ)),
      IsModelAt G L (spMap κ ≫ y) GW LW φ w →
        (∀ a : Fin r → W, ∃ σ, IsCombAt G L y κ N s GW LW φ w σ a) ∧
        ∀ σ, ∃! a : Fin r → W, IsCombAt G L y κ N s GW LW φ w σ a
def FramesAtTraits {R₁ : Type} [CommRing R₁] [IsDomain R₁] (y : Sp (FractionRing R₁) ⟶ S) (N : ℕ) {r : ℕ}
    (s : Fin r → PowSec L.L (pullback.fst G.hom y) N) : Prop :=
  CharZero R₁ ∧ Set.range y ⊆ abLocus G ∧
    BasisAlong L.L N (pullback.fst G.hom y) s (pullback.snd G.hom y) (𝟙 _) ∧ BasisAtTraits G L y N s
def LocalFrame (U : S.Opens) (N : ℕ) {r : ℕ} (s : Fin r → PowSec L.L (G.hom ⁻¹ᵁ U).ι N) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.UU.CDVR W → ∀ ξ : Sp W ⟶ S,
    Set.range (Out.jK W ≫ ξ) ⊆ abLocus G → ∀ ψ : pullback G.hom ξ ⟶ (G.hom ⁻¹ᵁ U).toScheme,
      ψ ≫ (G.hom ⁻¹ᵁ U).ι = pullback.fst G.hom ξ → BasisAlong L.L N (G.hom ⁻¹ᵁ U).ι s (pullback.snd G.hom ξ) ψ
def IsTransition (U V : S.Opens) (N : ℕ) {r : ℕ} (s : Fin r → PowSec L.L (G.hom ⁻¹ᵁ U).ι N)
    (s' : Fin r → PowSec L.L (G.hom ⁻¹ᵁ V).ι N) (M : Matrix (Fin r) (Fin r) Γ(S, U ⊓ V)) : Prop :=
  ∀ (T : Scheme.{0}) (x : T ⟶ (G.hom ⁻¹ᵁ U).toScheme) (x' : T ⟶ (G.hom ⁻¹ᵁ V).toScheme),
    x ≫ (G.hom ⁻¹ᵁ U).ι = x' ≫ (G.hom ⁻¹ᵁ V).ι → ∀ (z : T) (J : (T ⟶ G.left) → L.L.ι), Good L.L z J →
      ∀ k, sval (s k) x z J = ∑ l, gs (x ≫ (G.hom ⁻¹ᵁ U).ι ≫ G.hom) z (U ⊓ V) (M k l) * sval (s' l) x' z J
def detBundle {Ix : Type} (U : Ix → S.Opens) (a r : ℕ) (c d : ∀ i j, Γ(S, U i ⊓ U j)ˣ) : LB S :=
  ⟨Ix, U, fun i j => c i j ^ ((a : ℤ) * r + 1 - r) * d i j⟩
def IsAmpleFrames {O : Type} [CommRing O] (b : S ⟶ Sp O) (N a r : ℕ) {Ix : Type} (U : Ix → S.Opens)
    (θ : ∀ i, PowSec L.L (G.hom ⁻¹ᵁ U i).ι 1) (s : ∀ i, Fin r → PowSec L.L (G.hom ⁻¹ᵁ U i).ι N)
    (c : ∀ i j, Γ(S, U i ⊓ U j)ˣ) (M : ∀ i j, Matrix (Fin r) (Fin r) Γ(S, U i ⊓ U j))
    (d : ∀ i j, Γ(S, U i ⊓ U j)ˣ) : Prop :=
  (∀ i, LocalFrame G L (U i) 1 (fun _ : Fin 1 => θ i)) ∧ (∀ i, LocalFrame G L (U i) N (s i)) ∧
    (∀ i j, IsTransition G L (U i) (U j) 1 (fun _ : Fin 1 => θ i) (fun _ => θ j) (Matrix.of fun _ _ => (c i j).val)) ∧
    (∀ i j, IsTransition G L (U i) (U j) N (s i) (s j) (M i j)) ∧ (∀ i j, (d i j).val = (M i j).det) ∧
    (detBundle U a r c d).IsLB ∧ Out.RelAmple (Over.mk b) (detBundle U a r c d)
omit [IsCommMonObj G] [GrpObj G] in

def TraitDense : Prop :=
  IsReduced S ∧ ∀ V : S.Opens, (V : Set S).Nonempty → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W)
    (ξ : Sp W ⟶ S), GlobalTheory.UU.CDVR W ∧ Set.range ξ ⊆ V ∧ Set.range (Out.jK W ≫ ξ) ⊆ abLocus G
def HasAmpleFrames {O : Type} [CommRing O] (b : S ⟶ Sp O) (N r : ℕ) : Prop :=
  TraitDense G ∧ ∃ (a : ℕ) (Ix : Type) (U : Ix → S.Opens) (θ : ∀ i, PowSec L.L (G.hom ⁻¹ᵁ U i).ι 1)
    (s : ∀ i, Fin r → PowSec L.L (G.hom ⁻¹ᵁ U i).ι N) (c : ∀ i j, Γ(S, U i ⊓ U j)ˣ)
    (M : ∀ i j, Matrix (Fin r) (Fin r) Γ(S, U i ⊓ U j)) (d : ∀ i j, Γ(S, U i ⊓ U j)ˣ),
    1 ≤ a ∧ IsAmpleFrames G L b N a r U θ s c M d
end Frames
section Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  (Xo : Moduli D l) {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
def GoodRedAt {W : Type} [CommRing W] [IsDomain W] (v₀ : Sp (FractionRing W) ⟶ Xo.X) : Prop :=
  ∃ (t : SAB H (Sp W)) (t' : SAB H (Sp (FractionRing W))) (_ : SABMap t' t (Out.jK W)) (_ : SABMap t' Xo.univ.t v₀),
    IsProper t.G.hom
def ArcDataAt {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) {W : Type} [CommRing W]
    [IsDomain W] [IsLocalRing W] (f : O' →+* W) (u : W) (v₀ : Sp (FractionRing W) ⟶ Xo.X) : Prop :=
  ∃ (t : SAB H (Sp W)) (t' : SAB H (Sp (FractionRing W))) (m₁ : SABMap t' t (Out.jK W)) (m₂ : SABMap t' Xo.univ.t v₀)
    (P : PELUnif (IsLocalRing.maximalIdeal W) t) (φ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.D.toPre.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X),
    letI := H.starRing
    IsGrpPullback P.D.toPre.P.A a.D₀.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec P.D.toPre.P.A) (fun _ => 1)) P.D.toPre.rig
      (rigPullOf φ (spMap f) he a.D₀.P.L a.D₀.rig) ∧
    (∀ x, (P.oD.onB.act x).left ≫ φ = φ ≫ (a.oa.onB.act x).left) ∧
    (∀ y, (P.D.toPre.c (e y)).left ≫ φ = spMap f ≫ (a.D₀.c y).left) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing W) F] [Algebra (FractionRing O') F] (uF : F),
      (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing W) F (algebraMap W _ (f x))) →
      uF = algebraMap (FractionRing W) F (algebraMap W _ u) →
      (∀ y, GenRel w (LB.pullGen _ _ _ (P.D.toPre.psi (e y)) (Out.jFK (R := W) F))
        (LB.pullGen _ _ _ (a.D₀.psi y) (Out.jFK (R := O') F)) (uF ^ (a.be y y / 2))) ∧
      ∀ (k : ℕ) (p₀ : Out.QkPt a.D₀ (FractionRing O') k) (σ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G),
        ((k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Xo.univ.etaA v) ∨
          (k = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
            HEq p₀ (a.eta v) ∧ σ = Xo.univ.eta v)) →
        ∀ (q₀ : Out.QkPt a.D₀ F k) (q : Out.QkPt P.D.toPre F k) (x : Out.TFK (R := W) F ⟶ P.A.A)
          (x' : Sp F ⟶ t'.G.left), QkExt (algebraMap _ F) p₀ q₀ → q.y = e q₀.y →
          (∀ z, GenRel w (q.g.s (e z)) (q₀.g.s z) (uF ^ (a.be q₀.y z / k))) →
          x' ≫ m₁.φ = x.left ≫ P.U.gen.inv.left ≫ pullback.fst t.G.hom (Out.jK W) →
          x' ≫ m₂.φ = (spMap (algebraMap (FractionRing W) F) ≫ v₀) ≫ σ.left →
          P.ToA F k q x
def DataAtTraits {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'} (a : ArcIn D l β O' b) {R₁ : Type} [CommRing R₁]
    [IsDomain R₁] (f : PowerSeries O' →+* R₁) (y : Sp (FractionRing R₁) ⟶ Xo.XF c) : Prop :=
  CharZero R₁ ∧ Function.Injective (f.comp (PowerSeries.C (R := O'))) ∧ f PowerSeries.X ≠ 0 ∧
    y ≫ pullback.snd _ _ ≫ spMap β = Out.jK R₁ ≫ spMap f ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b ∧
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (ρ : R₁ →+* W) (κ : FractionRing R₁ →+* FractionRing W),
      IsTrait ρ κ →
      (¬ IsUnit (ρ (f PowerSeries.X)) →
        ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (i : W →+* W')
          (κ' : FractionRing R₁ →+* FractionRing W'), Function.Injective i ∧ i.Finite ∧ IsTrait (i.comp ρ) κ' ∧
          ArcDataAt Xo a (((i.comp ρ).comp f).comp (PowerSeries.C (R := O'))) (i (ρ (f PowerSeries.X)))
            (spMap κ' ≫ y ≫ pullback.fst _ _)) ∧
      (IsUnit (ρ (f PowerSeries.X)) → GoodRedAt Xo (spMap κ ≫ y ≫ pullback.fst _ _))
end Data
example (p : ℕ) [Fact p.Prime] : IsTrait (RingHom.id ℤ_[p]) (RingHom.id _) :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩, rfl⟩
example {R₁ W : Type} [CommRing R₁] [IsDomain R₁] [CommRing W] [IsDomain W] [IsLocalRing W] {ρ : R₁ →+* W} {κ}
    (h : IsTrait ρ κ) : Function.Injective ρ := by
  have : Function.Injective ((algebraMap W (FractionRing W)).comp ρ) := by
    rw [← h.2]; exact κ.injective.comp (IsFractionRing.injective R₁ _)
  exact Function.Injective.of_comp (f := algebraMap W (FractionRing W)) this
end GlobalTheory.IndefiniteRowSideFullHecke.LocalFramePowerSections
end


