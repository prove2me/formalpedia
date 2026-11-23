-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
-- name    : Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:25:23.768852+00:00
-- url     : https://prove2.me/theorems/cea712c8-5356-4cda-8f3c-eba320264b2a
-- title:
--   Is Square Determinant Comparison
-- statement:
--   Definitions and structural lemmas for Is Square Determinant Comparison, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/KeyFormula/IsSquareDeterminantComparison.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.KeyKa
variable {R : Type} [CommRing R]
abbrev RR (x : KeyIn R) (l : ℕ) : Type := LB.Sec (pw x.P.L (l : ℤ))
def Coords (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) (c : Fin N → R) (f : ∀ i, Γ(x.P.A.left, x.P.L.U i)) : Prop :=
  ∀ i, f i = ∑ k, cst x.P.A.hom (x.P.L.U i) (c k) * (show Γ(x.P.A.left, x.P.L.U i) from (b k).f i)
def IsBasis (x : KeyIn R) {l N : ℕ} (b : Fin N → RR x l) : Prop := ∀ s : RR x l, ∃! c, Coords x b c s.f
def SecVia {R' : Type} [CommRing R'] (x' : KeyIn R') (x : KeyIn R) (φ : x'.P.A.left ⟶ x.P.A.left)
    (w : LB.Iso x'.P.L (x.P.L.pull φ)) {l : ℕ} (s' : RR x' l) (s : RR x l) : Prop :=
  ∀ (j : (x.P.L.pull φ).ι) (i : x'.P.L.ι) (h : (x.P.L.pull φ).U j ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U (j PUnit.unit)),
    (φ.appLE _ _ h).hom (s.f (j PUnit.unit)) =
      (show Γ(x'.P.A.left, (x.P.L.pull φ).U j ⊓ x'.P.L.U i) from (w.s (j, i)).val) ^ l * resG _ inf_le_right (s'.f i)
def KeyVia {R' : Type} [CommRing R'] (x' : KeyIn R') (x : KeyIn R) (f : R →+* R') (φ : x'.P.A.left ⟶ x.P.A.left)
    (w : LB.Iso x'.P.L (x.P.L.pull φ)) : Prop :=
  ∃ (he : eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A) (hg : x'.P.g = x.P.g) (F : DualNumber R →+* DualNumber R'),
    IsGrpPullback x'.P.A x.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x'.P.A) (fun _ => 1)) x'.rig
      (rigPullOf φ (spMap f) he x.P.L x.rig) ∧
    (∀ (j : (x.P.L.pull φ).ι) (i : x'.P.L.ι)
      (h : (x.P.L.pull φ).U j ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (x.th.f (j PUnit.unit)) =
        (show Γ(x'.P.A.left, (x.P.L.pull φ).U j ⊓ x'.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x'.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x'.v i).left ≫ φ = spMap F ≫ (x.v (i.cast hg)).left
open Classical in

def valT {T : Type} [CommRing T] {X : Scheme.{0}} (w : Sp T ⟶ X) (U : X.Opens) (f : Γ(X, U)) : T :=
  if h : ⊤ ≤ w ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom ((w.appLE U ⊤ h).hom f) else 0
abbrev Pt (x : KeyIn R) : Type := 𝟙_ (Over (Sp R)) ⟶ x.P.A
def jac (x : KeyIn R) {n : ℕ} (s : Fin x.P.g → RR x n) (z : Pt x) (c : x.P.L.ι) : R :=
  (Matrix.of fun i k => TrivSqZeroExt.snd
    (valT (T := DualNumber R) ((toUnit (epsR R) ≫ z) * x.v k).left (x.P.L.U c) ((s i).f c))).det
def FinZ (x : KeyIn R) {n r : ℕ} (s : Fin r → RR x n) : Prop :=
  Set.Finite {y : x.P.A.left | ∀ i, y ∉ Out.nonzeroLocus (s i)}
def IsMul (x : KeyIn R) {n : ℕ} (l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n))
    (m : Fin x.P.g → ∀ j j', Matrix (Fin ((l - j * n) ^ x.P.g)) (Fin ((l - j' * n) ^ x.P.g)) R) : Prop :=
  ∀ i j, j < x.P.g → ∀ k, Coords x (b j) (fun k' => m i j (j + 1) k' k)
    (fun c => (show Γ(x.P.A.left, x.P.L.U c) from (s i).f c) * (show Γ(x.P.A.left, x.P.L.U c) from (b (j + 1) k).f c))
def KosVal (x : KeyIn R) {n d : ℕ} (l : ℕ) (s : Fin x.P.g → RR x n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι)
    (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (t : R) : Prop :=
  ∃ m, IsMul x l s b m ∧ TorsSq kdeg
    (kosD (N := fun j => (l - j * n) ^ x.P.g) m
      (fun j => Matrix.of fun a k => valT (T := R) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))) t
def alMap (x : KeyIn R) (al : Matrix (Fin 4) (Fin 4) ℤ) (r : Fin 4) (ξ : Pt x) : Out.powObj x.P.A 4 ⟶ x.P.A :=
  (List.ofFn fun c : Fin 4 => Out.powPr x.P.A c ^ al r c).prod * (toUnit _ ≫ ξ)
def IsSquareDeterminantComparison (x : KeyIn R) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (b : Fin (m ^ x.P.g) → RR x m) (lam : Rˣ) : Prop :=
  ∃ (ξ : (Fin 4 → Fin (m ^ x.P.g)) → Fin 4 → Pt x)
    (mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]))
    (w : ∀ I, LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4)
      (Sum.elim (fun r => (alMap x al r (ξ I r)).left) (fun c => (Out.powPr x.P.A c).left))
      (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))))
    (Q : Matrix (Fin 4 → Fin (m ^ x.P.g)) (Fin 4 → Fin (m ^ x.P.g)) R) (rho : (Fin 4 → Fin (m ^ x.P.g)) → Rˣ),
    (∀ I I', I ≠ I' → ∀ p : Sp R, ∃ r, (ξ I r).left p ≠ (ξ I' r).left p) ∧
    (∀ I c, (List.ofFn fun r : Fin 4 => ξ I r ^ al r c).prod = 1) ∧
    mu.IsGen ∧ (∀ I, (w I).IsGen) ∧
    (∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J →
      val mu (eSec x.P.A) p J = val x.rig (𝟙 _) p J ^ (1 - (m : ℤ) ^ 2) ∧
      ∀ I, (val (w I) (eSec (Out.powObj x.P.A 4)) p J ^ (m ^ 2) * ∏ r, val mu (ξ I r).left p J).val =
        gs (𝟙_ (Over (Sp R))).hom p ⊤ (cst (𝟙 (Sp R)) ⊤ (rho I)) * (val x.rig (𝟙 _) p J ^ (4 - 4 * (m : ℤ) ^ 3)).val) ∧
    (∀ I (y : (Out.powObj x.P.A 4).left) J, Good x.P.L y J →
      ∏ r, gs (alMap x al r (ξ I r)).left y _ (x.th.f (J (alMap x al r (ξ I r)).left)) =
        (val (w I) (𝟙 _) y J).val * ∑ I', gs (𝟙 _) y ⊤ (cst (Out.powObj x.P.A 4).hom ⊤ (Q I I')) *
          ∏ c, gs (Out.powPr x.P.A c).left y (x.P.L.U (J (Out.powPr x.P.A c).left)) ((b (I' c)).f (J (Out.powPr x.P.A c).left))) ∧
    (lam : R) = Q.det ^ (2 * m ^ 2) * ∏ I, (rho I : R) ^ 2
def EtZ (x : KeyIn R) {n d : ℕ} (s : Fin x.P.g → RR x n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι) : Prop :=
  (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) ∧
  (∀ a i, valT (T := R) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) ∧
  (∀ a, IsUnit (jac x s (z a) (ch a))) ∧
  (∀ a a', a ≠ a' → ∀ p : Sp R, (z a).left p ≠ (z a').left p) ∧
  ∀ y : x.P.A.left, (∀ i, y ∉ Out.nonzeroLocus (s i)) → ∃ a, ∃ p : Sp R, (z a).left p = y
def admitted (g n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) : Prop :=
  4 ≤ n ∧ g * n < l ∧ l < l' ∧ ∀ m, (al m).transpose * al m = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)
def KaVal (x : KeyIn R) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin x.P.g → RR x n) (κ : Rˣ) : Prop :=
  ∃ (z : Fin (x.P.g.factorial * n ^ x.P.g) → Pt x) (ch : _) (b : _) (b' : _) (t t' J : Rˣ) (lam lam' : ℕ → Rˣ),
    EtZ x s z ch ∧ (J : R) = ∏ a, jac x s (z a) (ch a) ∧
    (∀ j ≤ x.P.g, IsBasis x (b j) ∧ IsSquareDeterminantComparison x (l - j * n) (al (l - j * n)) (b j) (lam j)) ∧
    (∀ j ≤ x.P.g, IsBasis x (b' j) ∧ IsSquareDeterminantComparison x (l' - j * n) (al (l' - j * n)) (b' j) (lam' j)) ∧
    KosVal x l s z ch b t ∧ KosVal x l' s z ch b' t' ∧ κ = kaForm x.P.g n l l' t t' lam lam' J
end GlobalTheory.KeyKa
end


