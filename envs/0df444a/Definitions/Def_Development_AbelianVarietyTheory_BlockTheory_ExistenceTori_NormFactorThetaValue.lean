-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_NormFactorThetaValue
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_NormFactorThetaValue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:16.526269+00:00
-- url     : https://prove2.me/theorems/9c2267ad-6a7e-4ab7-8434-79c1c36acaf8
-- title:
--   Norm Factor Theta Value
-- statement:
--   Definitions and structural lemmas for Norm Factor Theta Value, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/NormFactorThetaValue.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
attribute [local instance] Over.cartesianMonoidalCategory
section TwoLifts
variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)
def IsTwoLifts (N : ℕ) {T : Over X} (s : LB.Sec (LPow A L.L 1 T)) (x₁ x₂ : T ⟶ A)
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  Odd N ∧ x₁ ^ (N ^ 2) = 1 ∧ x₂ ^ (N ^ 2) = 1 ∧
  ∃ (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1]))
    (s₁ s₂ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) (U₁ U₂ : ThetaGrp A L.L ((N : ℤ) ^ 2) T),
    α₀.IsGen ∧ IsNormMul A L.L L.rig N α₀ ∧ α.IsGen ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ ∧
    SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) x₁ U₁ ∧ IsActOf A L.L ((N : ℤ) ^ 2) U₁ s₁ s₂ ∧
    SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) x₂ U₂ ∧ IsActOf A L.L ((N : ℤ) ^ 2) U₂ s₂ F
end TwoLifts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
def InKer {n : ℕ} (N : ℕ) (Lm : Submodule (𝓞 E) (Fin n → E))
    (hN : ∀ j, N • (Pi.single j 1 : Fin n → E) ∈ Lm) {T : Over Xo.X} (a : Fin n → (T ⟶ Xo.univ.t.G)) : Prop :=
  (∀ j, a j ^ (N ^ 2) = 1) ∧
    ∀ (f : Lm →ₗ[𝓞 E] (Fin n → 𝓞 E)) (i : Fin n), ∏ j, a j ≫ Xo.univ.t.act.act (f ⟨_, hN j⟩ i) = 1
omit [NumberField E] [IsCMField E] in
theorem nsmul_single_mem_inter {n M N : ℕ} {Λ : Lat E n} (h : Λ.Admissible M N) (j : Fin n) :
    N • (Pi.single j 1 : Fin n → E) ∈ Λ.inter := by
  refine h.2.2 ?_
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (single_mem_stdMod j)
omit [NumberField E] [IsCMField E] in
theorem nsmul_single_mem {n M N : ℕ} {Λ : Lat E n} (h : Λ.Admissible M N) (j : Fin n) :
    N • (Pi.single j 1 : Fin n → E) ∈ Λ.L := (nsmul_single_mem_inter h j).2
def InZ {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {T : Over Xo.X} (a : Fin n → (T ⟶ Xo.univ.t.G)) : Prop :=
  InKer Xo N Λ.L (nsmul_single_mem h) a
def InKernelOfAdmissibleLattice {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {T : Over Xo.X} (a : Fin n → (T ⟶ Xo.univ.t.G)) : Prop :=
  InKer Xo N Λ.inter (nsmul_single_mem_inter h) a
def ptRes {S k : Type} [CommRing S] [CommRing k] (x0 : Sp S ⟶ Xo.X) (ψ : S →+* k) :
    ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap ψ) rfl
def SplitsZ {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    {J : Type} (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) : Prop :=
  (∀ i, InZ Xo h (z i)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : S →+* k) (a : Fin n → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G)),
      InZ Xo h a → ∃! i, ∀ j, a j = ptRes Xo x0 ψ ≫ z i j
def IsDivPt (N : ℕ) {T : Over Xo.X} (t t' : T ⟶ Xo.univ.t.G) : Prop :=
  t' ^ N = t ∧ KilledBy Xo (halfPart l N ^ 2) t'
def pairBox (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ} (k : ℤ)
    (P : MvPolynomial (LtN Dw n) c.F) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y k (F b) (colOf m b)
def normFactor {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (P : MvPolynomial (LtN Dw n) c.F) : c.F :=
  β⁻¹ * ((Λ.cardCenterZero (Dw.p + Dw.q) N : ℕ) : c.F)⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹
def SplitVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n N : ℕ} {Λ : Lat E n}
    (h : Λ.Admissible l.M N) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F)
    (v : S) : Prop :=
  ∃ (r : ℕ) (z : Fin r → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (t' : (Fin n → NamedCl Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → NamedCl Dw l) → Fin r → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))),
    SplitsZ Xo h y.x z ∧
    (∀ t b, IsDivPt Xo N (levPtCl Xo y.x (t b)) (t' t b)) ∧
    (∀ t i b, IsTwoLifts Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (t' t b) (F t i b)) ∧
    v = algebraMap c.F S (normFactor c Λ N β P) *
      ∑ t ∈ levelIndex Dw l n, algebraMap c.F S (cf t) * ∑ i, pairBox Xo c nab y ((N : ℤ) ^ 2) P (F t i)
def LocVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n N : ℕ} {Λ : Lat E n}
    (h : Λ.Admissible l.M N) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F)
    (v : S) : Prop :=
  ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S'),
    φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ SplitVal Xo c nab y' h β cf P (φ v)
def InRange {n : ℕ} (Λ : Lat E n) (β : c.F) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Λ.InGenus ∧ Λ.StdAt l.M ∧ β ≠ 0 ∧ P ∈ harmLat Dw c a Λ
def ThVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ} (Λ : Lat E n)
    (N : ℕ) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (v : S) : Prop :=
  InRange c Λ β a P ∧ ∃ h : Λ.Admissible l.M N, LocVal Xo c nab y h β cf P v
def ThValFun (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ} (Λ : Lat E n)
    (N : ℕ) (β : c.F) (φ : (Fin n → ConjCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (v : S) : Prop :=
  ThVal Xo c nab y Λ N β (fourier c φ) a P v
def ThValPt (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ} (Λ : Lat E n)
    (N : ℕ) (β : c.F) (t : Fin n → NamedCl Dw l) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (v : S) : Prop :=
  ThVal Xo c nab y Λ N β (Set.indicator {t} 1) a P v
def KerClaims : Prop :=
  ∀ (n N : ℕ) (Λ : Lat E n) (h : Λ.Admissible l.M N), Λ.InGenus → Λ.StdAt l.M →
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (x0 : Sp k ⟶ Xo.X), x0 ≫ Xo.s = sOf c k →
      (∀ a : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), InKernelOfAdmissibleLattice Xo h a → InZ Xo h a ∧ ∀ j, a j ^ N = 1) ∧
      (∀ a : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ j, KilledBy Xo (halfPart l N) (a j)) → InZ Xo h a) ∧
      Nat.card {a : Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G) // InKernelOfAdmissibleLattice Xo h a} = Λ.cardCenterZero (Dw.p + Dw.q) N
def ValTot (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n N : ℕ) (Λ : Lat E n) (β : c.F)
    (cf : (Fin n → NamedCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F),
    InRange c Λ β a P → Λ.Admissible l.M N → ∃! v, ThVal Xo c nab y Λ N β cf a P v
def FreeOfN (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n N N' : ℕ) (Λ : Lat E n) (β : c.F)
    (cf : (Fin n → NamedCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (v : S),
    Λ.Admissible l.M N' → ThVal Xo c nab y Λ N β cf a P v → ThVal Xo c nab y Λ N' β cf a P v
def StdAgrees (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n : ℕ) (x : Fin n → Dw.La)
    (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (v : S), P ∈ harmLat Dw c a (Lat.std E n) →
    (ThValPt Xo c nab y (Lat.std E n) l.M 1 (fun b => Submodule.Quotient.mk (x b)) a P v ↔
      ThValAt Xo c nab y x P v)
def SumOfTranslates (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n N : ℕ) (Λ : Lat E n) (β : c.F)
    (cf : (Fin n → NamedCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (w : (Fin n → NamedCl Dw l) → S), (∀ t, ThValPt Xo c nab y Λ N β t a P (w t)) →
    ThVal Xo c nab y Λ N β cf a P (∑ t ∈ levelIndex Dw l n, algebraMap c.F S (cf t) * w t)
def IsSection (nab : NabV Xo c) : Prop :=
  ∀ (n N : ℕ) (Λ : Lat E n) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c),
    (∀ (p : TRing c.F) (y : FrPt Xo c p.R), ThVal Xo c nab y Λ N β cf a P (f p y)) → f ∈ sec Xo c a n
def IsBlockSum {n₁ n₂ : ℕ} (Λ₁ : Lat E n₁) (Λ₂ : Lat E n₂) (Λ : Lat E (n₁ + n₂)) : Prop :=
  ∀ x, x ∈ Λ.L ↔ (fun b => x (Fin.castAdd n₂ b)) ∈ Λ₁.L ∧ (fun b => x (Fin.natAdd n₁ b)) ∈ Λ₂.L
def blockMul {n₁ n₂ : ℕ} (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F) :
    MvPolynomial (LtN Dw (n₁ + n₂)) c.F :=
  MvPolynomial.rename (fun ℓ : LtN Dw n₁ => (⟨ℓ.1, ℓ.2.1, Fin.castAdd n₂ ℓ.2.2⟩ : LtN Dw (n₁ + n₂))) P₁ *
    MvPolynomial.rename (fun ℓ : LtN Dw n₂ => (⟨ℓ.1, ℓ.2.1, Fin.natAdd n₁ ℓ.2.2⟩ : LtN Dw (n₁ + n₂))) P₂
def blockFun {X : Type} {n₁ n₂ : ℕ} (φ₁ : (Fin n₁ → X) → c.F) (φ₂ : (Fin n₂ → X) → c.F) :
    (Fin (n₁ + n₂) → X) → c.F :=
  fun x => φ₁ (fun b => x (Fin.castAdd n₂ b)) * φ₂ fun b => x (Fin.natAdd n₁ b)
def ProductClaim (nab : NabV Xo c) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (n₁ n₂ N : ℕ) (Λ₁ : Lat E n₁) (Λ₂ : Lat E n₂)
    (Λ : Lat E (n₁ + n₂)) (φ₁ : (Fin n₁ → ConjCl Dw l) → c.F) (φ₂ : (Fin n₂ → ConjCl Dw l) → c.F)
    (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ) (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F) (v₁ v₂ : S),
    IsBlockSum Λ₁ Λ₂ Λ → ThValFun Xo c nab y Λ₁ N 1 φ₁ a₁ P₁ v₁ → ThValFun Xo c nab y Λ₂ N 1 φ₂ a₂ P₂ v₂ →
      ThValFun Xo c nab y Λ N 1 (blockFun c φ₁ φ₂) (a₁ + a₂) (blockMul c P₁ P₂) (v₁ * v₂)
end GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue


