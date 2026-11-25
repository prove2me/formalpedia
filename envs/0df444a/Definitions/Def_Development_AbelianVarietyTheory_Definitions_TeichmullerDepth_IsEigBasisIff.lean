-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
-- name    : Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T17:24:47.729311+00:00
-- url     : https://prove2.me/theorems/b541a70c-9535-5c9c-8908-425394da7d43
-- title:
--   Is Eig Basis Iff
-- statement:
--   Definitions and structural lemmas for Is Eig Basis Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TeichmullerDepth/IsEigBasisIff.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
section Series
variable {R : Type} [CommRing R] {m n d e r g : ℕ}
def sub (a : Fin m → Fin d → PS R n e) (f : PS R m d) : PS R n e :=
  MvPowerSeries.subst (fun q : Fin m × Fin d => a q.1 q.2) f
def IsHomF (F : Fin d → PS R 2 d) (F' : Fin e → PS R 2 e) (φ : Fin e → PS R 1 d) : Prop :=
  (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) ∧ ∀ j, ev (n := 2) ![F] (φ j) =
    sub ![fun i => ev (n := 2) ![pt R d 0] (φ i), fun i => ev (n := 2) ![pt R d 1] (φ i)] (F' j)
def lin (φ : Fin e → PS R 1 d) : Matrix (Fin e) (Fin d) R :=
  Matrix.of fun i j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i)
def gmF (R : Type) [CommRing R] (r : ℕ) : Fin r → PS R 2 r :=
  fun i => MvPowerSeries.X (0, i) + MvPowerSeries.X (1, i) + MvPowerSeries.X (0, i) * MvPowerSeries.X (1, i)
def nv {S : Type} [CommRing S] (s : R →+* S) (f : PS R n d) (a : Fin n → Fin d → S) : S :=
  letI := s.toAlgebra
  nEval f (fun q : Fin n × Fin d => a q.1 q.2)
def SplitEx (A : Matrix (Fin d) (Fin r) R) (B : Matrix (Fin g) (Fin d) R) : Prop :=
  B * A = 0 ∧ ∃ (A' : Matrix (Fin r) (Fin d) R) (B' : Matrix (Fin d) (Fin g) R),
    A' * A = 1 ∧ B * B' = 1 ∧ A * A' + B' * B = 1
structure ExtSer (F : Fin d → PS R 2 d) (FB : Fin g → PS R 2 g) (I : Fin d → PS R 1 r)
    (Q : Fin g → PS R 1 d) : Prop where
  homI : IsHomF (gmF R r) F I
  homQ : IsHomF F FB Q
  exact : SplitEx (lin I) (lin Q)
def IsSum (F : Fin d → PS R 2 d) (φ φ' ψ : PS R 1 d →ₐ[R] R) : Prop :=
  ∃ Φ : PS R 2 d →ₐ[R] R, (∀ f, Φ (ev (n := 2) ![pt R d 0] f) = φ f) ∧
    (∀ f, Φ (ev (n := 2) ![pt R d 1] f) = φ' f) ∧ ∀ f, Φ (ev (n := 2) ![F] f) = ψ f
def Killed (F : Fin d → PS R 2 d) (N : ℕ) (φ : PS R 1 d →ₐ[R] R) : Prop := ∀ j, φ (mulF F N j) = 0
def Tors (p : ℕ) (F : Fin d → PS R 2 d) (φ : PS R 1 d →ₐ[R] R) : Prop := ∃ k, Killed F (p ^ k) φ
def FH (p : ℕ) (F : Fin d → PS R 2 d) : Prop :=
  ∀ k : ℕ, Module.Free R (QF F (p ^ k)) ∧ Module.Finite R (QF F (p ^ k)) ∧
    ∀ q : QF F (p ^ k), (∀ φ : QF F (p ^ k) →ₐ[R] R, φ q = 0) → q = 0
end Series
section Charts
variable {R : Type} [CommRing R] {d e : ℕ}
abbrev Fam (G : Over (Spec (CommRingCat.of R))) (d : ℕ) : Type 1 :=
  ∀ (S : Type) [CommRing S] [Algebra R S], (Fin d → S) → (sp (R₀ := R) S ⟶ G)
structure NilChart (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (F : Fin d → PS R 2 d) (X : Fam G d) : Prop where
  zero : ∀ (S : Type) [CommRing S] [Algebra R S], X S 0 = 1
  nat : ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S')
    (a : Fin d → S), (∀ i, IsNilpotent (a i)) → spMap φ ≫ X S a = X S' (fun i => φ (a i))
  inj : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin d → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → X S a = X S b → a = b
  surj : ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (ρ : S →ₐ[R] S')
    (σ : S' →ₐ[R] S), ρ.comp σ = AlgHom.id R S' → IsNilpotent (RingHom.ker ρ) →
    ∀ z : sp (R₀ := R) S ⟶ G, spMap ρ ≫ z = 1 → ∃ a : Fin d → S, (∀ i, ρ (a i) = 0) ∧ z = X S a
  law : ∀ (S : Type) [CommRing S] [Algebra R S] (a b : Fin d → S), (∀ i, IsNilpotent (a i)) →
    (∀ i, IsNilpotent (b i)) → X S a * X S b = X S (fun k => nv (algebraMap R S) (F k) ![a, b])
def Reads {G G' : Over (Spec (CommRingCat.of R))} (X : Fam G d) (X' : Fam G' e) (f : G ⟶ G')
    (φ : Fin e → PS R 1 d) : Prop :=
  (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) ∧
    ∀ (S : Type) [CommRing S] [Algebra R S] (a : Fin d → S), (∀ i, IsNilpotent (a i)) →
      X S a ≫ f = X' S (fun j => nv (algebraMap R S) (φ j) ![a])
def Kills (I : Ideal R) (k : ℕ) (S : Type) [CommRing S] [Algebra R S] : Prop :=
  ∀ t ∈ I ^ (k + 1), algebraMap R S t = 0
structure PtExt (I : Ideal R) (G B : Over (Spec (CommRingCat.of R))) [GrpObj G] [GrpObj B]
    (X : Type) [AddCommGroup X] where
  q : ∀ (S : Type) [CommRing S] [Algebra R S], (∃ k, Kills I k S) → (sp (R₀ := R) S ⟶ G) →* (sp (R₀ := R) S ⟶ B)
  i : ∀ (S : Type) [CommRing S] [Algebra R S], (∃ k, Kills I k S) → (Multiplicative X →* Sˣ) →* (sp (R₀ := R) S ⟶ G)
  q_nat : ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') h h' z,
    q S' h' (spMap φ ≫ z) = spMap φ ≫ q S h z
  i_nat : ∀ (S : Type) [CommRing S] [Algebra R S] (S' : Type) [CommRing S'] [Algebra R S'] (φ : S →ₐ[R] S') h h' χ,
    i S' h' ((Units.map (φ : S →* S')).comp χ) = spMap φ ≫ i S h χ
  i_inj : ∀ (S : Type) [CommRing S] [Algebra R S] h, Function.Injective (i S h)
  exact : ∀ (S : Type) [CommRing S] [Algebra R S] h z, q S h z = 1 ↔ ∃ χ, i S h χ = z
  lift : ∀ (S : Type) [CommRing S] [Algebra R S] h (S' : Type) [CommRing S'] [Algebra R S'] (ρ : S →ₐ[R] S')
    (σ : S' →ₐ[R] S), ρ.comp σ = AlgHom.id R S' → RingHom.ker ρ ^ 2 = ⊥ →
    ∀ y : sp (R₀ := R) S ⟶ B, spMap ρ ≫ y = 1 → ∃ z, spMap ρ ≫ z = 1 ∧ q S h z = y
variable [IsDomain R] {I : Ideal R} {D : Out.DegPre R} {k : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G]
def QRel (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S] (z : sp (R₀ := R) S ⟶ G)
    (y : sp (R₀ := R) S ⟶ D.P.A) : Prop :=
  ∃ w : Spec (CommRingCat.of S) ⟶ (Out.thickObj R I k G).left,
    w ≫ (Out.fstG I k G).left = z.left ∧ w ≫ c.pG.left = y.left
def IRel (c : Out.GtCoord I D k G) (S : Type) [CommRing S] [Algebra R S] (χ : Multiplicative D.X →* Sˣ)
    (z : sp (R₀ := R) S ⟶ G) : Prop :=
  ∃ w : Spec (CommRingCat.of S) ⟶ (splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X).left,
    (∀ x : D.X, (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
      (w.appTop.hom (charUnit (Spec (CommRingCat.of (R ⧸ I ^ (k + 1)))) D.X x).val) =
        (χ (Multiplicative.ofAdd x) : S)) ∧
    w ≫ c.i.left ≫ (Out.fstG I k G).left = z.left
end Charts
section OnBX
variable {R₀ : Type} [CommRing R₀] {g : ℕ}
structure BXChart (B : BX R₀) (O : LAlg R₀) (F : Fin g → PS (O : Type) 2 g)
    (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R) : Prop where
  zero : ∀ (R : LAlg R₀) s, Y R s 0 = 0
  nat : ∀ (R R' : LAlg R₀) (s : LHom O R) (f : LHom R R') (a : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) →
    B.map f (Y R s a) = Y R' (f.comp s) (fun i => f.1 (a i))
  inj : ∀ (R : LAlg R₀) s (a b : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) →
    Y R s a = Y R s b → a = b
  surj : ∀ (R S : LAlg R₀) (s : LHom O R) (π : LHom R S) (σ : LHom S R), π.comp σ = LHom.id S →
    σ.comp (π.comp s) = s → π.SqZero → ∀ x : B.G R, B.map π x = 0 →
    ∃ a : Fin g → (R : Type), (∀ i, π.1 (a i) = 0) ∧ x = Y R s a
  law : ∀ (R : LAlg R₀) s (a b : Fin g → (R : Type)), (∀ i, IsNilpotent (a i)) → (∀ i, IsNilpotent (b i)) →
    Y R s a + Y R s b = Y R s (fun k => nv s.1.toRingHom (F k) ![a, b])
def TanMat (B : BX R₀) (O : LAlg R₀) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R)
    (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (O : Type)) : Prop :=
  ∀ (R R' : LAlg R₀) (s : LHom O R) (π : LHom R R') (hπ : π.SqZero) (l : Fin g) (i : π.ker),
    B.tg π hπ (gb l ⊗ₜ[R₀] i) = Y R s (fun k => s.1 (S k l) * (i : (R : Type)))
def PairSer (B : BX R₀) (O : LAlg R₀) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R) (p : ℕ)
    (τ : ℕ → B.G O) (u : PS (O : Type) 1 g) : Prop :=
  ∀ (R : LAlg R₀) (s : LHom O R) (a : Fin g → (R : Type)) (n : ℕ) (z : (R : Type)ˣ), IsNilpotent (p : (R : Type)) →
    (∀ i, IsNilpotent (a i)) → B.IsPairing (p ^ (n + 1)) (Y R s a) (B.map s (τ n)) z →
    (z : (R : Type)) = nv s.1.toRingHom u ![a]
end OnBX
section Linear
def cjZ (OE : Type) [CommRing OE] [StarRing OE] : OE ≃ₐ[ℤ] OE :=
  AlgEquiv.ofRingEquiv (f := ((starRingAut : RingAut OE) : OE ≃+* OE)) (fun x => by simp)
abbrev sigE (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [StarRing OE] :
    (ℤ_[p] ⊗[ℤ] OE) ≃ₐ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] OE) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : ℤ_[p] ≃ₐ[ℤ_[p]] ℤ_[p]) (cjZ OE)
def EigB {O OE : Type} [CommRing O] [CommRing OE] {d s : ℕ} (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* O)
    (w : Fin s → Fin d → O) : Prop :=
  (∀ i a, (ρ a).mulVec (w i) = τ a • w i) ∧
    ∀ v : Fin d → O, (∀ a, (ρ a).mulVec v = τ a • v) → ∃! c : Fin s → O, ∑ i, c i • w i = v
def eigDim (C : Type) [Field C] {O OE κ : Type} [CommRing O] [Algebra O C] [CommRing OE] [Fintype κ] [DecidableEq κ]
    (ρ : OE → Matrix κ κ O) (τ : OE →+* C) : ℕ :=
  Module.finrank C ↥(⨅ a : OE, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C))) (τ a))
structure LinDat {p : ℕ} [Fact p.Prime] {g d r m : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] [Algebra ℤ_[p] O] {OE : Type} [CommRing OE] [StarRing OE] {cp : O}
    (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O)
    (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O) : Prop where
  noPad : H.P = 0 ∧ H.PL = 0
  exact : SplitEx A B
  eqB : ∀ a, B * ρG a = H.ρL (1 ⊗ₜ[ℤ] a) * B
  eqA : ∀ a, ρG a * A = A * (N a).map (Int.castRingHom O)
  fromB : ∀ i, ∃ k, s k = Bᵀ *ᵥ (fun l => H.Ht l i)
  fromT : ∀ i, ∃ k, Aᵀ *ᵥ s k = Pi.single i 1
end Linear
end GlobalTheory.ChF


