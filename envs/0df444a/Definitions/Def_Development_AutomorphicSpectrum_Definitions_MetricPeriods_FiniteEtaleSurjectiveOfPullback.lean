-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
-- name    : Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T09:08:18.738841+00:00
-- url     : https://prove2.me/theorems/76f80c9d-cc52-4028-9cc6-5e1e8e24692f
-- title:
--   Finite Etale Surjective Of Pullback
-- statement:
--   Definitions and structural lemmas for Finite Etale Surjective Of Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/MetricPeriods/FiniteEtaleSurjectiveOfPullback.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_IsPeriodOn
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_ExistsCoordsAtOfCoordTie
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_LatRestrictComapSpan
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
section Point
variable {Z : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
def InBlockChart (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (x : (Σ k, J k) → Ω) (c : ∀ k, J k) (q : Cpt ξ) : Prop :=
  ∀ k, InChart ξ (fun i => x ⟨k, i⟩) (c k) q
def ptIdeal (ξ : Spec (CommRingCat.of Ω) ⟶ Z) (x : (Σ k, J k) → Ω) (q : Cpt ξ) : Ideal (MRing J) :=
  Ideal.span {g | ∃ d : K → ℕ, IsMultiHomog g d ∧ ∀ c, InBlockChart ξ x c q →
    ¬ unitAt ξ q (MvPolynomial.aeval x g / ∏ k, x ⟨k, c k⟩ ^ d k)}
variable {ξ : Spec (CommRingCat.of Ω) ⟶ Z} {x : (Σ k, J k) → Ω} {R : Type} [Field R]
  {z : Spec (CommRingCat.of R) ⟶ Z} {w : (Σ k, J k) → R}
end Point
section Blocks
def omEmb (p q : ℕ) (a : Fin q) : Fin (p + q) := ⟨a, by omega⟩
def wEmb (p q : ℕ) (a : Fin p) : Fin (p + q) := ⟨q + a, by omega⟩
def omBlock {R : Type} {p q : ℕ} (T : Matrix (Fin (p + q)) (Fin (p + q)) R) : Matrix (Fin q) (Fin q) R :=
  T.submatrix (omEmb p q) (omEmb p q)
def wBlock {R : Type} {p q : ℕ} (T : Matrix (Fin (p + q)) (Fin (p + q)) R) : Matrix (Fin p) (Fin p) R :=
  T.submatrix (wEmb p q) (wEmb p q)
def blockEquiv (p q : ℕ) : Fin q ⊕ Fin p ≃ Fin (p + q) := finSumFinEquiv.trans (finCongr (Nat.add_comm q p))
variable {R : Type} [CommRing R] {p q : ℕ}
def colFrame {V : Type} [AddCommGroup V] [Module R V] {r : ℕ} (e : Fin r → V) (T : Matrix (Fin r) (Fin r) R) :
    Fin r → V := fun b => ∑ a, T a b • e a
example : omBlock (p := 1) (q := 2) !![(1 : ℤ), 2, 0; 3, 4, 0; 0, 0, 5] = !![1, 2; 3, 4] ∧
    wBlock (p := 1) (q := 2) !![(1 : ℤ), 2, 0; 3, 4, 0; 0, 0, 5] = !![5] := by
  constructor <;> decide
example : colFrame (R := ℤ) (fun a : Fin 2 => (Pi.single a 1 : Fin 2 → ℤ)) !![1, 2; 0, 1] 1 = ![2, 1] := by
  decide
end Blocks
section DualMetric
variable {Z : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over Z} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ Z}
  {Li : Type} [AddCommGroup Li] [Module Ω Li]
def DualGramAt (M : LieModel G ξ Li) (L : LB G.left) (z : Spec (CommRingCat.of ℂ) ⟶ Z) (V : Submodule Ω Li) {r : ℕ}
    (φ : Fin r → Module.Dual Ω V) (Γ' : Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∃ (v : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ), (∀ a b, φ a (v b) = if a = b then 1 else 0) ∧
    M.GramAt L z (fun b => (v b : Li)) Γ ∧ Γ'ᵀ * Γ = 1
example : (!![2, Complex.I; -Complex.I, 1] : Matrix (Fin 2) (Fin 2) ℂ)ᵀ * !![1, Complex.I; -Complex.I, 2] = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
end DualMetric
section Comparison₂
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
def omBundle {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {x : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S x)
    (τ : CMType H) : Lat 𝔐.ξ (Module.Dual Ω (𝔐.Vgen (.inr τ))) :=
  ((𝔐.V (.inr τ)).comap (𝔐.Vgen (.inr τ)).subtype).dual
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
structure FlagTie (M : FlagModel y (CMType H) (D.p + D.q) D.p) (𝔐 : HodgeCpt Y S M.x) where

  eW : ∀ τ : CMType H, Module.Basis (Fin D.p) M.Ω (𝔐.Vgen (.inl τ))

  eO : ∀ τ : CMType H, Module.Basis (Fin D.q) M.Ω (Module.Dual M.Ω (𝔐.Vgen (.inr τ)))
  frameW : ∀ (q : Cpt 𝔐.ξ) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F →
    M.GoodAt F (ptIdeal 𝔐.ξ M.x q) → ∀ τ,
      (𝔐.V (.inl τ)).IsFrameAt (colFrame (fun a => (eW τ a : 𝔐.Li)) (wBlock (F.T τ))) q
  frameO : ∀ (q : Cpt 𝔐.ξ) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk), M.IsFrame F →
    M.GoodAt F (ptIdeal 𝔐.ξ M.x q) → ∀ τ, (omBundle 𝔐 τ).IsFrameAt (colFrame (eO τ) (omBlock (F.T τ))) q
variable {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}
def FlagTie.wFrame (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin D.p → 𝔐.Li := colFrame (fun a => (tie.eW τ a : 𝔐.Li)) (wBlock (F.T τ))
def FlagTie.omFrame (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin D.q → Module.Dual M.Ω (𝔐.Vgen (.inr τ)) := colFrame (tie.eO τ) (omBlock (F.T τ))
structure BaseMetric.IsHodge {n : ℕ} (BM : BaseMetric M n) (tie : FlagTie M 𝔐) : Prop where
  interior : ∀ (x : BM.Rb.X) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X), CoordsAt 𝔐.ξ M.x z (BM.Rb.lift x x) →
    (x ∉ ReciprocityTheory.AnForm.P.bdry BM.s ↔ 𝔐.Interior z)
  gramW : ∀ i τ, ∀ x ∈ BM.O i \ ReciprocityTheory.AnForm.P.bdry BM.s, ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X,
    CoordsAt 𝔐.ξ M.x z (BM.Rb.lift x x) → 𝔐.M.GramAt 𝔐.t.PP.L z (tie.wFrame (BM.F i) τ) (wBlock (BM.G i τ x))
  gramO : ∀ i τ, ∀ x ∈ BM.O i \ ReciprocityTheory.AnForm.P.bdry BM.s, ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X,
    CoordsAt 𝔐.ξ M.x z (BM.Rb.lift x x) →
      DualGramAt 𝔐.M 𝔐.t.PP.L z (𝔐.Vgen (.inr τ)) (tie.omFrame (BM.F i) τ) (omBlock (BM.G i τ x))
end Comparison₂
end GlobalTheory.CompanionTheory.Ar.PB


