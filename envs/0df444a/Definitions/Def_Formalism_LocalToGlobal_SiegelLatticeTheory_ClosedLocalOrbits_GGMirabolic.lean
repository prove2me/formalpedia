-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:19.701834+00:00
-- url     : https://prove2.me/theorems/eea4cef2-70ef-48b0-b39f-74e926f63c25
-- title:
--   GGMirabolic
-- statement:
--   Definitions and structural lemmas for GGMirabolic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GGMirabolic.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicBase
import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.L2.SG.GGMirabolic
open Finset Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Classical
section One
variable {F : Type} [Field F] [Fintype F] (k : ℕ)
variable {k}
def psiNat (ψ₀ : AddChar F ℂ) (x : GL (Fin k) F) : ℂ := if IsUni k x then psiU ψ₀ x else 0
variable (F k) in

def cardU : ℕ := Nat.card {x : GL (Fin k) F // IsUni k x}
def gam (ψ₀ : AddChar F ℂ) (x : GL (Fin k) F) : ℂ :=
  ((cardU F k : ℂ))⁻¹ * ∑ y : GL (Fin k) F, psiNat ψ₀ (y * x * y⁻¹)
def repGam (ψ₀ : AddChar F ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V) : V →ₗ[ℂ] V :=
  ∑ x : GL (Fin k) F, gam ψ₀ x • π x
def Generic (ψ₀ : AddChar F ℂ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V) : Prop :=
  ∃ ℓ : Module.Dual ℂ V, ℓ ≠ 0 ∧ IsWhit ψ₀ π ℓ
end One
def MirabolicBound : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible → Generic ψ₀ π →
      ∏ i ∈ Finset.Ico 1 k, (Fintype.card F ^ i - 1) ≤ Module.finrank ℂ V
def CardUni : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ), cardU F k = Fintype.card F ^ (k * (k - 1) / 2)
def ConvScalar : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible →
      (gam ψ₀ (1 : GL (Fin k) F))⁻¹ • repGam ψ₀ π =
        if Generic ψ₀ π then ((cardU F k : ℂ) / (Module.finrank ℂ V : ℂ)) • LinearMap.id else 0
def ConvScalarOfLit : Prop := GelfandGraevMultOne → ConvScalar
def GenericRatio : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible → Generic ψ₀ π →
      (cardU F k : ℝ) / (Module.finrank ℂ V : ℝ) ≤
        ∏ i ∈ Finset.Ico 1 k, (1 - ((Fintype.card F : ℝ) ^ i)⁻¹)⁻¹
def GenericRatioOfBound : Prop := MirabolicBound → CardUni → GenericRatio
section Prod
variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}
def gamProd (ψ : ∀ v, AddChar (Fq v) ℂ) (x : ∀ v, GL (Fin k) (Fq v)) : ℂ := ∏ v, gam (ψ v) (x v)
end Prod
def GGMatrixBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (Fq : ι → Type) [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] (k : ℕ)
    (ψ : ∀ v, AddChar (Fq v) ℂ), (∀ v, ψ v ≠ 1) → (∀ v, 3 ≤ Fintype.card (Fq v)) →
    ∀ (X : Type) [Fintype X] [MulAction (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ X],
      (∀ (x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ) (j : X), x • j = j → x = 1) →
      ∀ d : X → X → (∀ v, GL (Fin k) (Fq v)),
        (∀ i j, (∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i) → MulOpposite.op (d i j) • j = i) →
        (Matrix.of fun i j =>
          if ∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i then gamProd ψ (d i j) else 0).PosSemidef ∧
        ((((∏ v, (1 + 3 / (Fintype.card (Fq v) : ℝ))) *
            (gamProd ψ (1 : ∀ v, GL (Fin k) (Fq v))).re : ℝ) : ℂ) • (1 : Matrix X X ℂ) -
          Matrix.of fun i j =>
            if ∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i then conj (gamProd ψ (d i j)) else 0).PosSemidef
def GGMatrixBoundOfLit : Prop := GelfandGraevMultOne → MirabolicBound → GGMatrixBound
def TermsGGBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (Fq : ι → Type) [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] (k : ℕ)
    (ψ : ∀ v, AddChar (Fq v) ℂ), (∀ v, ψ v ≠ 1) → (∀ v, 3 ≤ Fintype.card (Fq v)) →
    ∀ (X : Type) [Fintype X] [MulAction (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ X],
      (∀ (x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ) (j : X), x • j = j → x = 1) →
      ∀ d : X → X → (∀ v, GL (Fin k) (Fq v)),
        (∀ i j, (∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i) → MulOpposite.op (d i j) • j = i) →
      ∀ (τ Rw H H₁ : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw X H H₁),
        (∀ i j, T.GG i j =
          if ∃ x : (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ, x • j = i then conj (gamProd ψ (d i j)) else 0) →
        T.Gam1 = (gamProd ψ (1 : ∀ v, GL (Fin k) (Fq v))).re →
        T.GGBound (∏ v, (1 + 3 / (Fintype.card (Fq v) : ℝ)))
end
end Formalism.L2.SG.GGMirabolic


