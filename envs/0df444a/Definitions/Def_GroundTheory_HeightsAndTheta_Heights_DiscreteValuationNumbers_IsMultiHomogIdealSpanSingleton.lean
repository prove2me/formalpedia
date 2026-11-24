-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:49.104182+00:00
-- url     : https://prove2.me/theorems/6f8b9f0b-110b-4f31-9e36-2112d096cd4d
-- title:
--   Is Multi Homog Ideal Span Singleton
-- statement:
--   Definitions and structural lemmas for Is Multi Homog Ideal Span Singleton, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsMultiHomogIdealSpanSingleton.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
section Defs
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def IsEffectiveVertical (P : Ideal (MRing ι O)) (ϖ : O) (b : K → ℤ) (f g : MRing ι O) : Prop :=
  IsVerticalDivisor P ϖ b f g ∧ ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W →
    ∃ u v : MRing ι O, u ∉ W ∧ u * f - v * g ∈ P
open Classical in

def cutIdentity (ϖ : O) (P : Ideal (MRing ι O)) (b : K → ℤ) (f g : MRing ι O) (c : K → ℕ)
    (s : MRing ι O) {d : ℕ} (L : Fin d → K → ℤ) : Prop :=
  cycEval (fun G => vNum G (Matrix.vecCons (fun k => (c k : ℤ)) L)) (ratDiv P f g) =
    cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNum W (Matrix.vecCons b L)
        else cycEval (fun G => vNum G L) (ratDiv W f g)) (divCycle P s)
end Defs
section Lemmas
def DivCycleMul.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (x y : MRing ι R), P.IsPrime → x ∉ P → y ∉ P →
    divCycle P (x * y) = divCycle P x + divCycle P y
def DivCycleFiniteSupport.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (f : MRing ι R),
    (Function.support (divCycle P f)).Finite
def SupSpanMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (I : Ideal (MRing ι R))
    (x : MRing ι R) (e : K → ℕ), IsMultiHomogIdeal I → IsMultiHomog x e →
    IsMultiHomogIdeal (I ⊔ Ideal.span {x})
def MinimalPrimeMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (J W : Ideal (MRing ι R)), IsMultiHomogIdeal J → W ∈ J.minimalPrimes → IsMultiHomogIdeal W
def IntNumAddFirst.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (G : Ideal (MRing ι F)), G.IsPrime → IsMultiHomogIdeal G →
    ringKrullDim (MRing ι F ⧸ G) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (b₁ b₂ : K → ℤ) (L : Fin n → K → ℤ),
      intNum F G (Matrix.vecCons (b₁ + b₂) L) =
        intNum F G (Matrix.vecCons b₁ L) + intNum F G (Matrix.vecCons b₂ L)
def SpecialQuotDim.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι O)), (C ϖ : MRing ι O) ∈ W →
    ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
      ringKrullDim (MRing ι O ⧸ W)
def GenericDimBound.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    IsMultiProjPrime P → P.comap (C : O →+* MRing ι O) = ⊥ →
    ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) + 1 ≤ ringKrullDim (MRing ι O ⧸ P)
def GenericFibProps.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    IsMultiProjPrime P → P.comap (C : O →+* MRing ι O) = ⊥ →
    (genFib P).IsPrime ∧ IsMultiHomogIdeal (genFib P) ∧
    ∀ (s : MRing ι O) (c : K → ℕ), IsMultiHomog s c → s ∉ P →
      IsMultiHomog (MvPolynomial.map (algebraMap O (FractionRing O)) s) c ∧
        MvPolynomial.map (algebraMap O (FractionRing O)) s ∉ genFib P
open Classical in

def GenericCycleCorresp.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (s : MRing ι O), P.IsPrime →
    P.comap (C : O →+* MRing ι O) = ⊥ → s ∉ P →
    ∀ n : Ideal (MRing ι (FractionRing O)) → ℤ,
      cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then 0 else n (genFib W)) (divCycle P s) =
        cycEval n (divCycle (genFib P) (MvPolynomial.map (algebraMap O (FractionRing O)) s))
def ConservationOfNumberLE.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsMultiProjPrime P →
    P.comap (C : O →+* MRing ι O) = ⊥ →
    ringKrullDim (MRing ι O ⧸ P) ≤ ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ a : Fin d → K → ℤ, cycEval (fun W => vNum W a) (divCycle P (C ϖ)) = gNum P a
def UniformiserCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P 0 (C ϖ) 1 c s L
def ShiftByUniformiser.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ (L : Fin d → K → ℤ) (n : ℕ),
      cutIdentity ϖ P b (C ϖ ^ n * f) g c s L → cutIdentity ϖ P 0 (C ϖ) 1 c s L →
        cutIdentity ϖ P b f g c s L
def EffectiveShift.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (e : ℕ), IsModelOver P e →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor P ϖ b f g →
    ∃ n : ℕ, IsEffectiveVertical P ϖ b (C ϖ ^ n * f) g
def EffectiveCase.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → IsVerticalDivisor H ϖ b f g) →
    ∀ L : Fin d → K → ℤ, cutIdentity ϖ P b f g c s L
def Representative.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (b : K → ℤ) (f g : MRing ι O), IsMultiProjPrime P →
    IsVerticalDivisor P ϖ b f g → ∀ T : Finset (Ideal (MRing ι O)),
    (∀ H ∈ T, IsMultiProjPrime H ∧ P ≤ H ∧ (C ϖ : MRing ι O) ∉ H ∧
      ∃ h : MRing ι O, h ∉ P ∧ H ∈ (P ⊔ Ideal.span {h}).minimalPrimes) →
    ∃ f₁ g₁ : MRing ι O, IsVerticalDivisor P ϖ b f₁ g₁ ∧ ratDiv P f₁ g₁ = ratDiv P f g ∧
      ∀ H ∈ T, IsVerticalDivisor H ϖ b f₁ g₁
end Lemmas
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


