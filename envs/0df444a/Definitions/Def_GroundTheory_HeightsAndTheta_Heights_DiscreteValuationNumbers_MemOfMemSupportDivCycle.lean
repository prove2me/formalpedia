-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:47.306892+00:00
-- url     : https://prove2.me/theorems/2297901e-ad63-41c3-b736-a3ae40804afd
-- title:
--   Mem Of Mem Support Div Cycle
-- statement:
--   Definitions and structural lemmas for Mem Of Mem Support Div Cycle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/MemOfMemSupportDivCycle.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_GroundTheory_ArithmeticGeometry_IwasawaModules_SpanFinrankMaximalIdealLeTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
universe u v w
section Lengths
def colonMod {A : Type*} [CommRing A] (a b : A) : Submodule A (A ⧸ Ideal.span {a}) :=
  Submodule.map (Ideal.span {a}).mkQ ((Ideal.span {a}).colon (Ideal.span {b}) : Submodule A A)
def NumbersBirationalInvariance.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] (x : A),
    ringKrullDim A = 1 →
    length A (M ⧸ (Ideal.span {x} • ⊤ : Submodule A M)) ≠ ⊤ →
    length A (M ⧸ (Ideal.span {x} • ⊤ : Submodule A M)) =
      length A (Submodule.torsionBy A M x) +
        ∑ᶠ (p : PrimeSpectrum A)
          (_ : p.asIdeal ∈ (Module.annihilator A M).minimalPrimes ∧
            p.asIdeal ≠ IsLocalRing.maximalIdeal A),
          length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
            length A (A ⧸ (p.asIdeal ⊔ Ideal.span {x}))
def NumbersBirationalInvariance.LocalRingStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] (x : A),
    ringKrullDim A = 1 →
    length A (M ⧸ (Ideal.span {x} • ⊤ : Submodule A M)) ≠ ⊤ →
    length A (M ⧸ (Ideal.span {x} • ⊤ : Submodule A M)) =
      length A (Submodule.torsionBy A M x) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal ∈ (Module.annihilator A M).minimalPrimes),
          length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M) *
            length A (A ⧸ (p.asIdeal ⊔ Ideal.span {x}))
def NumbersSymmetry.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (a b : A),
    ringKrullDim A = 2 → a ≠ 0 → b ≠ 0 → length A (A ⧸ Ideal.span {a, b}) ≠ ⊤ →
    length A (A ⧸ Ideal.span {a, b}) = length A (colonMod a b) +
        ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1),
          length (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime p.asIdeal ⧸
                Ideal.span {algebraMap A (Localization.AtPrime p.asIdeal) a}) *
            length A (A ⧸ (p.asIdeal ⊔ Ideal.span {b})) ∧
      Nonempty (colonMod a b ≃ₗ[A] colonMod b a)
end Lengths
section Models
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def redMap : MRingOver O ι →+* MRingOver (IsLocalRing.ResidueField O) ι :=
  MvPolynomial.map (IsLocalRing.residue O)
def genMap : MRingOver O ι →+* MRingOver (FractionRing O) ι :=
  MvPolynomial.map (algebraMap O (FractionRing O))
def IsModelOver (P : Ideal (MRingOver O ι)) (d : ℕ) : Prop :=
  IsMultiProjPrime P ∧ P.comap (C : O →+* MRingOver O ι) = ⊥ ∧
    ringKrullDim (MRingOver O ι ⧸ P) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)
def intCyc {R : Type*} [CommRing R] (Z : Ideal (MRingOver R ι) →₀ ℕ) : Ideal (MRingOver R ι) →₀ ℤ :=
  Finsupp.mapRange (fun m : ℕ => (m : ℤ)) Nat.cast_zero Z
def specCyc (ϖ : O) (P : Ideal (MRingOver O ι)) : Ideal (MRingOver O ι) →₀ ℕ :=
  divCycle P (C ϖ)
def genFib (P : Ideal (MRingOver O ι)) : Ideal (MRingOver (FractionRing O) ι) :=
  P.map genMap
def divO (P : Ideal (MRingOver O ι)) (f g : MRingOver O ι) : Ideal (MRingOver O ι) →₀ ℤ :=
  intCyc (divCycle P f) - intCyc (divCycle P g)
def redEval (J : Ideal (MRingOver (IsLocalRing.ResidueField O) ι) → ℤ)
    (Z : Ideal (MRingOver O ι) →₀ ℤ) : ℤ :=
  Z.sum fun W m => m * J (W.map redMap)
def IsVerticalDiv (ϖ : O) (P : Ideal (MRingOver O ι)) (b : K → ℤ) (f g : MRingOver O ι) : Prop :=
  (∃ α β : K → ℕ, IsMultiHomog f α ∧ IsMultiHomog g β ∧ ∀ k, (α k : ℤ) - β k = b k) ∧
    g ∉ P ∧ ∀ W ∈ (divO P f g).support, C ϖ ∈ W
def IsRegSection (P : Ideal (MRingOver O ι)) (c : K → ℕ) (s : MRingOver O ι) : Prop :=
  IsMultiHomog s c ∧ s ∉ P
end Models
def NumbersMultilinearity.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
      (P : Ideal (MRingOver O ι)) (d : ℕ) (a : Fin d → K → ℤ)
      (Iκ : IFamily (IsLocalRing.ResidueField O) ι) (IK : IFamily (FractionRing O) ι),
      IsModelOver P d → IsFieldIntersection Iκ → IsFieldIntersection IK →
      redEval (fun W => Iκ W d a) (intCyc (specCyc ϖ P)) = IK (genFib P) d a
open Classical in

def NumbersProjectionFormula.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
      (P : Ideal (MRingOver O ι)) (n : ℕ) (b : K → ℤ) (f g : MRingOver O ι) (c : K → ℕ)
      (s : MRingOver O ι) (L : Fin n → K → ℤ) (Iκ : IFamily (IsLocalRing.ResidueField O) ι),
      IsModelOver P (n + 1) → IsVerticalDiv ϖ P b f g → IsRegSection P c s →
      IsFieldIntersection Iκ →
      (∀ H ∈ (divCycle P s).support, C ϖ ∉ H → IsVerticalDiv ϖ H b f g) →
      redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L (fun k => (c k : ℤ))))
          (divO P f g) =
        (divCycle P s).sum fun H m =>
          if C ϖ ∈ H then (m : ℤ) * Iκ (H.map redMap) (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b)
          else (m : ℤ) * redEval (fun G => Iκ G n L) (divO H f g)
def VerticalDivisorsCommuting.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type v) [Fintype K] (ι : K → Type w) [∀ k, Fintype (ι k)]
      (P : Ideal (MRingOver O ι)) (n : ℕ) (b b' : K → ℤ) (f g f' g' : MRingOver O ι)
      (L : Fin n → K → ℤ) (Iκ : IFamily (IsLocalRing.ResidueField O) ι),
      IsModelOver P (n + 1) → IsVerticalDiv ϖ P b f g → IsVerticalDiv ϖ P b' f' g' →
      IsFieldIntersection Iκ →
      redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b')) (divO P f g) =
        redEval (fun G => Iκ G (n + 1) (Fin.snoc (α := fun _ => K → ℤ) L b)) (divO P f' g')
section Inhabitants
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
end Inhabitants
section LengthInhabitants
open IsLocalRing
end LengthInhabitants
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR


