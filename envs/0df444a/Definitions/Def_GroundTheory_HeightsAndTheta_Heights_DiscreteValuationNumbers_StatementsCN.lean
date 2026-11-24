-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:58.557922+00:00
-- url     : https://prove2.me/theorems/2fa13c41-cfe1-45a2-8a4f-c6d83284c736
-- title:
--   Statements CN
-- statement:
--   Definitions and structural lemmas for Statements CN, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsCN.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
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
variable {K : Type*}
def DegLT (f : (K → ℤ) → ℤ) (n : ℕ) : Prop :=
  ∀ bs : Fin n → K → ℤ, ∀ᶠ m in Filter.atTop, mixedDiff bs f m = 0
def shiftFn (s : K → ℤ) (f : (K → ℤ) → ℤ) : (K → ℤ) → ℤ := fun m => f (m - s)
variable {ι : K → Type*}
open Classical in

def idealCycle {R : Type*} [CommRing R] (J W : Ideal (MRing ι R)) : ℤ :=
  if h : W ∈ J.minimalPrimes ∧ IsRelevant W then
    haveI : W.IsPrime := h.1.1.1
    ((multAt J W).toNat : ℤ)
  else 0
variable [DecidableEq K]
def gradedPieceR {R : Type*} [CommRing R] (P : Ideal (MRing ι R)) (m : K → ℕ) :
    Submodule R (MRing ι R ⧸ P) :=
  (weightedHomogeneousSubmodule R (blockWeight ι) m).map (Ideal.Quotient.mkₐ R P).toLinearMap
end Defs
section FunctionsOnMultidegrees
def MixedDiffLinear.Statement : Prop :=
  ∀ (K : Type) (n : ℕ) (bs : Fin n → K → ℤ) (f g : (K → ℤ) → ℤ) (c : ℤ) (s b : K → ℤ),
    mixedDiff bs (f + g) = mixedDiff bs f + mixedDiff bs g ∧
    mixedDiff bs (c • f) = c • mixedDiff bs f ∧
    mixedDiff bs (shiftFn s f) = shiftFn s (mixedDiff bs f) ∧
    mixedDiff bs (diffStep b f) = diffStep b (mixedDiff bs f) ∧
    mixedDiff (Matrix.vecCons b bs) f = diffStep b (mixedDiff bs f)
def DegLTClosure.Statement : Prop :=
  ∀ (K : Type) (n : ℕ) (f g : (K → ℤ) → ℤ) (c : ℤ) (s : K → ℤ),
    (DegLT f n → DegLT g n → DegLT (f + g) n) ∧
    (DegLT f n → DegLT (c • f) n) ∧
    (DegLT f n → DegLT (shiftFn s f) n) ∧
    (DegLT f n → DegLT f (n + 1)) ∧
    (f =ᶠ[Filter.atTop] g → DegLT f n → DegLT g n)
def DiffStepExpansion.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (b : K → ℤ),
    ∃ l : List ((K × (K → ℤ)) × ℤ), ∀ f : (K → ℤ) → ℤ,
      diffStep b f = (l.map fun t => t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)).sum
def DegLTOfUnitSteps.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (f : (K → ℤ) → ℤ),
    (∀ k, DegLT (diffStep (Pi.single k 1) f) n) → DegLT f (n + 1)
def DegLTEventuallyConst.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (f : (K → ℤ) → ℤ), DegLT f (n + 1) →
    ∀ bs : Fin n → K → ℤ, ∃ c : ℤ, ∀ᶠ m in Filter.atTop, mixedDiff bs f m = c
def EventualValueFacts.Statement : Prop :=
  ∀ (K : Type) (f : (K → ℤ) → ℤ) (c : ℤ) (s : K → ℤ),
    ((∀ᶠ m in Filter.atTop, f m = c) → eventualValue f = c) ∧
    ((∀ᶠ m in Filter.atTop, f m = c) → ∀ᶠ m in Filter.atTop, shiftFn s f m = c)
end FunctionsOnMultidegrees
section HilbertFunctions
def HilbFnVanishBlock.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι F)) (k : K),
    (∀ i, (X ⟨k, i⟩ : MRing ι F) ∈ Q) → ∀ m : K → ℤ, 1 ≤ m k → hilbFn Q m = 0
def GradedPieceQuot.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)) (m : K → ℕ),
    (Module.finrank F (gradedPiece I m) : ℤ) =
      Module.finrank F (weightedHomogeneousSubmodule F (blockWeight ι) m) -
        Module.finrank F ↥(weightedHomogeneousSubmodule F (blockWeight ι) m ⊓ I.restrictScalars F)
open Classical in

def CutPieces.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)) (x : MRing ι F) (e m : K → ℕ),
    IsMultiHomogIdeal I → IsMultiHomog x e → (∀ y, x * y ∈ I → y ∈ I) →
    (Module.finrank F ↥(weightedHomogeneousSubmodule F (blockWeight ι) m ⊓
        (I ⊔ Ideal.span {x}).restrictScalars F) : ℤ) =
      Module.finrank F ↥(weightedHomogeneousSubmodule F (blockWeight ι) m ⊓ I.restrictScalars F) +
        if e ≤ m then
          (Module.finrank F (weightedHomogeneousSubmodule F (blockWeight ι) (m - e)) : ℤ) -
            Module.finrank F ↥(weightedHomogeneousSubmodule F (blockWeight ι) (m - e) ⊓
              I.restrictScalars F)
        else 0
def HilbFnCut.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)) (x : MRing ι F) (e : K → ℕ),
    IsMultiHomogIdeal I → IsMultiHomog x e → (∀ y, x * y ∈ I → y ∈ I) →
    ∀ m : K → ℤ, hilbFn (I ⊔ Ideal.span {x}) m = hilbFn I m - hilbFn I (m - fun k => (e k : ℤ))
end HilbertFunctions
section Filtrations
def MultiHomogPrimeCriterion.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (Q : Ideal (MRing ι R)), IsMultiHomogIdeal Q → Q ≠ ⊤ →
    (∀ (a b : MRing ι R) (sa sb : K → ℕ), IsMultiHomog a sa → IsMultiHomog b sb → a * b ∈ Q →
      a ∈ Q ∨ b ∈ Q) →
    Q.IsPrime
def ColonMultiHomog.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [DecidableEq K] (ι : K → Type) (I : Ideal (MRing ι R))
    (f : MRing ι R) (s : K → ℕ), IsMultiHomogIdeal I → IsMultiHomog f s →
    IsMultiHomogIdeal (I.colon {f})
def AssociatedMultiHomogPrime.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (J : Ideal (MRing ι F)), IsMultiHomogIdeal J → J ≠ ⊤ →
    ∃ (f : MRing ι F) (s : K → ℕ), IsMultiHomog f s ∧ f ∉ J ∧ (J.colon {f}).IsPrime
def FiltrationStepHilb.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (L : Ideal (MRing ι F)) (f : MRing ι F) (s : K → ℕ),
    IsMultiHomogIdeal L → IsMultiHomog f s →
    ∀ m : K → ℤ, hilbFn L m = hilbFn (L ⊔ Ideal.span {f}) m +
      hilbFn (L.colon {f}) (m - fun k => (s k : ℤ))
def FiltrationStepLength.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) (ι : K → Type) (L W : Ideal (MRing ι R)) [W.IsPrime]
    (f : MRing ι R),
    multAt L W = multAt (L ⊔ Ideal.span {f}) W + multAt (L.colon {f}) W
def PrimeFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (J : Ideal (MRing ι F)), IsMultiHomogIdeal J →
    ∃ l : List (Ideal (MRing ι F) × (K → ℕ)),
      (∀ p ∈ l, p.1.IsPrime ∧ IsMultiHomogIdeal p.1 ∧ J ≤ p.1) ∧
      (∀ m : K → ℤ, hilbFn J m = (l.map fun p => hilbFn p.1 (m - fun k => (p.2 k : ℤ))).sum) ∧
      (∀ (W : Ideal (MRing ι F)) [W.IsPrime], multAt J W = (l.map fun p => multAt p.1 W).sum)
open Classical in

def MultAtPrimeAtMinimal.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) (ι : K → Type) (J Q W : Ideal (MRing ι R)) [Q.IsPrime]
    [W.IsPrime], J ≤ Q → W ∈ J.minimalPrimes → multAt Q W = if Q = W then 1 else 0
end Filtrations
section Dimension
def DimStrictDrop.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (Q Q' : Ideal A) [Q.IsPrime] [Q'.IsPrime], Q < Q' →
    ringKrullDim (A ⧸ Q') + 1 ≤ ringKrullDim (A ⧸ Q)
def BlockAdjoinPrime.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (Q : Ideal (MRing ι R)) (B : Set K), Q.IsPrime → IsMultiHomogIdeal Q →
    (Q ⊔ Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B ∧ p = X v}).IsPrime ∧
    ∀ v : Σ k, ι k, v.1 ∉ B →
      (X v ∈ Q ⊔ Ideal.span {p | ∃ w : Σ k, ι k, w.1 ∈ B ∧ p = X w} ↔ X v ∈ Q)
def RelevantDimGe.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (Q : Ideal (MRing ι R)), IsMultiProjPrime Q →
    ((Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι R ⧸ Q)
def HilbDegBound.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (Q : Ideal (MRing ι F)), Q.IsPrime → IsMultiHomogIdeal Q →
    ringKrullDim (MRing ι F ⧸ Q) < ((n + Fintype.card K : ℕ) : WithBot ℕ∞) → DegLT (hilbFn Q) n
def TopDimMinimal.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (J Q : Ideal A) [Q.IsPrime] (N : ℕ), J ≤ Q →
    ringKrullDim (A ⧸ J) < ((N + 1 : ℕ) : WithBot ℕ∞) →
    ¬ ringKrullDim (A ⧸ Q) < ((N : ℕ) : WithBot ℕ∞) → Q ∈ J.minimalPrimes
end Dimension
section Numbers
def IntNumVanish.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (Q : Ideal (MRing ι F)), Q.IsPrime → IsMultiHomogIdeal Q →
    (¬ IsRelevant Q ∨ ringKrullDim (MRing ι F ⧸ Q) < ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) →
    ∀ bs : Fin n → K → ℤ, intNum F Q bs = 0
def IntNumOfFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (J : Ideal (MRing ι F))
    (l : List (Ideal (MRing ι F) × (K → ℕ))), (∀ p ∈ l, DegLT (hilbFn p.1) (n + 1)) →
    (∀ m : K → ℤ, hilbFn J m = (l.map fun p => hilbFn p.1 (m - fun k => (p.2 k : ℤ))).sum) →
    ∀ bs : Fin n → K → ℤ, intNum F J bs = (l.map fun p => intNum F p.1 bs).sum
def IntNumAssoc.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (J : Ideal (MRing ι F)), IsMultiHomogIdeal J →
    ringKrullDim (MRing ι F ⧸ J) < ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ bs : Fin n → K → ℤ, intNum F J bs = cycEval (fun W => intNum F W bs) (idealCycle J)
def CutByForm.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) (G : Ideal (MRing ι F)), G.IsPrime → IsMultiHomogIdeal G →
    ringKrullDim (MRing ι F ⧸ G) < ((n + 2 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (s : MRing ι F) (c : K → ℕ), IsMultiHomog s c → s ∉ G →
    ∀ bs : Fin n → K → ℤ,
      intNum F G (Matrix.vecCons (fun k => (c k : ℤ)) bs) =
        cycEval (fun W => intNum F W bs) (divCycle G s)
end Numbers
section Fibres
def GradedPieceFree.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    (∀ x, C ϖ * x ∈ P → x ∈ P) → ∀ m : K → ℕ,
      Module.Free O (gradedPieceR P m) ∧ Module.Finite O (gradedPieceR P m)
def SpecialPieceRank.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    IsMultiHomogIdeal P → (∀ x, C ϖ * x ∈ P → x ∈ P) → ∀ m : K → ℕ,
      Module.finrank (IsLocalRing.ResidueField O) (gradedPiece (specialIdeal P) m) =
        Module.finrank O (gradedPieceR P m)
def GenericPieceRank.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)),
    IsMultiHomogIdeal P → ∀ m : K → ℕ,
      Module.finrank (FractionRing O) (gradedPiece (genFib P) m) = Module.finrank O (gradedPieceR P m)
def SpecialIdealMultiHomog.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [DecidableEq K]
    (ι : K → Type) (P : Ideal (MRing ι O)), IsMultiHomogIdeal P → IsMultiHomogIdeal (specialIdeal P)
def SpecialIdealCorresp.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι O)), W.IsPrime → (C ϖ : MRing ι O) ∈ W →
    (specialIdeal W).IsPrime ∧
    (W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ↔ specialIdeal W ∈ (specialIdeal P).minimalPrimes) ∧
    (IsRelevant W ↔ IsRelevant (specialIdeal W)) ∧
    ∀ W' : Ideal (MRing ι O), W'.IsPrime → (C ϖ : MRing ι O) ∈ W' →
      specialIdeal W' = specialIdeal W → W' = W
def SpecialIdealSurj.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (V : Ideal (MRing ι (IsLocalRing.ResidueField O))), V.IsPrime →
    ∃ W : Ideal (MRing ι O), W.IsPrime ∧ (C ϖ : MRing ι O) ∈ W ∧ specialIdeal W = V
def SpecialMultAt.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι O)) [W.IsPrime], (C ϖ : MRing ι O) ∈ W →
    ∀ [(specialIdeal W).IsPrime],
      multAt (P ⊔ Ideal.span {C ϖ}) W = multAt (specialIdeal P) (specialIdeal W)
def SpecialCycleEval.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (n : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ),
    cycEval (fun W => n (specialIdeal W)) (divCycle P (C ϖ)) = cycEval n (idealCycle (specialIdeal P))
def SpecialDimBound.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
    ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P) <
      ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)
end Fibres
section Examples
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


