-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:55.905245+00:00
-- url     : https://prove2.me/theorems/014774ab-b142-4edd-91aa-77f8029188f0
-- title:
--   Pf Contracted Hypotheses Example
-- statement:
--   Definitions and structural lemmas for Pf Contracted Hypotheses Example, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PfContractedHypothesesExample.lean

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u u' v v' w
section Objects
def HasRelDim {F : Type u} [Field F] {K : Type v} [Fintype K] {ι : K → Type w}
    (I : Ideal (MRing ι F)) (n : ℕ) : Prop :=
  ringKrullDim (MRing ι F ⧸ I) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)
def degZeroFractions {F : Type u} [Field F] {K : Type v} [DecidableEq K] {ι : K → Type w}
    (P : Ideal (MRing ι F)) [P.IsPrime] : Set (FractionRing (MRing ι F ⧸ P)) :=
  {x | ∃ (d : K → ℕ) (f g : MRing ι F), IsMultiHomog f d ∧ IsMultiHomog g d ∧ g ∉ P ∧
    x = algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)}
def funField {F : Type u} [Field F] {K : Type v} [DecidableEq K] {ι : K → Type w}
    (P : Ideal (MRing ι F)) [P.IsPrime] : IntermediateField F (FractionRing (MRing ι F ⧸ P)) :=
  IntermediateField.adjoin F (degZeroFractions P)
open Classical in

def resDeg {F : Type u} [Field F] {K : Type v} [DecidableEq K] {ι : K → Type w}
    (P : Ideal (MRing ι F)) : ℤ :=
  if h : P.IsPrime then
    haveI := h
    (Module.finrank F (funField P) : ℤ)
  else 0
structure IsRatSection {F : Type u} [Field F] {K : Type v} [DecidableEq K] {ι : K → Type w}
    (P : Ideal (MRing ι F)) (b : K → ℤ) (f g : MRing ι F) : Prop where
  degrees : ∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
    (fun k => (bf k : ℤ) - bg k) = b
  num_not_mem : f ∉ P
  den_not_mem : g ∉ P
open Classical in

def topCycle {F : Type u} [Field F] {K : Type v} [Fintype K] {ι : K → Type w}
    (I : Ideal (MRing ι F)) (n : ℕ) (W : Ideal (MRing ι F)) : ℤ :=
  if h : W ∈ I.minimalPrimes ∧ IsRelevant W ∧ HasRelDim W n then
    haveI : W.IsPrime := h.1.1.1
    ((multAt I W).toNat : ℤ)
  else 0
def blockIncl {F : Type u} [Field F] {K : Type v} {L : Type v'} {ι : K → Type w}
    (ι₂ : L → Type w) : MRing ι F →ₐ[F] MRing (Sum.elim ι ι₂) F :=
  rename (fun x : Σ k, ι k => (⟨Sum.inl x.1, x.2⟩ : Σ k, Sum.elim ι ι₂ k))
def contractBlocks {F : Type u} [Field F] {K : Type v} {L : Type v'} {ι : K → Type w}
    (ι₂ : L → Type w) (P' : Ideal (MRing (Sum.elim ι ι₂) F)) : Ideal (MRing ι F) :=
  P'.comap (blockIncl ι₂)
def pullDeg {K : Type v} {L : Type v'} (b : K → ℤ) : K ⊕ L → ℤ :=
  Sum.elim b 0
def pulledFractions {F : Type u} [Field F] {K : Type v} [DecidableEq K] {L : Type v'}
    {ι : K → Type w} (ι₂ : L → Type w) (P' : Ideal (MRing (Sum.elim ι ι₂) F)) [P'.IsPrime] :
    Set (FractionRing (MRing (Sum.elim ι ι₂) F ⧸ P')) :=
  {x | ∃ (d : K → ℕ) (f g : MRing ι F), IsMultiHomog f d ∧ IsMultiHomog g d ∧
    blockIncl ι₂ g ∉ P' ∧
    x = algebraMap (MRing (Sum.elim ι ι₂) F ⧸ P') _ (Ideal.Quotient.mk P' (blockIncl ι₂ f)) /
      algebraMap (MRing (Sum.elim ι ι₂) F ⧸ P') _ (Ideal.Quotient.mk P' (blockIncl ι₂ g))}
def pulledFunField {F : Type u} [Field F] {K : Type v} [DecidableEq K] {L : Type v'}
    {ι : K → Type w} (ι₂ : L → Type w) (P' : Ideal (MRing (Sum.elim ι ι₂) F)) [P'.IsPrime] :
    IntermediateField F (FractionRing (MRing (Sum.elim ι ι₂) F ⧸ P')) :=
  IntermediateField.adjoin F (pulledFractions ι₂ P')
def fibreDeg {F : Type u} [Field F] {K : Type v} [DecidableEq K] {L : Type v'} [DecidableEq L]
    {ι : K → Type w} (ι₂ : L → Type w) (P' : Ideal (MRing (Sum.elim ι ι₂) F)) [P'.IsPrime] : ℕ :=
  (pulledFunField ι₂ P').relfinrank (funField P')
def addBlock {F : Type u} [Field F] {K : Type v} {ι : K → Type w} (J : Type w)
    (P : Ideal (MRing ι F)) : Ideal (MRing (Sum.elim ι (fun _ : Unit => J)) F) :=
  P.map (blockIncl (fun _ : Unit => J))
def newBlockDeg {K : Type v} : K ⊕ Unit → ℤ :=
  Sum.elim 0 1
structure IsIntersectionTheory (F : Type u) [Field F] {K : Type v} [Fintype K] [DecidableEq K]
    (ι : K → Type w) (N : Ideal (MRing ι F) → (n : ℕ) → (Fin n → K → ℤ) → ℤ) : Prop where
  base : ∀ P : Ideal (MRing ι F), IsMultiProjPrime P → HasRelDim P 0 → N P 0 ![] = resDeg P
  cut : ∀ (P : Ideal (MRing ι F)) (n : ℕ), IsMultiProjPrime P → HasRelDim P (n + 1) →
    ∀ (bs : Fin n → K → ℤ) (b : K → ℤ) (f g : MRing ι F), IsRatSection P b f g →
      N P (n + 1) (Fin.snoc (α := fun _ => K → ℤ) bs b) =
        cycEval (fun W => N W n bs) (ratDiv P f g)
end Objects
def GradedFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)) (m : K → ℕ),
    FiniteDimensional F (gradedPiece I m) ∧
      hilbFn I (fun k => (m k : ℤ)) = (Module.finrank F (gradedPiece I m) : ℤ)
def HilbExactDivide.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I →
    ∀ (s : MRing ι F) (c : K → ℕ), IsMultiHomog s c →
      ∀ᶠ m in Filter.atTop, hilbFn I m - hilbFn (I.colon {s}) (m - fun k => (c k : ℤ)) =
        hilbFn (I ⊔ Ideal.span {s}) m
def PolyOfDiffs.Statement : Prop :=
  ∀ (K : Type v) [Fintype K] [DecidableEq K] (h : (K → ℤ) → ℤ) (d : ℕ),
    (∀ k : K, ∃ p : MvPolynomial K ℚ, (p = 0 ∨ p.totalDegree + 1 ≤ d) ∧
      ∀ᶠ m in Filter.atTop,
        (diffStep (Pi.single k 1) h m : ℚ) = MvPolynomial.eval (fun j => (m j : ℚ)) p) →
    ∃ q : MvPolynomial K ℚ, q.totalDegree ≤ d ∧
      ∀ᶠ m in Filter.atTop, (h m : ℚ) = MvPolynomial.eval (fun j => (m j : ℚ)) q
def HilbEventuallyPoly.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I →
    ∃ q : MvPolynomial K ℚ,
      ∀ᶠ m in Filter.atTop, (hilbFn I m : ℚ) = MvPolynomial.eval (fun k => (m k : ℚ)) q
def HilbDegreeBound.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I →
    (IsRelevant I → ∀ n : ℕ, HasRelDim I n →
      ∃ q : MvPolynomial K ℚ, q.totalDegree ≤ n ∧
        ∀ᶠ m in Filter.atTop, (hilbFn I m : ℚ) = MvPolynomial.eval (fun k => (m k : ℚ)) q) ∧
    (¬ IsRelevant I → ∀ᶠ m in Filter.atTop, hilbFn I m = 0)
def MixedDiffConst.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiHomogIdeal P → IsRelevant P →
    ∀ n : ℕ, HasRelDim P n →
      (∀ bs : Fin n → K → ℤ, ∃ c : ℤ, (∀ᶠ m in Filter.atTop, mixedDiff bs (hilbFn P) m = c) ∧
        eventualValue (mixedDiff bs (hilbFn P)) = c) ∧
      (∀ r : ℕ, n < r → ∀ bs : Fin r → K → ℤ,
        ∀ᶠ m in Filter.atTop, mixedDiff bs (hilbFn P) m = 0)
def IntNumSymm.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (n : ℕ) (bs : Fin n → K → ℤ)
    (σ : Equiv.Perm (Fin n)), intNum F P (bs ∘ σ) = intNum F P bs
def IntNumAdd.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiHomogIdeal P → IsRelevant P →
    ∀ n : ℕ, HasRelDim P n → ∀ (bs : Fin n → K → ℤ) (i : Fin n) (b b' : K → ℤ),
      intNum F P (Function.update bs i (b + b')) =
        intNum F P (Function.update bs i b) + intNum F P (Function.update bs i b')
def IntNumZeroSlot.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)),
    (∀ (n : ℕ) (bs : Fin n → K → ℤ) (i : Fin n), bs i = 0 → intNum F P bs = 0) ∧
    (IsMultiHomogIdeal P → IsRelevant P → ∀ d n : ℕ, HasRelDim P d → d < n →
      ∀ bs : Fin n → K → ℤ, intNum F P bs = 0)
def IntNumBase.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P), HasRelDim P 0 →
    haveI := hP.isPrime
    FiniteDimensional F (funField P) ∧
      intNum F P (![] : Fin 0 → K → ℤ) = (Module.finrank F (funField P) : ℤ)
open Classical in

def PrimeFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I →
    ∀ n : ℕ, HasRelDim I n →
    ∃ (r : ℕ) (Q : Fin r → Ideal (MRing ι F)) (c : Fin r → K → ℕ),
      (∀ j, (Q j).IsPrime ∧ IsMultiHomogIdeal (Q j) ∧ I ≤ Q j) ∧
      (∀ᶠ m in Filter.atTop, hilbFn I m = ∑ j, hilbFn (Q j) (m - fun k => (c j k : ℤ))) ∧
      (∀ (W : Ideal (MRing ι F)) (hW : W ∈ I.minimalPrimes), IsRelevant W → HasRelDim W n →
        haveI : W.IsPrime := hW.1.1
        (((Finset.univ.filter fun j => Q j = W).card : ℕ) : ℕ∞) = multAt I W) ∧
      (∀ j, (Q j ∈ I.minimalPrimes ∧ IsRelevant (Q j) ∧ HasRelDim (Q j) n) ∨
        ¬ IsRelevant (Q j) ∨ ∃ d < n, HasRelDim (Q j) d)
def MultEqualsCoeff.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I → IsRelevant I →
    ∀ n : ℕ, HasRelDim I n → ∀ bs : Fin n → K → ℤ,
      intNum F I bs = cycEval (fun W => intNum F W bs) (topCycle I n)
def CutRegular.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ∀ n : ℕ, HasRelDim P (n + 1) → ∀ (s : MRing ι F) (b : K → ℕ), IsMultiHomog s b → s ∉ P →
      ∀ bs : Fin n → K → ℤ,
        intNum F P (Fin.snoc (α := fun _ => K → ℤ) bs (fun k => (b k : ℤ))) =
          cycEval (fun W => intNum F W bs) (divCycle P s)
def CutRational.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ∀ n : ℕ, HasRelDim P (n + 1) → ∀ (b : K → ℤ) (f g : MRing ι F), IsRatSection P b f g →
      ∀ bs : Fin n → K → ℤ,
        intNum F P (Fin.snoc (α := fun _ => K → ℤ) bs b) =
          cycEval (fun W => intNum F W bs) (ratDiv P f g)
def DivPrincipalDegree.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P → HasRelDim P 1 →
    ∀ (f g : MRing ι F) (d : K → ℕ), IsMultiHomog f d → IsMultiHomog g d → f ∉ P → g ∉ P →
      cycEval resDeg (ratDiv P f g) = 0
def ExistsForm.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ∀ b : K → ℤ, ∃ f g : MRing ι F, IsRatSection P b f g
def IntNumUnique.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (N : Ideal (MRing ι F) → (n : ℕ) → (Fin n → K → ℤ) → ℤ),
    IsIntersectionTheory F ι N →
    ∀ P : Ideal (MRing ι F), IsMultiProjPrime P → ∀ n : ℕ, HasRelDim P n →
      ∀ bs : Fin n → K → ℤ, N P n bs = intNum F P bs
def IntNumBaseChange.Statement : Prop :=
  ∀ (F : Type u) [Field F] (F' : Type u') [Field F'] [Algebra F F'] (K : Type v) [Fintype K]
    [DecidableEq K] (ι : K → Type w) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)),
    IsMultiHomogIdeal I →
    (∀ m : K → ℤ, hilbFn (I.map (MvPolynomial.map (algebraMap F F'))) m = hilbFn I m) ∧
    (∀ (n : ℕ) (bs : Fin n → K → ℤ),
      intNum F' (I.map (MvPolynomial.map (algebraMap F F'))) bs = intNum F I bs) ∧
    (I.IsPrime → (I.map (MvPolynomial.map (algebraMap F (RatFunc F)))).IsPrime)
def PFContracted.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (L : Type v') [Fintype L]
    [DecidableEq L] (ι : K → Type w) [∀ k, Fintype (ι k)] (ι₂ : L → Type w) [∀ l, Fintype (ι₂ l)]
    (P' : Ideal (MRing (Sum.elim ι ι₂) F)), IsMultiProjPrime P' →
    ∀ n n' : ℕ, HasRelDim (contractBlocks ι₂ P') n → HasRelDim P' n' → n < n' →
      ∀ bs : Fin n' → K → ℤ, intNum F P' (fun i => pullDeg (L := L) (bs i)) = 0
def PFDegree.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (L : Type v') [Fintype L]
    [DecidableEq L] (ι : K → Type w) [∀ k, Fintype (ι k)] (ι₂ : L → Type w) [∀ l, Fintype (ι₂ l)]
    (P' : Ideal (MRing (Sum.elim ι ι₂) F)) (hP' : IsMultiProjPrime P'),
    ∀ n : ℕ, HasRelDim (contractBlocks ι₂ P') n → HasRelDim P' n →
      ∀ bs : Fin n → K → ℤ,
        haveI := hP'.isPrime
        intNum F P' (fun i => pullDeg (L := L) (bs i)) =
          (fibreDeg ι₂ P' : ℤ) * intNum F (contractBlocks ι₂ P') bs
def PNProduct.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type v) [Fintype K] [DecidableEq K] (ι : K → Type w)
    [∀ k, Fintype (ι k)] (J : Type w) [Fintype J] [Nonempty J] (P : Ideal (MRing ι F)),
    IsMultiProjPrime P → ∀ n : ℕ, HasRelDim P n →
    ∀ r m : ℕ, r + m = n + Fintype.card J - 1 → ∀ cs : Fin r → K → ℤ,
      intNum F (addBlock J P)
          (Fin.append (fun _ : Fin m => (newBlockDeg : K ⊕ Unit → ℤ))
            (fun i => pullDeg (L := Unit) (cs i))) =
        if m = Fintype.card J - 1 then intNum F P cs else 0
section Examples
abbrev projCoords (D : ℕ) : Unit → Type := fun _ => Fin (D + 1)
end Examples
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers


