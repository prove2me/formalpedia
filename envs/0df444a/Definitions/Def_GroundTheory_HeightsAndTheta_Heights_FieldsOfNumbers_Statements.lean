-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:15:52.453105+00:00
-- url     : https://prove2.me/theorems/3cdb7eb8-e9d2-4b1e-9d03-5c17df5d1ea8
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/Statements.lean

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
section Objects
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
def relDim [Fintype K] (I : Ideal (MRing ι F)) : WithBot (WithTop ℤ) :=
  WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d)
    (ringKrullDim (MRing ι F ⧸ I))
def EventuallyPoly (h : (K → ℤ) → ℤ) (p : MvPolynomial K ℚ) : Prop :=
  ∀ᶠ m in Filter.atTop, (h m : ℚ) = MvPolynomial.eval (fun k => (m k : ℚ)) p
def homFracDegZero (P : Ideal (MRing ι F)) [P.IsPrime] :
    IntermediateField F (FractionRing (MRing ι F ⧸ P)) :=
  IntermediateField.adjoin F {x | ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧
    IsMultiHomog g b ∧ g ∉ P ∧
    x = algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)}
open Classical in

def resDeg (P : Ideal (MRing ι F)) : ℕ :=
  if h : P.IsPrime then haveI := h; Module.finrank F (homFracDegZero P) else 0
open Classical in

def topCycle [Fintype K] (I : Ideal (MRing ι F)) (n : ℕ) (W : Ideal (MRing ι F)) : ℤ :=
  if h : W ∈ I.minimalPrimes ∧ IsRelevant W ∧ relDim W = n then
    haveI : W.IsPrime := h.1.1.1
    ((multAt I W).toNat : ℤ)
  else 0
end Objects
section Blocks
variable {K K' : Type*} {F : Type*} [Field F]
def blockIncl (j : K ↪ K') (ι' : K' → Type*) : (Σ k, ι' (j k)) → (Σ k', ι' k') :=
  fun v => ⟨j v.1, v.2⟩
def pullDeg (j : K ↪ K') (b : K → ℤ) : K' → ℤ :=
  Function.extend j b 0
def contractPrime (j : K ↪ K') {ι' : K' → Type*} (P' : Ideal (MRing ι' F)) :
    Ideal (MRing (fun k => ι' (j k)) F) :=
  P'.comap (rename (blockIncl j ι'))
instance contractPrime.isPrime (j : K ↪ K') {ι' : K' → Type*} (P' : Ideal (MRing ι' F))
    [P'.IsPrime] : (contractPrime j P').IsPrime :=
  Ideal.comap_isPrime _ _
def contractQuot (j : K ↪ K') {ι' : K' → Type*} (P' : Ideal (MRing ι' F)) :
    (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') →ₐ[F] (MRing ι' F ⧸ P') :=
  Ideal.quotientMapₐ P' (rename (blockIncl j ι')) le_rfl
def contractFracMap (j : K ↪ K') {ι' : K' → Type*} (P' : Ideal (MRing ι' F)) [P'.IsPrime] :
    FractionRing (MRing (fun k => ι' (j k)) F ⧸ contractPrime j P') →ₐ[F]
      FractionRing (MRing ι' F ⧸ P') :=
  IsFractionRing.liftAlgHom
    (g := (IsScalarTower.toAlgHom F (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      (contractQuot j P'))
    ((IsFractionRing.injective (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))).comp
      (Ideal.quotientMap_injective))
def relDeg [DecidableEq K] [DecidableEq K'] (j : K ↪ K') {ι' : K' → Type*}
    (P' : Ideal (MRing ι' F)) [P'.IsPrime] : ℕ :=
  IntermediateField.relfinrank ((homFracDegZero (contractPrime j P')).map (contractFracMap j P'))
    (homFracDegZero P')
def addBlock (ι : K → Type) (N : ℕ) : Option K → Type :=
  fun o => Option.elim o (Fin (N + 1)) ι
instance addBlock.fintype (ι : K → Type) [∀ k, Fintype (ι k)] (N : ℕ) :
    ∀ o, Fintype (addBlock ι N o)
  | none => (inferInstance : Fintype (Fin (N + 1)))
  | some k => (inferInstance : Fintype (ι k))
instance addBlock.nonempty (ι : K → Type) [∀ k, Nonempty (ι k)] (N : ℕ) :
    ∀ o, Nonempty (addBlock ι N o)
  | none => (inferInstance : Nonempty (Fin (N + 1)))
  | some k => (inferInstance : Nonempty (ι k))
def addBlockIncl (ι : K → Type) (N : ℕ) : (Σ k, ι k) → (Σ o, addBlock ι N o) :=
  fun v => ⟨some v.1, v.2⟩
def addBlockPrime {ι : K → Type} (N : ℕ) (P : Ideal (MRing ι F)) :
    Ideal (MRing (addBlock ι N) F) :=
  P.map (rename (addBlockIncl ι N))
def newBlockDeg : Option K → ℤ :=
  fun o => Option.elim o 1 (fun _ => 0)
end Blocks
def GradedFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)) (m : K → ℕ),
    FiniteDimensional F (gradedPiece I m) ∧
      hilbFn I (fun k => (m k : ℤ)) = Module.finrank F (gradedPiece I m)
def HilbExactDivide.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I →
    ∀ (c : K → ℕ) (s : MRing ι F), IsMultiHomog s c → ∀ m : K → ℤ,
      hilbFn I m - hilbFn (I.colon (Ideal.span {s})) (m - fun k => (c k : ℤ)) =
        hilbFn (I ⊔ Ideal.span {s}) m
def PolyOfDiffs.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (h : (K → ℤ) → ℤ) (d : ℕ),
    (∀ k, ∃ q : MvPolynomial K ℚ, (q = 0 ∨ q.totalDegree < d) ∧
      EventuallyPoly (diffStep (Pi.single k 1) h) q) →
    ∃ p : MvPolynomial K ℚ, p.totalDegree ≤ d ∧ EventuallyPoly h p
def HilbEventuallyPoly.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I →
    ∃ p : MvPolynomial K ℚ, EventuallyPoly (hilbFn I) p
def HilbDegreeBound.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I →
    (IsRelevant I → ∀ p : MvPolynomial K ℚ, EventuallyPoly (hilbFn I) p → p ≠ 0 →
        (p.totalDegree : WithBot (WithTop ℤ)) ≤ relDim I) ∧
      (¬ IsRelevant I → ∀ᶠ m in Filter.atTop, hilbFn I m = 0)
def MixedDiffConst.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I → IsRelevant I →
    ∀ n : ℕ, relDim I = n →
      (∀ bs : Fin n → K → ℤ, ∀ᶠ m in Filter.atTop, mixedDiff bs (hilbFn I) m = intNum F I bs) ∧
      (∀ r : ℕ, n < r → ∀ bs : Fin r → K → ℤ,
        ∀ᶠ m in Filter.atTop, mixedDiff bs (hilbFn I) m = 0)
def IntNumSymm.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)) (n : ℕ) (bs : Fin n → K → ℤ)
    (σ : Equiv.Perm (Fin n)), intNum F I (bs ∘ σ) = intNum F I bs
def IntNumAdd.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I → IsRelevant I →
    ∀ n : ℕ, relDim I = n → ∀ (bs : Fin n → K → ℤ) (i : Fin n) (b b' : K → ℤ),
      intNum F I (Function.update bs i (b + b')) =
        intNum F I (Function.update bs i b) + intNum F I (Function.update bs i b')
def IntNumZeroSlot.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)),
    (∀ (n : ℕ) (bs : Fin n → K → ℤ) (i : Fin n), bs i = 0 → intNum F I bs = 0) ∧
      (IsMultiHomogIdeal I → ∀ (n : ℕ) (bs : Fin n → K → ℤ), relDim I < n → intNum F I bs = 0)
def IntNumBase.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P), relDim P = 0 →
    haveI := hP.isPrime
    FiniteDimensional F (homFracDegZero P) ∧
      intNum F P (n := 0) ![] = Module.finrank F (homFracDegZero P)
open Classical in

def PrimeFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I →
    ∃ (r : ℕ) (Q : Fin r → Ideal (MRing ι F)) (c : Fin r → K → ℕ),
      (∀ j, (Q j).IsPrime ∧ IsMultiHomogIdeal (Q j) ∧ I ≤ Q j) ∧
      (∀ᶠ m in Filter.atTop, hilbFn I m = ∑ j, hilbFn (Q j) (m - fun k => (c j k : ℤ))) ∧
      (∀ W (hW : W ∈ I.minimalPrimes), IsRelevant W → relDim W = relDim I →
        haveI : W.IsPrime := hW.1.1
        ((((Finset.univ.filter fun j => Q j = W).card : ℕ) : ℕ∞) = multAt I W)) ∧
      (∀ j, ¬ IsRelevant (Q j) ∨ relDim (Q j) < relDim I ∨
        (Q j ∈ I.minimalPrimes ∧ relDim (Q j) = relDim I))
def MultEqualsCoeff.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)), IsMultiHomogIdeal I → IsRelevant I →
    ∀ n : ℕ, relDim I = n → ∀ bs : Fin n → K → ℤ,
      intNum F I bs = cycEval (fun W => intNum F W bs) (topCycle I n)
def CutRegular.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ (c : K → ℕ) (s : MRing ι F), IsMultiHomog s c → s ∉ P →
    ∀ bs : Fin n → K → ℤ,
      intNum F P (Fin.snoc (α := fun _ => K → ℤ) bs (fun k => (c k : ℤ))) =
        cycEval (fun W => intNum F W bs) (divCycle P s)
def CutRational.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ∀ n : ℕ, relDim P = (n + 1 : ℕ) → ∀ (bf bg : K → ℕ) (f g : MRing ι F),
    IsMultiHomog f bf → IsMultiHomog g bg → f ∉ P → g ∉ P → ∀ bs : Fin n → K → ℤ,
      intNum F P (Fin.snoc (α := fun _ => K → ℤ) bs (fun k => (bf k : ℤ) - bg k)) =
        cycEval (fun W => intNum F W bs) (ratDiv P f g)
def DivPrincipalDegree.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P → relDim P = 1 →
    ∀ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b → IsMultiHomog g b → f ∉ P → g ∉ P →
      cycEval (fun x => (resDeg x : ℤ)) (ratDiv P f g) = 0
def ExistsForm.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P → ∀ b : K → ℤ,
    ∃ (bf bg : K → ℕ) (f g : MRing ι F), IsMultiHomog f bf ∧ IsMultiHomog g bg ∧ f ∉ P ∧
      g ∉ P ∧ (fun k => (bf k : ℤ) - bg k) = b
structure IsIntersectionTheory {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
    (F : Type*) [Field F] (N : Ideal (MRing ι F) → (n : ℕ) → (Fin n → K → ℤ) → ℤ) : Prop where
  base : ∀ P : Ideal (MRing ι F), IsMultiProjPrime P → relDim P = 0 → N P 0 ![] = resDeg P
  cut : ∀ (P : Ideal (MRing ι F)) (n : ℕ), IsMultiProjPrime P → relDim P = (n + 1 : ℕ) →
    ∀ (bf bg : K → ℕ) (f g : MRing ι F), IsMultiHomog f bf → IsMultiHomog g bg → f ∉ P → g ∉ P →
    ∀ bs : Fin n → K → ℤ,
      N P (n + 1) (Fin.snoc (α := fun _ => K → ℤ) bs (fun k => (bf k : ℤ) - bg k)) =
        cycEval (fun W => N W n bs) (ratDiv P f g)
def IntNumUnique.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (N : Ideal (MRing ι F) → (n : ℕ) → (Fin n → K → ℤ) → ℤ),
    IsIntersectionTheory F N → ∀ P : Ideal (MRing ι F), IsMultiProjPrime P →
    ∀ n : ℕ, relDim P = n → ∀ bs : Fin n → K → ℤ, N P n bs = intNum F P bs
def IntNumBaseChange.Statement : Prop :=
  (∀ (F : Type u) [Field F] (F' : Type v) [Field F'] [Algebra F F'] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι F)),
    (∀ m, hilbFn (I.map (MvPolynomial.map (algebraMap F F'))) m = hilbFn I m) ∧
      ∀ (n : ℕ) (bs : Fin n → K → ℤ),
        intNum F' (I.map (MvPolynomial.map (algebraMap F F'))) bs = intNum F I bs) ∧
  (∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    IsMultiProjPrime (P.map (MvPolynomial.map (algebraMap F (RatFunc F)))))
def ProjectionFormulaContracted.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)), IsMultiProjPrime P' → ∀ n : ℕ, relDim P' = n →
    relDim (contractPrime j P') < n → ∀ bs : Fin n → K → ℤ,
      intNum F P' (fun i => pullDeg j (bs i)) = 0
def ProjectionFormulaDegree.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P'), ∀ n : ℕ, relDim P' = n →
    relDim (contractPrime j P') = n → ∀ bs : Fin n → K → ℤ,
      haveI := hP'.isPrime
      (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ homFracDegZero P' ∧
        intNum F P' (fun i => pullDeg j (bs i)) =
          relDeg j P' * intNum F (contractPrime j P') bs
def ProductWithProjectiveSpace.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)), IsMultiProjPrime P →
    ∀ e N r m : ℕ, relDim P = e → r + m = e + N → ∀ cs : Fin r → K → ℤ,
      intNum F (addBlockPrime N P)
          (Fin.append (fun _ : Fin m => (newBlockDeg : Option K → ℤ))
            (fun i => pullDeg Function.Embedding.some (cs i))) =
        if m = N then intNum F P cs else 0
end
end GroundTheory.Heights₂.Heights.FieldNumbers


