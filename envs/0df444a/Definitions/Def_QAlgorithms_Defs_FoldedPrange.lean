-- Prove2me | Definitions.Def_QAlgorithms_Defs_FoldedPrange
-- name    : QAlgorithms_Defs_FoldedPrange
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:38:30.140052+00:00
-- url     : https://prove2.me/theorems/cbe6fd6e-4049-43e2-b497-2ca5454ba881
-- title:
--   FoldedPrange
-- statement:
--   FoldedPrange
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\FoldedPrange.lean

import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_QAlgorithms_Defs_FoldedDQICircuits
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.FoldedOPI

/-- The first-J-target search with TOTAL fuel, not per-block fuel;
2610.02145 p.20 (4.11). Draws are independent uniform symbols with replacement. -/
def prangeSearch {F : Type*} [Field F] [Fintype F] {M h : ℕ}
    (A : BalancedInstance M (Fin h → F)) (J : ℕ) :
    ℕ → List (Fin h → F) → PMF (Option (List (Fin h → F)))
  | 0, found => PMF.pure (if found.length = J then some found else none)
  | fuel+1, found => if found.length = J then PMF.pure (some found) else
      if hi : found.length < M then
        (PMF.uniformOfFintype (Fin h → F)).bind fun z =>
          prangeSearch A J fuel
            (if z ∈ A.sets ⟨found.length,hi⟩ then found ++ [z] else found)
      else PMF.pure none

/-- Capped Prange output, with Lagrange interpolation at the actual selected points,
canonical coefficient padding, and zero on failure; 2610.02145 pp.19–20. -/
def prangeProcedure {F : Type*} [Field F] [Fintype F] {M h K : ℕ}
    (_hM : 0 < M) (_hh : 0 < h) (_lower : h ≤ K) (_upper : K ≤ M*h)
    (gamma : F) (_distinct : Function.Injective (fun t : Fin (M*h) => gamma^t.val))
    (A : BalancedInstance M (Fin h → F)) : PMF (Fin K → F) :=
  let J := K/h
  (prangeSearch A J (4*M) []).map fun found => match found with
    | none => 0
    | some values =>
        let alpha := fun t : Fin (J*h) => gamma^t.val
        let targets := fun t : Fin (J*h) =>
          (values.getD (finProdFinEquiv.symm t).1.val 0) (finProdFinEquiv.symm t).2
        let Q := Lagrange.interpolate Finset.univ alpha targets
        fun j => Q.coeff j.val

/-- Addressed classical block-membership access in the public basis;
2610.02145 pp.13,16,20. A valid address consists of its fixed block number
followed by all h encoded field values. Malformed addresses return false. -/
def prangeMembership {F : Type} [Field F] [Fintype F] {M h : ℕ}
    (E : OPI.publicFieldEncoding F) (A : BalancedInstance M (Fin h → F))
    (address : Complexity.Str) : Bool :=
  decide (∃ i : Fin M, ∃ z : Fin h → F,
    address = Complexity.encNat i.val ++
      (List.ofFn fun j => OPI.fieldBits E (z j)).flatten ∧ z ∈ A.sets i)

/-- The ideal capped-Prange law on the actual public field and computed dimensions;
2610.02145 pp.19–20. Public primitivity supplies distinct nonzero evaluation
points; this law retains the total 4M cap and zero-polynomial fallback. -/
def publicPrangeLaw (P : PublicDomain) (E : PublicFieldData P)
    (distinct : Function.Injective (fun t : Fin (P.M*(P.M+2)) => E.gamma^t.val))
    (dimensions : publicParameters P 3 ≤ P.M*(P.M+2))
    (A : BalancedInstance P.M (Fin (P.M+2) → publicField P)) :
    PMF (Fin (publicParameters P 3) → publicField P) :=
  prangeProcedure P.M_pos (by omega)
    (by simpa [publicParameters, Nat.cast_mul, Nat.cast_add] using P.enough)
    dimensions E.gamma distinct A

/-- Concrete priced uniform classical Prange realization;
2610.02145 pp.16,20. Agreement is with the capped law, and all interpolation
and sampling must execute in the bit/tape program. This subclass is used only
for the efficient upper bound, never for the unrestricted lower bound. -/
structure PrangeRealization (R : ℚ) where
  rate_domain : 0 < R ∧ R < 1
  construct : OPI.BitOracleProgram
  publicOnly : OPI.IsPublicPreprocessor construct
  program : FoldedOPI.PublicDomain → OPI.BitOracleProgram
  encoding : FoldedOPI.PublicDomain → Complexity.Str
  constructorOutput : FoldedOPI.PublicDomain → Complexity.Str
  serialization : ∀ P, constructorOutput P = OPI.bitProgramSerialization (program P)
  publicInput : ∀ P, encoding P = LocalHamiltonian.encBin P.M ++
    LocalHamiltonian.encBin P.u ++ LocalHamiltonian.encRat P.rate
  fieldData : (P : FoldedOPI.PublicDomain) → PublicFieldData P
  distinct : ∀ P, Function.Injective
    (fun t : Fin (P.M*(P.M+2)) => (fieldData P).gamma^t.val)
  dimensions : ∀ P, publicParameters P 3 ≤ P.M*(P.M+2)
  transitionCap : FoldedOPI.PublicDomain → ℕ
  bound : Polynomial ℕ
  executionBound : ∀ P, P.rate = R → transitionCap P ≤ bound.eval P.M ∧
    ∀ A : BalancedInstance P.M (Fin (P.M+2) → publicField P), ∀ random : ℕ → Bool,
      let result := OPI.bitProgramExecution (program P) (encoding P)
        (prangeMembership (fieldData P).encoding A) random (transitionCap P)
      result.status = some true ∧ result.time ≤ bound.eval P.M ∧
        result.visited.card ≤ bound.eval P.M ∧ result.calls.length ≤ 4*P.M
  realizes : ∀ P, P.rate = R →
    ∀ A : BalancedInstance P.M (Fin (P.M+2) → publicField P),
      (OPI.bitExecutionLaw (program P) (encoding P)
        (prangeMembership (fieldData P).encoding A) (transitionCap P)).map
          (fun result => OPI.coefficientOutput (fieldData P).encoding
            (publicParameters P 3) result.output) =
        publicPrangeLaw P (fieldData P) (distinct P) (dimensions P) A
  generated : ∀ P, P.rate = R →
    ∃ fuel, fuel ≤ bound.eval P.M ∧
      let result := OPI.bitProgramExecution construct (encoding P)
        (fun _ => false) (fun _ => false) fuel
      result.status = some true ∧ result.output = constructorOutput P ∧
        result.time ≤ bound.eval P.M ∧ result.visited.card ≤ bound.eval P.M

/-- Averaged score event over independent half-size subsets and an unrestricted
randomized decision tree fixed before those subsets;
2610.02145 pp.16,21,24. No computation/advice/description-size restriction. -/
def classicalScoreLaw {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {M h K : ℕ} (hM : 0 < M) (gamma : F)
    [Nonempty {A : Finset (Fin h → F) // 2*A.card = Fintype.card (Fin h → F)}]
    (algorithm : RandDecisionTree (Fin M × (Fin h → F)) Bool (Fin K → F))
    (event : ℝ → Prop) : ℝ :=
  ∑ sets : Fin M → {A : Finset (Fin h → F) // 2*A.card = Fintype.card (Fin h → F)},
    ((PMF.uniformOfFintype _ sets).toReal)*
      ((algorithm.map fun tree =>
        tree.eval (fun iz => decide (iz.2 ∈ (sets iz.1).val))).toOuterMeasure
          {x | event (score hM gamma ⟨fun i => (sets i).val,fun i => (sets i).property⟩ x)}).toReal

example {F : Type} [Field F] [Fintype F] {M h : ℕ}
    (E : OPI.publicFieldEncoding F) (A : BalancedInstance M (Fin h → F))
    (i : Fin M) (z : Fin h → F) (hz : z ∈ A.sets i) :
    prangeMembership E A (Complexity.encNat i.val ++
      (List.ofFn fun j => OPI.fieldBits E (z j)).flatten) = true := by
  simp only [prangeMembership, decide_eq_true_eq]
  exact ⟨i,z,rfl,hz⟩

example {F : Type*} [Field F] [Fintype F] {M h : ℕ}
    (A : BalancedInstance M (Fin h → F)) : prangeSearch A 0 0 [] = PMF.pure (some []) := by
  simp [prangeSearch]

example {F : Type*} [Field F] [Fintype F] {M h : ℕ}
    (A : BalancedInstance M (Fin h → F)) :
    prangeSearch A 1 0 [] = PMF.pure none := by simp [prangeSearch]


end QAlgorithms.FoldedOPI


