-- Prove2me | Definitions.Def_SatisfiableOrderingCSP_Optimal_Computation
-- name    : SatisfiableOrderingCSP_Optimal_Computation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T17:45:50.726452+00:00
-- url     : https://prove2.me/theorems/4b43f5c0-9b4c-411e-84c6-974d7df8a4ad
-- title:
--   Concrete input encodings and arithmetic, bit, and sampling execution
-- statement:
--   Natural numbers use self-delimiting binary codes and rational weights use a sign and binary numerator and denominator. The finite vertex list is explicit; constraint records include arity, a truth table of satisfying permutations and the ordered scope. RationalInstance supplies exact rational witnesses for the mathematical real weights. Bit approximation is a fixed CookPvsNP polynomial-time function from encoded input to an encoded permutation, with correctness on the indicated promise. Arithmetic approximation uses a finite imported RAM program restricted to rational constants and field operations; one polynomial bound applies to all real-weight inputs. The random machine adds one uniform finite-sampling primitive to the same charged-step semantics. Linear implementation forbids real-register instructions, bounds all natural words by a fixed polynomial along every run, halts in C(n+m+1) steps, and outputs exactly the mixture law on a pair of relaxed orders. Each array access, comparison and update is charged. Rational mixtures carry explicit rational coefficients and finite output encodings. This word model assumes unit-cost uniform finite sampling; fair-bit implementation of a fixed rational sample has expected constant cost and is not a worst-case bit-time assertion.
-- source:
--   Yury Makarychev (2026), Optimal Approximation Algorithms For Satisfiable Ordering CSPs, held STOC 2027 submission (not an acceptance claim), sha256:e49b7905adb41a36b93abcbd7818d1b18ca86a77dff069da884ba2f8e85775cc; citation_basis: published; Theorems 1.3, 4.4 and Appendix A.6; pp. 5, 18, 62–63 (PDF 8, 21, 65–66)

import Definitions.Def_SatisfiableOrderingCSP_Optimal_Transformations
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_NearLinearRSP_TwoResources_Machine

open scoped BigOperators

namespace SatisfiableOrderingCSP.Optimal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Self-delimiting binary words, including zero. -/
def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def encodeRat (q : ℚ) : List Bool :=
  [decide (q < 0)] ++ encodeNat q.num.natAbs ++ encodeNat q.den

def Predicate.table (φ : Predicate) : List ℕ :=
  ((List.finRange φ.arity).permutations).map fun l =>
    if ∃ τ ∈ φ.sat, List.ofFn (fun i => τ i) = l then 1 else 0

def Constraint.data {n : ℕ} (C : Constraint n) : List ℕ :=
  [C.predicate.arity] ++ C.predicate.table ++ List.ofFn (fun j => (C.scope j).val)

def Instance.data (I : Instance) : List ℕ :=
  [I.n, I.m] ++ (List.finRange I.m).flatMap (fun c => (I.constraint c).data)

structure RationalInstance where
  instanceData : Instance
  rationalWeight : Fin instanceData.m → ℚ
  weight_eq : ∀ c, instanceData.weight c = rationalWeight c

def RationalInstance.encode (I : RationalInstance) : List Bool :=
  List.replicate I.instanceData.n true ++ [false] ++
  I.instanceData.data.flatMap encodeNat ++
  (List.finRange I.instanceData.m).flatMap (fun c => encodeRat (I.rationalWeight c))

def encodeOrder {n : ℕ} (π : Order n) : List Bool :=
  (List.finRange n).flatMap (fun i => encodeNat (π i).val)

def BitApproximation (Lg : Language) (β : ℝ) (promise : Instance → Prop) : Prop :=
  ∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
    ∀ I : RationalInstance, I.instanceData.Over Lg → promise I.instanceData →
      ∃ π : Order I.instanceData.n, f I.encode = encodeOrder π ∧ β ≤ I.instanceData.score π

open NearLinearRSP.TwoResources

/-- Restrict the imported RAM to exact field arithmetic and rational constants. -/
def ArithmeticProgram (P : Program) : Prop :=
  ∀ i ∈ P, match i with
  | .realConst _ c => ∃ q : ℚ, c = q
  | .exp _ _ => False
  | _ => True

/-- The randomized scheme needs only words and uniform finite sampling; it does not
inspect the real weights. Bounded word values are enforced along every run below. -/
def WordProgram (P : Program) : Prop :=
  ∀ i ∈ P, match i with
  | .realConst _ _ | .realCopy _ _ | .realOp _ _ _ _ | .exp _ _ |
    .realBranch _ _ _ _ _ | .loadReal _ _ | .storeReal _ _ | .inputReal _ _ => False
  | _ => True

def Instance.ramInput (I : Instance) : RAMInput :=
  ⟨fun a => I.data[a]?.getD 0,
    fun a => (List.ofFn I.weight)[a]?.getD 0⟩

def OutputOrder {n : ℕ} (s : RAMState) (π : Order n) : Prop :=
  ∀ i, s.nm i.val = (π i).val

def ArithmeticApproximation (Lg : Language) (β : ℝ) (promise : Instance → Prop) : Prop :=
  ∃ (P : Program) (k : ℕ), ArithmeticProgram P ∧
    ∀ I : Instance, I.Over Lg →
      ∃ t ≤ (I.n + I.m + 1)^k + k, ∃ s,
        Execution P I.ramInput initialState s t ∧
        ∃ π : Order I.n, OutputOrder s π ∧ (promise I → β ≤ I.score π)

/-- A finite table of sampling overrides; each samples a uniform integer below the
specified natural register and costs one operation. Zero bounds sample zero. -/
structure RandomProgram where
  core : Program
  samples : List (Option (ℕ × ℕ × ℕ))

def RandomProgram.sampleAt (P : RandomProgram) (s : RAMState) : Option (ℕ × ℕ × ℕ) :=
  P.samples[s.pc]?.getD none

def sampledState (s : RAMState) (dst next value : ℕ) : RAMState :=
  { s with pc := next, nr := Function.update s.nr dst value }

/-- Finite operational expectation after t primitive steps; no user supplied cost field. -/
def RandomProgram.expect (P : RandomProgram) (input : RAMInput)
    (post : RAMState → ℝ) : ℕ → RAMState → ℝ
  | 0, s => post s
  | t + 1, s =>
    if s.halted then post s else
    match P.sampleAt s with
    | none => P.expect input post t (ramStep P.core input s)
    | some (dst,bound,next) =>
      (∑ j : Fin (max 1 (s.nr bound)),
        P.expect input post t (sampledState s dst next j.val)) / (max 1 (s.nr bound) : ℝ)

def RandomProgram.AllRuns (P : RandomProgram) (input : RAMInput)
    (post : RAMState → Prop) : ℕ → RAMState → Prop
  | 0, s => post s
  | t + 1, s =>
    if s.halted then post s else
    match P.sampleAt s with
    | none => P.AllRuns input post t (ramStep P.core input s)
    | some (dst,bound,next) => ∀ j : Fin (max 1 (s.nr bound)),
        P.AllRuns input post t (sampledState s dst next j.val)

/-- The word bound prevents unbounded integer arithmetic from being a free operation.
Real weights are read-only data for the randomized ordering procedure. -/
def WordBound (B : ℕ) (s : RAMState) : Prop :=
  (∀ i, s.nr i < B) ∧ (∀ i, s.nm i < B)

def LinearMixtureImplementation (Lg : Language) (ν : Mixture) : Prop :=
  ∃ (P : RandomProgram) (C k : ℕ), WordProgram P.core ∧
    ∀ I : Instance, I.Over Lg → I.CanonicallyFeasible →
      ∃ L R : Order I.n, I.RelaxedOrders L R ∧
        P.AllRuns I.ramInput
          (fun s => s.halted = true ∧ ∃ σ : Order I.n, OutputOrder s σ)
          (C * (I.n + I.m + 1)) initialState ∧
        (∀ t ≤ C * (I.n + I.m + 1),
          P.AllRuns I.ramInput (WordBound ((I.n + I.m + 2)^k)) t initialState) ∧
        ∀ σ : Order I.n,
          P.expect I.ramInput (fun s => if OutputOrder s σ then 1 else 0)
            (C * (I.n + I.m + 1)) initialState = ν.law L R σ

/-- A finite rational scheme carries explicit rational coefficients for output encoding. -/
structure RationalMixture where
  mixture : Mixture
  outer : Fin mixture.size → ℚ
  inner : (a : Fin mixture.size) → Fin (mixture.combination a).blocks → ℚ
  outer_eq : ∀ a, mixture.probability a = outer a
  inner_eq : ∀ a b, (mixture.combination a).probability b = inner a b

def blockCode : BlockLabel → ℕ
  | .IL => 0 | .DL => 1 | .IR => 2 | .DR => 3 | .U => 4

def RationalMixture.encode (ν : RationalMixture) : List Bool :=
  encodeNat ν.mixture.size ++ (List.finRange ν.mixture.size).flatMap fun a =>
    encodeRat (ν.outer a) ++ encodeNat (ν.mixture.combination a).blocks ++
      (List.finRange (ν.mixture.combination a).blocks).flatMap fun b =>
        encodeNat (blockCode ((ν.mixture.combination a).label b)) ++ encodeRat (ν.inner a b)

def Language.Encoding (Lg : Language) (code : List Bool) : Prop :=
  ∃ l : List Predicate, l.Nodup ∧ l.toFinset = Lg.predicates ∧
    code = encodeNat l.length ++ l.flatMap (fun φ =>
      encodeNat φ.arity ++ φ.table.flatMap encodeNat)

def MachineComputes (f : List Bool → List Bool) : Prop :=
  ∃ (Γ : Type) (_ : Fintype Γ) (ι : Bool ↪ Γ) (M : CookPvsNP.TM Γ),
    ∀ x, ∃ t, M.HaltsWithin t (x.map ι) ∧
      M.output (M.run t (M.init (x.map ι))) = (f x).map (some ∘ ι)

end
end SatisfiableOrderingCSP.Optimal


