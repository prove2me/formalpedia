-- Prove2me | Definitions.Def_DynEdgeColorLLL_Main_Supplement_DynamicLLL
-- name    : DynEdgeColorLLL_Main_Supplement_DynamicLLL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:02:23.99959+00:00
-- url     : https://prove2.me/theorems/4027f38a-49e2-4568-b2e5-6e63e5ff55dd
-- title:
--   Live-variable protocol, correct primitive interfaces and dynamic LLL specification
-- statement:
--   The live-variable protocol starts with no live variables and empty clauses. An operation introduces a fresh isolated variable, removes an isolated variable, or toggles a finite set of distinct clause–variable pairs. Birth identifiers range over $\operatorname{Fin}N$, where $N$ is arbitrary and is never fixed in the program. A reintroduced name can use a fresh birth identifier. Each variable has an arbitrary measurable value space and probability law; the truth-table family is the published one.
--
--   At each completed instance boundary, uniform parameters $k,s\ge1$, $d\ge2$, $k\le d$, $0<q<1/2$ and a fixed finite $K_0\ge0$ satisfy the asymmetric assumption (1), with a possibly different witness at each boundary. Intermediate incidences inside a batch need not satisfy that assumption. Primitive implementations are correct on every legal supplied assignment, have private mutable state, use fresh independent randomness, and have uniform finite expected costs $T_{\rm sample},T_{\rm eval},T_{\rm update}\ge1$, with $T_{\rm update}\le T_{\rm eval}$. Their joint reply-and-cost maps are measurable.
--
--   The dynamic specification reads values from the program's actual output cells. For $\overline K=\max(1,K_0)$, the batch bounds have the form
--
--   $$\mathbb E[\mathrm{time}]\le C_t|\mathcal B|\bigl[T_{\rm update}+\overline K k^2s^2dq(T_{\rm eval}+T_{\rm sample})\bigr],\qquad
--   \mathbb E^*[\mathrm{recourse}]\le C_r\overline K|\mathcal B|s^2q.$$
--
--   Recourse counts surviving live variables whose completed reported values differ. Upper expectation $\mathbb E^*$ agrees with expectation for measurable recourse, and does not require a measurable equality relation on arbitrary value domains. Completion and satisfying output are almost-sure conclusions; each operation's charged cost is measurable and its expectation is over the original persistent tape. Isolated introduction and removal have their separate time bounds. This definition is only an operational specification; it does not assert that a program meets it.
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), §3.1, Theorem 2 and §3.4, printed pp. 9–10, 14–16 (PDF pp. 11–12, 16–18)

import Definitions.Def_DynEdgeColorLLL_Main_LLLTranscript
import Definitions.Def_DynEdgeColorLLL_Main_Supplement_OracleRAM

set_option autoImplicit false

namespace DynEdgeColorLLL.Main.Supplement

open MeasureTheory
open scoped ENNReal
open scoped OracleRAM

/-! The operation protocol, primitive implementation contract and observable guarantees
for Theorem 2. Fin N is the set of birth IDs in any finite history, not a bound
built into the code. A removed ID is never born again; a reinsertion uses a fresh ID.
Dormant variables have no clause incidences. Parameters and the operation are input,
never oracle implementations, truth tables or advance knowledge of the history. -/

inductive Operation (N m : ℕ) where
  | introduce (x : Fin N)
  | remove (x : Fin N)
  | batch (B : Finset (Fin m × Fin N))

structure Instance (N m : ℕ) where
  live : Finset (Fin N)
  born : Finset (Fin N)
  vbl : Fin m → Finset (Fin N)

def emptyInstance (N m : ℕ) : Instance N m := ⟨∅, ∅, fun _ => ∅⟩

def applyOperation {N m : ℕ} (I : Instance N m) : Operation N m → Instance N m
  | .introduce x => { I with live := insert x I.live, born := insert x I.born }
  | .remove x => { I with live := I.live.erase x }
  | .batch B => { I with vbl := applyBatch I.vbl B }

def instanceAt {N m : ℕ} (history : List (Operation N m)) (t : ℕ) : Instance N m :=
  (history.take t).foldl applyOperation (emptyInstance N m)

def LegalOperation {N m : ℕ} (I : Instance N m) : Operation N m → Prop
  | .introduce x => x ∉ I.born
  | .remove x => x ∈ I.live ∧ ∀ C, x ∉ I.vbl C
  | .batch B => ∀ p ∈ B, p.2 ∈ I.live

def LegalHistory {N m : ℕ} {Ω : Fin N → Type*} [∀ x, MeasurableSpace (Ω x)]
    (D : (x : Fin N) → Measure (Ω x)) (f : TruthTables (Fin N) Ω m)
    (k s d : ℕ) (q K₀ : ℝ) (history : List (Operation N m)) : Prop :=
  k ≤ d ∧ 0 < q ∧ q < 1 / 2 ∧ 0 ≤ K₀ ∧
  (∀ t, t < history.length → ∀ op, history[t]? = some op →
    LegalOperation (instanceAt history t) op) ∧
  ∀ t, t ≤ history.length →
    (∀ C, (instanceAt history t).vbl C ⊆ (instanceAt history t).live) ∧
    HasParams (instanceAt history t).vbl k s d ∧
    ∃ xw : Fin m → ℝ, Assumption1 D f (instanceAt history t).vbl d q K₀ xw

abbrev Value {N : ℕ} (Ω : Fin N → Type*) := (x : Fin N) × Ω x

def valueTag {N : ℕ} {Ω : Fin N → Type*} (a : Value Ω) : ℕ := a.1.val

def argumentSet {N : ℕ} {Ω : Fin N → Type*} (args : List (Value Ω)) : Finset (Fin N) :=
  (args.map Sigma.fst).toFinset

def WellFormedArgs {N : ℕ} {Ω : Fin N → Type*} (args : List (Value Ω)) : Prop :=
  (args.map Sigma.fst).Nodup

def Agrees {N : ℕ} {Ω : Fin N → Type*} (σ : (x : Fin N) → Ω x)
    (args : List (Value Ω)) : Prop := ∀ a ∈ args, σ a.1 = a.2

def CorrectBit {N m : ℕ} {Ω : Fin N → Type*} (f : TruthTables (Fin N) Ω m)
    (C : Fin m) (args : List (Value Ω)) (b : Bool) : Prop :=
  ∀ σ : (x : Fin N) → Ω x, Agrees σ args → (b = true ↔ f C (argumentSet args) σ)

def insertArgument {N : ℕ} {Ω : Fin N → Type*} (args : List (Value Ω))
    (x : Fin N) (v : Option (Value Ω)) : List (Value Ω) :=
  v.toList ++ args.filter (fun a => a.1 ≠ x)

/-- A legal primitive request relative to a private clause-store view. The clause store
need not satisfy the LLL criterion between the individual toggles of a batch. -/
def LegalRequest {N m : ℕ} {Ω : Fin N → Type*} {H : Type*}
    (view : H → Fin m → List (Value Ω)) (h : H) (req : OracleRAM.Request (Value Ω)) : Prop :=
  (req.1 = 0 ∧ req.2.2.1 < N) ∨
  (req.1 = 1 ∧ ∃ C : Fin m, req.2.1 = C.val ∧ WellFormedArgs req.2.2.2.1 ∧
    argumentSet req.2.2.2.1 = argumentSet (view h C)) ∨
  (req.1 = 2 ∧ ∃ (C : Fin m) (x : Fin N), req.2.1 = C.val ∧ req.2.2.1 = x.val ∧
    match req.2.2.2.2 with
    | none => x ∈ argumentSet (view h C)
    | some a => a.1 = x ∧ x ∉ argumentSet (view h C))

/-- Semantic correctness of a single returned reply. All private mutations other than
the visible clause-store view are unrestricted. Samples have their exact laws separately. -/
def CorrectReply {N m : ℕ} {Ω : Fin N → Type*} {H : Type*}
    (f : TruthTables (Fin N) Ω m) (view : H → Fin m → List (Value Ω))
    (h : H) (req : OracleRAM.Request (Value Ω)) (ans : OracleRAM.Response (Value Ω) H) : Prop :=
  if req.1 = 0 then
    (∃ a, ans.1 = some a ∧ a.1.val = req.2.2.1) ∧ view ans.2.2.1 = view h
  else if req.1 = 1 then
    (∀ C : Fin m, C.val = req.2.1 → CorrectBit f C req.2.2.2.1 ans.2.1) ∧
    view ans.2.2.1 = view h
  else
    ∀ (C : Fin m) (x : Fin N), C.val = req.2.1 → x.val = req.2.2.1 →
      view ans.2.2.1 = Function.update (view h) C
        (insertArgument (view h C) x req.2.2.2.2) ∧
      CorrectBit f C (view ans.2.2.1 C) ans.2.1

def primitiveBound {A : Type*} (Ts Te Tu : ℝ) (req : OracleRAM.Request A) : ℝ≥0∞ :=
  ENNReal.ofReal (if req.1 = 0 then Ts else if req.1 = 1 then Te else Tu)

/-- Correct implementations of the three §3.1 interfaces. The specification is uniform
over private states and legal supplied assignments, so a call after any caller history
uses fresh private coins with the same conditional bound. No runtime or satisfaction
guarantee of the dynamic algorithm is a field of this predicate. -/
def CorrectImplementation {N m : ℕ} {Ω : Fin N → Type*}
    [∀ x, MeasurableSpace (Ω x)] {H Ξ : Type*}
    [MeasurableSpace H] [MeasurableSpace Ξ]
    (ν : Measure Ξ) (D : (x : Fin N) → Measure (Ω x))
    (f : TruthTables (Fin N) Ω m)
    (O : OracleRAM.Oracle (Value Ω) H Ξ) (view : H → Fin m → List (Value Ω))
    (Ts Te Tu : ℝ) : Prop :=
  1 ≤ Ts ∧ 1 ≤ Te ∧ 1 ≤ Tu ∧ Tu ≤ Te ∧
  (∀ C, view O.initial C = []) ∧
  Measurable (fun p : H × OracleRAM.Request (Value Ω) × Ξ => O.invoke p.1 p.2.1 p.2.2) ∧
  (∀ h req, (∀ C, WellFormedArgs (view h C)) → LegalRequest view h req →
    (∀ ξ, (O.invoke h req ξ).2.2.2 ≠ ⊤ →
      CorrectReply f view h req (O.invoke h req ξ)) ∧
    (∫⁻ ξ, (O.invoke h req ξ).2.2.2 ∂ν) ≤ primitiveBound Ts Te Tu req) ∧
  (∀ h (x : Fin N), (∀ C, WellFormedArgs (view h C)) →
    Measure.map (fun ξ => (O.invoke h (0, 0, x.val, [], none) ξ).1) ν =
      Measure.map (fun v : Ω x => some (Sigma.mk x v)) (D x))

/-- Input layout: m,k,s,d, operation tag, length/ID, then batch pairs. The
history itself is never an input. Empty batches are literal no-ops. -/
noncomputable def operationInput {N m : ℕ} (k s d : ℕ) (op : Operation N m) : ℕ → ℕ :=
  let payload : List ℕ := match op with
    | .introduce x => [0, x.val]
    | .remove x => [1, x.val]
    | .batch B => [2, B.card] ++ B.toList.flatMap (fun p => [p.1.val, p.2.val])
  fun i => ([m, k, s, d] ++ payload)[i]?.getD 0

def IsNoop {N m : ℕ} : Operation N m → Prop
  | .batch B => B = ∅
  | _ => False

noncomputable def executeOperation {N m : ℕ} {Ω : Fin N → Type*} {H Ξ : Type*}
    (O : OracleRAM.Oracle (Value Ω) H Ξ) (P : OracleRAM.Program)
    (k s d : ℕ) (live : Finset (Fin N)) (op : Operation N m) (ω : OracleRAM.Tape Ξ)
    (st : OracleRAM.State (Value Ω) H) : OracleRAM.State (Value Ω) H := by
  classical
  exact if st.failed then st else if IsNoop op then { st with own := 0, charged := 0 } else
    OracleRAM.completed valueTag O P (fun i => decide (∃ x ∈ live, x.val = i))
      (operationInput k s d op) ω (OracleRAM.prepare st)

noncomputable def stateAt {N m : ℕ} {Ω : Fin N → Type*} {H Ξ : Type*}
    (O : OracleRAM.Oracle (Value Ω) H Ξ) (P : OracleRAM.Program)
    (k s d : ℕ) (history : List (Operation N m)) (ω : OracleRAM.Tape Ξ) :
    ℕ → OracleRAM.State (Value Ω) H
  | 0 => OracleRAM.initial O
  | t + 1 => match history[t]? with
    | none => stateAt O P k s d history ω t
    | some op => executeOperation O P k s d (instanceAt history (t + 1)).live op ω (stateAt O P k s d history ω t)

noncomputable def operationTime {N m : ℕ} {Ω : Fin N → Type*} {H Ξ : Type*}
    (O : OracleRAM.Oracle (Value Ω) H Ξ) (P : OracleRAM.Program)
    (k s d : ℕ) (history : List (Operation N m)) (t : ℕ) (ω : OracleRAM.Tape Ξ) : ℝ≥0∞ := by
  classical
  let old := stateAt O P k s d history ω t
  exact if old.failed then ⊤ else match history[t]? with
    | none => 0
    | some op => if IsNoop op then 0 else
        OracleRAM.time valueTag O P
          (fun i => decide (∃ x ∈ (instanceAt history (t + 1)).live, x.val = i))
          (operationInput k s d op) ω (OracleRAM.prepare old)

/-- A reported assignment must be present in the output cells, with the right type tag,
for every live variable; its values must actually satisfy every clause. -/
def SatisfyingOutput {N m : ℕ} {Ω : Fin N → Type*} {H : Type*}
    (f : TruthTables (Fin N) Ω m) (I : Instance N m)
    (st : OracleRAM.State (Value Ω) H) : Prop :=
  st.done = true ∧ st.failed = false ∧
    ∃ σ : (x : Fin N) → Ω x,
      (∀ x ∈ I.live, st.output x.val = some (Sigma.mk x (σ x))) ∧
      (∀ x, x ∉ I.live → st.output x.val = none) ∧
      ∀ C, ¬ f C (I.vbl C) σ

open Classical in
/-- Actual changes in reported values of surviving variables; no resampling/write count. -/
noncomputable def recourse {N m : ℕ} {Ω : Fin N → Type*} {H Ξ : Type*}
    (O : OracleRAM.Oracle (Value Ω) H Ξ) (P : OracleRAM.Program)
    (k s d : ℕ) (history : List (Operation N m)) (t : ℕ) (ω : OracleRAM.Tape Ξ) : ℝ≥0∞ :=
  (((instanceAt history t).live ∩ (instanceAt history (t + 1)).live).filter
    (fun x => (stateAt O P k s d history ω t).output x.val ≠
      (stateAt O P k s d history ω (t + 1)).output x.val)).card

/-- Upper expectation agrees with expectation on measurable functions, and avoids
requiring measurable diagonals on the paper's arbitrary value spaces. It bounds
the actual number of changed values, even for a nonmeasurable equality relation. -/
noncomputable def upperExpectation {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (g : T → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ (b : T → ℝ≥0∞) (_ : Measurable b) (_ : ∀ ω, g ω ≤ b ω), ∫⁻ ω, b ω ∂μ

/-- The full observable specification of Theorem 2 for a fixed program and absolute
constants. Instances, primitive implementations and entire histories are universal.
Every operation expectation is over the original persistent tape, not an arbitrarily
conditioned previous state. Deletion has a deterministic bound on charged work. -/
def DynamicGuarantee (P : OracleRAM.Program) (Ci Cd Ct Cr : ℝ) : Prop :=
  ∀ (N m : ℕ) (Ω : Fin N → Type) [∀ x, MeasurableSpace (Ω x)]
    (D : (x : Fin N) → Measure (Ω x)) [∀ x, IsProbabilityMeasure (D x)]
    (f : TruthTables (Fin N) Ω m), IsTruthTableFamily f →
  ∀ (H Ξ : Type) [MeasurableSpace H] [MeasurableSpace Ξ]
    (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (O : OracleRAM.Oracle (Value Ω) H Ξ) (view : H → Fin m → List (Value Ω))
    (Ts Te Tu : ℝ), CorrectImplementation ν D f O view Ts Te Tu →
  ∀ (k s d : ℕ) (q K₀ : ℝ) (history : List (Operation N m)),
    LegalHistory D f k s d q K₀ history →
    (∀ᵐ ω ∂OracleRAM.tapeMeasure ν, ∀ t, t ≤ history.length →
      SatisfyingOutput f (instanceAt history t) (stateAt O P k s d history ω t)) ∧
    (∀ t, t < history.length → Measurable (operationTime O P k s d history t)) ∧
    (∀ t (x : Fin N), history[t]? = some (.introduce x) →
      (∫⁻ ω, operationTime O P k s d history t ω ∂OracleRAM.tapeMeasure ν) ≤
        ENNReal.ofReal (Ci * Ts)) ∧
    (∀ t (x : Fin N), history[t]? = some (.remove x) →
      ∀ ω, (stateAt O P k s d history ω t).done = true →
        (stateAt O P k s d history ω t).failed = false →
        operationTime O P k s d history t ω ≤ ENNReal.ofReal Cd) ∧
    (∀ t (B : Finset (Fin m × Fin N)), history[t]? = some (.batch B) →
      (∫⁻ ω, operationTime O P k s d history t ω ∂OracleRAM.tapeMeasure ν) ≤
        ENNReal.ofReal (Ct * B.card *
          (Tu + max 1 K₀ * (k : ℝ)^2 * (s : ℝ)^2 * d * q * (Te + Ts))) ∧
      upperExpectation (OracleRAM.tapeMeasure ν) (recourse O P k s d history t) ≤
        ENNReal.ofReal (Cr * max 1 K₀ * B.card * (s : ℝ)^2 * q))

end DynEdgeColorLLL.Main.Supplement


