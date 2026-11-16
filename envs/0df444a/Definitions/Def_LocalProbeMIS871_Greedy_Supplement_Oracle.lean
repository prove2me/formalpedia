-- Prove2me | Definitions.Def_LocalProbeMIS871_Greedy_Supplement_Oracle
-- name    : LocalProbeMIS871_Greedy_Supplement_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:01:45.098582+00:00
-- url     : https://prove2.me/theorems/04b0dc76-6fee-4366-82be-51aba3174c9d
-- title:
--   §2 — General adaptive stateless oracle interaction
-- statement:
--   Let $G$ be a finite simple graph with $n$ labeled vertices, and let $L$ give an arbitrary ordering of exactly the distinct neighbors of each vertex. A probe either asks for a vertex degree or for a single neighbor at a positive integer list position. An out-of-range position returns null, including position zero. The policy receives only $n$, the degree bound $\Delta$, the query label $v$, its entire input-independent shared tape $r$, and its finite history of probe/reply pairs. The next local computation may return a Boolean, make one probe, or diverge. There is no fixed probe horizon and no persistent state between queries. All computation and tape access are free.
--
--   Write $I_A(G,L,r)$ for the set of vertices whose actual runs return true, and $Q_A(G,L,v;r)$ for the supremum of the lengths of their finite probe histories. Thus
--
--   $$Q_A(G,L,v;r)=\sup_{t\in\mathbb N}|\mathrm{history}_t|.$$
--
--   Every oracle call, including a repeated call, appends one pair. On a terminating run the supremum is the actual finite number of calls; infinitely many calls have infinite cost. A locally divergent computation can make only finitely many probes, but it is never classified as terminating. The zero-error condition requires that, for every legal graph and list order, on one probability-one event all vertex runs terminate and their output indicators form an independent dominating set, equivalently one MIS. No preselected MIS is an input to the policy.
--
--   This interface represents arbitrary adaptive stateless LCAs, independently of the particular greedy algorithm in the base mission.
--
--   **Formalization Note** Only vertex labels use zero-based `Fin n`; list positions remain one-based. Tapes may have any measurable space and probability law. Each next-action equality event is measurable, the discrete observational measurability convention for such algorithms. The count is extended nonnegative real. Divergent or nonterminating queries are allowed off the correctness event, and the output set is computed from actual true returns there as well.
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 10, PDF p. 12, §2 (Oracle access; Zero-error stateless MIS LCAs)

import Definitions.Def_LocalProbeMIS871_Greedy_Model

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
universe uOracle

namespace LocalProbeMIS871.Greedy.Supplement

/-- Left: degree; right: individual neighbor position, indexed from one as in the source. -/
abbrev Probe (n : ℕ) := Fin n ⊕ (Fin n × ℕ)
abbrev Reply (n : ℕ) := ℕ ⊕ Option (Fin n)
abbrev History (n : ℕ) := List (Probe n × Reply n)

def oracle {n : ℕ} {G : SimpleGraph (Fin n)} (L : AdjacencyLists G) :
    Probe n → Reply n
  | .inl v => .inl (L.lists v).length
  | .inr (v, i) => .inr (if i = 0 then none else (L.lists v)[i - 1]?)

/-- None is a divergent local computation; some (inl b) halts; some (inr p) probes.
The only graph information supplied to the policy is its observed history. -/
structure Algorithm (Ω : Type uOracle) [MeasurableSpace Ω] where
  next : (n Δ : ℕ) → Fin n → History n → Ω → Option (Bool ⊕ Probe n)
  measurable_next : ∀ n Δ v h a, MeasurableSet {r | next n Δ v h r = a}

/-- Terminal status: none = running, some none = local divergence,
some (some o) = returned output. The history contains every oracle call. -/
abbrev State (n : ℕ) (O : Type*) := History n × Option (Option O)

def step {n : ℕ} {O : Type*} (reply : Probe n → Reply n)
    (policy : History n → Option (O ⊕ Probe n)) (s : State n O) : State n O :=
  match s.2 with
  | some _ => s
  | none => match policy s.1 with
    | none => (s.1, some none)
    | some (.inl o) => (s.1, some (some o))
    | some (.inr p) => (s.1 ++ [(p, reply p)], none)

def run {n : ℕ} {O : Type*} (reply : Probe n → Reply n)
    (policy : History n → Option (O ⊕ Probe n)) : ℕ → State n O
  | 0 => ([], none)
  | t + 1 => step reply policy (run reply policy t)

def queryRun {Ω : Type uOracle} [MeasurableSpace Ω] (A : Algorithm Ω)
    {n : ℕ} {G : SimpleGraph (Fin n)} (Δ : ℕ) (L : AdjacencyLists G)
    (v : Fin n) (r : Ω) (t : ℕ) : State n Bool :=
  run (oracle L) (fun h => A.next n Δ v h r) t

def Terminates {Ω : Type uOracle} [MeasurableSpace Ω] (A : Algorithm Ω)
    {n : ℕ} {G : SimpleGraph (Fin n)} (Δ : ℕ) (L : AdjacencyLists G)
    (v : Fin n) (r : Ω) : Prop :=
  ∃ t b, (queryRun A Δ L v r t).2 = some (some b)

def answersYes {Ω : Type uOracle} [MeasurableSpace Ω] (A : Algorithm Ω)
    {n : ℕ} {G : SimpleGraph (Fin n)} (Δ : ℕ) (L : AdjacencyLists G)
    (v : Fin n) (r : Ω) : Prop :=
  ∃ t, (queryRun A Δ L v r t).2 = some (some true)

/-- Extended count of actual probes, including repeated probes. On a terminating run
this is its finite history length; arbitrarily many probes give infinity. -/
def probeCount {Ω : Type uOracle} [MeasurableSpace Ω] (A : Algorithm Ω)
    {n : ℕ} {G : SimpleGraph (Fin n)} (Δ : ℕ) (L : AdjacencyLists G)
    (v : Fin n) (r : Ω) : ENNReal :=
  ⨆ t : ℕ, ((queryRun A Δ L v r t).1.length : ENNReal)

def outputSet {Ω : Type uOracle} [MeasurableSpace Ω] (A : Algorithm Ω)
    {n : ℕ} {G : SimpleGraph (Fin n)} (Δ : ℕ) (L : AdjacencyLists G)
    (r : Ω) : Finset (Fin n) :=
  Finset.univ.filter (fun v => answersYes A Δ L v r)

def DegreeBound {n : ℕ} (G : SimpleGraph (Fin n)) (Δ : ℕ) : Prop :=
  ∀ v, G.degree v ≤ Δ

def Independent {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v

def IsMIS {n : ℕ} (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  Independent G I ∧ ∀ v, v ∈ I ∨ ∃ u ∈ I, G.Adj v u

/-- Source §2: simultaneous termination and MIS consistency on one conull tape event,
for every legal input and fixed list ordering. No information persists between queries. -/
def ZeroError {Ω : Type uOracle} [MeasurableSpace Ω] (μ : Measure Ω)
    (Δ : ℕ) (A : Algorithm Ω) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (L : AdjacencyLists G), DegreeBound G Δ →
    ∀ᵐ r ∂μ, (∀ v, Terminates A Δ L v r) ∧ IsMIS G (outputSet A Δ L r)

end LocalProbeMIS871.Greedy.Supplement


