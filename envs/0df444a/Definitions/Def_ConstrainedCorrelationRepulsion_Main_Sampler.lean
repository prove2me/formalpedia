-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Sampler
-- name    : ConstrainedCorrelationRepulsion_Main_Sampler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:28:53.916433+00:00
-- url     : https://prove2.me/theorems/660530c3-2bfb-4db1-a110-8fddf08f51e5
-- title:
--   Figure 5 candidate law, targets and actual discrepancies
-- statement:
--   The candidate law first chooses a size with mass $y_{s,\varnothing}/Z$ and a pivot vertex with mass $y_{s,\{B(a)\}}/(s y_{s,\varnothing})$. If the pivot unit already has size $s$, it returns that unit. Otherwise it chooses $K$ uniformly from $\{0,\ldots,r/2-1\}$ and samples seeds with replacement, using probabilities $|D|z_D/(s-|B(a)|)$. Every new table entry uses the old numerator and denominator. Independent whole-unit Bernoulli draws follow the conditioning steps.
--
--   The ideal value $q^0_{uv}=(1-x_{uv})/Z$ is defined from the LP; $q_{uv}$ is the event probability under this actual law. They remain different functions. Cross-unit discrepancy is $d_{uv}=Z(q_{uv}-q^0_{uv})$. The sums $Y,D_s,P_+,D_+$ retain their source index sets, including hard pairs in the full signed and squared sums. $D_s$ is signed. Nonnegative expectations use extended nonnegative sums, so divergent real series cannot become zero.
-- source:
--   Yixin Cao, Ying Xu, Optimal Approximation for Constrained Correlation Clustering via Repulsion, STOC 2027 submission #869 (October 2026), Figure 5, equations (15)–(30), §§5.1–5.2; printed pp.11, 23–29 (PDF pp.12, 24–30)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_BoundedLP
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Repulsion
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Program

namespace ConstrainedCorrelationRepulsion.Main

open Classical
open scoped BigOperators ENNReal

structure DrawState (n : ℕ) where
  size : ℕ := 0
  pivot : Option (Fin n) := none
  seeds : List (Finset (Fin n)) := []
  table : Finset (Finset (Fin n)) → ℝ := fun _ => 0
  early : Bool := true

noncomputable def initialDraw {n : ℕ} (I : Instance n) (U : Units n)
    (y : LocalTable n) (r s : ℕ) (a : Fin n) : DrawState n :=
  {size := s, pivot := some a, early := decide ((unitOf U a).card = s),
   table := fun T => if T ⊆ eligible I U a ∧ T.card + 1 ≤ r then
     y s (insert (unitOf U a) T) / y s {unitOf U a} else 0}

/-- Every update uses the old table. Repeated seeds remain separate steps in `seeds`.
Only the retained entries are written; the analytical extension is `conditionalValue`. -/
noncomputable def seedUpdate {n : ℕ} (r j : ℕ) (D : Finset (Fin n))
    (h : DrawState n) : DrawState n :=
  {h with seeds := h.seeds ++ [D], table := fun T =>
    if T.card + 1 + j ≤ r then h.table (insert D T) / h.table {D} else 0}

noncomputable def seedStep {n : ℕ} (I : Instance n) (U : Units n)
    (r j : ℕ) (h : DrawState n) : PMF (DrawState n) :=
  match h.pivot with
  | none => PMF.pure h
  | some a =>
    let t : ℝ := (h.size : ℝ) - ((unitOf U a).card : ℝ)
    (categorical (fun D : Finset (Fin n) => if D ∈ eligible I U a then
      (D.card : ℝ) * h.table {D} / t else 0)).map fun chosen =>
      match chosen with
      | none => h
      | some D => seedUpdate r j D h

noncomputable def seedSteps {n : ℕ} (I : Instance n) (U : Units n) (r : ℕ)
    (initial : DrawState n) : ℕ → PMF (DrawState n)
  | 0 => PMF.pure initial
  | j + 1 => (seedSteps I U r initial j).bind (seedStep I U r (j + 1))

/-- Figure 5 through the random stopping index. The size and pivot categorical probabilities
are exactly the displayed formulas. Invalid/empty-domain choices return the specified empty
state; n>0 and LP feasibility imply that no such choice occurs. -/
noncomputable def preDrawLaw {n : ℕ} (I : Instance n) (U : Units n)
    (y : LocalTable n) (r : ℕ) : PMF (DrawState n) :=
  (categorical (fun s : Fin (n + 1) => if 0 < s.val then y s.val ∅ / Z y else 0)).bind fun sz =>
  match sz with
  | none => PMF.pure {}
  | some s =>
    (categorical (fun a : Fin n => y s.val {unitOf U a} / ((s.val : ℝ) * y s.val ∅))).bind fun pivot =>
    match pivot with
    | none => PMF.pure {}
    | some a =>
      let initial := initialDraw I U y r s.val a
      if initial.early then PMF.pure initial else
      (categorical (fun k : Fin (r / 2) => (1 : ℝ) / (r / 2 : ℕ))).bind fun stop =>
        match stop with
        | none => PMF.pure initial
        | some k => seedSteps I U r initial k.val

/-- Independent whole-unit inclusion, implemented as successive Bernoulli choices. -/
noncomputable def independentUnits {n : ℕ} (p : Finset (Fin n) → ℝ) :
    List (Finset (Fin n)) → PMF (Finset (Fin n))
  | [] => PMF.pure ∅
  | D :: rest => (flip (p D)).bind fun take =>
      (independentUnits p rest).map fun C => if take then D ∪ C else C

noncomputable def finishDraw {n : ℕ} (I : Instance n) (U : Units n)
    (h : DrawState n) : PMF (Finset (Fin n)) :=
  match h.pivot with
  | none => PMF.pure ∅
  | some a => if h.early then PMF.pure (unitOf U a) else
      (independentUnits (fun D => h.table {D}) (eligible I U a).toList).map fun C => unitOf U a ∪ C

noncomputable def candidateLaw {n : ℕ} (I : Instance n) (U : Units n)
    (y : LocalTable n) (r : ℕ) : PMF (Finset (Fin n)) :=
  (preDrawLaw I U y r).bind (finishDraw I U)

noncomputable def preSingle {n : ℕ} (U : Units n) (h : DrawState n) (v : Fin n) : ℝ :=
  match h.pivot with
  | none => 0
  | some a => if unitOf U v = unitOf U a then 1 else if h.early then 0 else h.table {unitOf U v}

noncomputable def preJoint {n : ℕ} (U : Units n) (h : DrawState n) (u v : Fin n) : ℝ :=
  if unitOf U u = unitOf U v then preSingle U h u else
  match h.pivot with
  | none => 0
  | some a => if h.early then 0 else
    if unitOf U u = unitOf U a then preSingle U h v else
    if unitOf U v = unitOf U a then preSingle U h u else h.table {unitOf U u, unitOf U v}

/-- Nonnegative expectation in extended nonnegative reals; no nonintegrable real integral
or unsummable real series can silently become zero. -/
noncomputable def nnExpectation {A : Type} (p : PMF A) (f : A → ℝ) : ℝ≥0∞ :=
  ∑' a, p a * ENNReal.ofReal (f a)

noncomputable def eventProbability {A : Type} (p : PMF A) (E : A → Prop) : ℝ :=
  (p.toOuterMeasure {a | E a}).toReal

noncomputable def qTarget {n : ℕ} (U : Units n) (y : LocalTable n) (u v : Fin n) : ℝ :=
  (1 - tableDistance U y u v) / Z y

noncomputable def qActual {n : ℕ} (I : Instance n) (U : Units n)
    (y : LocalTable n) (r : ℕ) (u v : Fin n) : ℝ :=
  eventProbability (candidateLaw I U y r) (fun C => u ∈ C ∧ v ∈ C)

noncomputable def discrepancy {n : ℕ} (I : Instance n) (U : Units n)
    (y : LocalTable n) (r : ℕ) (u v : Fin n) : ℝ :=
  Z y * (qActual I U y r u v - qTarget U y u v)

noncomputable def Y {n : ℕ} (U : Units n) (y : LocalTable n) : ℝ :=
  pairSum (fun u v => if unitOf U u ≠ unitOf U v then 1 - tableDistance U y u v else 0)

noncomputable def signedError {n : ℕ} (I : Instance n) (U : Units n)
    (y : LocalTable n) (r : ℕ) : ℝ := pairSum (fun u v =>
    if unitOf U u ≠ unitOf U v ∧ ¬ I.cannotLink.Adj u v then discrepancy I U y r u v else 0)

noncomputable def positivePairs {n : ℕ} (I : Instance n) (U : Units n) : ℝ :=
  pairSum (fun u v => if unitOf U u ≠ unitOf U v ∧ I.positive.Adj u v then 1 else 0)

noncomputable def positiveError {n : ℕ} (I : Instance n) (U : Units n)
    (y : LocalTable n) (r : ℕ) : ℝ := pairSum (fun u v =>
    if unitOf U u ≠ unitOf U v ∧ I.positive.Adj u v then |discrepancy I U y r u v| else 0)

end ConstrainedCorrelationRepulsion.Main


