-- Prove2me | Definitions.Def_BipartiteVRM_Competitive_Charging
-- name    : BipartiteVRM_Competitive_Charging
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:57.876827+00:00
-- url     : https://prove2.me/theorems/9f9485e5-5561-419a-906a-c4ccd856d8d5
-- title:
--   Optimal components and the actual Case 1 and Case 2 charge rates
-- statement:
--   Fix an optimal TA-distance perfect matching $M^*$ independently of the VRM run. For a free request $r$ at time $t$, follow alternating edges in $M^*$ and the current auxiliary matching $M_t$ to form $P_r^*(t)$, the component of $M_t\mathbin{\triangle}M^*$ starting at $r$. Its terminal server may be unarrived. Put
--
--   $$D_r^*(t)=D(P_r^*(t)\cap M^*).$$
--
--   At stable times, Case 1 charges one unit of rate to the last edge if the terminal server has not arrived. Case 2, when it has arrived, assigns to each $e\in P_r^*(t)\cap M^*$ the rate $D(e)/D_r^*(t)$. Sum these actual contributions over free requests to obtain the edge rate $q_e(t)$, and set all rates to zero at event times. Define
--
--   $$W_1=\int_0^\infty\sum_{e\in M^*}q^{(1)}_e(t)\,dt,\qquad Q_e=\int_0^\infty q_e(t)\,dt.$$
--
--   The module uses extended nonnegative integrals. The companion statements establish full-component coverage, positive denominators when Case 2 is used, integrability, and the exact charging identity. No charges are chosen to satisfy a desired estimate.
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), pp. 10–12, §4.2–§4.4, equations (4.3)–(4.4)

import Definitions.Def_BipartiteVRM_Competitive_Execution

set_option autoImplicit false

namespace BipartiteVRM.Competitive

open Classical MeasureTheory

/-! Kuo, §4.2–§4.4, pp. 10–12. Optimal paths and charges are computed, not
free parameters constrained by the inequalities that the analysis is supposed to prove. -/

noncomputable def requestMate (M : Matching) (r : ℕ) : Option ℕ :=
  ((M.filter (fun e => e.1 = r)).toList.head?).map Prod.snd

noncomputable def serverMate (M : Matching) (s : ℕ) : Option ℕ :=
  ((M.filter (fun e => e.2 = s)).toList.head?).map Prod.fst

/-- Follow an M*-edge forward and an M-edge backward. Starting at an M-free request
in a matching/perfect-matching pair, this visits the entire path component of M △ M*.
The finite bound is an analysis device, not part of the online algorithm. -/
noncomputable def optimalWalk (M Mstar : Matching) : ℕ → ℕ → List Vertex
  | 0, r => [.inl r]
  | n + 1, r => match requestMate Mstar r with
    | none => [.inl r]
    | some s => (.inl r) :: (.inr s) ::
        (match serverMate M s with | none => [] | some p => optimalWalk M Mstar n p)

noncomputable def optimalPath {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) (Mstar : Matching) (t : ℝ) (r : ℕ) : List Vertex :=
  optimalWalk (stateAt I γ tie t).off Mstar (I.size + 1) r

noncomputable def optimalPart {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) (Mstar : Matching) (t : ℝ) (r : ℕ) : Matching :=
  pathEdges (optimalPath I γ tie Mstar t r) ∩ Mstar

noncomputable def optimalLength {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) (Mstar : Matching) (t : ℝ) (r : ℕ) : ℝ :=
  matchingDistance I (optimalPart I γ tie Mstar t r)

def SymmetricDifferencePath (A : Finset Vertex) (M Mstar : Matching)
    (r : ℕ) (P : List Vertex) : Prop :=
  Augmenting A M r P ∧
    pathEdges P ⊆ (M \ Mstar) ∪ (Mstar \ M) ∧
    (∀ v ∈ P, ∀ e ∈ (M \ Mstar) ∪ (Mstar \ M),
      (v = .inl e.1 ∨ v = .inr e.2) → e ∈ pathEdges P)

/-- The arrival test uses the terminal server of the actual component. -/
def CaseTwo {X : Type*} [MetricSpace X] (I : Input X) (γ : ℝ) (tie : TieRule)
    (Mstar : Matching) (t : ℝ) (r : ℕ) : Prop :=
  ∃ s, terminal (optimalPath I γ tie Mstar t r) = some s ∧ I.arrival (.inr s) ≤ t

def CaseOne {X : Type*} [MetricSpace X] (I : Input X) (γ : ℝ) (tie : TieRule)
    (Mstar : Matching) (t : ℝ) (r : ℕ) : Prop :=
  ∃ s, terminal (optimalPath I γ tie Mstar t r) = some s ∧ t < I.arrival (.inr s)

/-- The last edge charged in Case 1 (the component is oriented from r). -/
def lastEdge (P : List Vertex) : Option Edge :=
  (P.zip P.tail).getLast?.bind (fun uv => pairEdge uv.1 uv.2)

noncomputable def caseOneEdgeRate {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) (Mstar : Matching) (e : Edge) (t : ℝ) : ℝ :=
  if stable I γ tie t then
    ∑ r ∈ freeAt I γ tie t,
      if CaseOne I γ tie Mstar t r ∧ lastEdge (optimalPath I γ tie Mstar t r) = some e
      then (1 : ℝ) else 0
  else 0

noncomputable def caseOneRate {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) (Mstar : Matching) (t : ℝ) : ℝ :=
  ∑ e ∈ Mstar, caseOneEdgeRate I γ tie Mstar e t

/-- (4.3): exact proportional Case 2 charge, zero at event times. No positivity
assumption on D(e) or OPT is added. Lemma 4.4 establishes positive denominators when used. -/
noncomputable def chargeRate {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) (Mstar : Matching) (e : Edge) (t : ℝ) : ℝ :=
  if stable I γ tie t then
    ∑ r ∈ freeAt I γ tie t,
      if CaseTwo I γ tie Mstar t r ∧ e ∈ optimalPart I γ tie Mstar t r
      then edgeDistance I e / optimalLength I γ tie Mstar t r else 0
  else 0

/-- Extended nonnegative integrals avoid the Bochner-integral default entirely. -/
noncomputable def Wone {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) (Mstar : Matching) : ENNReal :=
  ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (caseOneRate I γ tie Mstar t)

noncomputable def edgeCharge {X : Type*} [MetricSpace X] (I : Input X)
    (γ : ℝ) (tie : TieRule) (Mstar : Matching) (e : Edge) : ENNReal :=
  ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (chargeRate I γ tie Mstar e t)

end BipartiteVRM.Competitive


