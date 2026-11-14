-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_GoodReach
-- name    : KSATSingleFlip_Connect_GoodReach
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T08:29:05.730166+00:00
-- url     : https://prove2.me/theorems/fe0688e8-415b-41e1-af32-73fe5a628ce8
-- title:
--   Degree-truncated variable reachability in factor graphs
-- statement:
--   In a factor graph, retain the outgoing clause incidences of variables whose full-formula degree is at most $D$, and give variables above the cutoff no outgoing incidences. The degree-truncated variable reachability set consists of variables reachable from a root in at most $r$ variable–clause–variable steps through these directed incidences.
-- source:
--   Auxiliary definition for Lemma 2.7 in Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, printed pp. 12–13, STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_FactorGraph
import Definitions.Def_KSATSingleFlip_Connect_BoundedReach

noncomputable section
open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- The incident clauses of a variable whose full-formula degree is at most D;
variables above the cutoff have no outgoing edges. -/
def goodIncidentClauses {n : ℕ} (Φ : GFormula (Fin n)) (D : ℕ) (u : Fin n) : Finset (Fin Φ.length) :=
  if degree Φ u ≤ D then Finset.univ.filter (fun c => u ∈ vbl (Φ.get c)) else ∅

/-- Variables reachable through at most r variable–clause–variable steps
whose departure variables satisfy the degree cutoff. -/
def goodVariableReach {n : ℕ} (Φ : GFormula (Fin n)) (D : ℕ) (u : Fin n) (r : ℕ) : Finset (Fin n) :=
  boundedReachBall (fun v => (goodIncidentClauses Φ D v).biUnion (fun c => vbl (Φ.get c))) u r

end KSATSingleFlip.Connect


