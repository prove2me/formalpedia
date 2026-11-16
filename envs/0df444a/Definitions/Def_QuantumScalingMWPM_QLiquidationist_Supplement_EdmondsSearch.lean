-- Prove2me | Definitions.Def_QuantumScalingMWPM_QLiquidationist_Supplement_EdmondsSearch
-- name    : QuantumScalingMWPM_QLiquidationist_Supplement_EdmondsSearch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:23:02.871133+00:00
-- url     : https://prove2.me/theorems/ca638612-4d33-4056-ad47-3187c092cd16
-- title:
--   Classical Edmonds search from a specified set of free vertices
-- statement:
--   Let $G$ be a finite simple graph with a current mate array $M$, a laminar blossom family $\Omega$, vertex and blossom duals $y,z$, edge weights $w$, and a specified set $F$ of free source vertices. This module defines the classical search objects used by SMALLBLOSSOMLIQUIDATION and FINALIZATION.
--
--   Under Criterion 1 an edge is eligible when $yz(e)=w(e)$; under Criterion 3 it is eligible when
--   $$yz(e)\in\{w(e),w(e)-2\}.$$
--   The eligible alternating paths start at a free root blossom containing a vertex of $F$. Their even and odd reachability defines the outer and inner sets, with outer blossoms excluded from the inner set. An augmenting path must also end at a free root blossom. Blossom shrinking adjoins eligible odd alternating cycles of current roots with an outer base; the transition system subsequently requires maximality. Zero-valued root blossoms are dissolved repeatedly.
--
--   These are the objects of EdmondsSearch in [13, Figure 2], which the paper delegates to the classical routines. The actual transitions, including when to augment, adjust duals, stop a bounded search, and return, are in the separate algorithm module. No correctness, complementary-slackness invariant, or termination certificate is assumed.
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), §4.1, Criteria 1 and 3, p. 24; delegated PQSEARCH, p. 25. Ran Duan, Seth Pettie, Hsin-Hao Su, Scaling Algorithms for Weighted Matching in General Graphs, ACM TALG 14(1):8 (2018), DOI 10.1145/3155301; delegated procedures read in author version arXiv:1411.1919v6 (9 October 2017), https://arxiv.org/abs/1411.1919v6, §2.1, Criteria 1–3 p. 7, Figure 2 p. 8 and PQSEARCH semantics p. 9.

import Mathlib
import Definitions.Def_QuantumScalingMWPM_QLiquidationist_Blossom

/-!
# Classical Edmonds search with a specified free source set

Duan, Pettie and Su, *Scaling Algorithms for Weighted Matching in General Graphs*,
arXiv:1411.1919v6, §2.1 pp. 7–9, Figure 2 p. 8. This is the search that the quantum
paper's §4.1 (pp. 24–25) delegates to [13] for SMALLBLOSSOMLIQUIDATION and FINALIZATION.
Eligibility Criteria 1 and 3 are already in the published Blossom module; they are reused.

These predicates describe F-rooted eligible alternating reachability and legal maximal
blossom shrinking. No feasibility, complementary slackness, optimality or termination is
included as a condition on the input state. The state-machine transitions in Algorithm
implement the four actions of Figure 2 using these objects.
-/

namespace QuantumScalingMWPM.QLiquidationist.Supplement

open scoped Classical
open QuantumScalingMWPM.QLiquidationist

noncomputable section

variable {N : ℕ}

/-! ### EdmondsSearch / PQSEARCH ([13] Figure 2) -/

/-- Criterion 1 (`crit3 = false`) or Criterion 3 (`crit3 = true`) of eligibility. -/
def EligC (crit3 : Bool) (G : SimpleGraph (Fin N)) (w : Sym2 (Fin N) → ℤ) (Ω : Family N)
    (y : Fin N → ℤ) (z : Finset (Fin N) → ℤ) (u v : Fin N) : Prop :=
  if crit3 then Elig3 G w Ω y z u v else Elig1 G w Ω y z u v

/-- A free root blossom containing a free vertex of the source set `F`. -/
def FRoot (Φ : Family N) (M : Mate N) (F : Finset (Fin N)) (R : Finset (Fin N)) : Prop :=
  IsFreeRoot Φ M R ∧ ∃ v ∈ R, v ∈ F ∧ M v = none

/-- A contracted path whose first blossom is a free root blossom with a free `F`-vertex. -/
def StartsInF (Φ : Family N) (M : Mate N) (F : Finset (Fin N)) (es : List (Fin N × Fin N)) :
    Prop :=
  ∀ e ∈ es.head?, FRoot Φ M F (rootSet Φ e.1)

/-- `v ∈ V_out`: the root blossom of `v` is reachable from a free `F`-vertex by an even-length
eligible alternating path in `G/Φ` (length `0` included). -/
def IsOutF (G : SimpleGraph (Fin N)) (E : Fin N → Fin N → Prop) (M : Mate N) (Φ : Family N)
    (F : Finset (Fin N)) (v : Fin N) : Prop :=
  FRoot Φ M F (rootSet Φ v) ∨
    ∃ es, IsAltPathH G M Φ es ∧ StartsInF Φ M F es ∧ (∀ e ∈ es, E e.1 e.2) ∧ Even es.length ∧
      ∀ e ∈ es.getLast?, rootSet Φ e.2 = rootSet Φ v

/-- `v ∈ V_in`: reachable by an odd-length eligible alternating path from a free `F`-vertex. -/
def IsInF (G : SimpleGraph (Fin N)) (E : Fin N → Fin N → Prop) (M : Mate N) (Φ : Family N)
    (F : Finset (Fin N)) (v : Fin N) : Prop :=
  ¬ IsOutF G E M Φ F v ∧
  ∃ es, IsAltPathH G M Φ es ∧ StartsInF Φ M F es ∧ (∀ e ∈ es, E e.1 e.2) ∧ Odd es.length ∧
    ∀ e ∈ es.getLast?, rootSet Φ e.2 = rootSet Φ v

/-- An eligible augmenting path of `Ĝ_elig` from a free `F`-vertex (written from that end). -/
def IsEligAugFromF (G : SimpleGraph (Fin N)) (E : Fin N → Fin N → Prop) (M : Mate N)
    (Φ : Family N) (F : Finset (Fin N)) (P : List (Fin N × Fin N)) : Prop :=
  IsAugPathH G M Φ P ∧ StartsInF Φ M F P ∧ ∀ e ∈ P, E e.1 e.2

/-- Blossom Shrinking as a sequence of contractions: each new record is an odd alternating cycle
of root blossoms of the family built so far, with eligible cycle edges and a base child in
`V_out`; the final family is a valid blossom family. -/
def IsContractionSeqF (G : SimpleGraph (Fin N)) (E : Fin N → Fin N → Prop) (M : Mate N)
    (F : Finset (Fin N)) (Ω news : Family N) : Prop :=
  IsBlossomFamily G M (Ω ++ news) ∧
  ∀ j (h : j < news.length),
    (∀ C ∈ (news[j]).kids, ∃ v, C = rootSet (Ω ++ news.take j) v) ∧
    (∀ e ∈ (news[j]).cyc, E e.1 e.2) ∧
    ∀ C ∈ (news[j]).kids.head?, ∃ v ∈ C, IsOutF G E M (Ω ++ news.take j) F v

/-- Blossom Dissolution: repeatedly dissolve root blossoms with `z(B) = 0` (each round that
changes the family removes a record, so `|Φ|` rounds reach the fixed point). -/
def dissolveAll (Φ : Family N) (z : Finset (Fin N) → ℤ) : Family N :=
  (fun Ψ => dissolveZero Ψ z)^[Φ.length] Φ

end

end QuantumScalingMWPM.QLiquidationist.Supplement


