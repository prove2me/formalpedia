-- Prove2me | Definitions.Def_FengLiYangMatching_General_Process
-- name    : FengLiYangMatching_General_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:46:21.150222+00:00
-- url     : https://prove2.me/theorems/a9c3b7c5-374c-4697-b1ae-1977aef3c34c
-- title:
--   Algorithm 1, independent continuous arrivals, shadow history, counts and exact parameters
-- statement:
--   Let G be any finite simple undirected graph, with vertices relabelled by {0,...,n-1}, including n=0. An edge is an unordered pair of distinct vertices. A matching is a finite edge set with pairwise disjoint endpoints; OPT(G) is the maximum of the cardinalities of all matchings contained in G. The maximum is over a finite nonempty family containing the empty matching.
--
--   Algorithm 1 stores its actual matching M, shadow matching T and reserved vertices X, initially empty. Its transition receives only these sets, the current edge, its observed real arrival time and one reservation coin. Before a it selects edges with both endpoints free in T, puts them into T, and either reserves both endpoints or accepts the edge into M. From a up to b it accepts every new shadow edge into M. From b onward T is frozen, and the transition accepts an edge precisely when both endpoints are free in M and are not both in X. In particular YY edges are allowed. Execution is the chronological fold of this transition.
--
--   The arrival law is the published finite product of uniform laws on [0,1]. Independent Bernoulli(p) coins, one per edge, are read only when a shadow edge is selected before a; the endpoints share that coin. The expected objective is the cardinality of the final actual matching. For all analysis lemmas, 0≤a<b≤3/8 and 0≤p≤2/3.
--
--   The history H_b records only T_b and its accepted-edge times. Rejected-edge coordinates are filled with zero and carry no information. The candidate conditional law fixes recorded times and gives every unrecorded edge an independent uniform time on (min{τ_u,τ_v,b},1), with τ_v=+∞ for unmatched vertices. Its identification as the actual conditional law is a separate theorem obligation, Lemma 4.1. Reservation coins remain independent. Exact histories are never conditioned on by dividing by their probability.
--
--   The definitions include the reference vertices of each early shadow edge relative to an analysis-only maximum matching, recovery-only counts, the V₁Y and YY optimal edges, unmatched optimal edges U_t, retain-phase optimal edges M₂*, and actual Greedy survival on G−e. They do not encode any bound as a hypothesis. The scalar family is
--
--   $$L_k(a,b)=\frac6{11}+\frac{(1-a)^k-(1-b)^k}{2k}-\frac{(1-a)^k}{22}-\frac{(1-b)^k}{10},\quad k\ge1.$$
--
--   The parameter a* is total choice of a root of L₁(a,3/8)=L₁₂(a,3/8) in (0,3/8), with default zero only if no root exists. The goal must prove existence, uniqueness and that the chosen value is a root. The other parameters are b=3/8 and p=5/11. These shared definitions provide the concrete algorithm and random variables for every theorem in the mission.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, STOC 2027 submission #1018 (October 2026), §§1.1–1.2, 2–4, pp. 2–16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Mathlib
import Definitions.Def_RandomOrderCRS_ArrivalModel

open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General
noncomputable section

abbrev Edge (n : ℕ) := Sym2 (Fin n)
abbrev EdgeSet (n : ℕ) := Finset (Edge n)

def covered {n : ℕ} (F : EdgeSet n) : Finset (Fin n) := by
  classical
  exact univ.filter fun v => ∃ e ∈ F, v ∈ e

def IsMatching {n : ℕ} (F : EdgeSet n) : Prop :=
  (∀ e ∈ F, ¬ e.IsDiag) ∧ ∀ e ∈ F, ∀ f ∈ F, e ≠ f → ∀ v, v ∈ e → v ∉ f

def free {n : ℕ} (F : EdgeSet n) (e : Edge n) : Prop :=
  ∀ v, v ∈ e → v ∉ covered F

structure State (n : ℕ) where
  actual : EdgeSet n
  shadow : EdgeSet n
  reserved : Finset (Fin n)

def initial (n : ℕ) : State n := ⟨∅, ∅, ∅⟩

/-- Algorithm 1. No graph, edge count, optimum or unseen edge is an argument. -/
def step {n : ℕ} (a b : ℝ) (S : State n) (e : Edge n) (t : ℝ) (coin : Bool) : State n := by
  classical
  exact if t < a then
    if free S.shadow e then
      if coin then ⟨S.actual, insert e S.shadow, S.reserved ∪ covered {e}⟩
      else ⟨insert e S.actual, insert e S.shadow, S.reserved⟩
    else S
  else if t < b then
    if free S.shadow e then ⟨insert e S.actual, insert e S.shadow, S.reserved⟩ else S
  else if free S.actual e ∧ ¬ (∀ v, v ∈ e → v ∈ S.reserved) then
    ⟨insert e S.actual, S.shadow, S.reserved⟩
  else S

/-- A prefix fold: the only randomness read is the current edge's reservation coin. -/
def run {n : ℕ} (a b : ℝ) (stream : List (Edge n × ℝ × Bool)) : State n :=
  stream.foldl (fun S o => step a b S o.1 o.2.1 o.2.2) (initial n)

def graphEdges {n : ℕ} (G : SimpleGraph (Fin n)) : EdgeSet n := by
  classical
  exact univ.filter fun e => e ∈ G.edgeSet

abbrev Times {n : ℕ} (G : SimpleGraph (Fin n)) := G.edgeSet → ℝ
abbrev Coins {n : ℕ} (G : SimpleGraph (Fin n)) := G.edgeSet → Bool
abbrev Sample {n : ℕ} (G : SimpleGraph (Fin n)) := Times G × Coins G

def arrivalLaw {n : ℕ} (G : SimpleGraph (Fin n)) : Measure (Times G) := by
  classical
  exact RandomOrderCRS.arrivalTimeLaw G

def coinLaw {n : ℕ} (G : SimpleGraph (Fin n)) (p : ℝ) : Measure (Coins G) := by
  classical
  exact Measure.pi fun _ => RandomOrderCRS.survivalLaw p

def sampleLaw {n : ℕ} (G : SimpleGraph (Fin n)) (p : ℝ) : Measure (Sample G) :=
  (arrivalLaw G).prod (coinLaw G p)

/-- Sorting is performed only by the ex post execution environment. -/
def orderedEdges {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) : List G.edgeSet := by
  classical
  exact List.ofFn (RandomOrderCRS.arrivalOrder G t)

def stream {n : ℕ} (G : SimpleGraph (Fin n)) (w : Sample G) : List (Edge n × ℝ × Bool) :=
  (orderedEdges G w.1).map fun e => (e.val, w.1 e, w.2 e)

def execution {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G) : State n :=
  run a b (stream G w)

def ALG {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G) : ℝ :=
  (execution G a b w).actual.card

def OPT {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact Nat.cast (((((graphEdges G).powerset.filter IsMatching).sup Finset.card) : ℕ))

/-- Ordinary Greedy on a list; no arrival-time or graph oracle. -/
def greedy {n : ℕ} (l : List (Edge n)) : EdgeSet n := by
  classical
  exact l.foldl (fun F e => if free F e then insert e F else F) ∅

/-- Strict prefixes, consistently with the half-open phases in Algorithm 1. -/
def shadowAt {n : ℕ} (G : SimpleGraph (Fin n)) (t : Times G) (u : ℝ) : EdgeSet n :=
  greedy (((orderedEdges G t).filter fun e => t e < u).map Subtype.val)

abbrev History (n : ℕ) := EdgeSet n × (Edge n → ℝ)

def History.accepted {n : ℕ} (h : History n) : EdgeSet n := h.1
def History.time {n : ℕ} (h : History n) : Edge n → ℝ := h.2

/-- Only accepted shadow edges and their times are recorded; all other coordinates are zero. -/
def history {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (t : Times G) : History n := by
  classical
  exact ⟨shadowAt G t b, fun e => if h : e ∈ G.edgeSet then
    if e ∈ shadowAt G t b then t ⟨e,h⟩ else 0 else 0⟩

def historyLaw {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) : Measure (History n) :=
  (arrivalLaw G).map (history G b)

/-- min(tau_v,b), with b in place of the unmatched vertex's +infinity. -/
def matchTime {n : ℕ} (b : ℝ) (h : History n) (v : Fin n) : ℝ := by
  classical
  exact h.accepted.toList.foldl (fun s e => if v ∈ e then min s (h.time e) else s) b

/-- Conditional interval for a rejected edge; this is the source's endpoint minimum. -/
def lowerTime {n : ℕ} (b : ℝ) (h : History n) (e : Edge n) : ℝ :=
  (covered {e}).toList.foldl (fun s v => min s (matchTime b h v)) b

def residualLaw {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℝ) (h : History n) :
    Measure (Times G) := by
  classical
  exact Measure.pi fun e => if e.val ∈ h.accepted then Measure.dirac (h.time e.val)
    else (ENNReal.ofReal (1 - lowerTime b h e.val))⁻¹ •
      volume.restrict (Set.Ioo (lowerTime b h e.val) 1)

def conditionalLaw {n : ℕ} (G : SimpleGraph (Fin n)) (b p : ℝ) (h : History n) :
    Measure (Sample G) := (residualLaw G b h).prod (coinLaw G p)

def early {n : ℕ} (a : ℝ) (h : History n) : EdgeSet n := by
  classical
  exact h.accepted.filter fun e => h.time e < a

def Yset {n : ℕ} (h : History n) : Finset (Fin n) := by
  classical
  exact univ \ covered h.accepted

def references {n : ℕ} (M : EdgeSet n) (h : History n) (e : Edge n) : Finset (Fin n) := by
  classical
  exact (Yset h).filter fun y => ∃ x, x ∈ e ∧ s(x,y) ∈ M

def recovery {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G) : EdgeSet n := by
  classical
  exact (execution G a b w).actual.filter fun e => ∃ he : e ∈ G.edgeSet, b ≤ w.1 ⟨e,he⟩

def Nhat {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (e : Edge n) (w : Sample G) : ℝ := by
  classical
  exact Nat.cast (((((covered {e}) ∩ covered (recovery G a b w)).card) : ℕ))

def Rhat {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (a b : ℝ)
    (h : History n) (e : Edge n) (w : Sample G) : ℝ := by
  classical
  exact Nat.cast (((((references M h e) ∩ covered (recovery G a b w)).card) : ℕ))

def ZYY {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G) : ℝ := by
  classical
  exact Nat.cast <| ((recovery G a b w).filter fun e => ∀ v, v ∈ e →
    v ∈ Yset (history G b w.1)).card

def ZXY {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (w : Sample G) : ℝ := by
  classical
  exact Nat.cast <| ((recovery G a b w).filter fun e => ∃ x y,
    e = s(x,y) ∧ x ∈ (execution G a b w).reserved ∧ y ∈ Yset (history G b w.1)).card

def M1Y {n : ℕ} (M : EdgeSet n) (a : ℝ) (h : History n) : EdgeSet n := by
  classical
  exact M.filter fun e => ∃ x y, e = s(x,y) ∧ x ∈ covered (early a h) ∧ y ∈ Yset h

def MYY {n : ℕ} (M : EdgeSet n) (h : History n) : EdgeSet n := by
  classical
  exact M.filter fun e => ∀ v, v ∈ e → v ∈ Yset h

def U {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (t : Times G) (u : ℝ) : ℝ := by
  classical
  exact Nat.cast ((((M.filter fun e => free (shadowAt G t u) e).card) : ℕ))

def M2 {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (a b : ℝ) (t : Times G) : EdgeSet n := by
  classical
  exact M ∩ (shadowAt G t b \ shadowAt G t a)

def survival {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u : ℝ) : ℝ :=
  (arrivalLaw G).real {t | ∀ v ∈ A, v ∉ covered (shadowAt G t u)}

/-- The edge-deletion survival experiment used in (4)--(8). -/
def edgeSurvival {n : ℕ} (G : SimpleGraph (Fin n)) (e : Edge n) (u : ℝ) : ℝ :=
  survival (G.deleteEdges {e}) (covered {e}) u

def averageSurvival {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (u : ℝ) : ℝ :=
  (∑ e ∈ M, edgeSurvival G e u) / M.card

/-- The exact scalar family of Section 3.2; only positive n is used. -/
def L (n : ℕ) (a b : ℝ) : ℝ :=
  6/11 + ((1-a)^n - (1-b)^n) / (2*(n : ℝ)) - (1-a)^n/22 - (1-b)^n/10

def Root (a : ℝ) : Prop := 0 < a ∧ a < 3/8 ∧ L 1 a (3/8) = L 12 a (3/8)

/-- Total choice, with existence and uniqueness left as goal obligations. -/
def aStar : ℝ := by
  classical
  exact if h : ∃ a, Root a then Classical.choose h else 0

end
end FengLiYangMatching.General


