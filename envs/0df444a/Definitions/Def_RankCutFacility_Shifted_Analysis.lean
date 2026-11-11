-- Prove2me | Definitions.Def_RankCutFacility_Shifted_Analysis
-- name    : RankCutFacility_Shifted_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:20.226348+00:00
-- url     : https://prove2.me/theorems/7332f682-14ac-4eab-8175-e28607b4cd0c
-- title:
--   Cluster accounts, finite envelopes and exact parameters
-- statement:
--   Derived ranks, first-cluster anchors, ordered-prefix fibers, outside-order fibers, actual per-copy costs and the L, H, e accounts are computed from Algorithm 1 and a genuine optimal comparator. Retained exposed cost–benefit pairs and their sorted increments are defined directly. Finite upper envelopes, the full positive-integer switching sequence and its coefficient, the exact functions A and g, the canonical root muD, rhoD and deltaD are defined without storing any desired conclusion. Existence and uniqueness of the root and boundedness of the switching sequence remain theorem conclusions.
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Sections 3.1 and 4.1–4.6, equations (2)–(29), printed pp. 7–16 (PDF pp. 9–18)

import Definitions.Def_RankCutFacility_Shifted_Model

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted
variable {M : Type*} [MetricSpace M]

/-- Optimality and nearest assignment, with no unused open facility. No algorithmic bounds. -/
def IsOptimal {n : ℕ} (G : Geometry M) (u : Fin n → M) (Q : Comparator G n) : Prop :=
  offlineCost G u Q.opened = optimum G u ∧
  (∀ i, dist (u i) (G.site (Q.assignment i)) = connection G Q.opened (u i)) ∧
  (∀ y ∈ Q.opened, ∃ i, Q.assignment i = y)

def cluster {n : ℕ} {G : Geometry M} (Q : Comparator G n) (c : Fin G.m) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => Q.assignment i = c)

def ranks {n : ℕ} (C : Finset (Fin n)) (π : Arrival n) : Finset ℕ := C.image (rank π)

def firstRank {n : ℕ} (C : Finset (Fin n)) (π : Arrival n) : ℕ :=
  ((ranks C π).min).untopD 0

def anchor {n : ℕ} (C : Finset (Fin n)) (π : Arrival n) : Option (Fin n) :=
  (labelList π).find? (fun i => i ∈ C)

def outside {n : ℕ} (C : Finset (Fin n)) (π : Arrival n) : List (Fin n) :=
  (labelList π).filter (fun i => i ∉ C)

def anchorPrefix {n : ℕ} (C : Finset (Fin n)) (π : Arrival n) : List (Fin n) :=
  (labelList π).take (firstRank C π)

def prefixFiber {n : ℕ} (C : Finset (Fin n)) (π : Arrival n) : Finset (Arrival n) := by
  classical
  exact Finset.univ.filter (fun σ => anchorPrefix C σ = anchorPrefix C π)

def identityOutsideFiber {n : ℕ} (C : Finset (Fin n)) (p : Fin n)
    (o : List (Fin n)) : Finset (Arrival n) := by
  classical
  exact Finset.univ.filter (fun σ => anchor C σ = some p ∧ outside C σ = o)

def beforeCopy {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ δ : ℝ)
    (π : Arrival n) (p : Fin n) : Finset (Fin G.m) :=
  openAfter G n μ δ ((stream u π).take ((π.symm p).val))

def copyDistance {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ δ : ℝ)
    (π : Arrival n) (p : Fin n) : ℝ :=
  connection G (nextOpen G (beforeCopy G u μ δ π p)
    (penalty n (rank π p) μ δ) (u p)) (u p)

def copyCost {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ δ : ℝ)
    (π : Arrival n) (p : Fin n) : ℝ :=
  serviceCost G (beforeCopy G u μ δ π p) (penalty n (rank π p) μ δ) (u p)

def baseOpening {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ δ : ℝ)
    (c : Fin G.m) (π : Arrival n) (p : Fin n) : ℝ :=
  min (triggeredFee G (beforeCopy G u μ δ π p) (penalty n (rank π p) μ δ) (u p)) (G.fee c)

def highOpening {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ δ : ℝ)
    (c : Fin G.m) (π : Arrival n) (p : Fin n) : ℝ :=
  positivePart (triggeredFee G (beforeCopy G u μ δ π p)
    (penalty n (rank π p) μ δ) (u p) - G.fee c)

def excessDistance {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ δ : ℝ)
    (c : Fin G.m) (π : Arrival n) (p : Fin n) : ℝ :=
  positivePart (copyDistance G u μ δ π p - dist (u p) (G.site c))

def anchorAccount {n : ℕ} (C : Finset (Fin n)) (π : Arrival n)
    (a : Fin n → ℝ) : ℝ := match anchor C π with
  | none => 0
  | some p => a p

def radiusSum {n : ℕ} (G : Geometry M) (u : Fin n → M) (C : Finset (Fin n))
    (c : Fin G.m) : ℝ := ∑ i ∈ C, dist (u i) (G.site c)

/-- Finite pairs, not facilities; the origin is only an auxiliary analysis option. -/
def retained (P : Finset (ℝ × ℝ)) : Finset (ℝ × ℝ) := by
  classical
  exact P.filter (fun v => ∃ t : ℝ, 0 < t ∧ ∀ z ∈ P, z.2 - t * z.1 ≤ v.2 - t * v.1)

def vertices (P : Finset (ℝ × ℝ)) : List (ℝ × ℝ) := by
  classical
  exact (retained P).toList.mergeSort (fun v z => v.1 ≤ z.1)

def vertex (P : Finset (ℝ × ℝ)) (i : ℕ) : ℝ × ℝ := (vertices P).getD i (0, 0)
def edgeCount (P : Finset (ℝ × ℝ)) : ℕ := (vertices P).length - 1
def weight (P : Finset (ℝ × ℝ)) (i : ℕ) : ℝ := (vertex P (i+1)).1 - (vertex P i).1
def benefit (P : Finset (ℝ × ℝ)) (i : ℕ) : ℝ := (vertex P (i+1)).2 - (vertex P i).2
def switch (P : Finset (ℝ × ℝ)) (i : ℕ) : ℝ := benefit P i / weight P i

def decreasingEnvelope (P : Finset (ℝ × ℝ)) (t : ℝ) : ℝ :=
  sSup ((fun v : ℝ × ℝ => v.2 - t*v.1) '' (P : Set (ℝ × ℝ)))

def increasingEnvelope (P : Finset (ℝ × ℝ)) (t : ℝ) : ℝ :=
  max 0 (sSup ((fun v : ℝ × ℝ => t*v.1 - v.2) '' (P : Set (ℝ × ℝ))))

def savingPairs (G : Geometry M) (x : M) (B : ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact insert (0,0) (Finset.univ.image (fun y => (G.fee y, positivePart (B-dist x (G.site y)))))

/-- All positive integer switching indices. -/
def gamma (μ δ : ℝ) (h : ℕ) : ℝ :=
  (h : ℝ)^h * ((h : ℝ)+δ-μ)^(h+1) /
    (μ * ((h : ℝ)+δ)^h * ((h : ℝ)+1)^(h+1))
def gammaSet (μ δ : ℝ) : Set ℝ := {v | ∃ h : ℕ, 1 ≤ h ∧ v = gamma μ δ h}
def openingCoefficient (μ δ : ℝ) : ℝ := max (δ/μ) (1 + sSup (gammaSet μ δ))
def ratioBound (μ δ : ℝ) : ℝ := max (openingCoefficient μ δ) (3+2*μ+μ/δ)
def limitingA (μ : ℝ) : ℝ := 1 + Real.exp (-(1+μ))/μ
def balanceG (μ : ℝ) : ℝ := (3+2*μ+Real.sqrt ((3+2*μ)^2+4))/2
/-- Canonical root; its existence, uniqueness and admissibility are target conclusions. -/
def muD : ℝ := sInf {μ : ℝ | 0 < μ ∧ μ ≤ 1 ∧ limitingA μ = balanceG μ}
def rhoD : ℝ := limitingA muD
def deltaD : ℝ := muD * rhoD
end RankCutFacility.Shifted


