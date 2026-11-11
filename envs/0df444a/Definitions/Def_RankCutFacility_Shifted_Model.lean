-- Prove2me | Definitions.Def_RankCutFacility_Shifted_Model
-- name    : RankCutFacility_Shifted_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:14.442027+00:00
-- url     : https://prove2.me/theorems/b09d1444-2cd7-4def-a654-30bcd90ae59e
-- title:
--   Operational metric facility location and Algorithm 1
-- statement:
--   The candidate geometry consists of a finite nonempty injectively enumerated set in an arbitrary metric space, arbitrary positive real opening costs and a fixed tie order. The horizon, shifted rank, capped penalty, finite candidate scan, opening test and fold on observed locations define Algorithm 1. Its initial opening branch implements infinite empty-state distance. Costs use full opening fees and service-time connections. Demand labels, uniform finite averages, the true offline minimum over nonempty facility subsets and comparator assignments complete the model. No demand injectivity, finite ambient space or analysis inequality is assumed.
-- source:
--   Jianhao Jia, Bo Peng, Zhihao Gavin Tang, STOC 2027 submission #388 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/388.pdf, Sections 2–3, equations (1), (4)–(5), Algorithm 1, printed pp. 6–8 (PDF pp. 8–10)

import Mathlib

noncomputable section
open scoped BigOperators

namespace RankCutFacility.Shifted

/-- Candidate enumeration fixes the tie order. No request data belong to the geometry. -/
structure Geometry (M : Type*) [MetricSpace M] where
  m : ℕ
  m_pos : 0 < m
  site : Fin m → M
  site_injective : Function.Injective site
  fee : Fin m → ℝ
  fee_pos : ∀ y, 0 < fee y

variable {M : Type*} [MetricSpace M]

def positivePart (z : ℝ) : ℝ := max z 0

def clock (n t : ℕ) (δ : ℝ) : ℝ := ((t : ℝ) - 1 + δ) / n

def penalty (n t : ℕ) (μ δ : ℝ) : ℝ := min 1 (clock n t δ / μ)

/-- Empty-state value is unused by the opening test; that test has a separate infinity branch. -/
def connection (G : Geometry M) (O : Finset (Fin G.m)) (x : M) : ℝ :=
  sInf ((fun y => dist x (G.site y)) '' (O : Set (Fin G.m)))

/-- Finite scan; strict improvement preserves the first candidate in the fixed order. -/
def select (G : Geometry M) (β : ℝ) (x : M) : Fin G.m := by
  classical
  exact (List.finRange G.m).foldl
    (fun best y => if dist x (G.site y) + β * G.fee y <
      dist x (G.site best) + β * G.fee best then y else best) ⟨0, G.m_pos⟩

def phi (G : Geometry M) (α : ℝ) (x : M) : ℝ :=
  dist x (G.site (select G α x)) + α * G.fee (select G α x)

def opens (G : Geometry M) (O : Finset (Fin G.m)) (β : ℝ) (x : M) : Prop :=
  O = ∅ ∨ phi G β x ≤ connection G O x

def nextOpen (G : Geometry M) (O : Finset (Fin G.m)) (β : ℝ) (x : M) :
    Finset (Fin G.m) := by
  classical
  exact if opens G O β x then insert (select G β x) O else O

def triggeredFee (G : Geometry M) (O : Finset (Fin G.m)) (β : ℝ) (x : M) : ℝ := by
  classical
  exact if opens G O β x then G.fee (select G β x) else 0

def serviceCost (G : Geometry M) (O : Finset (Fin G.m)) (β : ℝ) (x : M) : ℝ :=
  triggeredFee G O β x + connection G (nextOpen G O β x) x

/-- Only the revealed location list is folded; hidden labels never enter a decision. -/
def openAfter (G : Geometry M) (n : ℕ) (μ δ : ℝ) (xs : List M) : Finset (Fin G.m) :=
  xs.zipIdx.foldl (fun O z => nextOpen G O (penalty n (z.2 + 1) μ δ) z.1) ∅

def streamCost (G : Geometry M) (n : ℕ) (μ δ : ℝ) (xs : List M) : ℝ :=
  (∑ y ∈ openAfter G n μ δ xs, G.fee y) +
  ((xs.zipIdx.map fun z => connection G
    (openAfter G n μ δ (xs.take (z.2 + 1))) z.1).sum)

abbrev Arrival (n : ℕ) := Equiv.Perm (Fin n)

def labelList {n : ℕ} (π : Arrival n) : List (Fin n) := List.ofFn π

def stream {n : ℕ} (u : Fin n → M) (π : Arrival n) : List M := (labelList π).map u

def rank {n : ℕ} (π : Arrival n) (a : Fin n) : ℕ := (π.symm a).val + 1

def avg {α : Type*} (S : Finset α) (f : α → ℝ) : ℝ := (∑ a ∈ S, f a) / S.card

def prob {α : Type*} (S : Finset α) (P : α → Prop) : ℝ := by
  classical
  exact avg S (fun a => if P a then 1 else 0)

def uniformAvg {n : ℕ} (f : Arrival n → ℝ) : ℝ := by
  classical
  exact avg Finset.univ f

def alg {n : ℕ} (G : Geometry M) (u : Fin n → M) (μ δ : ℝ) (π : Arrival n) : ℝ :=
  streamCost G n μ δ (stream u π)

def openingCost (G : Geometry M) (O : Finset (Fin G.m)) : ℝ := ∑ y ∈ O, G.fee y

def connectionCost {n : ℕ} (G : Geometry M) (u : Fin n → M)
    (O : Finset (Fin G.m)) : ℝ := ∑ i, connection G O (u i)

def offlineCost {n : ℕ} (G : Geometry M) (u : Fin n → M)
    (O : Finset (Fin G.m)) : ℝ := openingCost G O + connectionCost G u O

/-- The minimum is restricted to nonempty facility subsets for positive horizons. -/
def optimum {n : ℕ} (G : Geometry M) (u : Fin n → M) : ℝ :=
  sInf {v | ∃ O : Finset (Fin G.m), O.Nonempty ∧ v = offlineCost G u O}

structure Comparator (G : Geometry M) (n : ℕ) where
  opened : Finset (Fin G.m)
  nonempty : opened.Nonempty
  assignment : Fin n → Fin G.m
  assigned_mem : ∀ i, assignment i ∈ opened

end RankCutFacility.Shifted


