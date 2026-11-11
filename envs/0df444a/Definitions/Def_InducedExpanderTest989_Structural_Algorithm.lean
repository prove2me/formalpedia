-- Prove2me | Definitions.Def_InducedExpanderTest989_Structural_Algorithm
-- name    : InducedExpanderTest989_Structural_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:58:58.039618+00:00
-- url     : https://prove2.me/theorems/01d777e3-bbc3-4403-8257-4971ed566eba
-- title:
--   AnchorTest with executed walks, caching, merge sort and binary search
-- statement:
--   AnchorTest evaluates Algorithm 1 at κ′=max{κ,3/4}. It reads the full adjacency table exactly when k>n/Λ or 66Rℓ√(nΛk)>dn; this branch queries each of the nd slots once and then uses cached answers. Each endpoint sample draws a uniform length j<ℓ and executes j lazy steps, using a fair coin and, on a move attempt, a uniform slot and an oracle query or stored-table read.
--
--   Each of R independent anchors has one list A of m_A endpoints, which is sorted once by balanced merge sort. Each of its k fresh partners has m_D independent endpoints, all searched in the sorted array A by binary search. The collision count increments exactly when at least one search succeeds. An anchor is flagged if its fraction of collisions is at least α−β/2; acceptance requires a fraction of flags at least α/2:
--   $$\widehat f\ge\alpha-\beta/2,\qquad N_{\rm flag}/R\ge\alpha/2.$$
--   Coins, draws and oracle queries are program constructors. Moves, list storage, sorting comparisons and copying, binary-search probes and comparisons, counter updates, threshold tests, parameter arithmetic and table writes carry ticks. The graph is never available to this implementation except through queries. Defaults at n=0, d=0 or ℓ=0 lie outside the theorem domains. This supplies a concrete algorithm whose success probability and worst-case costs can be audited.
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.16 (PDF p.18), Algorithm 1; §3 p.13; running-time accounting p.32; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/989.pdf

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Programs
import Definitions.Def_InducedExpanderTest989_Structural_Parameters

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural

open Prog
attribute [local instance] Classical.propDecidable

/-- A cached table is data learned by queries, never a supplied graph. -/
abbrev Table (n d : ℕ) := Oracle n d

def tableRead {n d : ℕ} (T : Option (Table n d)) (v : Fin n) (i : Fin d) :
    Prog n d (Option (Fin n)) :=
  match T with
  | none => .query v i .ret
  | some t => .tick (.ret (t v i))

def readTable {n d : ℕ} (slots : List (Fin n × Fin d)) (T : Table n d) :
    Prog n d (Table n d) :=
  match slots with
  | [] => .ret T
  | (v,i)::xs => .query v i (fun z =>
      charge 3 (readTable xs (Function.update T v (Function.update (T v) i z))))

def walkStep {n d : ℕ} (hd : 0 < d) (T : Option (Table n d)) (x : Fin n) :
    Prog n d (Fin n) :=
  .sample 2 (by decide) fun b =>
    charge 1 (if b.val = 0 then .ret x else
      .sample d hd fun i => (tableRead T x i).bind fun z => .tick (.ret (z.getD x)))

def walkSteps {n d : ℕ} (hd : 0 < d) (T : Option (Table n d)) :
    ℕ → Fin n → Prog n d (Fin n)
  | 0, x => .ret x
  | j+1, x => (walkStep hd T x).bind (walkSteps hd T j)

/-- Sample the length, then execute that many coin/slot/query steps. -/
def endpoint {n d : ℕ} (hd : 0 < d) (T : Option (Table n d)) (ℓ : ℕ)
    (x : Fin n) : Prog n d (Fin n) :=
  if h : 0 < ℓ then .sample ℓ h (fun j => walkSteps hd T j.val x) else .ret x

def endpointList {n d : ℕ} (hd : 0 < d) (T : Option (Table n d)) (ℓ : ℕ)
    (x : Fin n) : ℕ → Prog n d (List (Fin n))
  | 0 => .ret []
  | m+1 => (endpoint hd T ℓ x).bind fun z =>
      (endpointList hd T ℓ x m).bind fun zs => .tick (.ret (z::zs))

/-- Merge compares labels at explicit tick nodes. Fuel is the sum of the lengths. -/
def mergeFuel {n d : ℕ} : ℕ → List (Fin n) → List (Fin n) → Prog n d (List (Fin n))
  | 0, a, b => charge (a.length+b.length) (.ret (a++b))
  | _+1, [], b => charge b.length (.ret b)
  | _+1, a, [] => charge a.length (.ret a)
  | f+1, x::xs, y::ys => charge 2 (
      if x ≤ y then (mergeFuel f xs (y::ys)).bind fun r => .tick (.ret (x::r))
      else (mergeFuel f (x::xs) ys).bind fun r => .tick (.ret (y::r)))

/-- Balanced merge sort. Splitting and copying are charged linearly at each level. -/
def sortFuel {n d : ℕ} : ℕ → List (Fin n) → Prog n d (List (Fin n))
  | 0, a => .ret a
  | f+1, a => charge 2 (if a.length ≤ 1 then .ret a else
      charge (20*a.length+20) (
        (sortFuel f (a.take (a.length/2))).bind fun l =>
        (sortFuel f (a.drop (a.length/2))).bind fun r =>
        mergeFuel (l.length+r.length) l r))

def sortAnchor {n d : ℕ} (a : List (Fin n)) : Prog n d (Array (Fin n)) :=
  (sortFuel a.length a).bind fun b => charge (b.length+1) (.ret b.toArray)

/-- Binary search uses random-access array probes and charged label comparisons. -/
def binaryFuel {n d : ℕ} (A : Array (Fin n)) (x : Fin n) :
    ℕ → ℕ → ℕ → Prog n d Bool
  | 0, _, _ => .ret false
  | f+1, lo, hi => charge 2 (if lo < hi then
      let mid := (lo+hi)/2
      charge 6 (match A[mid]? with
        | none => .ret false
        | some y => .tick (if y = x then .ret true else .tick (
            if y < x then binaryFuel A x f (mid+1) hi
            else binaryFuel A x f lo mid)))
    else .ret false)

def searchList {n d : ℕ} (A : Array (Fin n)) : List (Fin n) → Prog n d Bool
  | [] => .ret false
  | x::xs => (binaryFuel A x (A.size+1) 0 A.size).bind fun b =>
      (searchList A xs).bind fun c => charge 2 (.ret (b || c))

/-- Every partner uses a fresh vertex and a fresh list; A is reused. -/
def partnerCount {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (T : Option (Table n d))
    (ℓ mD : ℕ) (A : Array (Fin n)) : ℕ → Prog n d ℕ
  | 0 => .tick (.ret 0)
  | k+1 => .sample n hn fun y =>
      (endpointList hd T ℓ y mD).bind fun D =>
      (searchList A D).bind fun b =>
      (partnerCount hn hd T ℓ mD A k).bind fun c =>
      .tick (.ret (c + if b then 1 else 0))

def anchorFlag {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (T : Option (Table n d))
    (α κ ϕ : ℝ) : Prog n d Bool :=
  .sample n hn fun x =>
    (endpointList hd T (window n α κ ϕ) x (anchorsLength n α κ)).bind fun A =>
    (sortAnchor A).bind fun sorted =>
    (partnerCount hn hd T (window n α κ ϕ) (partnersLength n α κ) sorted
      (partners α κ)).bind fun c =>
    charge 5 (.ret (decide ((c : ℝ) / partners α κ ≥ α - beta α κ / 2)))

def flagCount {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (T : Option (Table n d))
    (α κ ϕ : ℝ) : ℕ → Prog n d ℕ
  | 0 => .tick (.ret 0)
  | r+1 => (anchorFlag hn hd T α κ ϕ).bind fun b =>
      (flagCount hn hd T α κ ϕ r).bind fun c =>
      .tick (.ret (c + if b then 1 else 0))

def experiment {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (T : Option (Table n d))
    (α κ ϕ δ : ℝ) : Prog n d Bool :=
  (flagCount hn hd T α κ ϕ (rounds α δ)).bind fun c =>
  charge 4 (.ret (decide ((c : ℝ) / rounds α δ ≥ α / 2)))

/-- Algorithm 1; 100 arithmetic ticks cover lines 1–6, including max κ (3/4).
All data-dependent intersections come from the ticked merge-sort/binary-search routines.
Defaults at n=0 or d=0 are outside every theorem's parameter domain. -/
def anchorTest (n d : ℕ) (α κ ϕ δ : ℝ) : Prog n d Bool := by
  classical
  exact charge 100 (if hn : 0 < n then if hd : 0 < d then
    let κ' := effectiveKappa κ
    if (partners α κ' : ℝ) > n / confidence α κ' ∨
      66 * rounds α δ * window n α κ' ϕ * Real.sqrt (n * confidence α κ' * partners α κ') >
        (d*n : ℕ) then
      (charge (n*d) (readTable (Finset.univ : Finset (Fin n × Fin d)).toList
        (fun _ _ => none))).bind fun T => experiment hn hd (some T) α κ' ϕ δ
    else experiment hn hd none α κ' ϕ δ
    else .ret false else .ret false)

end InducedExpanderTest989.Structural


