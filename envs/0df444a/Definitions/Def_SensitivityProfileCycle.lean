-- Prove2me | Definitions.Def_SensitivityProfileCycle
-- name    : SensitivityProfileCycle
-- status  : Definition
-- author  : @dmilosch
-- created : 2026-10-21T21:18:57.771912+00:00
-- url     : https://prove2.me/theorems/6f70ee20-3318-4365-9377-022df0d68b3f
-- title:
--   Finite tournament and sensitivity-profile cycle certificates
-- statement:
--   A certificate consists of finitely many tournament labels, nested-predicate recipes, and natural-number profile matrices. It is a sufficient-data interface for the recursive Boolean construction; it contains no Boolean-function witness or asymptotic separation assertion.
--
--   Choose a number of predicate states, an output state, a regular tournament on $K>1$ vertices, binary labels on its arcs, and a cycle of $p>0$ recipes. The labels satisfy specified finite-set bounds: every vertex set whose outgoing label disagreements with prescribed target colors are at most $q$ per vertex has size below its cutoff. A separate cutoff applies when a coherent set has a vertex pointing to every other vertex in that set.
--
--   For each phase there are two nonnegative integer matrices $Z_d,Y_d$, bounding simultaneous flips of nested predicates at inputs where both indexed predicates output false or both output true, respectively. The recipe validity and compatibility conditions are those of the cited construction. Every initial upper-triangular entry is at least one. Each next profile dominates the source's exact one-step recurrence on some contained interval of indices. At the end of the cycle, the matrices satisfy
--
--   $$Z_p(i,j)\le R Z_0(i,j),\qquad Y_p(i,j)\le R Y_0(i,j)\quad(i\le j).$$
--
--   The finite maxima, minima, binomial coefficients, and truncated natural-number subtractions in those recurrences are included verbatim in the definition. Once all scalar sizes and explicit graph, label, recipe, and matrix entries are fixed, each certificate obligation concerns finite data. The sizes themselves are unrestricted.
-- source:
--   Original variable-cycle generalization of the recursive bounds in accepted Prove2Me submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a, https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2, namespaces SensitivityNQ and SensitivitySourceCombinedPeriodic, especially profile_step_bounds and stage_blocks. Source authors: yousofy with Codex; retains the attributed OpenAI/math, Robin Kothari with Codex, and earlier community foundations. Mission motivation: https://github.com/bigospeedrun/site/issues/2. The source does not prove that this generalization attains 2.15.

import Mathlib

/-!
Finite combinatorial certificates for recursive sensitivity profiles.

The arithmetic recurrences below are copied faithfully from the accepted
Prove2Me submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a (theorem
46659a00-722d-4dc9-b28e-ef02d6a0c9c2), by yousofy with Codex. That source
retains the OpenAI sensitivity construction, Robin Kothari and Codex's
nested-predicate tournament construction, and earlier community attribution.

This file adds a variable-size, variable-period certificate interface. Its
fields are finite graph, label, recipe and natural-number matrix data.
It does not assert that any certificate attaining exponent 2.15 exists.
-/

set_option autoImplicit false
namespace SensitivityProfileCycle

def auxCost (s t : Fin 3) (b : Bool) : ℕ :=
  if s = 0 ∧ t = 2 then 0 else
  if b then (if s = 2 then 2 else 1) else (if t = 0 then 2 else 1)

structure Recipe (n : ℕ) where
  target : Fin n → Fin n
  gate : Fin n → Fin n
  aux : Fin n → Fin 3
  tol : Fin n → ℕ

variable {n : ℕ}

def Recipe.Valid (C : Recipe n) : Prop :=
  Monotone C.target ∧
  (∀ i j, i ≤ j → j.val < 3 → C.aux i ≤ C.aux j) ∧
  (∀ i j, i ≤ j → 3 ≤ i.val →
    C.gate j ≤ C.gate i ∧ C.tol j ≤ C.tol i ∧ C.gate i ≤ C.target i)

def rawOne (h : ℕ) (C : Recipe n) (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  if j.val < 3 then auxCost (C.aux i) (C.aux j) true*Y (C.target i) (C.target j)
  else if i.val < 3 then auxCost (C.aux i) 2 true*Y (C.target i) (C.target j)
  else 2*Y (C.target i) (C.target j) +
    if C.tol i = C.tol j then (h-(C.tol j))*Z (C.gate j) (C.gate i) else 0

def Compatible (C : Recipe n) (Z Y : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j, i ≤ j → 3 ≤ i.val →
    Z (C.gate j) (C.target j) ≤ Z (C.target i) (C.target j) ∧
    Y (C.gate j) (C.target j) ≤ Y (C.gate j) (C.gate i)


def targetCost (q v a b : ℕ) : ℕ :=
  min (v-1) (2*q+1)*a + ((v-1)-min (v-1) (2*q+1))*b


def coupledCost (q v a b c e : ℕ) : ℕ :=
  (Finset.range (2*q+2)).sup fun n =>
    (Finset.range (2*q+4)).sup fun m =>
      if (n+m).choose 2 ≤ q*n+(q+1)*m then
        n*a+((v-1)-n)*b+((m*(q+1)-m.choose 2)*c+m.choose 2*e)
      else 0


def rawZeroCoupled (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  let a := Z (C.target i) (C.target j)
  let b := Z (C.gate j) (C.target j)
  let c := Y (C.gate j) (C.gate i)
  let e := Y (C.gate j) (C.target j)
  if j.val < 3 then k*(auxCost (C.aux i) (C.aux j) false*a)
  else if i.val < 3 then
    if C.aux i = 0 then 0
    else if C.tol j = 0 then
      max (a+(t-2)*Z (min (C.target i) (C.gate j)) (C.target j))
        ((t-1)*Z (min (C.target i) (C.gate j)) (C.target j))
    else targetCost (C.tol j) (v (C.tol j)) a
      (min a (Z (min (C.target i) (C.gate j)) (C.target j)))
  else if C.tol j = 0 then
    if C.tol i = 0 then
      max (max (max (max (a+c+(t-3)*b) (a+e+(t-2)*b)) (c+e+(t-3)*b)) (2*e+(t-2)*b)) (3*e+(t-4)*b)
    else max (a+(t-2)*b) ((t-1)*b)
  else if C.tol i = C.tol j then
    coupledCost (C.tol j) (v (C.tol j)) a b c e
  else targetCost (C.tol j) (v (C.tol j)) a b


def ordinaryLimit (q m u : ℕ) : ℕ :=
  min (u*(q+1)-u.choose 2) (m*(q+1)-m.choose 2)

def ordinaryCost (q v a b c e : ℕ) : ℕ :=
  (Finset.range (2*q+2)).sup fun n =>
    (Finset.range (2*q+4)).sup fun m =>
      (Finset.range (2*q+4)).sup fun u =>
        if (n+m).choose 2 ≤ q*n+(q+1)*m ∧
            n+u ≤ v-1 ∧ u ≤ m ∧ u ≤ ordinaryLimit q m u then
          n*a+(v-1-u-n)*b+ordinaryLimit q m u*c+
            (m*(q+1)-ordinaryLimit q m u)*e
        else 0


def effectiveCutoff (v w n u : ℕ) : ℕ := if n+u = 0 then v else w

def sourceCost (v w a b c e : ℕ) : ℕ :=
  (Finset.range 2).sup fun n =>
    (Finset.range 4).sup fun m =>
      (Finset.range 4).sup fun u =>
        if (n+m).choose 2 ≤ m ∧ n+u ≤ effectiveCutoff v w n u-1 ∧
            u ≤ m ∧ u ≤ ordinaryLimit 0 m u then
          n*a+(effectiveCutoff v w n u-1-u-n)*b+
            ordinaryLimit 0 m u*c+
            (m-ordinaryLimit 0 m u)*e
        else 0


def strictSourceCost (t w a b c e : ℕ) : ℕ :=
  max (max (max (max (max (a+c+(w-3)*b) (a+e+(w-2)*b))
    (c+e+(w-3)*b)) (2*e+(w-2)*b)) (3*e+(w-3)*b)) ((t-1)*b)


def rawZeroOrdinary (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  if 3 ≤ i.val ∧ C.tol i = C.tol j then
    min (rawZeroCoupled k t v C Z Y i j)
      (ordinaryCost (C.tol j) (v (C.tol j))
        (Z (C.target i) (C.target j)) (Z (C.gate j) (C.target j))
        (Y (C.gate j) (C.gate i)) (Y (C.gate j) (C.target j)))
  else rawZeroCoupled k t v C Z Y i j


def rawZeroSource (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  if 3 ≤ i.val ∧ C.tol i = 0 ∧ C.tol j = 0 then
    min (rawZeroOrdinary k t v C Z Y i j)
      (sourceCost t w
        (Z (C.target i) (C.target j)) (Z (C.gate j) (C.target j))
        (Y (C.gate j) (C.gate i)) (Y (C.gate j) (C.target j)))
  else rawZeroOrdinary k t v C Z Y i j


def rawZeroSourceFull (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  let a := Z (C.target i) (C.target j)
  let b := Z (C.gate j) (C.target j)
  let c := Y (C.gate j) (C.gate i)
  let e := Y (C.gate j) (C.target j)
  if j.val < 3 then rawZeroSource k t v w C Z Y i j
  else if i.val < 3 then
    if C.aux i = 0 then rawZeroSource k t v w C Z Y i j
    else if C.tol j = 0 then
      max (a+(w-2)*Z (min (C.target i) (C.gate j)) (C.target j))
        ((t-1)*Z (min (C.target i) (C.gate j)) (C.target j))
    else rawZeroSource k t v w C Z Y i j
  else if C.tol j = 0 then
    if C.tol i = 0 then
      min (rawZeroSource k t v w C Z Y i j)
        (strictSourceCost t w a b c e)
    else max (a+(w-2)*b) ((t-1)*b)
  else rawZeroSource k t v w C Z Y i j


def externalSlots (q m : ℕ) : ℕ := m*(q+1)-m.choose 2

/-- Residual outgoing budget after all arcs in the positive-target/guard
union are counted.  Under the coupled constraint this equals
`externalSlots - max(0,n*m+choose(n,2)-q*n)`. -/
def positiveResidual (q n m : ℕ) : ℕ :=
  min (externalSlots q m) (q*n+(q+1)*m-(n+m).choose 2)

def dedupLimit (q n m u : ℕ) : ℕ :=
  min (ordinaryLimit q m u) (positiveResidual q n m+u*n)

def dedupChoice (q n m u : ℕ) : ℕ :=
  max u (min (dedupLimit q n m u) (positiveResidual q n m+n))

def dedupCost (internal : ℕ → ℕ) (q v a b c e : ℕ) : ℕ :=
  (Finset.range (2*q+2)).sup fun n =>
    (Finset.range (2*q+4)).sup fun m =>
      (Finset.range (2*q+4)).sup fun u =>
        if (n+m).choose 2 ≤ q*n+(q+1)*m ∧
            n+u ≤ v-1 ∧ u ≤ m ∧ u ≤ dedupLimit q n m u then
          n*a+(v-1-u-n)*b+
            min (dedupChoice q n m u) (positiveResidual q n m+n)*c+
            (externalSlots q m-dedupChoice q n m u+internal m)*e
        else 0




def ordinaryDedupInternalCost (r q v a b c e : ℕ) : ℕ :=
  dedupCost (fun m => min (m.choose 2) (r*m)) q v a b c e


def rawZeroDedupBoth (k t : ℕ) (v : ℕ → ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  if 3 ≤ i.val ∧ C.tol i = C.tol j then
    min (rawZeroCoupled k t v C Z Y i j)
      (ordinaryDedupInternalCost 2 (C.tol j) (v (C.tol j))
        (Z (C.target i) (C.target j)) (Z (C.gate j) (C.target j))
        (Y (C.gate j) (C.gate i)) (Y (C.gate j) (C.target j)))
  else rawZeroCoupled k t v C Z Y i j


def rawZeroSourceCombined (k t : ℕ) (v : ℕ → ℕ) (w : ℕ) (C : Recipe n)
    (Z Y : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  min (rawZeroSourceFull k t v w C Z Y i j) (rawZeroDedupBoth k t v C Z Y i j)

def extendCutoffs {q : ℕ} (v : Fin q → ℕ) (a : ℕ) : ℕ :=
  if h : a < q then v ⟨a, h⟩ else 0

open scoped Classical

/-- Finite data sufficient for an iterated nested-predicate construction.
The phase profiles include both endpoints, numbered `0` through `period`.
All certificate tests are statements about finite sets or natural numbers. -/
structure Certificate where
  states : ℕ
  output : Fin states
  vertices : ℕ
  vertices_gt_one : 1 < vertices
  degree : ℕ
  period : ℕ
  period_pos : 0 < period
  radius : ℕ
  ordinaryCutoff : ℕ
  ordinary_ge_four : 4 ≤ ordinaryCutoff
  sourceCutoff : ℕ
  source_ge_four : 4 ≤ sourceCutoff
  toleranceCount : ℕ
  cutoffs : Fin toleranceCount → ℕ
  cutoff_zero : extendCutoffs cutoffs 0 = ordinaryCutoff
  adj : Fin vertices → Fin vertices → Prop
  loopless : ∀ i, ¬ adj i i
  complement : ∀ {i j}, i ≠ j → (adj i j ↔ ¬ adj j i)
  outdegree : ∀ i, (Finset.univ.filter (adj i)).card = degree
  label : Fin vertices → Fin vertices → Fin 2
  coherent : ∀ (I : Finset (Fin vertices)) (colors : Fin vertices → Fin 2),
    (∀ i ∈ I, ∀ j ∈ I, adj i j → label i j = colors j) →
      I.card < ordinaryCutoff
  defect : ∀ q : Fin toleranceCount,
    ∀ (I : Finset (Fin vertices)) (colors : Fin vertices → Fin 2),
      (∀ i ∈ I, (I.filter (fun j => adj i j ∧ label i j ≠ colors j)).card ≤ q.val) →
        I.card < cutoffs q
  source : ∀ (I : Finset (Fin vertices)) (colors : Fin vertices → Fin 2),
    (∃ s ∈ I, ∀ j ∈ I, j ≠ s → adj s j) →
    (∀ i ∈ I, (I.filter (fun j => adj i j ∧ label i j ≠ colors j)).card ≤ 0) →
      I.card < sourceCutoff
  recipe : Fin period → Recipe states
  valid : ∀ d, (recipe d).Valid
  tolerance_bound : ∀ d i, 3 ≤ i.val → 0 < (recipe d).tol i →
    (recipe d).tol i < toleranceCount
  zeroProfile : Fin (period + 1) → Fin states → Fin states → ℕ
  oneProfile : Fin (period + 1) → Fin states → Fin states → ℕ
  initial_positive : ∀ i j, i ≤ j →
    1 ≤ zeroProfile 0 i j ∧ 1 ≤ oneProfile 0 i j
  compatible : ∀ d, Compatible (recipe d)
    (zeroProfile d.castSucc) (oneProfile d.castSucc)
  zero_step : ∀ d i j, i ≤ j → ∃ a b, i ≤ a ∧ a ≤ b ∧ b ≤ j ∧
    rawZeroSourceCombined vertices ordinaryCutoff (extendCutoffs cutoffs) sourceCutoff
      (recipe d) (zeroProfile d.castSucc) (oneProfile d.castSucc) a b ≤
        zeroProfile d.succ i j
  one_step : ∀ d i j, i ≤ j → ∃ a b, i ≤ a ∧ a ≤ b ∧ b ≤ j ∧
    rawOne degree (recipe d) (zeroProfile d.castSucc) (oneProfile d.castSucc) a b ≤
      oneProfile d.succ i j
  zero_cycle : ∀ i j, i ≤ j →
    zeroProfile (Fin.last period) i j ≤ zeroProfile 0 i j * radius
  one_cycle : ∀ i j, i ≤ j →
    oneProfile (Fin.last period) i j ≤ oneProfile 0 i j * radius

end SensitivityProfileCycle


