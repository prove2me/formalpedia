-- Prove2me | Definitions.Def_InfoLossLAR_RegevSearch_CoherentCopy
-- name    : InfoLossLAR_RegevSearch_CoherentCopy
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T02:28:45.35217+00:00
-- url     : https://prove2.me/theorems/9bd171ea-00fb-4c55-b3c7-a67abed9e4e5
-- title:
--   Copying a decoded answer over one shared Gaussian pool
-- statement:
--   A fixed rational decoder query has a nearby rational dual point and an integer answer. On a superposition of such queries, retain the query, native workspace and a clean answer register. Compare copying the decoded answer with copying the ideal answer in Euclidean norm and average this norm over independent Gaussian samples forming one shared classical pool. The budget bounds the resulting change under a public polynomial number of uses.
-- source:
--   Coherent-use interface for https://prove2.me/theorems/9fdfd0c1-342f-4e71-9410-562b6727463a, specializing the compute, copy and uncompute step in Regev, §3.2.2, Lemma 3.14, https://cims.nyu.edu/~regev/papers/qcrypto.pdf, to the native shared-pool decoder and finite query registers.

import Definitions.Def_InfoLossLAR_RegevSearch_SharedPoolBDD

set_option autoImplicit false
set_option maxHeartbeats 700000
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
open InfoLossLAR.WorstCase.RegevSearch RegevLWE.GaussConv
open scoped BigOperators Classical

namespace SharedPoolCoherence
noncomputable section
variable {n : ℕ}

/-- Copying a classical output into a fresh basis register. The first coordinate retains
all of the decoder's workspace, including deferred measurement registers. -/
noncomputable def copied {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (ψ : α → ℂ) (readout : α → β) : EuclideanSpace ℂ (α × β) :=
  open Classical in
  WithLp.toLp 2 (fun p => if p.2 = readout p.1 then ψ p.1 else 0)

def poolWeight (m : ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (R : ℝ)
    (pool : Fin m → Fin n → ℤ) : ℝ := ∏ j, coefficientMass B R (pool j)

/-- A query, its promised rational nearest dual point and its exact integer
answer. The coefficient vector is relative to the original input matrix. -/
structure Query {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (R : ℚ) where
  input : Fin n → ℚ
  nearest : Fin n → ℚ
  answer : Fin n → ℤ
  coords : ∀ j, ∑ i, (B i j : ℚ) * nearest i = (answer j : ℚ)
  close : (R : ℝ)^2 * (∑ i, (((input i-nearest i : ℚ) : ℝ))^2) < (famσ n : ℝ)^2 / 4

/-- The entire set of quantum work bits may differ between query inputs, even
on the same classical pool. The query index is retained in the direct sum. -/
abbrev Outcomes (C : MFamily) {I : Type} (w : I → Str) :=
  (i : I) × Bits ((w i).length + (C.anc (w i).length + 1))

def nativeAmplitude (C : MFamily) (w : Str) :=
  runLayered (C.circ w.length) (basisInput (toBits w))

def nativeOutput (C : MFamily) (w : Str) (a : Bits (w.length + (C.anc w.length + 1))) : Str :=
  List.ofFn (fun j => a (C.outW w.length j))

/-- Copy an actual finite decoder answer, preserving the query index and all of
the native circuit's workspace. -/
def copyGap {I : Type} [Fintype I] (C : MFamily) (w : I → Str) (a : I → ℂ) {b : ℕ}
    (read : Outcomes C w → Bits b) (target : I → Bits b) : ℝ :=
  let ψ (x : Outcomes C w) := a x.1 * nativeAmplitude C (w x.1) x.2
  ‖SharedPoolCoherence.copied ψ read - SharedPoolCoherence.copied ψ (fun x => target x.1)‖

abbrev word {n m : ℕ} {B : Matrix (Fin n) (Fin n) ℤ} {R : ℚ} (k : ℕ)
    (pool : Fin m → Fin n → ℤ) (q : Query B R) : Str := poolBDDInput B R k pool q.input

/-- For each promised query its copied answer agrees with the desired finite
answer exactly on the native machine's signed-vector prefix success event. -/
structure Register {n m t : ℕ} (C : MFamily) {B : Matrix (Fin n) (Fin n) ℤ} {R : ℚ}
    (k : ℕ) (pool : Fin m → Fin n → ℤ) (q : Fin (t+1) → Query B R) where
  width : ℕ
  read : Outcomes C (fun i => word k pool (q i)) → Bits width
  answer : Fin (t+1) → Bits width
  correct : ∀ x, read x = answer x.1 ↔
    encVec encI (q x.1).answer <+: nativeOutput C (word k pool (q x.1)) x.2

/-- Countable common-pool estimate directly in native circuit state norm. It
also holds after applying the same isometric inverse to the two copied states. -/
def CopyBudget (C : MFamily) (P calls : Polynomial ℕ) (N : ℕ) (S : Set ℕ) (e : ℕ → ℝ) : Prop :=
  ∀ n ∈ S, N ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
  ∀ R : ℚ, 0 < R →
    Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) < (R : ℝ) →
  ∀ (k t : ℕ) (q : Fin (t+1) → Query B R) (a : Fin (t+1) → ℂ), (∑ i, ‖a i‖^2 = 1) →
  let prec := poolBDDPrecision (calls.eval n) k
  ∀ regs : (p : Fin (P.eval n) → Fin n → ℤ) → Register C prec p q,
    (∑' p, poolWeight (P.eval n) B R p *
      (2 * ((calls.eval n : ℕ) : ℝ) *
       copyGap C (fun i => word prec p (q i)) a (regs p).read (regs p).answer)) ≤
      e n + 1/(4*((k:ℝ)+1))

end
end SharedPoolCoherence


