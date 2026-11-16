-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Construction
-- name    : QuantumSepPoly_Frobenius_Supplement_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:48:28.695246+00:00
-- url     : https://prove2.me/theorems/7eb0e4ae-2319-48a7-8e9b-9e28e2671406
-- title:
--   Finite-program CSP construction and sampler interface
-- statement:
--   The constructor's first-halting state decodes a finite Boolean edge table and returns no instance for an empty constraint table. The sampler is a finite program together with the saved constructor memory; its finite query is loaded into reserved registers, and it returns one alphabet value per queried vertex.
--
--   The sampler specification requires one assignment law $D$ supported on fully satisfying assignments, exact equality of every permitted marginal law, measurability, and a separate expected-cost bound. The construction specification requires polynomial termination on every run, positive quasilinear size N=128(q+1)ℓ with integer ℓ≥1, sparsity, completeness for every construction outcome, and unsatisfiable-input soundness probability $99/100$. Both specifications are predicates asserted by Lemma 6.4; neither is an assumed structure field or an axiom. The companion theorem assumes neither predicate.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Section 6, p. 25–27 (PDF p. 25–27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_CNF
import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_SparseCSP

noncomputable section
open scoped ENNReal BigOperators

namespace QuantumSepPoly.Frobenius.Supplement
/-- Decoding an actually written CSP: N=n[0], edges at 100+10*N+iN+j,
and Boolean tables after the N² edge slots. Invalid empty tables return none. -/
def decodeCSP (A : ℕ) (s : RAMState) : Option (Σ N, MaxCSP N 2 (Fin A)) := by
  classical
  let N := s.nat 0
  let C := (Finset.univ : Finset (Fin 2 → Fin N)).filter
    (fun t => t 0 < t 1 ∧ s.nat (100+10*N+(t 0).val*N+(t 1).val) = 1)
  exact if h : C.Nonempty then some ⟨N, {
    constraints := C, nonempty := h,
    predicate := fun t a => if s.nat (100+10*N+N^2+
      (((t 0).val*N+(t 1).val)*A+(a 0).val)*A+(a 1).val) = 1 then 1 else 0 }⟩ else none

/-- The returned sampler is a fixed finite program with the construction's saved
memory as its closure. n[0]=N is preserved; n[1] and n[2..] hold the query. -/
def sampleInitial {N : ℕ} (s : RAMState) (S : Finset (Fin N)) : RAMState :=
  let q := S.sort (· ≤ ·)
  {s with
    pc := 0
    stopped := false
    randomIndex := 0
    cost := q.length+1
    nat := fun i => if i = 1 then q.length else
      if 2 ≤ i ∧ i < q.length+2 then (q[i-2]?.map Fin.val).getD 0 else s.nat i}

/-- The sampler writes one alphabet index for each vertex at 10+i. -/
def sampleOutput {N A : ℕ} (hA : 0 < A) (P : RAMProgram) (s : RAMState)
    (S : Finset (Fin N)) (r : RandomTape) : S → Fin A :=
  fun i => ⟨(ramResult P (sampleInitial s S) r).nat (10+i.val.val) % A, Nat.mod_lt _ hA⟩

/-- This is an output contract asserted by Lemma 6.4, never a field of a
construction object. One D works simultaneously for every allowed query. -/
def SamplerSpec {N A n m : ℕ} (hA : 0 < A) (P : RAMProgram) (s : RAMState)
    (I : MaxCSP N 2 (Fin A)) (p : ℝ) : Prop :=
  ∃ D : PMF (Fin N → Fin A),
    (∀ z, D z ≠ 0 → cspValue I z = 1) ∧
    ∀ S : Finset (Fin N), S.card ≤ n+m+2 →
      Measurable (sampleOutput hA P s S) ∧
      (∀ a : S → Fin A,
        tapeLaw {r | sampleOutput hA P s S r = a} =
          D.toMeasure {z | (fun i : S => z i) = a}) ∧
      (∫⁻ r, executionCost P (sampleInitial s S) r ∂tapeLaw) ≤ ENNReal.ofReal p

/-- Entire CSP-construction contract; it occurs only as a theorem conclusion,
or as inherited context for a support about this construction. -/
def ConstructionSpec (P Sample : RAMProgram) (q A δ : ℕ) (ξ C : ℝ)
    (e : ℕ) (C₀ : ℝ) (a₀ : ℕ) : Prop :=
  0 < A ∧ 1 ≤ δ ∧ 0 < ξ ∧ ξ ≤ 1 ∧ 0 < C ∧ 0 < C₀ ∧
  ∀ n m (f : CNF3 n m),
    (∀ r, RAMTerminates P (cnfInput f) (polyBound C e n m) r ∧
      ∃ (N : ℕ) (I : MaxCSP N 2 (Fin A)),
        decodeCSP A (ramResult P (cnfInput f) r) = some ⟨N,I⟩ ∧ 1 ≤ N ∧
        (∃ ℓ : ℕ, 1 ≤ ℓ ∧ N = 128*(q+1)*ℓ) ∧
        (N : ℝ) ≤ C₀*inputSize n m*(Real.logb 2 (inputSize n m))^a₀ ∧ Sparse I δ ∧
        (Satisfiable f → ∃ hA : 0 < A,
          @SamplerSpec N A n m hA Sample (ramResult P (cnfInput f) r) I (polyBound C e n m))) ∧
    (¬ Satisfiable f → ENNReal.ofReal (99/100 : ℝ) ≤ tapeLaw {r |
      ∃ (N : ℕ) (I : MaxCSP N 2 (Fin A)),
        decodeCSP A (ramResult P (cnfInput f) r) = some ⟨N,I⟩ ∧ cspOPT I ≤ 1-ξ})
end QuantumSepPoly.Frobenius.Supplement


