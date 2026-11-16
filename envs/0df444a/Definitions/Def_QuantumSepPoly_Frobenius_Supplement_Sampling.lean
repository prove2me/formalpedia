-- Prove2me | Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Sampling
-- name    : QuantumSepPoly_Frobenius_Supplement_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:50:23.856878+00:00
-- url     : https://prove2.me/theorems/092fb132-7298-429c-bdd2-edd2c6fbc253
-- title:
--   Independent empirical reconstruction with a global cutoff
-- statement:
--   For every nonempty query $S$ with $|S|\le4k$, the experiment makes $s$ sampler calls on independent tape subsequences. Empirical frequencies count the returned partial assignments. Nontermination contributes infinite total cost. The matrix entry is zero when repeated vertex indices carry inconsistent labels; otherwise it is $N^{-2k}\widehat p_S(a)$ for the joint partial assignment on all $4k$ row/column occurrences.
--
--   The good event is the conjunction of total sampling cost at most $200s(N|\Omega|)^{4k}p$ and Frobenius error at most $\varepsilon/[32(N|\Omega|)^{2k}]$. Independence is obtained by an injective pairing of query/repetition/draw indices, not by replacing actual sampler execution with ideal marginals.
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Section 6, p. 29–31 (PDF p. 29–31); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_Construction
import Definitions.Def_QuantumSepPoly_Frobenius_Supplement_IdealState

noncomputable section
open scoped ENNReal BigOperators

namespace QuantumSepPoly.Frobenius.Supplement
/-- Pairwise-disjoint random-tape subsequences for each query and repetition. -/
def splitTape (r : RandomTape) (tag : ℕ) : RandomTape :=
  (fun i => r.1 (Nat.pair tag i), fun i => r.2 (Nat.pair tag i.1, i.2))

def queryCode {N : ℕ} (S : Finset (Fin N)) : ℕ := ∑ i ∈ S, 2^i.val

def callTape {N : ℕ} (r : RandomTape) (S : Finset (Fin N)) (j : ℕ) : RandomTape :=
  splitTape r (Nat.pair (queryCode S) j)

/-- Full sampling experiment before the global cutoff; nonhalting calls have
infinite cost, so cannot belong to the successful event. -/
def totalSamplingCost {N : ℕ} (P : RAMProgram) (s₀ : RAMState) (k s : ℕ)
    (r : RandomTape) : ℝ≥0∞ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin N))).filter (fun S => S.Nonempty ∧ S.card ≤ 4*k),
    ∑ j ∈ Finset.range s, executionCost P (sampleInitial s₀ S) (callTape r S j)

def empirical {N A : ℕ} (hA : 0 < A) (P : RAMProgram) (s₀ : RAMState)
    (s : ℕ) (r : RandomTape) (S : Finset (Fin N)) (a : S → Fin A) : ℝ :=
  ((Finset.range s).filter (fun j => sampleOutput hA P s₀ S (callTape r S j) = a)).card / (s : ℝ)

/-- The 4k vertex-label occurrences of a matrix coordinate pair. -/
def occurrences {N A k : ℕ} (x y : Block N A k × Block N A k) :
    Fin (4*k) → Register N A :=
  fun j => if h : j.val < k then x.1 ⟨j.val,h⟩ else
    if h : j.val < 2*k then x.2 ⟨j.val-k,by omega⟩ else
    if h : j.val < 3*k then y.1 ⟨j.val-2*k,by omega⟩ else y.2 ⟨j.val-3*k,by omega⟩

def empiricalState {N A : ℕ} (hA : 0 < A) (P : RAMProgram) (s₀ : RAMState)
    (k s : ℕ) (r : RandomTape) : TwoBlockOp N A k := by
  classical
  exact fun x y =>
    let o := occurrences x y
    let S := Finset.univ.image (fun j => (o j).1)
    if h : ∀ i j, (o i).1 = (o j).1 → (o i).2 = (o j).2 then
      let a : S → Fin A := fun i =>
        (o (Classical.choose (Finset.mem_image.mp i.property))).2
      ((N : ℂ)^(- (2*k : ℤ))) * (empirical hA P s₀ s r S a : ℂ)
    else 0

def SamplingEvent {N A : ℕ} (hA : 0 < A) (P : RAMProgram) (s₀ : RAMState)
    (k s : ℕ) (ε : ℚ) (p : ℝ) (D : PMF (Fin N → Fin A)) (r : RandomTape) : Prop :=
  totalSamplingCost (N := N) P s₀ k s r ≤ ENNReal.ofReal (samplerBudget N A k s p) ∧
  frob (empiricalState hA P s₀ k s r - idealState k D) ≤
    (ε : ℝ)/(32*((N*A : ℕ) : ℝ)^(2*k))
end QuantumSepPoly.Frobenius.Supplement


