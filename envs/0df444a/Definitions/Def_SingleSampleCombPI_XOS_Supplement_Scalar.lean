-- Prove2me | Definitions.Def_SingleSampleCombPI_XOS_Supplement_Scalar
-- name    : SingleSampleCombPI_XOS_Supplement_Scalar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:38:17.489562+00:00
-- url     : https://prove2.me/theorems/287dad8a-79c7-487d-b886-b53a4a6a57b8
-- title:
--   Native concave scalar valuations, supremal and grid benchmarks, and Algorithm 9
-- statement:
--   Scalar valuations $v:[0,1]\to\mathbb R_{\ge0}$ are normalized, monotone and concave; continuity at zero and supporting-price input are not required. An online policy sees the sample, revealed real prefix and current valuation. Feasibility means $x_i\in[0,1]$ and $\sum_i x_i\le1$. The continuous benchmark is the supremum over all feasible allocations. The finite-grid benchmark restricts allocations to $k_i/M$ with integers $0\le k_i\le M$ and $\sum_i k_i\le M$.
--
--   For $M\ge1$, Algorithm 9 forms the marginals $v((k+1)/M)-v(k/M)$, independently permutes each buyer's sample marginals and real marginals among the $M$ slots, and invokes the published Algorithm 7 in each slot with independent symmetric ranks. A buyer receives its number of won slots divided by $M$. Its actual reward is its scalar valuation at this allocation, rather than the sum of slot rewards. The finite random seed includes all independent permutations and ranks, without revealing any future real valuation.
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Algorithm 9 and §5.3, printed pp. 31–32 / PDF pp. 33–34; Lemma 5.9 proof, printed p. 43 / PDF p. 45.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Algorithms

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Native scalar valuations: no supporting-price input and no continuity at 0. -/
abbrev Scalar := ℝ → ℝ

def ScalarValid (v : Scalar) : Prop :=
  v 0 = 0 ∧ (∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ v x) ∧
  MonotoneOn v (Set.Icc 0 1) ∧ ConcaveOn ℝ (Set.Icc 0 1) v

def scalarFeasible {n : ℕ} (x : Fin n → ℝ) : Prop :=
  (∀ i, x i ∈ Set.Icc 0 1) ∧ ∑ i, x i ≤ 1

noncomputable def scalarOpt {n : ℕ} (r : Fin n → Scalar) : ℝ :=
  sSup {z | ∃ x, scalarFeasible x ∧ z = ∑ i, r i (x i)}

/-- The finite grid benchmark, including zero allocations. Supremum is a maximum
on this finite grid; the continuous benchmark need not attain its supremum. -/
noncomputable def scalarGridOpt {n : ℕ} (M : ℕ) (r : Fin n → Scalar) : ℝ :=
  sSup {z | ∃ k : Fin n → Fin (M+1), (∑ i, (k i).val) ≤ M ∧
    z = ∑ i, r i ((k i).val / (M:ℝ))}

structure ScalarPolicy (n : ℕ) where
  Ω : Type
  seed : RandomSource Ω
  act : Ω → (Fin n → Scalar) → List (Fin n × Scalar) → Fin n → Scalar → ℝ

def scalarRun {n : ℕ} (S : ScalarPolicy n) (ω : S.Ω) (s r : Fin n → Scalar)
    (ρ : Equiv.Perm (Fin n)) : Fin n → ℝ :=
  fun i => S.act ω s (prefixOf ρ r i) i (r i)

def ScalarPolicy.Valid {n : ℕ} (S : ScalarPolicy n) : Prop :=
  ∀ ω s r ρ, (∀ i, ScalarValid (s i)) → (∀ i, ScalarValid (r i)) →
    scalarFeasible (scalarRun S ω s r ρ)

noncomputable def scalarExp {n : ℕ} (S : ScalarPolicy n)
    (V : Fin n → Fin 2 → Scalar) (ρ : Equiv.Perm (Fin n)) : ℝ≥0∞ :=
  pexp S.seed (fun ω => avg (fun c : Fin n → Bool =>
    let s := fun i => (gogPair (V i) (c i)).1
    let r := fun i => (gogPair (V i) (c i)).2
    ENNReal.ofReal (∑ i, r i (scalarRun S ω s r ρ i))))

noncomputable def scalarOptExp {n : ℕ} (V : Fin n → Fin 2 → Scalar) : ℝ≥0∞ :=
  avg (fun c : Fin n → Bool =>
    ENNReal.ofReal (scalarOpt (fun i => (gogPair (V i) (c i)).2)))

/-- Marginal k+1; k is zero based. Only M≥1 is used by the theorems. -/
noncomputable def scalarMarginal (M : ℕ) (v : Scalar) (k : Fin M) : ℝ :=
  v (((k.val:ℝ)+1)/M) - v ((k.val:ℝ)/M)

/-- Independent sample permutations, real permutations, and Algorithm 7 ranks. -/
abbrev ScalarSeed (n M : ℕ) :=
  (Fin n → Equiv.Perm (Fin M)) × (Fin n → Equiv.Perm (Fin M)) × (Fin M → Ranks n)

/-- Algorithm 9, using the immutable tie-corrected Algorithm 7 independently
in all M slots. Actual welfare is v(number of won slots / M). -/
noncomputable def alg9 (n M : ℕ) : ScalarPolicy n where
  Ω := ScalarSeed n M
  seed := RandomSource.ofPMF (PMF.uniformOfFintype (ScalarSeed n M))
  act := fun ω s hist i v =>
    (∑ k : Fin M,
      (alg7 n).act (ω.2.2 k)
        (fun _ j => (scalarMarginal M (s j) (ω.1 j k), 1))
        (hist.map fun e => (e.1, (scalarMarginal M e.2 (ω.2.1 e.1 k), 1)))
        i (scalarMarginal M v (ω.2.1 i k), 1)) / (M:ℝ)

noncomputable def concaveRatio : ℝ := (1 - Real.exp (-1))/2

end SingleSampleCombPI.XOS.Supplement


