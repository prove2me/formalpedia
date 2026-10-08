-- Prove2me | Definitions.Def_SecretaryWD_Weighted_ReservationAlgorithm
-- name    : SecretaryWD_Weighted_ReservationAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:06:42.20586+00:00
-- url     : https://prove2.me/theorems/4de2da8f-e206-40d7-9b20-869b4f30c8be
-- title:
--   Value classes, reservation rule, classical rule, and Algorithm A
-- statement:
--   For a positive value $x$, its integer value class $i$ is the unique class with $2^{i-1}\le x<2^i$; zero belongs to no class. In a uniform random arrival order $\pi$, the reservation rule first draws $\tau\sim\mathrm{Binom}(n,1/2)$ and observes the first $\tau$ agents. Among these it keeps the best $\min(K,\tau)$, reserving one good in the appropriate value class for each positive-valued kept agent. Higher classes receive heavier goods. Each later agent receives the heaviest still available good of its class, if one exists.
--
--   The classical rule observes $\lfloor n/e\rfloor$ arrivals and selects the first subsequent agent better than every earlier agent. Algorithm $A$ runs the reservation rule with probability $8/(3e+8)$ and the classical rule, assigning its winner the heaviest good, with probability $3e/(3e+8)$. Its expected value is
--
--   $$\mathbb E[A]=\frac{8}{3e+8}\mathbb E[R]+\frac{3e}{3e+8}w(1)\mathbb E[v(e_{\mathrm{sec}})].$$
--
--   This module also defines the class counts $u_i,f_i$, the starting offsets $b_i,o_i$, and the class contributions $R_i,\mathrm{OPT}_i$ used by Lemmas 3.1–3.3.
--
--   **Formalization Note** Arrivals and goods use zero-based `Fin` indices; the paper's time $t$ is Lean index $t-1$. Equal-valued agents are ordered by smaller agent index. The secretary input records both the arrival value and agent identity to preserve this tie break.
-- source:
--   Babaioff, Dinitz, Gupta, Immorlica and Talwar, Secretary Problems: Weights and Discounts, SODA 2009 (authors' version), pp. 4–5, Sections 2–3; p. 12, Appendix C (value classes)

import Mathlib
import Definitions.Def_SecretaryWD_Weighted_Assignment

namespace SecretaryWD.Weighted

/-- The class `[2^(i-1),2^i)` of a positive value. Zero has no class. -/
noncomputable def valueClass (x : ℝ) : ℤ :=
  if 0 < x then Int.floor (Real.log x / Real.log 2) + 1 else 0

def inClass (x : ℝ) (i : ℤ) : Prop := 0 < x ∧ valueClass x = i

/-- The sample is the first `τ` arrivals of `π`; `π` maps time to agent. -/
def inSample {n : ℕ} (π : Equiv.Perm (Fin n)) (τ : ℕ) (e : Fin n) : Prop :=
  (π.symm e).val < τ

/-- The highest `min(K,τ)` sampled agents, using the global tie break. -/
noncomputable def sampleTop {n : ℕ} (v : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) (τ K : ℕ) (e : Fin n) : Prop := by
  classical
  exact inSample π τ e ∧
    (Finset.univ.filter (fun f => inSample π τ f ∧ better v f e)).card < K

/-- The number of sample agents reserving goods in class `i`. -/
noncomputable def reservedCount {n : ℕ} (v : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) (τ K : ℕ) (i : ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun e => sampleTop v π τ K e ∧ inClass (v e) i)).card

/-- Number of reservations in classes strictly above `i`; this is `bᵢ`. -/
noncomputable def reservationStart {n : ℕ} (v : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) (τ K : ℕ) (i : ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun e => sampleTop v π τ K e ∧ 0 < v e ∧ i < valueClass (v e))).card

/-- The `q`-th post-sample agent of a value class takes its `q`-th reserved good. -/
noncomputable def earlierInClass {n : ℕ} (v : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) (τ : ℕ) (e : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun f =>
    τ ≤ (π.symm f).val ∧ (π.symm f).val < (π.symm e).val ∧
      inClass (v f) (valueClass (v e)))).card

/-- The good offered to `e` by the reservation algorithm, if any. -/
noncomputable def reservedGood {n K : ℕ} (v : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) (τ : ℕ) (e : Fin n) : Option (Fin K) := by
  classical
  let i := valueClass (v e)
  let q := earlierInClass v π τ e
  let b := reservationStart v π τ K i
  if h : τ ≤ (π.symm e).val ∧ 0 < v e ∧ q < reservedCount v π τ K i ∧ b + q < K then
    exact some ⟨b + q, h.2.2.2⟩
  else exact none

/-- Final assignment of the reservation algorithm, with a binomial sample size. -/
noncomputable def reservationAssignment {n K : ℕ} (v : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) (τ : ℕ) : Fin K → Option (Fin n) := by
  classical
  intro k
  exact if h : ∃ e : Fin n, reservedGood v π τ e = some k then
    some (Classical.choose h) else none

/-- Agent `e` is earlier than `f` in the total order used by the secretary rule. -/
def betterEntry {m : ℕ} (x : Fin m → ℝ × Fin m) (e f : Fin m) : Prop :=
  (x f).1 < (x e).1 ∨ ((x e).1 = (x f).1 ∧ (x e).2.val < (x f).2.val)

/-- The classical rule observes `⌊m/e⌋` arrivals and takes the first later record. -/
noncomputable def classicalSecretary (m : ℕ) (x : Fin m → ℝ × Fin m) :
    Option (Fin m) := by
  classical
  let cutoff := Nat.floor ((m : ℝ) / Real.exp 1)
  let candidate : Fin m → Prop := fun t => cutoff ≤ t.val ∧
    ∀ s : Fin m, s.val < t.val → betterEntry x t s
  exact if h : ∃ t : Fin m, candidate t ∧
      ∀ s : Fin m, candidate s → t.val ≤ s.val then
    some (Classical.choose h) else none

/-- Number of optimum agents in class `i`, denoted `uᵢ`. -/
noncomputable def optimalClassCount {n K : ℕ} (v : Fin n → ℝ) (i : ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun e : Fin n => valueRank v e < K ∧ inClass (v e) i)).card

/-- Number of optimum goods belonging to classes higher than `i`, denoted `oᵢ`. -/
noncomputable def optimalStart {n K : ℕ} (v : Fin n → ℝ) (i : ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter
    (fun e : Fin n => valueRank v e < K ∧ 0 < v e ∧ i < valueClass (v e))).card

/-- `fᵢ`: goods actually assigned in class `i` by the reservation rule. -/
noncomputable def assignedClassCount {n K : ℕ} (v : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) (τ : ℕ) (i : ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun k : Fin K =>
    ∃ e : Fin n, reservationAssignment v π τ k = some e ∧ inClass (v e) i)).card

/-- The optimum contribution `OPTᵢ` of value class `i`. -/
noncomputable def optimalClassValue {n K : ℕ} (v : Fin n → ℝ)
    (w : Fin K → ℝ) (i : ℤ) : ℝ := by
  classical
  exact ∑ k : Fin K, if h : ∃ e : Fin n, optimalAssignment v k = some e ∧ inClass (v e) i then
    v (Classical.choose h) * w k else 0

/-- The reservation rule's contribution `Rᵢ` of value class `i`. -/
noncomputable def reservedClassValue {n K : ℕ} (v : Fin n → ℝ)
    (w : Fin K → ℝ) (π : Equiv.Perm (Fin n)) (τ : ℕ) (i : ℤ) : ℝ := by
  classical
  exact ∑ k : Fin K, if h : ∃ e : Fin n,
      reservationAssignment v π τ k = some e ∧ inClass (v e) i then
    v (Classical.choose h) * w k else 0

/-- Uniform average over all arrival permutations. -/
noncomputable def orderAverage {n : ℕ} (F : Equiv.Perm (Fin n) → ℝ) : ℝ :=
  (1 / (Nat.factorial n : ℝ)) * ∑ π : Equiv.Perm (Fin n), F π

/-- Conditional expectation over `τ ∼ Binom(n,1/2)`. -/
noncomputable def binomialAverage (n : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ τ ∈ Finset.range (n + 1), ((n.choose τ : ℝ) / (2 : ℝ) ^ n) * F τ

noncomputable def expectedAssignedClassCount {n K : ℕ} (v : Fin n → ℝ)
    (i : ℤ) : ℝ :=
  orderAverage (fun π => binomialAverage n
    (fun τ => (assignedClassCount (K := K) v π τ i : ℝ)))

noncomputable def expectedReservedClassValue {n K : ℕ} (v : Fin n → ℝ)
    (w : Fin K → ℝ) (i : ℤ) : ℝ :=
  orderAverage (fun π => binomialAverage n
    (fun τ => reservedClassValue v w π τ i))

noncomputable def expectedReservationValue {n K : ℕ} (v : Fin n → ℝ)
    (w : Fin K → ℝ) : ℝ :=
  orderAverage (fun π => binomialAverage n
    (fun τ => assignmentValue v w (reservationAssignment v π τ)))

/-- Expected value of the selected agent, with no selection worth zero. -/
noncomputable def expectedSecretaryValue {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  orderAverage (fun π =>
    ((classicalSecretary n (fun t => (v (π t), π t))).map
      (fun t => v (π t))).getD 0)

/-- Expected value of Algorithm A's explicitly weighted mixture. -/
noncomputable def expectedAlgorithmA {n K : ℕ} (v : Fin n → ℝ)
    (w : Fin K → ℝ) (hK : 0 < K) : ℝ :=
  let e := Real.exp 1
  (8 / (3 * e + 8)) * expectedReservationValue v w +
    ((3 * e) / (3 * e + 8)) * w ⟨0, hK⟩ * expectedSecretaryValue v

end SecretaryWD.Weighted


