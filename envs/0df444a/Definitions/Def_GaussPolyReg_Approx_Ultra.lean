-- Prove2me | Definitions.Def_GaussPolyReg_Approx_Ultra
-- name    : GaussPolyReg_Approx_Ultra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:36.312644+00:00
-- url     : https://prove2.me/theorems/7a5e5850-1221-4641-bd7f-4631576cb1d0
-- title:
--   Sequence-level Gaussian chaos ultraproduct and primitive basis interfaces
-- statement:
--   Let $U$ be a nonprincipal ultrafilter on $\mathbb N$. The bounded sequences $B_d$ consist of $p_n\in H_{\le d}(X_1,\ldots,X_n)$ with uniformly bounded L² norms. Two sequences represent the same class when $\|p_n-q_n\|_2\to_U0$. The pairing and norm are the corresponding real ultralimits.
--
--   $$\langle[p],[q]\rangle=\lim_U\mathbb E[p_nq_n],\qquad \|[p]\|=\lim_U\|p_n\|_2.$$
--
--   A primitive homogeneous sequence is orthogonal along $U$ to every top product of two bounded sequences of positive complementary degrees. A primitive basis is a graded family orthonormal for this pairing and dense in each primitive space. Its representatives have squared norm one for $U$-almost every $n$. All grades are positive.
--
--   The Hilbert-sequence predicate spells out existence of the limits, representative independence, bilinearity, symmetry, positivity, identification of the nullspace and completeness. It is a proposition to be proved in Lemma 3.3, not an assumed instance. The Hermite-basis predicate similarly spells out the conclusions to be proved in Theorem 3.5. L² expansions use convergence of the net of finite partial sums, allowing arbitrary, even uncountable, index sets.
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), §3.2–3.3.1, pp.5–10, (3.2),(3.6)–(3.8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_GaussPolyReg_Approx_Tensors

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx
attribute [local instance] Classical.propDecidable

abbrev Sequence := ℕ → Original

def boundedLE (d : ℕ) (p : Sequence) : Prop :=
  (∀ n, p n ∈ finiteChaosLE n d) ∧ ∃ C : ℝ, ∀ n, ‖p n‖ ≤ C

def boundedHom (d : ℕ) (p : Sequence) : Prop :=
  (∀ n, p n ∈ finiteChaos n d) ∧ ∃ C : ℝ, ∀ n, ‖p n‖ ≤ C

def ultraPair (U : Ultrafilter ℕ) (p q : Sequence) : ℝ :=
  Filter.limUnder (U : Filter ℕ) (fun n => pairing (p n) (q n))
def ultraNorm (U : Ultrafilter ℕ) (p : Sequence) : ℝ :=
  Filter.limUnder (U : Filter ℕ) (fun n => ‖p n‖)
def sameClass (U : Ultrafilter ℕ) (p q : Sequence) : Prop :=
  Tendsto (fun n => ‖p n - q n‖) (U : Filter ℕ) (𝓝 0)
def seqTop (r s : ℕ) (p q : Sequence) : Sequence :=
  fun n => topProduct r s (p n) (q n)

/-- Orthogonal to the generating products, equivalently to their closed span, (3.2). -/
def primitive (U : Ultrafilter ℕ) (d : ℕ) (p : Sequence) : Prop :=
  boundedHom d p ∧ ∀ r, 0 < r → r < d → ∀ u v : Sequence,
    boundedHom r u → boundedHom (d-r) v →
    Tendsto (fun n => pairing (p n) (topProduct r (d-r) (u n) (v n)))
      (U : Filter ℕ) (𝓝 0)

/-- Sequence formulation of an inner product on B_d/N_d, including representative
independence, its actual ultralimit, its radical N_d, and metric completeness.
No Hilbert-space instance or proof of Lemma 3.3 is contained in this definition. -/
def HilbertSequenceLaws (U : Ultrafilter ℕ) (d : ℕ) : Prop :=
  (∀ p q, boundedLE d p → boundedLE d q →
    Tendsto (fun n => pairing (p n) (q n)) (U : Filter ℕ) (𝓝 (ultraPair U p q))) ∧
  (∀ p q, boundedLE d p → boundedLE d q →
    Tendsto (fun n => ‖p n - q n‖) (U : Filter ℕ) (𝓝 (ultraNorm U (p-q)))) ∧
  (∀ p p' q q', boundedLE d p → boundedLE d p' → boundedLE d q → boundedLE d q' →
    sameClass U p p' → sameClass U q q' → ultraPair U p q = ultraPair U p' q') ∧
  (∀ p q r, boundedLE d p → boundedLE d q → boundedLE d r →
    ultraPair U (p+q) r = ultraPair U p r + ultraPair U q r) ∧
  (∀ (a : ℝ) p q, boundedLE d p → boundedLE d q →
    ultraPair U (a • p) q = a * ultraPair U p q) ∧
  (∀ p q, boundedLE d p → boundedLE d q → ultraPair U p q = ultraPair U q p) ∧
  (∀ p, boundedLE d p → 0 ≤ ultraPair U p p ∧
    ultraNorm U p = Real.sqrt (ultraPair U p p) ∧
    (ultraPair U p p = 0 ↔ sameClass U p 0)) ∧
  (∀ p : ℕ → Sequence, (∀ j, boundedLE d (p j)) →
    (∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ j ≥ K, ∀ k ≥ K,
      ultraNorm U (p j - p k) < ε) →
    ∃ q : Sequence, boundedLE d q ∧
      Tendsto (fun j => ultraNorm U (p j-q)) atTop (𝓝 0))

/-- The paper's arbitrary orthonormal basis of each positive-grade primitive space.
Density here is only in the primitive spaces, never in the whole chaos (Theorem 3.5). -/
def PrimitiveBasis {I : Type*} (U : Ultrafilter ℕ) (g : I → ℕ)
    (e : I → Sequence) : Prop :=
  (∀ i, 1 ≤ g i ∧ primitive U (g i) (e i)) ∧
  (∀ i, ∀ᶠ n in (U : Filter ℕ), ‖e i n‖ ^ 2 = 1) ∧
  (∀ i j, ultraPair U (e i) (e j) = if i = j then 1 else 0) ∧
  (∀ d, 0 < d → ∀ p, primitive U d p → ∀ ε : ℝ, 0 < ε →
    ∃ c : I →₀ ℝ, (∀ i ∈ c.support, g i = d) ∧
      ultraNorm U (p - c.sum (fun i a => a • e i)) < ε)

/-- Raw ψ_α(e_n), with no unjustified class formed. -/
def psiSequence {I : Type*} (e : I → Sequence) (α : I →₀ ℕ)
    (n : ℕ) (x : Sample) : ℝ := psiMulti α (fun i => e i n x)

def topMulti {I : Type*} (g : I → ℕ) (e : I → Sequence) (α : I →₀ ℕ)
    (n : ℕ) : Original :=
  (Real.sqrt (multiFactorial α : ℝ))⁻¹ •
    chaosProjection (grade g α) (toOriginal (fun x => α.prod (fun i a => (e i n x) ^ a)))

/-- Orthonormal basis in sequence form: L² membership, representatives in the homogeneous
chaos modulo N, pairwise ultralimit orthonormality, and finite-span density. -/
def HermiteUltraBasis {I : Type*} (U : Ultrafilter ℕ) (g : I → ℕ)
    (e : I → Sequence) (d : ℕ) : Prop :=
  (∀ α, grade g α = d →
    (∀ n, MemLp (psiSequence e α n) 2 (gaussianProduct ℕ)) ∧
    boundedLE d (fun n => toOriginal (psiSequence e α n)) ∧
    ∃ h, boundedHom d h ∧
      sameClass U h (fun n => toOriginal (psiSequence e α n))) ∧
  (∀ α β, grade g α = d → grade g β = d →
    Tendsto (fun n => ∫ x, psiSequence e α n x * psiSequence e β n x ∂gaussianProduct ℕ)
      (U : Filter ℕ) (𝓝 (if α = β then 1 else 0))) ∧
  (∀ p, boundedHom d p → ∀ ε : ℝ, 0 < ε →
    ∃ c : (I →₀ ℕ) →₀ ℝ, (∀ α ∈ c.support, grade g α = d) ∧
      ultraNorm U (p - fun n => toOriginal
        (fun x => c.sum fun α a => a * psiSequence e α n x)) < ε)

/-- The coefficients in the basis expansion, Theorem 3.5. -/
def ultraCoefficient {I : Type*} (U : Ultrafilter ℕ) (e : I → Sequence)
    (p : Sequence) (α : I →₀ ℕ) : ℝ :=
  Filter.limUnder (U : Filter ℕ)
    (fun n => ∫ x, p n x * psiSequence e α n x ∂gaussianProduct ℕ)

/-- L² sum defined by the net of finite partial sums, not a pointwise series.
This relation asks for existence and convergence; it assumes neither. -/
def HasGradedExpansion {I : Type*} (g : I → ℕ) (d : ℕ)
    (c : (I →₀ ℕ) → ℝ) (p : GaussianL2 I) : Prop :=
  p ∈ gradedChaos g d ∧
  Tendsto (fun F : Finset {α : I →₀ ℕ // grade g α = d} =>
      ∫⁻ x, ENNReal.ofReal ((p x - ∑ α ∈ F, c α.val * psiMulti α.val x) ^ 2)
        ∂gaussianProduct I) atTop (𝓝 0)

end GaussPolyReg.Approx


