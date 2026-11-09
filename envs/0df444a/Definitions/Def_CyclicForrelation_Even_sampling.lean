-- Prove2me | Definitions.Def_CyclicForrelation_Even_sampling
-- name    : CyclicForrelation_Even_sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:31:48.868197+00:00
-- url     : https://prove2.me/theorems/8f4b02ec-bd85-4296-a149-038fd4acf70d
-- title:
--   Conditional cycle moments and the Cartesian sampling estimator
-- statement:
--   Fix any sign-function tuple on $G$. For $S\subseteq\{0,\ldots,k-1\}$, define $h_S(x_S)$ by uniformly averaging the cyclic kernel over the complementary coordinates. Its normalized squared norm is
--   $$\|h_S\|_2^2=\frac1{N^{|S|}}\sum_{x_S\in G^S}h_S(x_S)^2.$$
--   A set is cycle independent when it contains no vertex together with its wraparound successor. For an array $X=(X_{j,i})_{j<k,i<q}$, define
--   $$\widetilde T_k=\frac{N^{k/2-1}}{q^k}\sum_{i_0,\ldots,i_{k-1}<q}h_f(X_{0,i_0},\ldots,X_{k-1,i_{k-1}}).$$
--   The uniform law on the full array is independent uniform sampling with replacement. The actual query list contains each pair $(j,X_{j,i})$ in oracle-major order and has length exactly $kq$. A concrete postprocessor evaluates the displayed sum using only the seed array and the recorded answer at offset $jq+i$; the resulting algorithm has no access to unqueried oracle values.
--
--   These definitions retain all overlap patterns, including singleton sets, the whole cycle, and every independent set. They provide both the algebraic estimator and an operational implementation for the upper-bound branch.
--
--   **Formalization Note** Subtypes represent $S$ and its complement, so each normalized average ranges over exactly the intended coordinates. Empty coordinate sets have one assignment. The estimator is used at $q>0$ in the paper; at $q=0$ Lean division returns zero, and the defined empty-query algorithm outputs zero. No theorem asserts accuracy for that boundary. Missing-answer defaults apply only to malformed lists.
-- source:
--   Yuxin Zhang, Changpeng Shao, STOC 2027 submission #333 (October 2026), pp. 16–17, Eq. (28) and conditional-moment definitions; p. 18, sampling proof

import Definitions.Def_CyclicForrelation_Even_cyclicTrace
import Definitions.Def_CyclicForrelation_Even_queryModel

namespace CyclicForrelation.Even

/-- Uniform averaging over exactly the complementary coordinates. -/
noncomputable def conditionalKernel {n k : ℕ} (f : OracleTuple n k) (S : Finset (Fin k))
    (x : {j // j ∈ S} → Cube n) : ℝ :=
  (∑ y : ({j // j ∉ S} → Cube n),
    cycleKernel f (fun j => if hj : j ∈ S then x ⟨j, hj⟩ else y ⟨j, hj⟩)) /
      (Fintype.card ({j // j ∉ S} → Cube n) : ℝ)

/-- Normalized uniform squared L2 norm on G^S, never an unnormalized counting norm. -/
noncomputable def conditionalSecondMoment {n k : ℕ} (f : OracleTuple n k)
    (S : Finset (Fin k)) : ℝ :=
  (∑ x : ({j // j ∈ S} → Cube n), (conditionalKernel f S x) ^ 2) /
    (Fintype.card ({j // j ∈ S} → Cube n) : ℝ)

def CycleIndependent {k : ℕ} (S : Finset (Fin k)) : Prop :=
  ∀ j ∈ S, cycleNext j ∉ S

abbrev SampleArray (n k q : ℕ) := Fin k → Fin q → Cube n

/-- Uniform on the whole array gives independent samples with replacement. -/
noncomputable def sampleLaw (n k q : ℕ) : PMF (SampleArray n k q) :=
  PMF.uniformOfFintype (SampleArray n k q)

/-- Eq. (28), at a realized sample array. The source uses q>0. -/
noncomputable def cartesianEstimator {n k q : ℕ} (f : OracleTuple n k)
    (X : SampleArray n k q) : ℝ :=
  (cubeSize n : ℝ) ^ ((k : ℝ) / 2 - 1) / (q : ℝ) ^ k *
    ∑ i : (Fin k → Fin q), cycleKernel f (fun j => X j (i j))

/-- The actual ordered list of kq queries; duplicates remain and are charged. -/
def sampleQueries {n k q : ℕ} (X : SampleArray n k q) : List (Fin k × Cube n) :=
  (List.finRange k).flatMap (fun j => (List.finRange q).map (fun i => (j, X j i)))

/-- The estimator evaluated from the kq recorded answers, in oracle-major order.
It cannot evaluate any oracle at an unqueried location. -/
noncomputable def samplePostprocess {n k q : ℕ} (X : SampleArray n k q)
    (a : List Bool) : ℝ :=
  (cubeSize n : ℝ) ^ ((k : ℝ) / 2 - 1) / (q : ℝ) ^ k *
    ∑ i : (Fin k → Fin q),
      (∏ j : Fin k, signValue (a.getD (j.val * q + (i j).val) false)) *
        signValue (decide ((∑ j, binaryDot (X j (i j))
          (X (cycleNext j) (i (cycleNext j)))) = 1))

/-- The single-run sampling algorithm, before amplification and the exhaustive branch. -/
noncomputable def samplingAlgorithm (n k q : ℕ) :
    NonadaptiveAlgorithm (Fin k × Cube n) where
  Seed := SampleArray n k q
  seedMeasurable := inferInstance
  law := (sampleLaw n k q).toMeasure
  probability := inferInstance
  queries := sampleQueries
  queries_measurable := by
    let : MeasurableSpace (List (Fin k × Cube n)) := ⊤
    exact measurable_of_countable _
  output := samplePostprocess
  output_measurable := fun _ => measurable_of_countable _

/-- Structural cost API: the Cartesian sum uses kq oracle calls, including repetitions. -/
@[simp] theorem sampleQueries_length {n k q : ℕ} (X : SampleArray n k q) :
    (sampleQueries X).length = k * q := by
  simp [sampleQueries, List.length_flatMap]

end CyclicForrelation.Even


