-- Prove2me | Definitions.Def_GinibrePermanent977_Anticoncentration_Supplement_Model
-- name    : GinibrePermanent977_Anticoncentration_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:35:45.675464+00:00
-- url     : https://prove2.me/theorems/f12cbc02-9114-43f7-b688-b11352f7a89f
-- title:
--   Independent row covariance, Lebesgue densities and ordered quaternionic suffixes
-- statement:
--   This interface adds the objects in Appendix C to the published Ginibre model. For a row $r$ and a right coefficient column $c$, $rc=\sum_j r_jc_j$. A row law is isotropic at scale $\sigma^2$ when every covariance entry $\overline r_jr_l$ is integrable and has expectation $\sigma^2\delta_{jl}$. This expresses the finite covariance matrix in (36), without coordinate independence, Gaussianity or a tail assumption. The normalized determinantal power $\Delta_n$ is $|\det A|^2/n!$ over the real and complex fields and $\operatorname{Sdet}(A)^2/n!$ over quaternions; these are aliases of the base model's operations.
--
--   For a scalar random variable $X$ on a measure space with law $\mu$, a Lebesgue density $p$ is measurable and satisfies
--   $$\mu(X\in E)=\int_E p(z)\,dz$$
--   for every Borel set $E$. The normalized perturbed permanent is $\operatorname{per}_{\mathbb K}(Z+G)/\sqrt{n!}$.
--
--   For quaternionic suffixes, source row $k+1$ has zero-based index $k$. Let $\mathcal S_k$ be the column subsets of size $n-k$. The suffix minor $P_k(S)$ sums the increasing-row product over every bijection from rows $k,\ldots,n-1$ to $S$. The empty suffix has value $1$. Coefficients multiply on the right:
--   $$P_k[a]=\sum_{S\in\mathcal S_k}P_k(S)a_S,\qquad a'_T=\sigma\sum_{j\notin T}a_{T\cup\{j\}}h_j.$$
--   One vector $h$ supplies all new coefficients; their mutual independence is not asserted. These objects express the conditional row replacement of Lemma C.5 and keep quaternionic multiplication order explicit.
--
--   **Formalization Note** Finite column subsets are cardinality subtypes, not arbitrary coordinate extensions. The finite product Borel sigma-algebra on the coefficient vector uses the published quaternion carrier. Suffix evaluation requires $k\le n$, and contraction requires $k<n$. No theorem or unproved fact is assumed by this interface.
-- source:
--   Frederic Koehler, Pui Kuen Leung, STOC 2027 submission #977 (October 2026), §1.2, §4, Appendix C (36), §C.2, p.4,14,19–21 (PDF SHA256 e25737f1d5e3492905f8eeaa41d92c55d95f73622a3b5846cc87aac6a346d4ec)

import Mathlib
import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory
open scoped Quaternion BigOperators Nat ENNReal

namespace GinibrePermanent977.Anticoncentration.Supplement

/-- The unconjugated row action of (36), p.19; coefficients multiply on the right. -/
noncomputable def rowAction {F : Scalar} {n : ℕ} (r c : Fin n → F.K) : F.K :=
  ∑ j, r j * c j

/-- Finite entrywise covariance in (36). Integrability makes the finite expectations literal. -/
def RowIsotropic {F : Scalar} {n : ℕ} (μ : Measure (Fin n → F.K)) (σ : ℝ) : Prop :=
  ∀ j l : Fin n,
    Integrable (fun r => star (r j) * r l) μ ∧
    (∫ r, star (r j) * r l ∂μ) = if j = l then (σ ^ 2) • (1 : F.K) else 0

/-- The normalized determinantal benchmark of §1.2, p.4, reused in (37), p.19. -/
noncomputable def deltaPower : (F : Scalar) → {n : ℕ} → (Fin n → Fin n → F.K) → ℝ
  | .real, n, A => ‖cdetK A‖ ^ 2 / (Nat.factorial n : ℝ)
  | .complex, n, A => ‖cdetK A‖ ^ 2 / (Nat.factorial n : ℝ)
  | .quaternion, n, A => studyDet A ^ 2 / (Nat.factorial n : ℝ)

/-- Lebesgue density of a scalar random variable, with the Borel σ-algebra inherited from F. -/
def IsDensity {F : Scalar} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → F.K) (p : F.K → ℝ≥0∞) : Prop :=
  Measurable p ∧ ∀ t : Set F.K, MeasurableSet t → μ (X ⁻¹' t) = ∫⁻ z in t, p z

/-- Normalized permanent after an independent additive perturbation (p.14). -/
noncomputable def perturbedPer {F : Scalar} {n : ℕ}
    (ZG : (Fin n → Fin n → F.K) × (Fin n → Fin n → F.K)) : F.K :=
  normPer (ZG.1 + ZG.2)

/-- The source's S_{k+1}, pp.20–21, in zero-based row coordinates k. -/
abbrev ColumnSets (n k : ℕ) := {S : Finset (Fin n) // S.card = n - k}

/-- A coefficient for every suffix column set, on the right of the suffix permanent. -/
abbrev Coeff (n k : ℕ) := ColumnSets n k → Scalar.quaternion.K

/-- P_{k+1}(S): sum over all bijections from suffix rows to S, in increasing row order.
For k=n, S=∅ the unique empty map contributes the empty product 1. -/
noncomputable def suffixMinor {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (A : Fin n → Fin n → Scalar.quaternion.K) (S : Finset (Fin n)) : Scalar.quaternion.K := by
  classical
  exact ∑ π ∈ (Finset.univ : Finset (Fin (n-k) → Fin n)).filter
      (fun π => Function.Injective π ∧ ∀ j, j ∈ S ↔ ∃ i, π i = j),
    (List.ofFn fun i : Fin (n-k) => A ⟨k+i.val, by omega⟩ (π i)).prod

/-- P_{k+1}[a], with coefficients multiplying on the right (p.21). -/
noncomputable def suffixEval {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (A : Fin n → Fin n → Scalar.quaternion.K) (a : Coeff n k) : Scalar.quaternion.K := by
  classical
  exact ∑ S : ColumnSets n k, suffixMinor k hk A S.val * a S

/-- Overwrite just the current row k before evaluating a suffix. -/
noncomputable def replaceRow {n : ℕ} (k : ℕ) (A : Fin n → Fin n → Scalar.quaternion.K)
    (r : Fin n → Scalar.quaternion.K) : Fin n → Fin n → Scalar.quaternion.K :=
  fun i => if i.val = k then r else A i

/-- The one fresh vector h supplies every new coefficient simultaneously:
a'_T = σ ∑_{j∉T} a_{T∪{j}} h_j. Quaternion multiplication is on the RIGHT. -/
noncomputable def contractCoeff {n : ℕ} (k : ℕ) (hk : k < n) (σ : ℝ)
    (a : Coeff n k) (h : Fin n → Scalar.quaternion.K) : Coeff n (k+1) := by
  classical
  exact fun T => σ • ∑ j : {j : Fin n // j ∉ T.val},
    a ⟨insert j.val T.val, by
      rw [Finset.card_insert_of_notMem j.property]
      have hT := T.property
      omega⟩ * h j.val

end GinibrePermanent977.Anticoncentration.Supplement


