-- Prove2me | Definitions.Def_HermiteLaptop_MaxAgree_KSpokes
-- name    : HermiteLaptop_MaxAgree_KSpokes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:15:34.787292+00:00
-- url     : https://prove2.me/theorems/3649d78c-4251-4b93-bd64-10a795d01dce
-- title:
--   The Frieze–Jerrum k-spokes rounding (Algorithm 1), Algorithm 2's expected value, and the collision probability P_k(ρ) (Eq. (7))
-- statement:
--   **k-spokes rounding** (Algorithm 1). Given unit vectors $v_1,\dots,v_n\in\mathbb R^n$ and $k\ge1$, draw independent $g_1,\dots,g_k\sim N(0_n,I_n)$ and put node $i$ in cluster $C_p$ for $p\in\arg\max_{q\in[k]} v_i\cdot g_q$; ties have probability zero and are broken towards the least index.
--
--   **Algorithm 2** applies the 4-spokes and the 5-spokes rounding to the same vectors and returns the clustering of larger value; its expected value is
--   $$\mathbb E\big[\max(\mathrm{val}(\mathcal C_4),\mathrm{val}(\mathcal C_5))\big],$$
--   the expectation over the $4+5$ independent spokes.
--
--   **Collision probability** (Eq. (7)). For $\rho\in[-1,1]$ let $L,G$ be independent $N(0_k,I_k)$ vectors and $R=\rho L+\sqrt{1-\rho^2}\,G$, so that $(L,R)$ are $\rho$-correlated standard Gaussian vectors in $\mathbb R^k$. Then
--   $$P_k(\rho)=\Pr\Big[\arg\max_{p\in[k]}L_p=\arg\max_{p\in[k]}R_p\Big].$$
--   For unit vectors with $v_i\cdot v_j=\rho$ this is the probability that k-spokes puts $i$ and $j$ in the same cluster.
--
--   **Formalization Note.** `spokeIndex x` is the least `p : Fin k` with `x q ≤ x p` for all `q` (as a natural number; junk `0` when `k = 0`, which no statement uses). `kSpokes v g i = spokeIndex (q ↦ ⟪v i, g q⟫)`. `spokeMeasure n k` is the product over `Fin k` of Mathlib's `stdGaussian` on `EuclideanSpace ℝ (Fin n)`. `Instance.spokesValue I k v` is the Bochner integral of `val (kSpokes v g)`; `Instance.algorithm2Value` integrates `max (val C4) (val C5)` against `spokeMeasure n 4 ⊗ spokeMeasure n 5`. `gaussPi k` is the product of `gaussianReal 0 1` on `Fin k → ℝ`, and `collisionProb k ρ` is the `(gaussPi k ⊗ gaussPi k)`-measure of the agreement event, as a real number.
-- source:
--   García-Soriano, Miyauchi, Hermite Brings a Laptop, arXiv:2609.35453 (held version, sha256 97504f90…), p. 13 (PDF 16), §2.2, Algorithm 1 and Eq. (7); p. 28 (PDF 31), Algorithm 2

import Mathlib
import Definitions.Def_HermiteLaptop_MaxAgree_Instance

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

/-!
# The Frieze–Jerrum k-spokes rounding (Algorithm 1), Algorithm 2, and the collision probability

García-Soriano, Miyauchi, *Hermite Brings a Laptop*, arXiv:2609.35453 (held version, sha256
97504f90…), §2.2 p. 13 (PDF 16), Algorithm 1 and Eq. (7); §4.3 p. 28 (PDF 31), Algorithm 2.

"For an integer k ≥ 1, the k-spokes rounding generates k independent Gaussian vectors
g1, . . . , gk ∼ N(0n, In), and for each p = 1, . . . , k, constructs a cluster
Cp ← {i ∈ V : p ∈ arg max_{q∈[k]} vi · gq}. Ties occur with probability zero and may be broken
arbitrarily." — "Pk(ρ) = Pr[arg max_{p∈[k]} Lp = arg max_{p∈[k]} Rp]" for a pair (L, R) of
ρ-correlated standard Gaussian vectors in ℝᵏ.

Conventions.
* Spokes are indexed by `Fin k` (0-based). `spokeIndex x` is the **least** index `p` with
  `x q ≤ x p` for all `q` (tie rule: least index; ties have probability zero). For `k = 0` there
  is no spoke and the value is the junk `0`; every statement assumes `k ≥ 1`.
* `kSpokes v g i = spokeIndex (q ↦ v_i · g_q)` is the cluster label of node `i`.
* `spokeMeasure n k` is the law of `k` independent standard Gaussian vectors in
  `EuclideanSpace ℝ (Fin n)` (Mathlib `stdGaussian`, product over `Fin k`).
* `algorithm2Value I v` is the expected value of Algorithm 2's output on the SDP vectors `v`:
  `C4`, `C5` use independent spokes (`4` and `5` vectors), and the output has value
  `max (val C4) (val C5)`.
* `gaussPi k` is `N(0_k, I_k)` on `Fin k → ℝ` (product of `gaussianReal 0 1`). A ρ-correlated
  pair is `(L, ρ L + √(1 − ρ²) G)` with `L, G` independent `N(0_k, I_k)` (p. 12).
  `collisionProb k ρ` is `P_k(ρ)` of Eq. (7).
-/

namespace HermiteLaptop.MaxAgree

/-- The arg max with the least-index tie rule: the least `p : Fin k` with `x q ≤ x p` for all
`q`, as a natural number (junk `0` when `k = 0`). -/
noncomputable def spokeIndex {k : ℕ} (x : Fin k → ℝ) : ℕ :=
  ((List.finRange k).find? (fun p => decide (∀ q, x q ≤ x p))).elim 0 (fun p => p.val)

/-- Algorithm 1 (k-spokes): node `i` joins cluster `C_p` for `p` the arg max of `v_i · g_q`. -/
noncomputable def kSpokes {n k : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n))
    (g : Fin k → EuclideanSpace ℝ (Fin n)) : Fin n → ℕ :=
  fun i => spokeIndex (fun q => ⟪v i, g q⟫)

/-- The law of `k` independent spokes `g_1, …, g_k ∼ N(0_n, I_n)`. -/
noncomputable def spokeMeasure (n k : ℕ) : Measure (Fin k → EuclideanSpace ℝ (Fin n)) :=
  Measure.pi (fun _ : Fin k => stdGaussian (EuclideanSpace ℝ (Fin n)))

/-- `E[val(k-spokes(v))]`, the expectation over the spokes. -/
noncomputable def Instance.spokesValue {n : ℕ} (I : Instance n) (k : ℕ)
    (v : Fin n → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ g, I.val (kSpokes v g) ∂(spokeMeasure n k)

/-- Algorithm 2's expected value: `E[max(val(C4), val(C5))]`, with `C4 = 4-spokes(v)` and
`C5 = 5-spokes(v)` built from independent spokes. -/
noncomputable def Instance.algorithm2Value {n : ℕ} (I : Instance n)
    (v : Fin n → EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ g, max (I.val (kSpokes v g.1)) (I.val (kSpokes v g.2))
    ∂((spokeMeasure n 4).prod (spokeMeasure n 5))

/-- The standard Gaussian measure `γ_k = N(0_k, I_k)` on `Fin k → ℝ`. -/
noncomputable def gaussPi (k : ℕ) : Measure (Fin k → ℝ) :=
  Measure.pi (fun _ : Fin k => gaussianReal 0 1)

/-- The second vector of a ρ-correlated pair built from `(L, G)`: `ρ L + √(1 − ρ²) G`. -/
noncomputable def corrPartner {k : ℕ} (ρ : ℝ) (x y : Fin k → ℝ) : Fin k → ℝ :=
  fun q => ρ * x q + Real.sqrt (1 - ρ ^ 2) * y q

/-- The collision probability `P_k(ρ)` of Eq. (7): the probability that the arg max indices of a
pair of ρ-correlated standard Gaussian vectors in `ℝᵏ` agree. -/
noncomputable def collisionProb (k : ℕ) (ρ : ℝ) : ℝ :=
  (((gaussPi k).prod (gaussPi k))
    {p : (Fin k → ℝ) × (Fin k → ℝ) | spokeIndex p.1 = spokeIndex (corrPartner ρ p.1 p.2)}).toReal

end HermiteLaptop.MaxAgree


