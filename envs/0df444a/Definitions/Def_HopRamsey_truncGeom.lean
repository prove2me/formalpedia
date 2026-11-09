-- Prove2me | Definitions.Def_HopRamsey_truncGeom
-- name    : HopRamsey_truncGeom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:43:53.314635+00:00
-- url     : https://prove2.me/theorems/e9f0b6ee-1887-4074-89c4-1846b453fe25
-- title:
--   Geometric and truncated geometric laws
-- statement:
--   For $p\in(0,1]$ the **geometric law** on $\{0,1,2,\dots\}$ is $\Pr[\tau=R]=(1-p)^R p$. For an integer $k\ge1$ the **truncated geometric law** on $\{0,\dots,k-1\}$ is
--
--   $$
--   \Pr[R]=\frac{(1-p)^R\,p}{1-(1-p)^k},\qquad 0\le R<k .
--   $$
--
--   Algorithm 2 draws the radius of every carved ball from the truncated law with parameter $p_\ell$; the analysis compares it with untruncated geometric variables (the "tape process").
--
--   **Formalization Note** Both laws are obtained by normalizing the weights $(1-p)^R p$, which for $p\in(0,1]$ gives exactly the displayed formulas. Outside the parameter range where the formula is a law (for the geometric law, $p\notin(0,1]$; for the truncated law, $k=0$ or $p\le 0$) the definitions return the point mass at $0$, a case no statement of the mission uses.
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), proof of Lemma 1, p.19 (PDF p.21); Algorithm 2, line 5, p.16 (PDF p.18)

import Mathlib

open scoped ENNReal

namespace HopRamsey

/-- The weights `(1 − p)^R · p` of the geometric law on `{0, 1, 2, …}`. -/
noncomputable def geomWeight (p : ℝ) (R : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - p) ^ R * p)

/-- The (untruncated) geometric law with parameter `p ∈ (0, 1]` on `{0, 1, 2, …}`,
`Pr[τ = R] = (1 − p)^R · p` (proof of Lemma 1, p.19, PDF p.21: "Pr[τ_{ℓ,i} = R] = (1−p_ℓ)^R·p_ℓ
for every integer R ≥ 0").

**Formalization Note.** For `0 < p ≤ 1` the weights `(1−p)^R·p` sum to `1`, so normalizing them
(as the definition does) changes nothing and this is the printed law. Outside `0 < p ≤ 1` the
formula is not a law; the definition then returns the point mass at `0`, a value that no statement
of the mission uses (they all assume `0 < p ≤ 1`). -/
noncomputable def geomLaw (p : ℝ) : PMF ℕ :=
  if hp : 0 < p ∧ p ≤ 1 then
    PMF.normalize (geomWeight p)
      (by
        intro h0
        have hle : geomWeight p 0 ≤ ∑' R, geomWeight p R := ENNReal.le_tsum _
        rw [h0] at hle
        have : 0 < geomWeight p 0 := by simp [geomWeight, hp.1]
        exact absurd hle (not_le.2 this))
      (by
        have hs : Summable fun R : ℕ => (1 - p) ^ R * p :=
          (summable_geometric_of_lt_one (by linarith [hp.2]) (by linarith [hp.1])).mul_right p
        have hnn : ∀ R : ℕ, 0 ≤ (1 - p) ^ R * p := fun R =>
          mul_nonneg (pow_nonneg (by linarith [hp.2]) _) hp.1.le
        unfold geomWeight
        rw [← ENNReal.ofReal_tsum_of_nonneg hnn hs]
        exact ENNReal.ofReal_ne_top)
  else PMF.pure 0

/-- The unnormalized weights `(1 − p)^R · p` of the truncated geometric law on `[0, k)`. -/
noncomputable def truncGeomWeight (p : ℝ) (k : ℕ) (R : Fin k) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 - p) ^ (R : ℕ) * p)

/-- The truncated geometric law with parameter `p` on the integers `R ∈ [0, k)`.

Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), Algorithm 2,
line 5, p.16 (PDF p.18): "Sample an integer R ∈ [0,k) using a truncated geometric distribution with
parameter p_ℓ [...] That is, Pr[R] = (1−p_ℓ)^R·p_ℓ / (1−(1−p_ℓ)^k)."

**Formalization Note.** The weights `(1−p)^R·p` are normalized by their sum, which equals
`1 − (1 − p)^k` for `0 < p ≤ 1`, so for such `p` this is the printed law. The definition needs
only `0 < k` and `0 < p` to normalize; otherwise it returns the point mass at `0`, a case no
statement of the mission reaches (`k ≥ 1` and `0 < p_ℓ ≤ 1` under the standing hypotheses). -/
noncomputable def truncGeom (p : ℝ) (k : ℕ) : PMF ℕ :=
  if h : 0 < k ∧ 0 < p then
    PMF.map (fun R : Fin k => (R : ℕ)) (PMF.normalize (truncGeomWeight p k)
      (by
        intro h0
        have hle : truncGeomWeight p k ⟨0, h.1⟩ ≤ ∑' R, truncGeomWeight p k R :=
          ENNReal.le_tsum _
        rw [h0] at hle
        have : 0 < truncGeomWeight p k ⟨0, h.1⟩ := by
          simp [truncGeomWeight, h.2]
        exact absurd hle (not_le.2 this))
      (by
        rw [tsum_fintype]
        exact ENNReal.sum_ne_top.2 fun _ _ => ENNReal.ofReal_ne_top))
  else PMF.pure 0

end HopRamsey


