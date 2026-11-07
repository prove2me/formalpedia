-- Prove2me | Definitions.Def_FairKMeans_Comparison
-- name    : FairKMeans_Comparison
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:16.958986+00:00
-- url     : https://prove2.me/theorems/94e8c66f-6bd9-40b3-9493-bb5a4370a969
-- title:
--   Comparison solutions $(S^\circ,\phi^\circ)$ and the alignment $C_e$
-- statement:
--   A **comparison solution** $(S^\circ,\phi^\circ)$ is a finite indexed family of centers with an $(\alpha,\beta)$-fair fractional assignment of $P$ in which every center lies at the weighted centroid of its points:
--
--   $$s=\frac{\sum_{p}\phi^\circ(p,s)\,p}{\sum_p\phi^\circ(p,s)}\qquad\text{for every } s\in S^\circ. \tag{31}$$
--
--   For a relaxed solution $(T,\phi_T)$ with means $\nu_p$, set $\nu^\circ_p=\sum_{s}\phi^\circ(p,s)\,s$ and define the **alignment**
--
--   $$C_e=\sum_{p\in P}(\nu_p-p)^\top(p-\nu^\circ_p). \tag{32}$$
--
--   Comparison solutions are the reference solutions of the analysis; an optimal fair solution is one.
--
--   **Formalization Note** (31) is defined only for a nonzero column, and the reduction of Section 6.2 deletes zero columns, so every column of a comparison solution has positive weight. $C_e$ is the second expression of (32), equal to the first because the rows of $\phi^\circ$ sum to one.
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Section 6.2, (31), p.27 (PDF p.29), and (32), p.28 (PDF p.30)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_RelaxedSolution

namespace FairKMeans

/-!
# Comparison solutions and the alignment `C_e`

Cheng–Mo–Song–Ding, arXiv:2609.07974 (held version, sha256 73e9312c…), Section 6.2, (31),
p.27 (PDF 29), and (32), p.28 (PDF 30).

**Formalization Note.** (31) places every center at the weighted centroid of its points; its
right-hand side is defined only for a nonzero column, and the reduction of p.27 deletes zero
columns. So a comparison solution here has every column weight positive and `s = π(s)`.
`C_e` is the second expression of (32), `∑_p (ν_p − p)ᵀ(p − ν°_p)`, which equals the first since
the rows of `φ°` sum to one.
-/

variable {d n m : ℕ}

/-- `(S°, φ°)` is a comparison solution (31): `φ°` is an `(α, β)`-fair fractional assignment of
`P` to `S°` and every center `s` has positive column weight and lies at the weighted centroid
`∑_p φ°(p,s) p / ∑_p φ°(p,s)` of its points. -/
def IsComparison {s : ℕ} (I : Instance d n m) (S : Fin s → E d) (φ : Fin n → Fin s → ℝ) :
    Prop :=
  IsAssignment φ ∧ IsFair I φ ∧ ∀ j, 0 < clusterWeight φ j ∧ S j = cen I φ j

/-- `ν°_p = ∑_s φ°(p,s) s` (32). -/
noncomputable def nuCmp {s : ℕ} (S : Fin s → E d) (φ : Fin n → Fin s → ℝ) (p : Fin n) : E d :=
  ∑ j, φ p j • S j

/-- The alignment `C_e = ∑_p (ν_p − p)ᵀ(p − ν°_p)` of a relaxed solution `φ` with a comparison
solution `(S°, φ°)` (32). -/
noncomputable def Ce {s s' : ℕ} (I : Instance d n m) (φ : Fin n → Fin s → ℝ) (S : Fin s' → E d)
    (φc : Fin n → Fin s' → ℝ) : ℝ :=
  ∑ p, inner ℝ (nu I φ p - I.pts p) (I.pts p - nuCmp S φc p)

end FairKMeans


