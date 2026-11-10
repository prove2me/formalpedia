-- Prove2me | Definitions.Def_RevRedSAT_mu
-- name    : RevRedSAT_mu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:33.126194+00:00
-- url     : https://prove2.me/theorems/ed3e3367-cc7d-416d-8453-4b77e6f59050
-- title:
--   Thresholds $t_p$, weights $w_s$, sparsity, $\tau(\mathcal F)$, the measure $\mu$ and $T_d(\delta)$
-- statement:
--   Fix $d\ge2$ and $\delta=2^{-j}$ for an integer $j\ge2$, and put $A=2d/\delta=2^{j+1}d$. App. B, (17), p.87 defines
--
--   $$t_p=\frac{A^{4p}}{4d}\quad(1\le p\le d-1),\qquad w_s=\tfrac12A^{4-4s}\quad(1\le s\le d).$$
--
--   **Definition B.3.** A layer is **sparse** if, for every positive petal size $p$, it contains no flower with at least $t_p$ members; it is **almost sparse** with threshold $2t_p$ instead. A family is sparse when all its layers are sparse. A flower with at least $t_p$ members is **eligible** for branching. $\tau(\mathcal F)$ is the largest index in $\{1,\dots,d\}$ such that layers $1,\dots,\tau(\mathcal F)$ are all almost sparse, and the **measure** is
--
--   $$\mu(\mathcal F)=k-\sum_{s=1}^{\tau(\mathcal F)}w_s|\mathcal F_s|.\qquad(18)$$
--
--   The frequency bound of Theorem 6.2 is
--
--   $$T_d(\delta)=1+\sum_{p=1}^{d-1}\frac{(2d/\delta)^{4p}}{4d}.$$
--
--   **Formalization Note** All quantities are real numbers; $w_s$ uses an integer power of $A$.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. B, (17), Definition B.3 and (18), p.87; Theorem 6.2, p.39 (T_d(δ))

import Mathlib
import Definitions.Def_RevRedSAT_reduceFam

set_option autoImplicit false

namespace RevRedSAT

/-- `δ = 2^{−j}` (Theorem 6.2, p.39: "δ = 2^{−j} for an integer j ≥ 2"). -/
noncomputable def deltaOf (j : ℕ) : ℝ := ((2 : ℝ) ^ j)⁻¹

/-- `A = 2d/δ` ((17), p.87). -/
noncomputable def Aval (d j : ℕ) : ℝ := 2 * d / deltaOf j

/-- **The thresholds `t_p = A^{4p}/(4d)` ((17), p.87).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. B, p.87: "Set A = 2d/δ,
and define the thresholds and weights by t_p = A^{4p}/(4d) (1 ≤ p ≤ d − 1), w_s = ½A^{4−4s}
(1 ≤ s ≤ d). (17) Since A = 2^{j+1}d, every threshold t_p is an integer at least two." -/
noncomputable def tp (d j p : ℕ) : ℝ := Aval d j ^ (4 * p) / (4 * d)

/-- The weights `w_s = ½ A^{4−4s}` ((17), p.87). -/
noncomputable def ws (d j s : ℕ) : ℝ := (1 / 2) * Aval d j ^ ((4 : ℤ) - 4 * s)

/-- **Sparse families (Definition B.3).** Definition B.3, p.87: "A layer is sparse if, for every
positive petal size p, it contains no flower with at least t_p members. It is almost sparse if the
corresponding forbidden threshold is 2t_p. A family is sparse when all its layers are sparse. A
flower with at least t_p members is called eligible for branching." -/
def IsSparse {n : ℕ} (d j : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ∀ s, NoFlowerAtLeast (layer F s) s (tp d j)

/-- The layer `F_s` is almost sparse (Definition B.3): no flower of petal size `p` with at least
`2t_p` members. -/
def AlmostSparseLayer {n : ℕ} (d j : ℕ) (F : Finset (Finset (Fin n))) (s : ℕ) : Prop :=
  NoFlowerAtLeast (layer F s) s (fun p => 2 * tp d j p)

/-- `Z` is an eligible flower in the layer `F_s`: a flower with at least `t_p` members, `p` its petal
size (Definition B.3). -/
def IsEligible {n : ℕ} (d j : ℕ) (F : Finset (Finset (Fin n))) (s : ℕ)
    (Z : Finset (Finset (Fin n))) : Prop :=
  IsFlower F s Z ∧ tp d j (s - (core Z).card) ≤ Z.card

/-- `τ(F)`, "the largest index in {1, . . . , d} such that layers 1, . . . , τ(F) are all almost
sparse" (Definition B.3, p.87). -/
noncomputable def tau {n : ℕ} (d j : ℕ) (F : Finset (Finset (Fin n))) : ℕ := by
  classical
  exact ((Finset.Icc 1 d).filter fun t => ∀ s ∈ Finset.Icc 1 t, AlmostSparseLayer d j F s).sup id

/-- **The measure `µ(F) = k − Σ_{s=1}^{τ(F)} w_s |F_s|` ((18), p.87).** -/
noncomputable def mu {n : ℕ} (d j k : ℕ) (F : Finset (Finset (Fin n))) : ℝ :=
  k - ∑ s ∈ Finset.Icc 1 (tau d j F), ws d j s * (layer F s).card

/-- **The frequency bound `T_d(δ) = 1 + Σ_{p=1}^{d−1} (2d/δ)^{4p}/(4d)`** (Theorem 6.2, p.39). -/
noncomputable def Td (d j : ℕ) : ℝ := 1 + ∑ p ∈ Finset.Icc 1 (d - 1), tp d j p

end RevRedSAT


