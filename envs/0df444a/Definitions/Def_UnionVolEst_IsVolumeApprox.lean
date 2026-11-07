-- Prove2me | Definitions.Def_UnionVolEst_IsVolumeApprox
-- name    : UnionVolEst_IsVolumeApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:02:45.197276+00:00
-- url     : https://prove2.me/theorems/1af51b91-a7d4-49f8-8804-e40185f34e79
-- title:
--   $\kappa$-factor approximation of a volume
-- statement:
--   A number $\tilde V$ is a **$\kappa$-factor approximation** of the volume of $K\subseteq\mathbb R^n$ if
--   $$
--   (1-\kappa)\,\mathrm{Vol}(K) \le \tilde V \le (1+\kappa)\,\mathrm{Vol}(K).
--   $$
--   This is the event whose probability the PAC volume oracle ComputeVolume guarantees to be at least $1-\delta_v$.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.2 I, p.14 (PDF p.16); Claim 11, p.21

import Mathlib

open MeasureTheory

namespace UnionVolEst

/-- A `κ`-factor approximation of the volume of `K` (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar, *Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §4.2, printed p.14, PDF p.16, and
Claim 11, printed p.21): `(1 − κ) Vol(K) ≤ Ṽ ≤ (1 + κ) Vol(K)`.

**Formalization Note** Closed inequalities as on the page; `Vol(K)` is Lebesgue measure read in
`ℝ` (finite in every use). -/
def IsVolumeApprox {n : ℕ} (κ : ℝ) (K : Set (EuclideanSpace ℝ (Fin n))) (v : ℝ) : Prop :=
  (1 - κ) * (volume K).toReal ≤ v ∧ v ≤ (1 + κ) * (volume K).toReal

end UnionVolEst


