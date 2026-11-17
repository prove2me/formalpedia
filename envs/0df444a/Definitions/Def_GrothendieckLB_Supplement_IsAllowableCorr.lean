-- Prove2me | Definitions.Def_GrothendieckLB_Supplement_IsAllowableCorr
-- name    : GrothendieckLB_Supplement_IsAllowableCorr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:36:02.827999+00:00
-- url     : https://prove2.me/theorems/ba784ca3-b59d-475a-ae41-aeb25f179eb3
-- title:
--   Allowable correlation map (Definition 3.5)
-- statement:
--   A function $\rho:(-1,1)\to\mathbb R$ is an **allowable correlation map** if it admits an odd power-series expansion with absolutely summable coefficients of total mass at most one:
--   $$
--   \rho(t)=\sum_{\substack{d\ge1\\ d\text{ odd}}}c_d\,t^d,\qquad \sum_{\substack{d\ge1\\ d\text{ odd}}}|c_d|\le1 .
--   $$
--   Allowable maps are the coordinate correlations permitted in a limiting Krivine scheme; the identity $\rho(t)=t$ is allowable, so ordinary Krivine schemes are a special case.
--
--   **Formalization Note** $\rho$ is a real function on $\mathbb R$ constrained only on $(-1,1)$; the coefficients form a sequence $c:\mathbb N\to\mathbb R$ vanishing at every even index, and absolute summability is stated explicitly.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 3.5, p.18

import Mathlib

namespace GrothendieckLB

namespace Supplement

/-- An allowable correlation map (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Definition 3.5, p.18): `ρ : (−1, 1) → ℝ` admits an
expansion `ρ(t) = ∑_{d ≥ 1, d odd} c_d t^d` with `∑_{d odd} |c_d| ≤ 1`.

**Formalization Note** `ρ` is a function on `ℝ` and only its values on `(−1, 1)` are
constrained. The coefficients are a sequence `c : ℕ → ℝ` vanishing at every even index
(including `d = 0`), so sums over `ℕ` are the page's sums over odd `d ≥ 1`; the absolute
summability is explicit, since `tsum` of a non-summable sequence is `0` in Lean. -/
def IsAllowableCorr (ρ : ℝ → ℝ) : Prop :=
  ∃ c : ℕ → ℝ, (∀ d, Even d → c d = 0) ∧ Summable (fun d => |c d|) ∧
    ∑' d, |c d| ≤ 1 ∧ ∀ t : ℝ, |t| < 1 → ρ t = ∑' d, c d * t ^ d

end Supplement

end GrothendieckLB


