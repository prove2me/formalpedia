-- Prove2me | Definitions.Def_NAMatchEst_degTest
-- name    : NAMatchEst_degTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:53:06.84754+00:00
-- url     : https://prove2.me/theorems/df5241f3-5354-4087-9773-41882eb5131c
-- title:
--   The first-layer degree test
-- statement:
--   The **first-layer degree test** (display (12)). Take $s_D:=\lceil cnL/k\rceil$ independent uniform vertex samples $v_1,\dots,v_{s_D}$, with replacement, and query their degrees. Let $X_D$ be the number of draws whose degree is at least $\Delta$. The test accepts exactly when
--
--   $$
--   X_D\ge \frac{s_D\,k}{16n}.
--   $$
--
--   Repeated draws are counted with multiplicity.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.4, display (12), p.23 (PDF 27)

import Mathlib
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_NAMatchEst_cc
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_Delta

namespace NAMatchEst

/-- The **first-layer degree test** (display (12)). Take `s_D := ⌈cnL/k⌉` independent uniform
vertex samples `v₁, …, v_{s_D}` (with replacement) and query their degrees; let `X_D` count the
draws whose degree is at least `∆`; accept (`true`) exactly when `X_D ⩾ s_D k/(16n)`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.4, p.23 (PDF 27): "Take sD := ⌈cnL/k⌉ independent uniform vertex samples and query their
degrees. Let XD count the draws whose degree is at least ∆. The first-layer degree test accepts
exactly when XD ⩾ sD k/(16n). (12)"

**Formalization Note** The seed is the vector of draws `Fin s_D → Fin n` with the uniform distribution
(public `ShallowShadows.ShadowNorm.uniformDist`; `[NeZero n]` makes the vertex set nonempty). Repeated draws are counted with multiplicity, as in
the source (§3.2, p.20). -/
noncomputable def degTest (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) : RandAlg n Bool :=
  open Classical in
  { Ω := Fin ⌈cc * n * L n / k⌉₊ → Fin n
    dist := ShallowShadows.ShadowNorm.uniformDist _
    queries := fun ω => List.ofFn fun j => Query.deg (ω j)
    output := fun ω d _ =>
      decide ((⌈cc * n * L n / k⌉₊ : ℝ) * k / (16 * n) ≤
        ((Finset.univ.filter fun j => ∃ x ∈ d (ω j), Delta k α ≤ x).card : ℝ)) }

end NAMatchEst


