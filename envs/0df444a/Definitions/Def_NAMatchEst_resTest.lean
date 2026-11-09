-- Prove2me | Definitions.Def_NAMatchEst_resTest
-- name    : NAMatchEst_resTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:53:14.457204+00:00
-- url     : https://prove2.me/theorems/b2b87fe6-7bb9-4d93-85df-52aa54c2f309
-- title:
--   The residual-total test
-- statement:
--   The **residual-total test** (display (13)). Take $s_M:=\lceil cnL/\alpha^2\rceil$ independent full-row samples $v_1,\dots,v_{s_M}$ (degree and the first $\Delta$ positions of the list). For a sampled vertex put $Z(v):=d_{\bar H}(v)$ if $v\in U$ (read from its degree and its row) and $Z(v):=0$ otherwise, and let
--
--   $$
--   \widehat R_H:=\frac{n}{s_M}\sum_{j=1}^{s_M}Z(v_j).
--   $$
--
--   The test accepts exactly when $\widehat R_H\ge k\alpha/8$.
--
--   **Formalization Note** The queries do not depend on $H$ ("All vertex samples and queried positions are chosen without using H; its labels are used only to process the answers", p.22); the output is the acceptance decision as a function of $H$.
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.4, display (13), p.23 (PDF 27)

import Mathlib
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_NAMatchEst_cc
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_Delta
import Definitions.Def_NAMatchEst_rowQueries
import Definitions.Def_NAMatchEst_rowNbrs

namespace NAMatchEst

/-- The **residual-total test** (display (13)), with the output given as a function of the set
`H`. Take `s_M := ⌈cnL/α²⌉` independent full-row samples `v₁, …, v_{s_M}` (degree and the first `∆`
positions). For a sampled vertex put `Z(v) := d_{H̄}(v)` if `v ∈ U` (its degree answer is below
`∆`) and `Z(v) := 0` otherwise, where `d_{H̄}(v)` is read from the revealed row; let
`R̂_H := (n/s_M) Σ_j Z(v_j)`; accept exactly when `R̂_H ⩾ kα/8`.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), §3.4, p.23 (PDF 27): "Independently take sM := ⌈cnL/α²⌉ full-row samples v1, …, vsM. The
degree answers tell us which sampled vertices belong to U. For each such vertex, its full
neighbourhood and the identity of H give d_H̄(v). Define Z(v) := d_H̄(v) if v ∈ U, 0 if v ∉ U,
R̂_H := (n/sM) Σ_{j=1}^{sM} Z(vj). … The residual-total test accepts exactly when R̂_H ⩾ kα/8. (13)"

**Formalization Note** The queries do not depend on `H` ("All vertex samples and queried positions
are chosen without using H; its labels are used only to process the answers", p.22); the output
is the acceptance decision for every `H` at once. -/
noncomputable def resTest (n : ℕ) [NeZero n] (α : ℝ) (k : ℕ) :
    RandAlg n (Finset (Fin n) → Bool) :=
  open Classical in
  { Ω := Fin ⌈cc * n * L n / α ^ 2⌉₊ → Fin n
    dist := ShallowShadows.ShadowNorm.uniformDist _
    queries := fun ω => (List.ofFn fun j => rowQueries (ω j) (Delta k α)).flatten
    output := fun ω d m H =>
      decide ((k : ℝ) * α / 8 ≤ (n : ℝ) / ⌈cc * n * L n / α ^ 2⌉₊ *
        ∑ j, (if ∃ x ∈ d (ω j), x < Delta k α then
          ((rowNbrs m (ω j) (Delta k α) \ H).card : ℝ) else 0)) }

end NAMatchEst


