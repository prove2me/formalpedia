-- Prove2me | Definitions.Def_PrideGuilt_tauStar
-- name    : PrideGuilt_tauStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:32.572992+00:00
-- url     : https://prove2.me/theorems/75837422-2971-48f5-be63-bc8e5298c98f
-- title:
--   Equilibrium recycling rate $\tau^*(f)$ of Lemma 1
-- statement:
--   The equilibrium recycling rate induced by the reward $f$ is the rate given by Lemma 1:
--
--   1. $\tau^*(f)=0$ for $f\le c_r-\max(\gamma_P,\gamma_G)$;
--   2. $\tau^*(f)=1$ for $f\ge c_r-\min(\gamma_P,\gamma_G)$;
--   3. for $c_r-\max(\gamma_P,\gamma_G)<f<c_r-\min(\gamma_P,\gamma_G)$: if $\gamma_P>\gamma_G$ then $\tau^*(f)=\tau_m(f)$ (Lemma 1(iv)); if $\gamma_G>\gamma_P$ then $\tau^*(f)=1$ when $\tau^0\ge\tau_m(f)$ and $\tau^*(f)=0$ when $\tau^0<\tau_m(f)$ (Lemma 1(ii)).
--
--   The manufacturer's demand and costs are built on this rate.
--
--   **Formalization Note** The Lemma 1 formula is taken as the definition, because the manufacturer's problem uses it ("Using the equilibrium recycling rate $\tau^*(f)$ derived in the previous section", p.11). It keeps the printed values at the endpoints $f=c_r-\gamma_P$ and $f=c_r-\gamma_G$ when $\gamma_P>\gamma_G$ (where Definition 1 has no stable equilibrium; see the Lemma 1 milestone) and at the tie $\tau^0=\tau_m(f)$. When $\gamma_P=\gamma_G$ (excluded by the paper) the first test takes precedence.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Lemma 1, p.9; used in §4, p.11

import Mathlib
import Definitions.Def_PrideGuilt_tauM

namespace PrideGuilt

/-- **The equilibrium recycling rate `τ*(f)` of Lemma 1.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Lemma 1, p.9 (PDF 10); used by the manufacturer's problem, §4, p.11 (PDF 12).

(i) `τ*(f) = 0` for `f ≤ c_r − max(γ_P, γ_G)`;
(iii) `τ*(f) = 1` for `f ≥ c_r − min(γ_P, γ_G)`;
strictly between these two values: (iv) `τ*(f) = τ_m(f)` if `γ_P > γ_G`, and
(ii) if `γ_G > γ_P`, `τ*(f) = 1` when `τ⁰ ≥ τ_m(f)` and `0` when `τ⁰ < τ_m(f)`.

**Formalization Note.** This is the Lemma 1 formula, taken as the definition of `τ*(f)`, because
the manufacturer's problem (3)–(5) is built on it ("Using the equilibrium recycling rate `τ*(f)`
derived in the previous section", p.11). It keeps the printed values everywhere, including the
two endpoints `f = c_r − γ_P`, `f = c_r − γ_G` when `γ_P > γ_G` (where Definition 1 has no stable
equilibrium; see `lemma_1`) and the tie `τ⁰ = τ_m(f)` in case (ii). When `γ_P = γ_G` (excluded by
the paper) cases (i) and (iii) overlap at `f = c_r − γ_P` and the first test wins. -/
noncomputable def tauStar (P : Params) (γP γG f : ℝ) : ℝ :=
  if f ≤ cr P - max γP γG then 0
  else if cr P - min γP γG ≤ f then 1
  else if γG < γP then tauM P γP γG f
  else if tauM P γP γG f ≤ P.τ0 then 1 else 0

end PrideGuilt


