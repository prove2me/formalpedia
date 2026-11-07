-- Prove2me | Definitions.Def_MatroidEquitability_supportPlus
-- name    : MatroidEquitability_supportPlus
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:52.287009+00:00
-- url     : https://prove2.me/theorems/7180e068-cd79-4789-ad7c-a90f127c5742
-- title:
--   Supports $\mathcal H^+,\mathcal H^-$ of the marginals of $\lambda$
-- statement:
--   For $\lambda$ on $\mathcal F^+\times\mathcal F^-$, the two families
--
--   $$
--   \mathcal H^+:=\{B\in\mathcal F^+:\lambda_{B,D}>0\text{ for some }D\in\mathcal F^-\},\qquad
--   \mathcal H^-:=\{D\in\mathcal F^-:\lambda_{B,D}>0\text{ for some }B\in\mathcal F^+\}
--   $$
--
--   are the supports of the two marginals of $\lambda$. The chain (6) is a sum over $\mathcal H^+\times\mathcal H^-$.
-- source:
--   Bérczi, Liu, Reis, Tarnawski, Weighted Equitability and Matroid-Constrained Discrepancy, arXiv:2608.13983 (held version sha256 0675891a…), Proof of Theorem 2, p.9 (PDF p.11)

import Mathlib

namespace MatroidEquitability

open Classical in
/-- `H⁺ := {B ∈ F⁺ : λ_{B,D} > 0 for some D ∈ F⁻}` (proof of Theorem 2, printed p.9 = PDF p.11 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)). -/
noncomputable def supportPlus {α : Type*} (Fp Fm : Finset (Set α)) (lam : Set α → Set α → ℝ) :
    Finset (Set α) :=
  Fp.filter fun B => ∃ D ∈ Fm, 0 < lam B D

open Classical in
/-- `H⁻ := {D ∈ F⁻ : λ_{B,D} > 0 for some B ∈ F⁺}` (proof of Theorem 2, printed p.9 = PDF p.11 of
Bérczi, Liu, Reis, Tarnawski, *Weighted Equitability and Matroid-Constrained Discrepancy*, arXiv:2608.13983 (held version sha256 0675891a…)). -/
noncomputable def supportMinus {α : Type*} (Fp Fm : Finset (Set α)) (lam : Set α → Set α → ℝ) :
    Finset (Set α) :=
  Fm.filter fun D => ∃ B ∈ Fp, 0 < lam B D

end MatroidEquitability


