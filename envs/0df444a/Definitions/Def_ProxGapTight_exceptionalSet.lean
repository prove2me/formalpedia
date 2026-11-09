-- Prove2me | Definitions.Def_ProxGapTight_exceptionalSet
-- name    : ProxGapTight_exceptionalSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:48:16.161988+00:00
-- url     : https://prove2.me/theorems/afe6862c-af92-4cac-8a5f-228ac655a9ee
-- title:
--   Exceptional coefficients $\mathcal Z_\rho(f,g;C)$
-- statement:
--   Let $C\subseteq \mathbb F_q^{n}$ be a linear code over a finite field, $f,g\in\mathbb F_q^n$ and $\rho\in\mathbb R$. The set of **exceptional coefficients** of $f,g$ at radius $\rho$ is
--   $$
--   \mathcal Z_\rho(f,g;C)=\{z\in\mathbb F_q:\ \delta(f+zg,C)\le\rho\}.
--   $$
--
--   The proximity-gaps property at radius $\rho$ asks that this set be small (at most $\mathrm{err}\cdot q$) whenever $f$ or $g$ is far from $C$; the main theorem exhibits codes for which it has at least $cq$ elements although both $f$ and $g$ are far.
--
--   **Formalization Note** A finite subset of the field; the inequality is non-strict, as printed.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §2, p.6, display

import Mathlib
import Definitions.Def_ProxGapTight_distToCode

namespace ProxGapTight

/-- **Exceptional coefficients** `𝒵_ρ(f, g; C) := {z ∈ F_q : δ(f + zg, C) ≤ ρ}`, Kominers, Thaler,
Zheng, manuscript (Sept. 2026), §2, p.6, display.

**Formalization Note.** A `Finset` of the finite field `K` (so `|𝒵_ρ|` is `Finset.card`); the
filter predicate is a real inequality, decided classically. The inequality is non-strict, as
printed. -/
noncomputable def exceptionalSet {K ι : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype ι]
    (ρ : ℝ) (f g : ι → K) (C : Submodule K (ι → K)) : Finset K := by
  classical
  exact Finset.univ.filter (fun z : K => distToCode (f + z • g) C ≤ ρ)

end ProxGapTight


