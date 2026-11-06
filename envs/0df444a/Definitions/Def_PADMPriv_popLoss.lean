-- Prove2me | Definitions.Def_PADMPriv_popLoss
-- name    : PADMPriv_popLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:10.142573+00:00
-- url     : https://prove2.me/theorems/a9bbfc44-a2bd-4c7e-a4b2-86220c7c0a6c
-- title:
--   Population loss $F(x)=\mathbb E_{d\sim P_R}[f(x,d)]$
-- statement:
--   Let $R$ be the domain of data records, $P_R$ a distribution on $R$ and $f:\mathbb R^p\times R\to\mathbb R$ a sample loss. The **population loss** is
--   $$
--   F(x) := \mathbb E_{d\sim P_R}\big[f(x,d)\big].
--   $$
--   Model (1) is to be solved for this $F$, while PADM only ever sees the sample losses $f_k = f(\cdot,d_{(k)})$.
--
--   **Formalization Note** A Bochner integral; statements using it assume $f(x,\cdot)$ measurable and $P_R$-integrable for every $x$.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Section 3.3, p.8

import Mathlib

namespace PADMPriv

open MeasureTheory

/-- The population loss `F(x) := E_{d ∼ P_R}[f(x, d)]` of Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d),
Section 3.3, p.8, for a sample loss `f : ℝᵖ × R → ℝ` and a record distribution `P_R` on `R`.

**Formalization Note** A Bochner integral; every statement using it assumes `f(x, ·)`
measurable and `P_R`-integrable for each `x`, so the junk value `0` of a non-integrable
integrand never occurs. -/
noncomputable def popLoss {p : ℕ} {R : Type*} [MeasurableSpace R]
    (f : EuclideanSpace ℝ (Fin p) → R → ℝ) (PR : Measure R) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∫ d, f x d ∂PR

end PADMPriv


