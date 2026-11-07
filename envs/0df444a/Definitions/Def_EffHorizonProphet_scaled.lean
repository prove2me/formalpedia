-- Prove2me | Definitions.Def_EffHorizonProphet_scaled
-- name    : EffHorizonProphet_scaled
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:34.923087+00:00
-- url     : https://prove2.me/theorems/a67e2e08-f821-4405-9608-30152f476991
-- title:
--   The factor $F(z/w)$ with $F(z/0):=1$
-- statement:
--   For a distribution function $F$, this is the factor $F(z/w)$, with the paper's convention $F(z/0):=\lim_{u\to\infty}F(u)=1$ for $z\ge0$.
--
--   **Formalization Note** In Lean $z/0=0$, which is not this convention, so the case $w=0$ is explicit.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Lemma 3, p.8; Lemma 15, p.27

import Mathlib

namespace EffHorizonProphet

/-- The factor `F(z/w)` with the paper's convention `F(z/0) := lim_{u→∞} F(u) = 1` for `z ≥ 0`
(Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Lemma 3, p.8; Lemma 15, p.27).

**Formalization Note** Lean's `z / 0 = 0` is not this convention, hence the explicit case. -/
noncomputable def scaled (F : ℝ → ℝ) (w z : ℝ) : ℝ :=
  if w = 0 then 1 else F (z / w)

end EffHorizonProphet


