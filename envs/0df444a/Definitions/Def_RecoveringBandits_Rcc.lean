-- Prove2me | Definitions.Def_RecoveringBandits_Rcc
-- name    : RecoveringBandits_Rcc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:53:30.062287+00:00
-- url     : https://prove2.me/theorems/06a35877-2a0c-4ec5-81c0-a8c71a9c45be
-- title:
--   The upper concave envelope $R^{cc}_i$
-- statement:
--   A function $f:\{0,1,2,\dots\}\to\mathbb R$ is **concave** when its increments $f(d+1)-f(d)$ are non-increasing in $d$. The **upper concave envelope** of $r=R_i$ is the pointwise minimum of all concave majorants:
--
--   $$R^{cc}_i(d)=\min\{f(d)\ :\ f\text{ concave},\ f(e)\ge r(e)\ \forall e\ge0\}.$$
--
--   The envelope is used in the analysis of the long-run values $F_i$ (Claims 1–2).
--
--   **Formalization Note** For an admissible arm the constant $R_{\max}$ is a concave majorant and every value is at least $r(d)$, so the infimum is real (and attained).
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, §4.1, p.10

import Mathlib

namespace RecoveringBandits

/-- **Concavity on `ℤ₊ ∪ {0}`**: the increments `f(d + 1) − f(d)` are non-increasing in `d`. -/
def DiscreteConcave (f : ℕ → ℝ) : Prop :=
  ∀ d : ℕ, f (d + 2) - f (d + 1) ≤ f (d + 1) - f d

/-- **The upper concave envelope `R^cc_i`** (arXiv:2106.14813v2, §4.1, p.10): "the point-wise
minimum of all concave functions `F : ℤ₊ ∪ {0} → ℝ` that satisfy `F(d) ≥ R_i(d)` for all
non-negative integer `d`".

**Formalization Note.** A function on `ℤ₊ ∪ {0}` is concave when its first differences are
non-increasing (`DiscreteConcave`), the same as being the restriction of a concave function on
`[0, ∞)`. For an admissible arm the constant `Rmax` is such a majorant and every value is
`≥ r d`, so the set below is nonempty and bounded below and `sInf` is the real infimum
(in fact the minimum: the pointwise infimum of concave majorants is a concave majorant). -/
noncomputable def Rcc (r : ℕ → ℝ) (d : ℕ) : ℝ :=
  sInf {v : ℝ | ∃ f : ℕ → ℝ, DiscreteConcave f ∧ (∀ e, r e ≤ f e) ∧ v = f d}

end RecoveringBandits


