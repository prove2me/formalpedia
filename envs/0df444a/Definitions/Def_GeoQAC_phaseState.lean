-- Prove2me | Definitions.Def_GeoQAC_phaseState
-- name    : GeoQAC_phaseState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:46.888438+00:00
-- url     : https://prove2.me/theorems/e43418ce-329f-43aa-a904-d2b29722995b
-- title:
--   The phase state $|\chi_f\rangle$
-- statement:
--   The phase state of a Boolean function $f:\{0,1\}^n\to\{0,1\}$ is
--   $$
--   |\chi_f\rangle = 2^{-n/2}\sum_{x\in\{0,1\}^n} i^{f(x)}\,|x\rangle ,
--   $$
--   the "$i^f$ encoding". A circuit that computes $f$ exactly yields $|\chi_f\rangle$ at twice the depth, so variance bounds on circuit outputs constrain $f$.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), §3.4, p.24

import Mathlib

namespace GeoQAC

/-- The phase state `|χ_f⟩ = 2^{−n/2} ∑_x i^{f(x)} |x⟩` of a Boolean function (arXiv:2604.07178,
version of 2026-11-03, §3.4, p.24; the "`i^f` encoding").

**Formalization Note.** `i^{f(x)}` is `i` when `f(x) = 1` and `1` otherwise; the vector is indexed by
`x : Fin n → Bool`. -/
noncomputable def phaseState {n : ℕ} (f : (Fin n → Bool) → Bool) : (Fin n → Bool) → ℂ :=
  fun x => ((Real.sqrt (2 ^ n))⁻¹ : ℂ) * (if f x then Complex.I else 1)

end GeoQAC


