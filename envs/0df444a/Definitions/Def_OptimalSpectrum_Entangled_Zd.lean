-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_Zd
-- name    : OptimalSpectrum_Entangled_Zd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:30.33972+00:00
-- url     : https://prove2.me/theorems/8fb51c72-6ca0-4158-afcd-4fa2016ece9b
-- title:
--   Candidate spectra $Z_d=\{z\in[0,L]^d: z_1\ge\cdots\ge z_d,\ \sum_i z_i\le1\}$
-- statement:
--   For $L>0$,
--
--   $$Z_d=\Big\{z\in[0,L]^d:\ z_1\ge\cdots\ge z_d,\ \sum_{i=1}^d z_i\le1\Big\}.$$
--
--   It contains the true spectrum of a small-bucket state $0\preceq\sigma\preceq LI_d$ with $\mathrm{tr}\,\sigma\le1$, and the least-squares estimators of Section 6 choose their output from it.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §6 Setup, p. 13 (PDF p. 15)

import Mathlib

namespace OptimalSpectrum.Entangled

/-- **Candidate spectra `Z_d`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §6 Setup, printed p. 13 (PDF p. 15): "assume that α belongs to the compact set
Z_d = {z ∈ [0, L]^d : z₁ ⩾ ⋯ ⩾ z_d, ∑_(i=1)^d z_i ⩽ 1}."

**Formalization Note.** Coordinates are indexed by `Fin d`; "z₁ ⩾ ⋯ ⩾ z_d" is `Antitone z`. -/
def Zd (d : ℕ) (L : ℝ) : Set (Fin d → ℝ) :=
  {z | (∀ i, z i ∈ Set.Icc 0 L) ∧ Antitone z ∧ ∑ i, z i ≤ 1}

end OptimalSpectrum.Entangled


