-- Prove2me | Definitions.Def_StretchDepth_testOf
-- name    : StretchDepth_testOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:05:58.058217+00:00
-- url     : https://prove2.me/theorems/0427d4b6-287b-4a69-bb89-3c8edd47c5e0
-- title:
--   The test $T_\rho$ and the range probability
-- statement:
--   For a construction $H$ and a partial assignment $\rho$, the test $T_\rho:\{0,1\}^M\to\{0,1\}$ accepts $y$ exactly when $y\in\mathrm{range}(H^{F})$ for some total $F\supseteq\rho$. The **range probability**
--   $$
--   \Pr_{\rho\sim\mathcal R^{n,N}_p,\,y\sim U_M}\bigl[\exists G\supseteq\rho,\ y\in\mathrm{range}(H^G)\bigr]=\mathbb E_\rho\,2^{-M}|\{y: T_\rho(y)=1\}|
--   $$
--   is the quantity bounded by Lemma 1. The test is the one used to refute a reduction in the proof of Theorem 1.
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Theorem 1, p.19; Lemma 1, p.16

import Definitions.Def_StretchDepth_PartialAssign

namespace StretchDepth

variable {n N m M : ℕ}

open Classical in
/-- **The test `T_ρ`.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Theorem 1, p.19: "Set T = Tρ, where Tρ(y) = 1 if and only if there
exists G′ ⊇ ρ such that y ∈ range(HG′)." -/
noncomputable def testOf (H : Bits m → RoundTree n N M) (ρ : PartialAssign n N) (y : Bits M) :
    Bool :=
  decide (∃ F : Bits n → Bits N, Extends F ρ ∧ ∃ x, run F (H x) = y)

/-- The left side of Lemma 1, p.16: `Pr_{ρ ∼ R^{n,N}_p, y ∼ U_M}[∃ G ⊇ ρ, y ∈ range(H^G)]`, which
the proof writes `E_ρ 2^{−M} |Y^ρ|`. -/
noncomputable def rangeProb (p : ℝ) (H : Bits m → RoundTree n N M) : ℝ :=
  expRho p fun ρ => ((Finset.univ.filter fun y : Bits M => testOf H ρ y = true).card : ℝ) / 2 ^ M

end StretchDepth


