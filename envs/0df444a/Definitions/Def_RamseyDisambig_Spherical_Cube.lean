-- Prove2me | Definitions.Def_RamseyDisambig_Spherical_Cube
-- name    : RamseyDisambig_Spherical_Cube
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:25:02.575635+00:00
-- url     : https://prove2.me/theorems/f0f3242f-c8a8-43fd-bca4-a2617f5a5ec3
-- title:
--   Hamming cubes and Gap-Hamming disambiguations
-- statement:
--   Let $Q_N=\{0,1\}^N$, with $d_H(x,y)$ the number of coordinates on which $x$ and $y$ differ. For $N\ge1$ and $0<\varepsilon<1/2$, the Gap-Hamming partial matrix is
--   $$H_\varepsilon^N[x,y]=\begin{cases}0&d_H(x,y)\le\varepsilon N,\\1&d_H(x,y)\ge(1-\varepsilon)N,\\\star&\text{otherwise}.\end{cases}$$
--   A Gap-Hamming disambiguation is any binary matrix preserving its specified entries. Since $\operatorname{diam}(Q_N)=N$, this is precisely the $\varepsilon$-gap condition for the Hamming cube in the stated range.
--
--   This object is the target of Theorem 2 and the discrete precursor of the spherical result.
--
--   **Formalization Note** The carrier is `Fin N → Bool`, and `hammingDist` is cast to $\mathbb R$ before comparing thresholds; no rounding occurs. The total matrix function gives precedence to the near case when the prescriptions overlap outside the supported positive-dimensional parameter range. Theorem 2 chooses a positive threshold dimension.
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), §1 and §2.1, pp. 4, 8 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Matrices
import Definitions.Def_RamseyDisambig_Spherical_GapColoring

set_option autoImplicit false

noncomputable section

namespace RamseyDisambig.Spherical

/-- The Hamming cube Q_N (pp. 4, 8). -/
abbrev Cube (N : ℕ) := Fin N → Bool

def cubeDistance {N : ℕ} (x y : Cube N) : ℝ := (hammingDist x y : ℝ)

/-- The Gap-Hamming partial matrix, for use with N ≥ 1 and 0 < ε < 1/2. -/
def gapHammingMatrix (ε : ℝ) (N : ℕ) : PartialMatrix (Cube N) (Cube N) :=
  fun x y => if cubeDistance x y ≤ ε * N then some false
    else if (1 - ε) * N ≤ cubeDistance x y then some true else none

def IsGapHammingDisambiguation (ε : ℝ) (N : ℕ) (c : Cube N → Cube N → Bool) : Prop :=
  IsDisambiguation (gapHammingMatrix ε N) c

end RamseyDisambig.Spherical


