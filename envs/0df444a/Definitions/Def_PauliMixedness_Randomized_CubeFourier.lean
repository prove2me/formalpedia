-- Prove2me | Definitions.Def_PauliMixedness_Randomized_CubeFourier
-- name    : PauliMixedness_Randomized_CubeFourier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:40:27.347056+00:00
-- url     : https://prove2.me/theorems/98046e66-944b-467b-8119-38b268a6906e
-- title:
--   Boolean cube probabilities and correlation energies
-- statement:
--   Let $x\in\{0,1\}^N$, with $0$ representing $+1$ and $1$ representing $-1$. A probability mass function $p$ ranges over all distributions on this cube, allowing zero masses. For $S\subseteq[N]$, define $\chi_S(x)=\prod_{j\in S}(-1)^{x_j}$ and
--
--   $$a_S=\sum_xp(x)\chi_S(x),\qquad E(p)=\sum_{S\ne\varnothing}a_S^2,\qquad E_k(p)=\sum_{|S|=k}a_S^2.$$
--
--   The distribution is $(\Delta,k,\beta)$-wise correlated when $E_k(p)\ge\beta E(p)$ and $E_k(p)\ge\beta\Delta$. Parameter restrictions $0<\Delta,\beta\le1$ and $1\le k\le N$ belong to the theorem. The empty character is one; the empty coefficient is excluded from $E$. The uniform distribution has mass $2^{-N}$ on every string.
--
--   This interface connects physical basis outcomes to correlation-concentrated testing. The published Fourier transform uses uniform expectation, so it is applied to the density $2^N p(x)$, giving exactly the coefficients above.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, §3.5 pp.11–12, Definition 3.3 p.12

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier

noncomputable section
open scoped BigOperators

namespace PauliMixedness.Randomized

/-- §3.5, pp.11–12: bit 0 represents +1 and bit 1 represents −1. -/
abbrev Cube (N : ℕ) := Fin N → ZMod 2

/-- The real probability mass of a finite PMF. No support restriction is imposed. -/
def mass {Ω : Type*} (p : PMF Ω) (x : Ω) : ℝ := (p x).toReal

/-- §3.5: the sign represented by a bit. -/
def sign (b : ZMod 2) : ℝ := (-1 : ℝ) ^ b.val

/-- §3.5: χ_S(x), including χ_∅ = 1. -/
def chi {N : ℕ} (S : Finset (Fin N)) (x : Cube N) : ℝ :=
  ∏ j ∈ S, sign (x j)

/-- Indicator vector of a subset in the published F₂ Fourier representation. -/
def subsetVector {N : ℕ} (S : Finset (Fin N)) : Cube N :=
  fun j => if j ∈ S then 1 else 0

/-- §3.5: a_S = Σ_x p(x)χ_S(x). The published transform takes uniform
expectation, so its input is the density 2^N p, not the probability mass p. -/
def fourierCoeff {N : ℕ} (p : PMF (Cube N)) (S : Finset (Fin N)) : ℝ :=
  QAlgorithms.boolFourier (fun x => (2 : ℝ)^N * mass p x) (subsetVector S)

/-- §3.5 / Definition 3.3: energy omits the identity (empty subset). -/
def fourierEnergy {N : ℕ} (p : PMF (Cube N)) : ℝ :=
  ∑ S : Finset (Fin N), if S = ∅ then 0 else fourierCoeff p S ^ 2

/-- Definition 3.3: energy at precisely weight k. -/
def weightEnergy {N : ℕ} (p : PMF (Cube N)) (k : ℕ) : ℝ :=
  ∑ S : Finset (Fin N), if S.card = k then fourierCoeff p S ^ 2 else 0

/-- Definition 3.3, p.12. The parameter domains are theorem hypotheses. -/
def WiseCorrelated {N : ℕ} (p : PMF (Cube N)) (Δ : ℝ) (k : ℕ) (β : ℝ) : Prop :=
  β * fourierEnergy p ≤ weightEnergy p k ∧ β * Δ ≤ weightEnergy p k

/-- Uniform distribution on the full cube, including all 2^N strings. -/
def cubeUniform (N : ℕ) : PMF (Cube N) := PMF.uniformOfFintype (Cube N)

end PauliMixedness.Randomized


