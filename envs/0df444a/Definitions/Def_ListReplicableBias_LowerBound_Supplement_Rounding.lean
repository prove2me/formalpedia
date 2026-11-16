-- Prove2me | Definitions.Def_ListReplicableBias_LowerBound_Supplement_Rounding
-- name    : ListReplicableBias_LowerBound_Supplement_Rounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:22:44.273834+00:00
-- url     : https://prove2.me/theorems/039d09aa-049f-459c-9415-85576be6136b
-- title:
--   Definitions 6.1, 6.2, 6.6 — good shifts, shifted rounding, canonical list, uniform shift
-- statement:
--   Fix a grid width $\varepsilon>0$.
--
--   1. A shift $u$ is **$\alpha$-good** for $p$ if the half-open interval $[p-\alpha,p+\alpha)$, shifted by $u$, lies in one grid cell: there is an integer $k$ with
--   $$[(p+u)-\alpha,(p+u)+\alpha)\subseteq[k\varepsilon,(k+1)\varepsilon).$$
--   2. The **$u$-rounding** of $x\in\mathbb R$ is $R_u(x)=\lfloor (x+u)/\varepsilon\rfloor\,\varepsilon$; for a vector it is applied coordinatewise.
--   3. The **canonical list** of $p\in[0,1]^d$ is $\mathcal L_p=\{R_u(p):u\in[0,\varepsilon)\}$.
--   4. The random shift has law $\mathrm{Unif}([0,\varepsilon))$.
--
--   These objects drive the upper-bound algorithms of §6: a random shift makes rounding of a noisy estimate agree with rounding of the true bias, and the canonical list is the list of possible outputs.
--
--   **Formalization Note** Good shifts are defined for every real $p$ (the algorithm applies the notion to empirical means), and the range $u\in[0,\varepsilon)$ is a hypothesis of each result rather than part of the predicate. The finiteness and size of $\mathcal L_p$ are Lemma 6.7, not part of the definition. The uniform law is Lebesgue measure conditioned on $[0,\varepsilon)$.
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, Definitions 6.1, 6.2, PDF p. 8; Definition 6.6, PDF p. 9; Lemma 6.5, PDF p. 8

import Mathlib

noncomputable section

open MeasureTheory ProbabilityTheory

namespace ListReplicableBias.LowerBound.Supplement

/-- Definition 6.1, PDF p. 8: the shift u is α-good for p when the half-open
interval [p − α, p + α), shifted by u, lies inside one half-open grid cell
[kε, (k+1)ε) for some integer k. Stated for every real p (Algorithm 1 applies it
to empirical means); the range u ∈ [0, ε) is a hypothesis of each result. -/
def IsGoodShift (ε α p u : ℝ) : Prop :=
  ∃ k : ℤ, Set.Ico ((p + u) - α) ((p + u) + α) ⊆
    Set.Ico ((k : ℝ) * ε) (((k : ℝ) + 1) * ε)

/-- Definition 6.2, PDF p. 8: the u-rounding R_u(x) = ⌊(x + u)/ε⌋ · ε. -/
def roundShift (ε u x : ℝ) : ℝ := (⌊(x + u) / ε⌋ : ℝ) * ε

/-- Definition 6.2, PDF p. 8: coordinatewise u-rounding of a vector. -/
def roundVec {d : ℕ} (ε u : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => roundShift ε u (x i)

/-- Definition 6.6, PDF p. 9: the canonical list L_p = {R_u(p) | u ∈ [0, ε)}.
Its finiteness and size bound are Lemma 6.7, not part of the definition. -/
def canonicalList {d : ℕ} (ε : ℝ) (p : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {y | ∃ u ∈ Set.Ico (0 : ℝ) ε, y = roundVec ε u p}

/-- The uniform law Unif([0, ε)) of the random shift (Lemma 6.5, Algorithm 1
line 1): Lebesgue measure conditioned on the half-open interval [0, ε). -/
def uniformShift (ε : ℝ) : Measure ℝ := volume[|Set.Ico (0 : ℝ) ε]

end ListReplicableBias.LowerBound.Supplement


