-- Prove2me | Definitions.Def_WeightedSpectralSketch_LowerBound_Stat
-- name    : WeightedSpectralSketch_LowerBound_Stat
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:56:30.713804+00:00
-- url     : https://prove2.me/theorems/b87a468d-17ae-40d6-ab6c-63e474d2d7b8
-- title:
--   Hellinger distance $H^2$, the shifted Beta noise, product noise, sketch laws and uniform averages
-- statement:
--   1. For probability measures $P,Q$ with densities $p,q$ against a common dominating measure $\mu$, the **squared Hellinger distance** is (p. 9)
--   $$H^2(P,Q)=\tfrac12\int\big(\sqrt p-\sqrt q\big)^2\,d\mu ,$$
--   independent of $\mu$; we take $\mu=P+Q$.
--   2. The **noise** $Z=\tfrac12+\mathrm{Beta}(3,3)$ has density (Eq. (4))
--   $$f(z)=\mathbf 1\{\tfrac12\le z\le\tfrac32\}\cdot 30\,(z-\tfrac12)^2(\tfrac32-z)^2 ,$$
--   so $Z\in[\tfrac12,\tfrac32]$ and $\mathbb E Z=1$. For a finite coordinate set $E$, the product noise is the law of independent copies $(Z_e)_{e\in E}$.
--   3. For a fixed sketch matrix $A\in\mathbb R^{N\times E}$, base weights $w\in\mathbb R^E$ and a deterministic shift $s\in\mathbb R^E$, the **sketch law** is the law of $A\tilde w$ with $\tilde w_e=w_eZ_e+s_e$. Taking $s=0$ gives the No case and $s=\mathbf 1_q$ the Yes case of §4.1.
--   4. For a finite set $S$ and the uniform distribution on it: $\mathrm{avg}(f)=|S|^{-1}\sum_{s}f(s)$, $\Pr(E)=|E|/|S|$, and $\mathbb E[f\mid E]=|E|^{-1}\sum_{s\in E}f(s)$.
--
--   These are the statistical ingredients of the reduction from distinguishing Yes/No to leverage scores (§3.2, §4).
--
--   **Formalization Note.** $H^2$ is half of the published `FoundationsRL.DECLower.hellingerSq`, which has no factor $\tfrac12$, so every constant matches the page. All noises are real and continuous; nothing is discretized.
-- source:
--   Chen, Chen and Yang, A Tight Superlinear Lower Bound on the Sketching Dimension of Weighted Spectral Sparsification, STOC 2027 submission #109 (2026), pinned preprint SHA-256 94f9d972f8c75c577e7195e080b6ed59e722471145d40426a2f0c92315be9f44, p. 9, §3.2 (Hellinger distance, product distributions); p. 10, Eq. (4) (noise Z); pp. 10, 12 (Yes/No perturbed weights), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/109.pdf

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_hellingerSq

open MeasureTheory Matrix
open scoped ENNReal

namespace WeightedSpectralSketch.LowerBound

/-- The squared Hellinger distance with the paper's normalisation (p. 9):
`H²(P, Q) = ½ ∫ (√p - √q)² dμ` for densities against a common dominating measure (here `P + Q`).
It is half of the published `FoundationsRL.DECLower.hellingerSq`, which has no factor `½`. -/
noncomputable def hellinger2 {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ≥0∞ :=
  FoundationsRL.DECLower.hellingerSq μ ν / 2

/-- The density (4), p. 10, of the noise `Z = ½ + Beta(3, 3)`:
`f(z) = 1{½ ≤ z ≤ 3/2} · 30 (z - ½)² (3/2 - z)²`. -/
noncomputable def noiseDensity (z : ℝ) : ℝ :=
  Set.indicator (Set.Icc (1 / 2 : ℝ) (3 / 2)) (fun z => 30 * (z - 1 / 2) ^ 2 * (3 / 2 - z) ^ 2) z

/-- The law of the noise `Z` on `ℝ`: Lebesgue measure with density `noiseDensity`. -/
noncomputable def noiseLaw : Measure ℝ :=
  volume.withDensity fun z => ENNReal.ofReal (noiseDensity z)

/-- Independent copies `(Z_e)_{e ∈ E}` of the noise, one per coordinate. -/
noncomputable def noiseProd (E : Type*) [Fintype E] : Measure (E → ℝ) :=
  Measure.pi fun _ : E => noiseLaw

/-- The law of the sketch `A w̃` of the perturbed weights `w̃_e = w_e Z_e + shift_e`, for a fixed
sketch matrix `A`, fixed base weights `w` and a fixed deterministic shift (`0` for No, the unit
vector of the query edge for Yes; §4.1, p. 10, and p. 12). -/
noncomputable def sketchLaw {E : Type*} [Fintype E] {N : ℕ} (A : Matrix (Fin N) E ℝ)
    (w shift : E → ℝ) : Measure (Fin N → ℝ) :=
  (noiseProd E).map fun z => A *ᵥ (fun e => w e * z e + shift e)

/-- The average of `f` under the uniform distribution on the finite type `S`. -/
noncomputable def avg {S : Type*} [Fintype S] (f : S → ℝ) : ℝ :=
  (∑ s, f s) / Fintype.card S

/-- The probability of the event `E` under the uniform distribution on the finite type `S`. -/
noncomputable def prob {S : Type*} [Fintype S] (E : S → Prop) : ℝ :=
  open Classical in ((Finset.univ.filter E).card : ℝ) / Fintype.card S

/-- The conditional expectation `E[f | E]` under the uniform distribution on `S`: the average of
`f` over the outcomes in `E`. -/
noncomputable def condAvg {S : Type*} [Fintype S] (E : S → Prop) (f : S → ℝ) : ℝ :=
  open Classical in (∑ s ∈ Finset.univ.filter E, f s) / (Finset.univ.filter E).card

end WeightedSpectralSketch.LowerBound


