-- Prove2me | Definitions.Def_SliceLinearity_Tests_Transfer
-- name    : SliceLinearity_Tests_Transfer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T02:39:37.774914+00:00
-- url     : https://prove2.me/theorems/096431a3-5a63-430e-8ea8-b6a756fc5111
-- title:
--   Biased testers, the test average $T_\lambda$, the transfer conditions (Definition 6.7), soundness guarantees and the conditioned test on $S(w)$
-- statement:
--   Fix $0<p<1$.
--
--   1. **Biased tester** (§6.2). A $k$-query $p$-biased tester is a distribution $\lambda$ on $H^{(k)}_{\rm even}\subseteq\mathbb F_2^k$ whose every marginal is $\mathrm{Ber}(p)$. It samples $(z_1,\dots,z_k)\sim\lambda^{\otimes n}$ and accepts $f$ when $\sum_i f(z_i)=0$.
--   2. **Test average** (p. 44). $T_\lambda(h_1,\dots,h_k)=\mathbb E_{(z_1,\dots,z_k)\sim\lambda^{\otimes n}}\prod_ih_i(z_i)$ for real functions $h_i$.
--   3. **Transfer conditions** (Definition 6.7).
--      - *Sampling:* the bits under $\lambda$ are pairwise independent, and the zero vector and every weight-two vector have positive probability.
--      - *Multilinear estimate:* there is a constant $C$, independent of $n$, such that for all real $h_1,\dots,h_k$ and every $i$, $|T_\lambda(h_1,\dots,h_k)|\le C\max_\chi|\langle h_i,\chi\rangle_{\mu_p}|\prod_{j\ne i}\|h_j\|_{2,\mu_p}$.
--   4. **Soundness guarantee** (§6, p. 36). The tester has soundness guarantee $s$ (with error $0$) if, in every dimension, acceptance probability at least $(1+\delta)/2$ with $0<\delta\le1$ implies $\max_{\varphi\text{ affine}}\mathrm{agr}_{\mu_p}(f,\varphi)\ge(1+s(\delta))/2$.
--   5. **Conditioned biased test** (p. 42). Sample $(z_1,\dots,z_k)\sim\lambda^{\otimes n}$ conditioned on $|z_1|=\dots=|z_k|=w$, query $f$ at $z_1,\dots,z_k$, and accept if $\sum_if(z_i)=0$.
--
--   **Formalization Note** The conditioned test is the weight function "$\lambda^{\otimes n}$ restricted to $S(w)^k$, divided by the probability of $S(w)^k$". When that probability is $0$ every weight is $0$, so no completeness claim about it can hold vacuously. Signed characters $\sigma\chi$ are affine maps, and $\pm1$ inputs are written in $\mathbb F_2$.
-- source:
--   Aydin, Larsen, Mittal, Richelson, Roy, Low Soundness Linearity Testing on Subsets of the Hypercube, STOC 2027 submission (manuscript sha256 457be236…), §6 p. 36 (PDF 38); §6.2 pp. 42–44 (PDF 44–46): the biased tester, the conditioned biased test, Definition 6.7, T_λ

import Mathlib
import Definitions.Def_SliceLinearity_Tests_SliceTests
import Definitions.Def_SliceLinearity_Tests_BiasedAnalysis
import Definitions.Def_SliceLinearity_Tests_ActiveSet

set_option autoImplicit false

namespace SliceLinearity.Tests

/-! # Biased testers, the transfer conditions, soundness guarantees and the conditioned test

Aydin, Larsen, Mittal, Richelson, Roy, *Low Soundness Linearity Testing on Subsets of the Hypercube*,
STOC 2027 submission (manuscript sha256 457be236…), §6 p. 36 (PDF 38), §6.2 pp. 42–44 (PDF 44–46,
Definition 6.7, the test average `T_λ`, the conditioned biased test). -/

/-- A `k`-query `p`-biased tester (§6.2): a distribution `λ` on the even-weight vectors `H^{(k)}_even`
of `F₂^k` whose every marginal is `Ber(p)`. It samples `(z₁, …, z_k) ∼ λ^{⊗n}`. -/
def IsBiasedTester (p : ℝ) {k : ℕ} (lam : (Fin k → ZMod 2) → ℝ) : Prop :=
  IsDistW lam ∧ (∀ v, lam v ≠ 0 → ∑ j, v j = 0) ∧ ∀ j, bitProb lam j 1 = p

/-- The test average `T_λ(h₁, …, h_k) = E_{(z₁,…,z_k)∼λ^{⊗n}} ∏ᵢ hᵢ(zᵢ)` (p. 44). -/
noncomputable def testAvg {k : ℕ} (lam : (Fin k → ZMod 2) → ℝ) {n : ℕ} (h : Fin k → Cube n → ℝ) : ℝ :=
  ∑ z : Fin k → Cube n, tensorPow lam n z * ∏ i, h i (z i)

/-- Definition 6.7(1), sampling: the bits under `λ` are pairwise independent, and the zero vector
and every weight-two vector have positive probability. -/
def SamplingCondition {k : ℕ} (lam : (Fin k → ZMod 2) → ℝ) : Prop :=
  PairwiseIndepBits lam ∧ 0 < lam 0 ∧
    ∀ v : Fin k → ZMod 2, (Finset.univ.filter fun j => v j ≠ 0).card = 2 → 0 < lam v

/-- Definition 6.7(2), the multilinear estimate with constant `C`: for every dimension `n`, all real
`h₁, …, h_k` and every `i`, `|T_λ(h)| ≤ C · max_χ |⟨hᵢ, χ⟩_{μ_p}| · ∏_{j≠i} ‖h_j‖_{2,μ_p}`. -/
def MultilinearEstimate (p : ℝ) {k : ℕ} (lam : (Fin k → ZMod 2) → ℝ) (C : ℝ) : Prop :=
  ∀ (n : ℕ) (h : Fin k → Cube n → ℝ) (i : Fin k),
    |testAvg lam h| ≤ C * maxCorr (muP p) (h i) * ∏ j ∈ Finset.univ.erase i, norm2W (muP p) (h j)

/-- Definition 6.7, the transfer conditions: sampling, and the multilinear estimate for some
constant `C` independent of `n`. -/
def TransferConditions (p : ℝ) {k : ℕ} (lam : (Fin k → ZMod 2) → ℝ) : Prop :=
  SamplingCondition lam ∧ ∃ C : ℝ, MultilinearEstimate p lam C

/-- The biased tester `λ^{⊗n}` has soundness guarantee `s` (with error `0`): in every dimension, if
`f` passes with probability at least `(1 + δ)/2`, `0 < δ ≤ 1`, then some affine map (signed
character) agrees with `f` under `μ_p` with probability at least `(1 + s(δ))/2` (§6, p. 36). -/
def SoundnessGuarantee (p : ℝ) {k : ℕ} (lam : (Fin k → ZMod 2) → ℝ) (s : ℝ → ℝ) : Prop :=
  ∀ (n : ℕ) (f : Cube n → ZMod 2) (δ : ℝ), 0 < δ → δ ≤ 1 →
    (1 + δ) / 2 ≤ accW (tensorPow lam n) f → (1 + s δ) / 2 ≤ maxAffAgrW (muP p) f

/-- The **conditioned biased test** on `S(w)` (p. 42): `(z₁, …, z_k) ∼ λ^{⊗n}` conditioned on
`|z₁| = ⋯ = |z_k| = w`. The weight of a tuple is its `λ^{⊗n}` weight on the event, divided by the
probability of the event. -/
noncomputable def condWeight {k : ℕ} (lam : (Fin k → ZMod 2) → ℝ) (n w : ℕ)
    (z : Fin k → Cube n) : ℝ :=
  (if ∀ i, z i ∈ slice n w then tensorPow lam n z else 0) /
    ∑ z' : Fin k → Cube n, if ∀ i, z' i ∈ slice n w then tensorPow lam n z' else 0

end SliceLinearity.Tests


