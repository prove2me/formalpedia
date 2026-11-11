-- Prove2me | Definitions.Def_OptTwoSrcExt_fourier
-- name    : OptTwoSrcExt_fourier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:41.9962+00:00
-- url     : https://prove2.me/theorems/29fdeb49-bd91-4d17-837e-ea40daab473f
-- title:
--   Fourier coefficients $\hat P(\lambda)=\mathbb E_{Z\sim P}(-1)^{\lambda\cdot Z}$ of a law on $\mathbb F_2^m$
-- statement:
--   For a law $P$ on $\mathbb F_2^m$ and $\lambda\in\mathbb F_2^m$, the **Fourier coefficient** (character expectation) is
--   $$\hat P(\lambda)=\mathbb E_{Z\sim P}(-1)^{\lambda\cdot Z}=\sum_{z}P(z)(-1)^{\lambda\cdot z},\qquad \lambda\cdot z=\sum_i\lambda_i z_i\in\mathbb F_2 .$$
--   Its absolute value is the **bias** of the character $\lambda$. For a law $P$ of a pair $(A,B)$ on $\mathbb F_2^a\times\mathbb F_2^v$, the coefficient at $(\lambda,\mu)$ is $\hat P(\lambda,\mu)=\mathbb E(-1)^{\lambda\cdot A+\mu\cdot B}$; $\lambda$ is the coefficient on $A$.
--
--   These coefficients control statistical distance to uniform (Lemma 2.11), the basic tool behind every extraction bound of the paper.
--
--   **Formalization Note** The module also defines the sign $(-1)^b$ of a bit $b\in\mathbb F_2$ (through $b\in\{0,1\}$) and the binary inner product. The coefficient is signed; the published `LowErrExt.bias` is its absolute value.
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Lemma 2.11, p.17 (PDF p.19); Lemma 3.27, p.46 (PDF p.48)

import Mathlib

namespace OptTwoSrcExt

/-- **The sign `(−1)^b` of a bit `b ∈ 𝔽₂`**, computed through the representative `b.val ∈ {0, 1}`. -/
def signF2 (b : ZMod 2) : ℝ :=
  (-1 : ℝ) ^ b.val

/-- **The binary inner product `λ · z = ∑ᵢ λᵢ zᵢ ∈ 𝔽₂`** on `𝔽₂^ι`. -/
def dotF2 {ι : Type*} [Fintype ι] (l z : ι → ZMod 2) : ZMod 2 :=
  ∑ i, l i * z i

/-- **Fourier coefficient (character expectation) of a law on `𝔽₂^m`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Lemma 2.11, printed p.17 (PDF p.19): "Let P, Q be laws on
F_2^m, and write P̂(λ) = E_{Z∼P}(−1)^{λ·Z}."

`fourier P λ = ∑_z P(z) (−1)^{λ·z}`, a real number in `[−1, 1]`. Its absolute value is the bias of
the character `λ`.

**Formalization Note.** This is the signed coefficient; the published `LowErrExt.bias` is its
absolute value and is not used here. -/
noncomputable def fourier {ι : Type*} [Fintype ι] (P : PMF (ι → ZMod 2)) (l : ι → ZMod 2) : ℝ :=
  ∑' z, (P z).toReal * signF2 (dotF2 l z)

/-- **Fourier coefficient of a law of a pair `(A, B)` on `𝔽₂^a × 𝔽₂^v`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Lemma 2.11, printed p.17 (PDF p.19) and Lemma 3.27,
printed p.46 (PDF p.48) ("mixed character with nonzero coefficient on Z").

`fourierPair P λ μ = E_{(A,B)∼P} (−1)^{λ·A + μ·B}`: the character `(λ, μ)` of the concatenated
vector `(A, B)`; `λ` is the coefficient on `A`. -/
noncomputable def fourierPair {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : PMF ((ι → ZMod 2) × (κ → ZMod 2))) (l : ι → ZMod 2) (m : κ → ZMod 2) : ℝ :=
  ∑' z, (P z).toReal * signF2 (dotF2 l z.1 + dotF2 m z.2)

end OptTwoSrcExt


