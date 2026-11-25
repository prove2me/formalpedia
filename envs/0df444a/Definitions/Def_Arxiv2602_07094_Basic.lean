-- Prove2me | Definitions.Def_Arxiv2602_07094_Basic
-- name    : Arxiv2602_07094_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T18:37:49.727679+00:00
-- url     : https://prove2.me/theorems/2fafacc0-42a6-5508-9f48-fb7dc6211a1d
-- title:
--   Sinclair matrix, Pauli decomposition, sample coherency matrix, entropy and alpha angle
-- statement:
--   Objects of Section 3.1 and Section 4 of Gabot, Frontera-Pons, Fix, Ren and Ovarlez (2026).
--
--   1. **Sinclair matrix (eq. 1).** Each pixel carries a complex $2\times2$ scattering matrix $\mathbf S=\begin{pmatrix}S_{hh}&S_{vh}\\S_{hv}&S_{vv}\end{pmatrix}$, with $h$ indexed by $0$ and $v$ by $1$. It is **reciprocal** if $S_{hv}=S_{vh}$ (the monostatic configuration).
--   2. **Channel amplitudes.** The amplitudes of $\mathbf S$ are the four moduli $|S_{ij}|$. They are all that an amplitude-only model sees of $\mathbf S$ (Section 4).
--   3. **Pauli decomposition (eq. 4).** For reciprocal $\mathbf S$, the Pauli coefficients are $\alpha=(S_{hh}+S_{vv})/\sqrt2$, $\beta=(S_{hh}-S_{vv})/\sqrt2$ and $\gamma=\sqrt2\,S_{hv}$, and the Pauli vector is $\mathbf k=(\alpha,\beta,\gamma)^T\in\mathbb C^3$.
--   4. **Sample coherency matrix (eq. 7).** For $N$ Pauli vectors $\mathbf k_1,\dots,\mathbf k_N$, $\hat{\mathbf T}=\frac1N\sum_{i=1}^N\mathbf k_i\mathbf k_i^H$, a Hermitian positive semidefinite $3\times3$ matrix.
--   5. **$H$-$\alpha$ quantities.** Let $\lambda_1,\lambda_2,\lambda_3$ be the eigenvalues of a Hermitian $3\times3$ matrix $\mathbf T$, with orthonormal eigenvectors $\mathbf e_1,\mathbf e_2,\mathbf e_3$, and let $p_i=\lambda_i/\sum_j\lambda_j$. The entropy is $H=-\sum_ip_i\log_3p_i$ (a term with $p_i=0$ contributes $0$), and the mean alpha angle is $\bar\alpha=\sum_ip_i\arccos|e_{i1}|$, where $e_{i1}$ is the first component of $\mathbf e_i$.
--   6. **Simple positive spectrum.** $\mathbf T$ has a simple positive spectrum if its nonzero eigenvalues, counted with multiplicity, are pairwise distinct. Then every $\mathbf e_i$ with $p_i>0$ is unique up to a phase factor, so $\bar\alpha$ does not depend on the choice of eigenvectors.
--
--   **Formalization Note** The eigenvalues and orthonormal eigenvectors are those Mathlib attaches to a Hermitian matrix (`IsHermitian.eigenvalues` and the columns of `eigenvectorUnitary`). $H$ and $\bar\alpha$ are set to $0$ on non-Hermitian matrices, a case that never occurs for $\hat{\mathbf T}$. The paper prints $H=\sum_ip_i\log p_i$ with no sign or base while stating $0\le H\le1$. The definition uses the Cloude–Pottier entropy $-\sum_ip_i\log_3p_i$, which satisfies that range. The simple-positive-spectrum condition is not in the paper: it is the condition under which the paper's definition of $\bar\alpha$ is unambiguous.
-- source:
--   Gabot, Frontera-Pons, Fix, Ren and Ovarlez, Exploring Polarimetric properties preservation for PolSAR image reconstruction with Complex-valued Convolutional Neural Networks, arXiv:2602.07094v1 (2026), Section 3.1 (eqs. (1)-(4), (7), PDF pp. 4-5) and Section 4 (PDF p. 10)

import Mathlib

/-!
Gabot, Frontera-Pons, Fix, Ren and Ovarlez, *Exploring Polarimetric properties preservation for
PolSAR image reconstruction with Complex-valued Convolutional Neural Networks*, arXiv:2602.07094v1
(2026): the Sinclair matrix, reciprocity, the Pauli decomposition, the sample coherency matrix and
the entropy and mean alpha angle of the `H`-`α` decomposition (Section 3.1, eqs. (1)-(4) and (7),
PDF pp. 4-5), and the channel amplitudes seen by an amplitude-only model (Section 4, PDF p. 10).
-/

noncomputable section

namespace Arxiv2602_07094

/-- Eq. (1), Section 3.1, p. 4: the Sinclair (scattering) matrix of a pixel,
`S = [[S_hh, S_vh], [S_hv, S_vv]]`, with index `0` for `h` and `1` for `v`. So `S 0 0 = S_hh`,
`S 0 1 = S_vh`, `S 1 0 = S_hv`, `S 1 1 = S_vv`. -/
abbrev SinclairMatrix : Type := Matrix (Fin 2) (Fin 2) ℂ

/-- Section 3.1, p. 4: the reciprocity principle of the monostatic configuration, `S_hv = S_vh`. -/
def IsReciprocal (S : SinclairMatrix) : Prop := S 1 0 = S 0 1

/-- Section 4, p. 10: the channel amplitudes `|S_ij|`, which are all that an amplitude-only model
sees of a Sinclair matrix. -/
def channelAmplitudes (S : SinclairMatrix) : Matrix (Fin 2) (Fin 2) ℝ := fun i j => ‖S i j‖

/-- Eq. (4), Section 3.1, p. 4: the Pauli coefficient `α = (S_hh + S_vv)/√2`. -/
def pauliAlpha (S : SinclairMatrix) : ℂ := (S 0 0 + S 1 1) / (Real.sqrt 2 : ℂ)

/-- Eq. (4), Section 3.1, p. 4: the Pauli coefficient `β = (S_hh - S_vv)/√2`. -/
def pauliBeta (S : SinclairMatrix) : ℂ := (S 0 0 - S 1 1) / (Real.sqrt 2 : ℂ)

/-- Eq. (4), Section 3.1, p. 4: the Pauli coefficient `γ = √2 S_hv`. -/
def pauliGamma (S : SinclairMatrix) : ℂ := (Real.sqrt 2 : ℂ) * S 1 0

/-- Section 3.1, p. 4: the Pauli vector `k = (α, β, γ)ᵀ`. -/
def pauliVector (S : SinclairMatrix) : Fin 3 → ℂ := ![pauliAlpha S, pauliBeta S, pauliGamma S]

/-- Eq. (7), Section 3.1, p. 5: the sample coherency (covariance) matrix of `N` Pauli vectors,
`T̂ = (1/N) ∑ᵢ kᵢ kᵢᴴ`. -/
def sampleCoherency {N : ℕ} (k : Fin N → Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun a b => (N : ℂ)⁻¹ * ∑ i, k i a * star (k i b)

/-- Section 3.1, p. 5: the pseudo-probabilities `p_i = λ_i / ∑_j λ_j` of a Hermitian `3 × 3`
matrix, `λ_i` its eigenvalues. -/
def pseudoProb {T : Matrix (Fin 3) (Fin 3) ℂ} (hT : T.IsHermitian) (i : Fin 3) : ℝ :=
  hT.eigenvalues i / ∑ j, hT.eigenvalues j

open Classical in
/-- Section 3.1, p. 5: the entropy `H = -∑_i p_i log₃ p_i` of the coherency matrix (with
`0 log 0 = 0`). The paper prints `∑_i p_i log p_i` and states `0 ≤ H ≤ 1`; the sign and base used
here are those of the cited Cloude–Pottier entropy, which satisfies that range. The value `0` off
Hermitian matrices is never used: every sample coherency matrix is Hermitian. -/
def entropyH (T : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  if hT : T.IsHermitian then -∑ i, pseudoProb hT i * Real.logb 3 (pseudoProb hT i) else 0

open Classical in
/-- Section 3.1, p. 5: the mean alpha angle `α = ∑_i p_i α_i`, `α_i = arccos |e_{i1}|`, where
`e_i` is a unit eigenvector of the coherency matrix for its `i`-th eigenvalue and `e_{i1}` its
first component. The eigenvectors are those of Mathlib's orthonormal eigenbasis (the columns of
`eigenvectorUnitary`); the value is independent of that choice when the positive eigenvalues are
distinct (`HasSimplePositiveSpectrum`). -/
def alphaAngle (T : Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  if hT : T.IsHermitian then
    ∑ i, pseudoProb hT i * Real.arccos ‖(hT.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℂ) 0 i‖
  else 0

open Classical in
/-- Section 3.1, p. 5 (condition implicit in the definition of the alpha angle): the nonzero
eigenvalues of `T`, i.e. the nonzero roots of its characteristic polynomial counted with
multiplicity, are pairwise distinct. Then each unit eigenvector `e_i` with `p_i > 0` is unique up
to a phase, so `|e_{i1}|` and the alpha angle do not depend on the choice of eigenvectors. -/
def HasSimplePositiveSpectrum (T : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  (T.charpoly.roots.filter (· ≠ 0)).Nodup

end Arxiv2602_07094


