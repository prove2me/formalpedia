-- Prove2me | Definitions.Def_LesHouchesWidth_GaussianMLP
-- name    : LesHouchesWidth_GaussianMLP
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T21:55:59.952022+00:00
-- url     : https://prove2.me/theorems/cc949131-a8ea-40ce-ad0c-2cb9fb491878
-- title:
--   Fully connected networks with Gaussian initialization and the NNGP kernel
-- statement:
--   Fully connected networks with Gaussian initialization, shared by the whole series.
--
--   Fix a depth $L$ and widths $n_0,\dots,n_{L+1}$ (a sequence $n:\mathbb N\to\mathbb N$), constants $C_b,C_W$ and a function $\sigma:\mathbb R\to\mathbb R$. In the notation of Lectures 1–3, $C_b=\sigma_b^2$, $C_W=\sigma_w^2$ and $\sigma=\varphi$.
--
--   1. **Parameters.** One standard Gaussian coordinate $\theta$ per bias and per weight, all independent (`stdGaussianParams`). The biases are $b^{(\ell)}_i=C_b^{1/2}\theta$ and the weights are $W^{(\ell)}_{ij}=(C_W/n_{\ell-1})^{1/2}\theta$. Thus $b^{(\ell)}_i\sim\mathcal N(0,C_b)$ and $W^{(\ell)}_{ij}\sim\mathcal N(0,C_W/n_{\ell-1})$, independent (eq. (119)).
--   2. **Preactivations** (eq. (118)): $z^{(1)}=b^{(1)}+W^{(1)}x$ and $z^{(\ell+1)}=b^{(\ell+1)}+W^{(\ell+1)}\sigma(z^{(\ell)})$ for $\ell\ge1$ (`mlpZ`; layer $0$ is the input).
--   3. **Gaussian pair average** (eq. (15)): $F_\sigma(\Sigma_{11},\Sigma_{12},\Sigma_{22})=\mathbb E[\sigma(u_1)\sigma(u_2)]$ for $(u_1,u_2)\sim\mathcal N(0,\Sigma)$ (`gaussPairAvg`).
--   4. **NNGP kernel** (eqs. (13)–(14), (120)): $K^{(1)}(x,x')=C_b+C_W\,x\cdot x'/n_0$ and $K^{(\ell+1)}=C_b+C_WF_\sigma(K^{(\ell)}(x,x),K^{(\ell)}(x,x'),K^{(\ell)}(x',x'))$ (`nngpKernel`).
--   5. **Uniform widths and output vectors.** `uniformWidths n0 nOut L N` has input width $n_0$, output width $n_{\mathrm{out}}$ and all hidden widths equal to $N$. `outputVector` is the vector $(z^{(L+1)}_i(x_a))_{i,a}$ on finitely many inputs. `blockDiagCov` is the covariance $\delta_{ij}K(x_a,x_b)$.
--   6. **Pairings.** `pairings N` is the set of perfect matchings of $\{0,\dots,N-1\}$, encoded as fixed-point-free involutions.
--
--   **Formalization Note** Layers are indexed as in Lectures 4–5, so $z^l$ and $K^l$ of Lecture 1 are $z^{(l+1)}$ and $K^{(l+1)}$ here. $F_\sigma$ uses Mathlib's `multivariateGaussian`, which is a point mass when the matrix is not positive semidefinite.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), pp. 2–5, eqs. (1)–(3), (5), (13)–(15); p. 28, eqs. (118)–(119); p. 32, eq. (120); p. 11, Result 2 (pairings).

import Mathlib

/-!
# Fully connected networks with Gaussian initialization (Les Houches lectures)

Shared definitions for the series formalizing Bahri–Hanin–Brossollet–Erba–Keup–Pacelli–Simon,
*Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3.

Indexing follows Lectures 4–5 (Section 4.2, eqs. (118)–(119)): widths `n 0, …, n (L+1)`,
preactivations `z^{(1)}, …, z^{(L+1)}`, and
`z^{(1)} = b^{(1)} + W^{(1)} x`, `z^{(ℓ+1)} = b^{(ℓ+1)} + W^{(ℓ+1)} σ(z^{(ℓ)})` for `ℓ ≥ 1`,
with independent `b^{(ℓ)}_i ∼ N(0, C_b)` and `W^{(ℓ)}_{ij} ∼ N(0, C_W / n_{ℓ-1})`.
(In the notation of Lectures 1–3, `z^l = z^{(l+1)}`, `σ_b^2 = C_b`, `σ_w^2 = C_W`, `φ = σ`.)
-/

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

/-- Index set of the parameters of a network of depth `L` with widths `n 0, …, n (L+1)`:
`inl ⟨ℓ, i⟩` is the bias `b^{(ℓ+1)}_i` and `inr ⟨ℓ, (i, j)⟩` is the weight `W^{(ℓ+1)}_{ij}`
(`ℓ ≤ L`, `i < n (ℓ+1)`, `j < n ℓ`). -/
abbrev ParamIndex (n : ℕ → ℕ) (L : ℕ) : Type :=
  (Σ ℓ : Fin (L + 1), Fin (n (ℓ.val + 1))) ⊕
    (Σ ℓ : Fin (L + 1), Fin (n (ℓ.val + 1)) × Fin (n ℓ.val))

/-- A configuration of standardized parameters (one real number per bias and weight). -/
abbrev Params (n : ℕ → ℕ) (L : ℕ) : Type := ParamIndex n L → ℝ

/-- The law of the standardized parameters: i.i.d. standard Gaussians `N(0, 1)`. -/
noncomputable def stdGaussianParams (n : ℕ → ℕ) (L : ℕ) : Measure (Params n L) :=
  Measure.pi fun _ => gaussianReal 0 1

instance (n : ℕ → ℕ) (L : ℕ) : IsProbabilityMeasure (stdGaussianParams n L) := by
  unfold stdGaussianParams; infer_instance

/-- The bias `b^{(ℓ+1)}_i = C_b^{1/2} θ_{b,ℓ,i}` (so `b^{(ℓ+1)}_i ∼ N(0, C_b)`; `0` if `ℓ > L`). -/
noncomputable def mlpBias {n : ℕ → ℕ} {L : ℕ} (Cb : ℝ) (θ : Params n L) (ℓ : ℕ)
    (i : Fin (n (ℓ + 1))) : ℝ :=
  if h : ℓ < L + 1 then Real.sqrt Cb * θ (Sum.inl ⟨⟨ℓ, h⟩, i⟩) else 0

/-- The weight `W^{(ℓ+1)}_{ij} = (C_W / n_ℓ)^{1/2} θ_{W,ℓ,i,j}`
(so `W^{(ℓ+1)}_{ij} ∼ N(0, C_W / n_ℓ)`; `0` if `ℓ > L`). -/
noncomputable def mlpWeight {n : ℕ → ℕ} {L : ℕ} (CW : ℝ) (θ : Params n L) (ℓ : ℕ)
    (i : Fin (n (ℓ + 1))) (j : Fin (n ℓ)) : ℝ :=
  if h : ℓ < L + 1 then Real.sqrt (CW / (n ℓ : ℝ)) * θ (Sum.inr ⟨⟨ℓ, h⟩, (i, j)⟩) else 0

/-- Preactivations in the indexing of Lectures 4–5: `mlpZ … 0 = x` (the input) and, for
`ℓ ≥ 0`, `mlpZ … (ℓ+1) = z^{(ℓ+1)}(x)`, where
`z^{(1)}_i = b^{(1)}_i + ∑_j W^{(1)}_{ij} x_j` and
`z^{(ℓ+1)}_i = b^{(ℓ+1)}_i + ∑_j W^{(ℓ+1)}_{ij} σ(z^{(ℓ)}_j)` for `ℓ ≥ 1` (eq. (118)). -/
noncomputable def mlpZ {n : ℕ → ℕ} {L : ℕ} (Cb CW : ℝ) (σ : ℝ → ℝ) (θ : Params n L)
    (x : Fin (n 0) → ℝ) : (ℓ : ℕ) → Fin (n ℓ) → ℝ
  | 0 => x
  | ℓ + 1 => fun i => mlpBias Cb θ ℓ i +
      ∑ j, mlpWeight CW θ ℓ i j * (if ℓ = 0 then mlpZ Cb CW σ θ x ℓ j else σ (mlpZ Cb CW σ θ x ℓ j))

/-- `F_σ(Σ₁₁, Σ₁₂, Σ₂₂) = E[σ(u₁) σ(u₂)]` for `(u₁, u₂) ∼ N(0, Σ)` with
`Σ = [[Σ₁₁, Σ₁₂], [Σ₁₂, Σ₂₂]]` (eq. (15)). -/
noncomputable def gaussPairAvg (σ : ℝ → ℝ) (s11 s12 s22 : ℝ) : ℝ :=
  ∫ u, σ (u 0) * σ (u 1) ∂(multivariateGaussian 0 !![s11, s12; s12, s22])

/-- The infinite-width (NNGP) kernel `K^{(ℓ)}(x, x')` of eq. (120) (equivalently eqs. (13)–(14)):
`K^{(1)}(x, x') = C_b + C_W (x · x') / n_0` and
`K^{(ℓ+1)}(x, x') = C_b + C_W F_σ(K^{(ℓ)}(x, x), K^{(ℓ)}(x, x'), K^{(ℓ)}(x', x'))` for `ℓ ≥ 1`.
The value at `ℓ = 0` is a placeholder `0` and is never used. -/
noncomputable def nngpKernel (Cb CW : ℝ) (σ : ℝ → ℝ) {n0 : ℕ} :
    ℕ → (Fin n0 → ℝ) → (Fin n0 → ℝ) → ℝ
  | 0, _, _ => 0
  | 1, x, x' => Cb + CW * (∑ j, x j * x' j) / (n0 : ℝ)
  | ℓ + 2, x, x' => Cb + CW * gaussPairAvg σ (nngpKernel Cb CW σ (ℓ + 1) x x)
      (nngpKernel Cb CW σ (ℓ + 1) x x') (nngpKernel Cb CW σ (ℓ + 1) x' x')

/-- Widths of a network of depth `L` whose hidden layers `1, …, L` all have width `N`, with input
width `n0` and output width `nOut`. -/
def uniformWidths (n0 nOut L N : ℕ) : ℕ → ℕ :=
  fun ℓ => if ℓ = 0 then n0 else if ℓ = L + 1 then nOut else N

theorem uniformWidths_last (n0 nOut L N : ℕ) : uniformWidths n0 nOut L N (L + 1) = nOut := by
  simp [uniformWidths]

/-- The vector of outputs `(z^{(L+1)}_i(x_a))_{i, a}` (`i < nOut`, `a < m`) of the network on
finitely many inputs `x_1, …, x_m`, as an element of Euclidean space indexed by `(i, a)`;
`h : n (L+1) = nOut` identifies the output layer with `Fin nOut`. -/
noncomputable def outputVector {n : ℕ → ℕ} {L m nOut : ℕ} (Cb CW : ℝ) (σ : ℝ → ℝ)
    (h : n (L + 1) = nOut) (xs : Fin m → Fin (n 0) → ℝ) (θ : Params n L) :
    EuclideanSpace ℝ (Fin nOut × Fin m) :=
  (WithLp.equiv 2 _).symm fun ia => mlpZ Cb CW σ θ (xs ia.2) (L + 1) (Fin.cast h.symm ia.1)

/-- The limiting covariance `δ_{ij} K(x_a, x_b)` on the index set `(i, a)`. -/
def blockDiagCov {k m : ℕ} (K : Fin m → Fin m → ℝ) : Matrix (Fin k × Fin m) (Fin k × Fin m) ℝ :=
  Matrix.of fun ia jb => if ia.1 = jb.1 then K ia.2 jb.2 else 0

/-- The pairings of `{0, …, N-1}`: fixed-point-free involutions `π` (each `k` is paired with
`π k ≠ k`, and `π (π k) = k`). -/
def pairings (N : ℕ) : Finset (Equiv.Perm (Fin N)) :=
  Finset.univ.filter fun π => ∀ k, π (π k) = k ∧ π k ≠ k

end LesHouchesWidth


