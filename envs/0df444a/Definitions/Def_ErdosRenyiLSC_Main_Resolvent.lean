-- Prove2me | Definitions.Def_ErdosRenyiLSC_Main_Resolvent
-- name    : ErdosRenyiLSC_Main_Resolvent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:54.700677+00:00
-- url     : https://prove2.me/theorems/9f98ba9e-2237-4001-b281-8dfa7bfb5e8b
-- title:
--   §3, §7, pp. 15–19, 66–69 — minors G^(T), Z_ij, Z_i, 𝒜_i, Υ_i, [v], Λ, Λ_d, Λ_o, Ω̃(η), Φ, ordered eigenvalues
-- statement:
--   This module collects the proof objects of Sections 3 and 7 for a real $N\times N$ matrix $M$ (later $M=H$ or $M=A=H+f|e\rangle\langle e|$) and a spectral parameter $z=E+i\eta$; $G(z)=(M-z)^{-1}$ and $m(z)=N^{-1}\operatorname{Tr}G(z)$ are as in the setting module.
--
--   1. **Minors** (Definition 3.3). For $\mathbb T\subset\{1,\dots,N\}$, $M^{(\mathbb T)}$ is the $(N-|\mathbb T|)\times(N-|\mathbb T|)$ matrix obtained by deleting the rows and columns indexed by $\mathbb T$, with the remaining indices keeping their names, and $G^{(\mathbb T)}(z)=(M^{(\mathbb T)}-z)^{-1}$. The entry $G^{(\mathbb T)}_{kl}$ is used only for $k,l\notin\mathbb T$.
--   2. **Quadratic forms** (3.14), (3.15). $Z_{ij}=\sum^{(ij)}_{k,l}h_{ik}G^{(ij)}_{kl}h_{lj}$, the sum over $k,l\notin\{i,j\}$, and
--   $$Z_i=\sum^{(i)}_{k,l}\Bigl(h_{ik}h_{li}-\frac1N\delta_{kl}\Bigr)G^{(i)}_{kl},\qquad [Z]=\frac1N\sum_i Z_i .$$
--   3. **Self-consistent equation terms** (3.24), Lemma 3.10. $\mathcal A_i=\frac1N\sum_j G_{ij}G_{ji}/G_{ii}$, $\Upsilon_i=h_{ii}-Z_i+\mathcal A_i$, and $[v]=\frac1N\sum_i(G_{ii}-m_{\mathrm{sc}})$.
--   4. **Error parameters** (3.9), (7.1). $\Lambda=|m-m_{\mathrm{sc}}|$, $\Lambda_d=\max_i|G_{ii}-m_{\mathrm{sc}}|$, $\Lambda_o=\max_{i\ne j}|G_{ij}|$; applied to $A$ they are $\widetilde\Lambda,\widetilde\Lambda_d,\widetilde\Lambda_o$.
--   5. **Good event and control parameter** (7.4), (7.13). For $N^{-1}(\log N)^L\le\eta\le3$, $\widetilde\Omega(\eta)$ is the event $\sup_{z\in D_L,\ \operatorname{Im}z=\eta}(\widetilde\Lambda_d(z)+\widetilde\Lambda_o(z))\le(\log N)^{-\xi}$, and
--   $$\Phi(z)=\frac{(\log N)^{\xi}}{q}+(\log N)^{2\xi}\Bigl(\sqrt{\frac{\operatorname{Im}\widetilde m(z)}{N\eta}}+\frac1{N\eta}\Bigr).$$
--   6. **High probability uniformly in $z$.** For an $N$-dependent set $S_N$ of spectral parameters, an event $E_N(z)$ holds with $(\xi,\nu)$-high probability uniformly in $z\in S_N$ if $\mathbb P(E_N(z)^c)\le e^{-\nu(\log N)^\xi}$ for all $N\ge N_0$ and all $z\in S_N$; the version "on $\Omega_0$" bounds $\mathbb P(\Omega_0\cap E_N(z)^c)$ instead (Definition 2.6).
--   7. **Ordered eigenvalues** (p. 10). $\lambda_1\le\dots\le\lambda_N$ are the eigenvalues of a real symmetric matrix in increasing order, counted with multiplicity.
--
--   These objects state the intermediate results (Lemmas 3.4, 3.10, 4.1, 6.1, 7.7, Proposition 7.6 and Corollary 6.7) on which the local semicircle law is built.
--
--   **Formalization Note** Indices are $0,\dots,N-1$. $G^{(\mathbb T)}_{kl}$ is extended by $0$ to $k\in\mathbb T$ or $l\in\mathbb T$; all sums exclude these indices. $Z_i$ is defined by the last expression of (3.15); it equals the paper's $Z_i=\mathbb{IE}_iZ_{ii}$ because all entries have variance $1/N$. Maxima over an empty index set are $0$. The $k$-th ordered eigenvalue is the $k$-th smallest root (with multiplicity) of the characteristic polynomial. The uniform-in-$z$ high-probability notions encode the paper's "for fixed $z$ … with high probability" statements with one threshold $N_0$ for all $z$.
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, pp. 10, 15–19, 65–66, 69, Definition 3.3, (3.9), (3.11), (3.14), (3.15), (3.24), (7.1), Definition 7.3 (7.4), (7.13), Definition 2.6

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting

noncomputable section
open ProbabilityTheory

namespace ErdosRenyiLSC.Main

/-- The minor `M^(T)` of Definition 3.3: rows and columns indexed by `T` are removed,
and the remaining indices keep their names. -/
def minor {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (T : Finset (Fin N)) :
    Matrix {i : Fin N // i ∉ T} {i : Fin N // i ∉ T} ℝ :=
  M.submatrix Subtype.val Subtype.val

/-- The resolvent `G^(T)(z) = (M^(T) - z)^{-1}` of the minor, indexed by `{i // i ∉ T}`. -/
def minorResolvent {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (T : Finset (Fin N)) (z : ℂ) :
    Matrix {i : Fin N // i ∉ T} {i : Fin N // i ∉ T} ℂ :=
  ((minor M T).map (fun x : ℝ => (x : ℂ)) -
    z • (1 : Matrix {i : Fin N // i ∉ T} {i : Fin N // i ∉ T} ℂ))⁻¹

/-- The entry `G^(T)_{kl}(z)` under the original index names `k, l`; it is set to `0`
when `k ∈ T` or `l ∈ T` (such entries never occur in the paper's formulas, whose sums
`Σ^(T)` exclude `T`). -/
def minorG {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (T : Finset (Fin N)) (z : ℂ)
    (k l : Fin N) : ℂ :=
  if h : k ∉ T ∧ l ∉ T then minorResolvent M T z ⟨k, h.1⟩ ⟨l, h.2⟩ else 0

/-- (3.14): `Z_ij = Σ^(ij)_{k,l} h_ik G^(ij)_kl h_lj`, the sum over `k, l ∉ {i, j}`. -/
def Zpair {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i j : Fin N) : ℂ :=
  ∑ k ∈ Finset.univ.filter (fun k => k ∉ ({i, j} : Finset (Fin N))),
    ∑ l ∈ Finset.univ.filter (fun l => l ∉ ({i, j} : Finset (Fin N))),
      (M i k : ℂ) * minorG M {i, j} z k l * (M l j : ℂ)

/-- The last expression of (3.15):
`Z_i = Σ^(i)_{k,l} (h_ik h_li - N^{-1} δ_kl) G^(i)_kl`. -/
def Zcent {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i : Fin N) : ℂ :=
  ∑ k ∈ Finset.univ.filter (fun k => k ≠ i),
    ∑ l ∈ Finset.univ.filter (fun l => l ≠ i),
      (((M i k * M l i : ℝ) : ℂ) - (if k = l then (1 : ℂ) / (N : ℂ) else 0)) *
        minorG M {i} z k l

/-- The average `[Z] = N^{-1} Σ_i Z_i` (p. 18 notation `[F]`). -/
def Zavg {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℂ :=
  ((1 : ℂ) / (N : ℂ)) * ∑ i, Zcent M z i

/-- (3.24): `A_i = N^{-1} Σ_j G_ij G_ji / G_ii`. -/
def Acal {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i : Fin N) : ℂ :=
  ((1 : ℂ) / (N : ℂ)) *
    ∑ j, resolvent M z i j * resolvent M z j i / resolvent M z i i

/-- `Υ_i = h_ii - Z_i + A_i` (Lemma 3.10). -/
def Upsilon {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) (i : Fin N) : ℂ :=
  (M i i : ℂ) - Zcent M z i + Acal M z i

/-- `[v] = N^{-1} Σ_i v_i` with `v_i = G_ii - m_sc` (3.9). -/
def vAvg {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℂ :=
  ((1 : ℂ) / (N : ℂ)) * ∑ i, (resolvent M z i i - msc z)

/-- `Λ = |m - m_sc|` (3.9), and `Λ̃` when applied to `A`. -/
def Lam {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℝ :=
  ‖stieltjes M z - msc z‖

/-- `Λ_d = max_i |G_ii - m_sc|` (3.9); the maximum over an empty index set is `0`. -/
def LamD {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℝ :=
  ((Finset.univ.sup fun i : Fin N => ‖resolvent M z i i - msc z‖₊ : NNReal) : ℝ)

/-- `Λ_o = max_{i ≠ j} |G_ij|` (3.9); the maximum over an empty index set is `0`. -/
def LamO {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℝ :=
  (((Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2).sup
      fun p => ‖resolvent M z p.1 p.2‖₊ : NNReal) : ℝ)

/-- Definition 7.3, (7.4), as a property of a matrix `M` (applied to `M = A`):
`sup_{z ∈ D(η)} (Λ_d(z) + Λ_o(z)) ≤ (log N)^{-ξ}` where `D(η) = {z ∈ D_L : Im z = η}`. -/
def GoodAt (Sigma : ℝ) (L : ℕ → ℝ) (xi : ℝ) {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ)
    (η : ℝ) : Prop :=
  ∀ z ∈ domDL Sigma L N, z.im = η →
    LamD M z + LamO M z ≤ Real.log (N : ℝ) ^ (-xi)

/-- The control parameter (7.13):
`Φ(z) = (log N)^ξ / q + (log N)^{2ξ} (√(Im m(z) / (Nη)) + 1/(Nη))`, with `m` the
normalized resolvent trace of `M` (applied to `M = A`, so `m = m̃`). -/
def Phi (xi q : ℝ) {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (z : ℂ) : ℝ :=
  Real.log (N : ℝ) ^ xi / q +
    Real.log (N : ℝ) ^ (2 * xi) *
      (Real.sqrt ((stieltjes M z).im / ((N : ℝ) * z.im)) + 1 / ((N : ℝ) * z.im))

/-- High probability uniformly in a spectral parameter ranging over an `N`-dependent set
(the "for fixed z ∈ D_L" statements, uniform in z): for `N ≥ N₀` and every `z ∈ S N`,
`P((E N z)ᶜ) ≤ exp(-ν (log N)^ξ)`. -/
def HighProbUnif {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (ξ : ℕ → ℝ) (ν : ℝ) (S : ℕ → Set ℂ) (E : ℕ → ℂ → Set Ω) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ z ∈ S N,
    P (E N z)ᶜ ≤ ENNReal.ofReal (Real.exp (-ν * Real.log (N : ℝ) ^ ξ N))

/-- The "on Ω₀" form of Definition 2.6, uniformly in `z ∈ S N`:
`P(E₀ N z ∩ (E N z)ᶜ) ≤ exp(-ν (log N)^ξ)` for `N ≥ N₀`. -/
def HighProbOnUnif {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (ξ : ℕ → ℝ) (ν : ℝ) (S : ℕ → Set ℂ) (E₀ E : ℕ → ℂ → Set Ω) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ z ∈ S N,
    P (E₀ N z ∩ (E N z)ᶜ) ≤ ENNReal.ofReal (Real.exp (-ν * Real.log (N : ℝ) ^ ξ N))

/-- The eigenvalues of a real symmetric matrix in increasing order, `λ₁ ≤ ⋯ ≤ λ_N`
(p. 10), zero-based: `eigAsc M k` is the `(k+1)`-st smallest root of the characteristic
polynomial, counted with multiplicity. -/
def eigAsc {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (k : ℕ) : ℝ :=
  (M.charpoly.roots.sort (· ≤ ·)).getD k 0

end ErdosRenyiLSC.Main


