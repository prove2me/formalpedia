-- Prove2me | Definitions.Def_Z2PostSamp_Cavity
-- name    : Z2PostSamp_Cavity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:08:02.224215+00:00
-- url     : https://prove2.me/theorems/727677f4-3aa6-4789-abe1-305a3dadb107
-- title:
--   The one-site cavity quantities $Y_i$, $v_i$, $\mathcal Z_i$, $D_i$ of §3.5
-- statement:
--   Fix $k$ and a free site $i\in R_k$. Delete site $i$ and its incident interactions, retaining the fields $h^{(k)}_j(\theta_{S_k})$ for $j\in R_k\setminus\{i\}$, and let $\langle\cdot\rangle_{-i}$ be the resulting Gibbs average on $\{\pm1\}^{R_k\setminus\{i\}}$, with mean $m^{-i}$. With $N=n-k-1$ define, for $-1\le s\le1$,
--
--   $$Y_i(\sigma)=\sum_{j\in R_k\setminus\{i\}}J_{ij}(\sigma_j-m^{-i}_j),\qquad v_i=\frac{\lambda^2}n\big(N-\|m^{-i}\|^2\big),$$
--
--   $$\mathcal Z_i(s)=\langle e^{sY_i(\sigma)}\rangle_{-i},\qquad D_i(s)=\frac{\mathcal Z_i'(s)}{\mathcal Z_i(s)}-s\,v_i .$$
--
--   These quantities measure how far the cavity field of a deleted site is from Gaussian, which controls the TAP gradient residual.
--
--   **Formalization Note** The derivative $\mathcal Z_i'(s)$ is written as its value $\langle Y_ie^{sY_i}\rangle_{-i}$ (derivative of a finite sum). The cavity average is a ratio of finite sums over configurations agreeing with the prefix off $R_k\setminus\{i\}$.
-- source:
--   Z. Li, Efficient Posterior Sampling for ℤ₂ Synchronization, arXiv:2610.08199 (held version, sha256 536ad4d8…), §3.5, p.29

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_Z2PostSamp_RevealPath

set_option autoImplicit false

open OAI.CriticalSK

namespace Z2PostSamp

noncomputable section

/-!
# The one-site cavity quantities of §3.5

Z. Li, *Efficient Posterior Sampling for ℤ₂ Synchronization*, arXiv:2610.08199 (held version,
sha256 536ad4d8…), §3.5, p.29: "Fix `k` and a free site `i ∈ R_k`. Delete site `i` and all its
incident interactions, retaining the fields `h_j^{(k)}(θ_{S_k})` for `j ∈ R_k∖{i}`. Denote the
resulting Gibbs average by `⟨·⟩_{−i}`, its mean by `m^{−i}` … put `N = n − k − 1`. … Define, for
`−1 ≤ s ≤ 1`, `Y_i(σ) = Σ_{j ∈ R_k∖{i}} J_ij(σ_j − m_j^{−i})`, `v_i = (λ²/n)(N − ‖m^{−i}‖²)`,
`𝒵_i(s) = ⟨e^{sY_i(σ)}⟩_{−i}`, `D_i(s) = 𝒵_i'(s)/𝒵_i(s) − s v_i`."

**Formalization Note.** `⟨·⟩_{−i}` is the Gibbs average on `{±1}^{R_k∖{i}}` with weights
`exp{½ Σ_{j,l ∈ R_k∖{i}} J_jl σ_j σ_l + Σ_{j ∈ R_k∖{i}} h_j^{(k)}(x_{S_k}) σ_j}` (the law (2.4) with
site `i` deleted); it is a sum over the configurations agreeing with `x` off `R_k∖{i}`. The derivative
`𝒵_i'(s)` is written as its value `⟨Y_i e^{sY_i}⟩_{−i}` (differentiation of a finite sum).
-/

/-- The cavity free set `R_k ∖ {i}`. -/
def cavSet {n : ℕ} (I : Equiv.Perm (Fin n)) (k : ℕ) (i : Fin n) : Finset (Fin n) :=
  (Rset I k).erase i

/-- The configurations agreeing with `x` off `R_k ∖ {i}`. -/
def cavCompletions {n : ℕ} (I : Equiv.Perm (Fin n)) (x : Spin n) (k : ℕ) (i : Fin n) :
    Finset (Spin n) :=
  Finset.univ.filter fun y => ∀ j, j ∉ cavSet I k i → y j = x j

/-- The cavity Gibbs weight of a configuration `y`. -/
def cavW {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n)) (x : Spin n) (k : ℕ)
    (i : Fin n) (y : Spin n) : ℝ :=
  Real.exp ((1 / 2 : ℝ) * (∑ j ∈ cavSet I k i, ∑ l ∈ cavSet I k i,
      J j l * spinValue (y j) * spinValue (y l)) +
    ∑ j ∈ cavSet I k i, field J I x k j * spinValue (y j))

/-- The cavity Gibbs average `⟨g⟩_{−i}`. -/
def cavAvg {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n)) (x : Spin n) (k : ℕ)
    (i : Fin n) (g : Spin n → ℝ) : ℝ :=
  (∑ y ∈ cavCompletions I x k i, cavW J I x k i y * g y) /
    ∑ y ∈ cavCompletions I x k i, cavW J I x k i y

/-- The cavity mean `m_j^{−i} = ⟨σ_j⟩_{−i}`. -/
def cavMean {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n)) (x : Spin n) (k : ℕ)
    (i j : Fin n) : ℝ :=
  cavAvg J I x k i fun y => spinValue (y j)

/-- `Y_i(σ) = Σ_{j ∈ R_k∖{i}} J_ij (σ_j − m_j^{−i})`. -/
def cavY {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n)) (x : Spin n) (k : ℕ)
    (i : Fin n) (y : Spin n) : ℝ :=
  ∑ j ∈ cavSet I k i, J i j * (spinValue (y j) - cavMean J I x k i j)

/-- `v_i = (λ²/n)(N − ‖m^{−i}‖²)`, `N = n − k − 1`. -/
def cavV {n : ℕ} (lam : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n)) (x : Spin n)
    (k : ℕ) (i : Fin n) : ℝ :=
  lam ^ 2 / n * (((n : ℝ) - k - 1) - ∑ j ∈ cavSet I k i, cavMean J I x k i j ^ 2)

/-- `D_i(s) = 𝒵_i'(s)/𝒵_i(s) − s v_i` with `𝒵_i(s) = ⟨e^{sY_i}⟩_{−i}`, `𝒵_i'(s) = ⟨Y_i e^{sY_i}⟩_{−i}`. -/
def cavD {n : ℕ} (lam : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (I : Equiv.Perm (Fin n)) (x : Spin n)
    (k : ℕ) (i : Fin n) (s : ℝ) : ℝ :=
  cavAvg J I x k i (fun y => cavY J I x k i y * Real.exp (s * cavY J I x k i y)) /
      cavAvg J I x k i (fun y => Real.exp (s * cavY J I x k i y))
    - s * cavV lam J I x k i

end

end Z2PostSamp


