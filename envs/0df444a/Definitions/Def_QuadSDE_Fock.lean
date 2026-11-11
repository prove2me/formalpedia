-- Prove2me | Definitions.Def_QuadSDE_Fock
-- name    : QuadSDE_Fock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:11.271195+00:00
-- url     : https://prove2.me/theorems/cc171aa6-dc9f-42c7-947b-d26d833818e6
-- title:
--   Bosonic Fock space, ladder operators, $C_0$ and degree projections
-- statement:
--   The **Fock space** of $N$ harmonic oscillators is
--   $$\mathcal F=\Big\{\psi:\mathbb Z_{\ge0}^N\to\mathbb C:\ \sum_{\mathbf m}|\psi_{\mathbf m}|^2<\infty\Big\},$$
--   with occupation basis $|\mathbf m\rangle$ and total degree $|\mathbf m|=\sum_im_i$. The ladder and number operators are
--   $$a_i|\mathbf m\rangle=\sqrt{m_i}\,|\mathbf m-e_i\rangle,\qquad a_i^\dagger|\mathbf m\rangle=\sqrt{m_i+1}\,|\mathbf m+e_i\rangle,\qquad M=\sum_ia_i^\dagger a_i,$$
--   with $a_i|\mathbf m\rangle=0$ when $m_i=0$, and the drift operator is
--   $$C_0=\sum_{i,j,k}c_{ijk}\big(a_i^\dagger a_ja_k-a_k^\dagger a_j^\dagger a_i\big)\qquad(32).$$
--   $Q_n$ projects onto total degree $n$, and $\Pi_k=\sum_{n=1}^kQ_n$ projects onto $\mathcal H_k=\mathrm{span}\{|\mathbf m\rangle:1\le|\mathbf m|\le k\}$ (35). The module also provides $\|Q_nv\|^2$, the inner product $\langle u,v\rangle=\sum_{\mathbf m}\overline{u_{\mathbf m}}v_{\mathbf m}$ and the vacuum $|0,\dots,0\rangle$.
--
--   **Formalization Note** $\mathcal F$ is Mathlib's $\ell^2$ space `lp (fun _ => ℂ) 2` over multi-indices `Fin N → ℕ`. The ladder operators are the published `GaussTesting.lower` ($a_i$) and `GaussTesting.raise` ($a_i^\dagger$), acting coefficientwise on all functions $\mathbb Z_{\ge0}^N\to\mathbb C$: $(a_iv)_{\mathbf m}=\sqrt{m_i+1}\,v_{\mathbf m+e_i}$ and $(a_i^\dagger v)_{\mathbf m}=\sqrt{m_i}\,v_{\mathbf m-e_i}$; each output coefficient is a finite expression, and $C_0$, $M$, $Q_n$, $\Pi_k$ act the same way. $\|Q_nv\|^2$ is a finite sum. The inner product is used only with a finitely supported first argument.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.2, Eq. (32), p. 19; Eq. (35), p. 20

import Mathlib
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_GaussTesting_quadrature

noncomputable section

namespace QuadSDE

/-- Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §4.2, p. 19: a
multi-index `m ∈ ℤ_{≥0}^N`, the label of the occupation basis vector `|m⟩` (and of the Hermite
polynomial `H_m`). -/
abbrev MIdx (N : ℕ) := Fin N → ℕ

/-- p. 17: the total degree `|m| = Σ_i m_i`. -/
def mdeg {N : ℕ} (m : MIdx N) : ℕ := ∑ i, m i

/-- §4.2, p. 19: the bosonic Fock space of `N` harmonic oscillators,
`𝓕 = {ψ : ℤ_{≥0}^N → ℂ : Σ_m |ψ_m|² < ∞}`, as Mathlib's `ℓ²` space. -/
abbrev Fock (N : ℕ) := lp (fun _ : MIdx N => ℂ) 2

/-- p. 19: the number operator `M = Σ_i a_i† a_i`, which multiplies `|m⟩` by `|m|`. -/
def numOp {N : ℕ} (v : MIdx N → ℂ) : MIdx N → ℂ := fun m => (mdeg m : ℂ) * v m

/-- Eq. (32), p. 19: `C₀ = Σ_{i,j,k} c_{ijk} (a_i† a_j a_k − a_k† a_j† a_i)`, where (p. 19)
`a_i |m⟩ = √m_i |m − e_i⟩` and `a_i† |m⟩ = √(m_i + 1) |m + e_i⟩`, with `a_i |m⟩ = 0` when `m_i = 0`.

**Formalization Note.** The ladder operators are the published `GaussTesting.lower` (`a_i`,
`(a_i v)_m = √(m_i + 1) v_{m + e_i}`) and `GaussTesting.raise` (`a_i†`, `(a_i† v)_m = √m_i v_{m − e_i}`),
which act coefficientwise on all functions `ℤ_{≥0}^N → ℂ`: every output coefficient is a finite
expression. `C₀`, the number operator and the projections below act the same way; they are applied
to finite Hermite vectors and to `ℓ²` vectors where the paper does. -/
def C0 {N : ℕ} (c : Coeff N) (v : MIdx N → ℂ) : MIdx N → ℂ :=
  fun m => ∑ i, ∑ j, ∑ k,
    (c i j k : ℂ) * (GaussTesting.raise i (GaussTesting.lower j (GaussTesting.lower k v)) m -
      GaussTesting.raise k (GaussTesting.raise j (GaussTesting.lower i v)) m)

/-- p. 19: `Q_n`, the projection onto total degree `n`. -/
def Qdeg {N : ℕ} (n : ℕ) (v : MIdx N → ℂ) : MIdx N → ℂ :=
  fun m => if mdeg m = n then v m else 0

/-- Eq. (35), p. 20: `Π_k = Σ_{n=1}^k Q_n`, the projection onto
`𝓗_k = span{|m⟩ : 1 ≤ |m| ≤ k}`. -/
def Pik {N : ℕ} (k : ℕ) (v : MIdx N → ℂ) : MIdx N → ℂ :=
  fun m => if 1 ≤ mdeg m ∧ mdeg m ≤ k then v m else 0

/-- `‖Q_n v‖²`, the squared norm of the degree-`n` part of `v`.

**Formalization Note.** There are finitely many `m` with `|m| = n`, so the sum is a finite sum. -/
def degNormSq {N : ℕ} (n : ℕ) (v : MIdx N → ℂ) : ℝ :=
  ∑' m : MIdx N, if mdeg m = n then ‖v m‖ ^ 2 else 0

/-- The inner product `⟨u, v⟩ = Σ_m conj(u_m) v_m` (antilinear in `u`).

**Formalization Note.** Used only when `u` has finite support (a finite Hermite vector), so that
the sum is finite. -/
def fockInner {N : ℕ} (u v : MIdx N → ℂ) : ℂ := ∑' m : MIdx N, star (u m) * v m

/-- The vacuum `|0, …, 0⟩`. -/
def vacuum (N : ℕ) : MIdx N → ℂ := fun m => if m = 0 then 1 else 0

end QuadSDE


