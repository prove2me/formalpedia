-- Prove2me | Definitions.Def_UnitalMIP_Supplement_nnorm4
-- name    : UnitalMIP_Supplement_nnorm4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:15:32.07593+00:00
-- url     : https://prove2.me/theorems/1810781f-87d7-4214-b25b-ba8d4a63b19d
-- title:
--   Normalized Schatten 4-norm $\|X\|_4=\tau_d((X^\dagger X)^2)^{1/4}$ and $M_{d_0}$-valued Pauli coefficients on $M_{d_0}\otimes M_2^{\otimes n}$
-- statement:
--   For $X\in M_d$ let $|X|=(X^\dagger X)^{1/2}$ and let $\tau_d=\frac1d\mathrm{Tr}$ be the normalized trace. The **normalized Schatten 4-norm** is
--
--   $$
--   \|X\|_4:=\tau_d(|X|^4)^{1/4}=\tau_d\bigl((X^\dagger X)^2\bigr)^{1/4}.
--   $$
--
--   On $M_{d_0}\otimes M_2^{\otimes n}$ the trace is $\tau_{d_0}\otimes\tau_{2^n}$, i.e. the trace divided by $d_0 2^n$.
--
--   For $F\in M_{d_0}\otimes M_2^{\otimes n}$ write $F_{ij}\in M_2^{\otimes n}$ for its blocks, so that $F=\sum_{i,j}|i\rangle\langle j|\otimes F_{ij}$. The **$M_{d_0}$-valued Pauli coefficient** of $F$ at a Pauli label $\alpha\in G^n$ is
--
--   $$
--   \widehat F(\alpha):=(\mathrm{id}\otimes\tau_{2^n})\bigl((\mathbb 1\otimes P_\alpha^\dagger)F\bigr)\in M_{d_0},\qquad \widehat F(\alpha)_{ij}=\tau_{2^n}(P_\alpha^\dagger F_{ij}),
--   $$
--
--   so that $F=\sum_{\alpha}\widehat F(\alpha)\otimes P_\alpha$. The operator $F$ has **Pauli degree at most $k$ in the qubit factor** (it lies in the subspace $E_{\le k}$) when $\widehat F(\alpha)=0$ for every $\alpha$ of weight $|\alpha|>k$; no condition is placed on the $M_{d_0}$ factor.
--
--   These objects state the Hermitian low-degree approximation theorem (Theorem 4.11), which is the analytic core of the positive low-degree approximation of smoothed strategies.
--
--   **Formalization Note** The 4-norm is the real $1/4$-th power of the real part of the published normalized trace `UnitalMIP.ntr` of $(X^\dagger X)^2$, a nonnegative real number. $M_{d_0}\otimes M_2^{\otimes n}$ is indexed by `d0 × (Fin n → Fin 2)`; the qubit factor uses the basis of the published `UnitalMIP.pauliString`, and the scalar coefficient of each block is the published `UnitalMIP.pauliCoeff`.
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), (7), p.11; Definitions 2.7–2.8, p.12; Definition 4.17, p.45; Remark 4.19, p.48

import Mathlib
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals
import Definitions.Def_UnitalMIP_pauliString

open scoped Matrix

namespace UnitalMIP

namespace Supplement

/-- The **normalized Schatten 4-norm** `‖X‖₄ := τ_d(|X|⁴)^{1/4}`, `|X| = (X†X)^{1/2}`
(Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*,
arXiv:2609.39318, version of 2026-11-03, sha256 56ebc59e…, (7), p.11). Since `|X|⁴ = (X†X)²`,
`‖X‖₄ = τ_d((X†X)²)^{1/4}`.

**Formalization Note** `τ_d` is the published normalized trace `UnitalMIP.ntr` (trace divided by
the cardinality of the index type). `τ_d((X†X)²)` is a nonnegative real number; the definition takes
the real `1/4`-th power of its real part. On `M_{d₀} ⊗ M_{2ⁿ}`, indexed by
`Fin d₀ × (Fin n → Fin 2)`, the trace is `τ_{d₀} ⊗ τ_{2ⁿ}` (Remark 4.19, p.48), as the paper
normalizes. -/
noncomputable def nnorm4 {d : Type} [Fintype d] (X : Matrix d d ℂ) : ℝ :=
  (ntr ((Xᴴ * X) * (Xᴴ * X))).re ^ ((1 : ℝ) / 4)

/-- The `(i, j)` block `F_{ij} ∈ M_2^{⊗n}` of an operator `F ∈ M_{d₀} ⊗ M_2^{⊗n}`:
`(F_{ij})_{x y} = F_{(i,x),(j,y)}`, so that `F = ∑_{i,j} |i⟩⟨j| ⊗ F_{ij}`. -/
def qubitBlock {d0 : Type} {n : ℕ} (F : Matrix (d0 × (Fin n → Fin 2)) (d0 × (Fin n → Fin 2)) ℂ)
    (i j : d0) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun x y => F (i, x) (j, y)

/-- The `M_{d₀}`-valued **Pauli coefficient** `F̂(α) = (id ⊗ τ_{2ⁿ})((1 ⊗ P_α†) F) ∈ M_{d₀}` of
`F ∈ M_{d₀} ⊗ M_2^{⊗n}` (arXiv:2609.39318, Definitions 2.7–2.8, p.12, with `V = M_{d₀}`):
its `(i, j)` entry is the scalar Pauli coefficient `UnitalMIP.pauliCoeff` of the block `F_{ij}`.
Then `F = ∑_{α ∈ Gⁿ} F̂(α) ⊗ P_α`. -/
noncomputable def blockPauliCoeff {d0 : Type} {n : ℕ}
    (F : Matrix (d0 × (Fin n → Fin 2)) (d0 × (Fin n → Fin 2)) ℂ) (α : Fin n → Fin 2 × Fin 2) :
    Matrix d0 d0 ℂ :=
  Matrix.of fun i j => pauliCoeff (qubitBlock F i j) α

/-- `F ∈ M_{d₀} ⊗ M_2^{⊗n}` has **Pauli degree at most `k` in the qubit factor**
(arXiv:2609.39318, Definition 4.17, p.45, the subspace `E_{≤k}`): `F̂(α) = 0` whenever `|α| > k`,
i.e. `F = ∑_{|α| ≤ k} F̂(α) ⊗ P_α` with `F̂(α) ∈ M_{d₀}`. No condition is placed on the `M_{d₀}`
factor. -/
def HasQubitDegreeLE {d0 : Type} {n : ℕ}
    (F : Matrix (d0 × (Fin n → Fin 2)) (d0 × (Fin n → Fin 2)) ℂ) (k : ℕ) : Prop :=
  ∀ α : Fin n → Fin 2 × Fin 2, k < weight α → blockPauliCoeff F α = 0

end Supplement

end UnitalMIP


