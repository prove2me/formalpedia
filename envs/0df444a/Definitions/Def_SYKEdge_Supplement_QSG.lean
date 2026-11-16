-- Prove2me | Definitions.Def_SYKEdge_Supplement_QSG
-- name    : SYKEdge_Supplement_QSG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:21:52.122139+00:00
-- url     : https://prove2.me/theorems/750464d1-c085-424e-9890-264ea61f5d69
-- title:
--   The $k$-local quantum spin glass Hamiltonian $H_{k-\mathrm{QSG}}$
-- statement:
--   Let $\mathrm{Id}_2, X, Y, Z$ be the single-qubit Pauli matrices. For $P=\bigotimes_{i=1}^n P_i\in\{\mathrm{Id},X,Y,Z\}^{\otimes n}$ let $\mathrm{wt}(P)$ be the number of $i$ with $P_i\ne\mathrm{Id}$, and let $\mathcal P_{n,k}$ be the set of Pauli strings of weight exactly $k$; $|\mathcal P_{n,k}|=3^k\binom nk$. The **$k$-local quantum spin glass Hamiltonian** is the $2^n\times 2^n$ random matrix
--   $$H_{k-\mathrm{QSG}}:=\frac1{\sqrt m}\sum_{P\in\mathcal P_{n,k}} g_P\,P,\qquad m:=3^k\binom nk,$$
--   where $(g_P)_{P\in\mathcal P_{n,k}}$ are i.i.d. $N(0,1)$ disorder variables.
--
--   It is the qubit analogue of the SYK model, and Theorem 6.1 bounds its expected operator norm.
--
--   **Formalization Note** $\mathcal P_{n,k}$ and the matrices of Pauli strings are the published `QPSpinProfile.PauliString n k` and `QPSpinProfile.PauliString.mat` (words in $\{I,X,Y,Z\}^n$ with exactly $k$ non-identity letters, acting on $(\mathbb C^2)^{\otimes n}$). The disorder is a point $g\in\mathbb R^{\mathcal P_{n,k}}$; its law is the published `SYKEdge.stdGauss`.
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, §1, p.5 (PDF p.5); recalled in §6, p.42

import Mathlib
import Definitions.Def_QPSpinProfile_PauliString

namespace SYKEdge.Supplement

open QPSpinProfile

/-!
# The `k`-local quantum spin glass Hamiltonian

A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, §1, p.5 (PDF p.5), recalled in §6, p.42.

For `P ∈ {Id, X, Y, Z}^{⊗n}`, `wt(P)` is the number of tensor factors different from `Id`, and
`𝒫_{n,k}` is the set of Pauli strings of weight exactly `k`, `|𝒫_{n,k}| = 3^k (n choose k)`. The
`k`-local quantum spin glass Hamiltonian is
`H_{k−QSG} := m^{−1/2} Σ_{P ∈ 𝒫_{n,k}} g_P P` with `m := 3^k (n choose k)` and `(g_P)` i.i.d. `N(0,1)`.

**Formalization Note.**
* `𝒫_{n,k}` and the matrices of Pauli strings are the published `QPSpinProfile.PauliString n k`
  (words `Fin n → Fin 4` with exactly `k` non-identity letters) and `QPSpinProfile.PauliString.mat`,
  acting on `(ℂ²)^{⊗n}` with basis `QPSpinProfile.Qubits n = Fin n → Fin 2`.
* The disorder `g : PauliString n k → ℝ` is a point of `ℝ^{𝒫_{n,k}}`; its law is `SYKEdge.stdGauss`.
* The normalization is the page's `m = 3^k (n choose k)`, written as that number.
-/

/-- The `k`-local quantum spin glass Hamiltonian
`H_{k−QSG}(g) := (3^k (n choose k))^{−1/2} Σ_{P ∈ 𝒫_{n,k}} g_P P` on `n` qubits (p.5). -/
noncomputable def qsg (n k : ℕ) (g : PauliString n k → ℝ) : Matrix (Qubits n) (Qubits n) ℂ :=
  (((1 / Real.sqrt ((3 : ℝ) ^ k * (n.choose k : ℝ)) : ℝ)) : ℂ) •
    ∑ P : PauliString n k, ((g P : ℝ) : ℂ) • P.mat

end SYKEdge.Supplement


