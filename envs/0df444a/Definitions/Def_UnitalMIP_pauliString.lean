-- Prove2me | Definitions.Def_UnitalMIP_pauliString
-- name    : UnitalMIP_pauliString
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:38:30.979754+00:00
-- url     : https://prove2.me/theorems/12d34446-6d5b-4a7f-b54a-6e8998bde199
-- title:
--   Pauli matrices, Pauli strings, weight, Pauli coefficients and Pauli degree
-- statement:
--   The one-qubit Pauli labels form $G=\mathbb F_2^2$, and $P_{(a,b)}=i^{ab}X^aZ^b$, so $P_{(0,0)}=\mathbb 1$, $P_{(1,0)}=X$, $P_{(0,1)}=Z$, $P_{(1,1)}=Y$. For $\alpha\in G^n$ the **Pauli string** is $P_\alpha=P_{\alpha_1}\otimes\cdots\otimes P_{\alpha_n}$, its **weight** is $|\alpha|=|\{i:\alpha_i\neq0\}|$, and every operator $F$ on $n$ qubits has the expansion
--
--   $$
--   F=\sum_{\alpha\in G^n}\hat F(\alpha)P_\alpha,\qquad \hat F(\alpha)=\tau_{2^n}(P_\alpha^\dagger F).
--   $$
--
--   $F$ has **Pauli degree at most $k$** when $\hat F(\alpha)=0$ for all $|\alpha|>k$. The module also defines the tensor power $U^{\otimes n}$ of a one-qubit operator.
--
--   Pauli analysis is the language of the smoothing, low-degree approximation and dimension-reduction steps.
--
--   **Formalization Note** Labels are `Fin 2 × Fin 2`; the basis of $(\mathbb C^2)^{\otimes n}$ is indexed by `Fin n → Fin 2`. Degree is stated as the vanishing of high-weight coefficients, which covers $\deg(0)=-\infty$.
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Definitions 2.3–2.5, 2.7, 2.8, pp.12; (12), p.14

import Mathlib
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals

open scoped Matrix

namespace UnitalMIP

/-- The **Pauli matrices** `P_{(a,b)} := i^{ab} X^a Z^b` for `(a, b) ∈ G = 𝔽₂²`
(arXiv:2609.39318, version of 2026-11-03, sha256 56ebc59e…, Definitions 2.3–2.4, p.12), with
`X = [[0,1],[1,0]]`, `Z = [[1,0],[0,−1]]`; thus `P_{(0,0)} = 𝟙`, `P_{(1,0)} = X`, `P_{(0,1)} = Z`,
`P_{(1,1)} = Y = [[0,−i],[i,0]]`.

**Formalization Note** A label is a pair in `Fin 2 × Fin 2` (componentwise addition modulo 2 is
the addition of `Fin 2`); qubit indices are `Fin 2` (`0 = |0⟩`, `1 = |1⟩`). -/
noncomputable def pauli (s : Fin 2 × Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Complex.I ^ (s.1.val * s.2.val)) •
    ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) ^ s.1.val *
      (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) ^ s.2.val)

/-- The **Pauli string** `P_α := P_{α_1} ⊗ ⋯ ⊗ P_{α_n}` of a label `α ∈ Gⁿ` (arXiv:2609.39318,
Definition 2.5, p.12), as an operator on `(ℂ²)^{⊗n}` with basis indexed by `Fin n → Fin 2`. -/
noncomputable def pauliString {n : ℕ} (α : Fin n → Fin 2 × Fin 2) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun x y => ∏ i, pauli (α i) (x i) (y i)

/-- The **Pauli weight** `|α| := |supp(α)|`, `supp(α) = {i : α_i ≠ 0}` (arXiv:2609.39318,
Definition 2.5, p.12). -/
def weight {n : ℕ} (α : Fin n → Fin 2 × Fin 2) : ℕ :=
  (Finset.univ.filter fun i => α i ≠ 0).card

/-- The **Pauli coefficient** `F̂(α) = ⟨P_α, F⟩₂ = τ_{2^n}(P_α† F)` of an operator `F` on `n` qubits
(arXiv:2609.39318, version of 2026-11-03, Definitions 2.7–2.8, p.12, and (12), p.14, the case
`V = ℂ`). -/
noncomputable def pauliCoeff {n : ℕ} (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (α : Fin n → Fin 2 × Fin 2) : ℂ :=
  ntr ((pauliString α)ᴴ * F)

/-- `F` has **Pauli degree at most `k`** (arXiv:2609.39318, version of 2026-11-03, Definition 2.8,
p.12): every Pauli coefficient `F̂(α)` with `|α| > k` vanishes, i.e.
`deg(F) = max_{α ∈ supp_P(F)} |α| ≤ k` (with `deg(0) = −∞`). -/
def HasPauliDegreeLE {n : ℕ} (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (k : ℕ) : Prop :=
  ∀ α : Fin n → Fin 2 × Fin 2, k < weight α → pauliCoeff F α = 0

/-- The tensor power `U^{⊗n}` of a single-qubit operator `U`, on `(ℂ²)^{⊗n}`
(arXiv:2609.39318, Proposition 2.28 item 4, p.20). -/
def kronPow {n : ℕ} (U : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  Matrix.of fun x y => ∏ i, U (x i) (y i)

end UnitalMIP


