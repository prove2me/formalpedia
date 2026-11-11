-- Prove2me | Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction
-- name    : MomentPolytopes_QuantumFunctionals_TensorAction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:02:34.455884+00:00
-- url     : https://prove2.me/theorems/344707f7-a551-4e9f-95de-6df3667828ba
-- title:
--   Tensor tuples, the tensor action of GL(n₁)×⋯×GL(n_d), partial traces and the moment map µ (one-body quantum marginals)
-- statement:
--   Fix $d$, $n_0$ and $n_1,\dots,n_d$. A **tensor tuple** is an element $T$ of $\mathrm{Ten}(n_0;n_1,\dots,n_d)=\mathbb C^{n_0}\otimes\mathbb C^{n_1}\otimes\dots\otimes\mathbb C^{n_d}$, i.e. a complex array $T_{i_0,i_1,\dots,i_d}$; equivalently an $n_0$-tuple $(t_1,\dots,t_{n_0})$ of tensors $t_i\in\mathbb C^{n_1}\otimes\dots\otimes\mathbb C^{n_d}$. It carries the standard inner product $\langle S,T\rangle=\sum\overline{S_x}T_x$ and norm $\|T\|=\langle T,T\rangle^{1/2}$.
--
--   The group $G=\mathrm{GL}(n_1)\times\dots\times\mathrm{GL}(n_d)$ acts by the **tensor action**
--   $$(g_1,\dots,g_d)\cdot T=(I\otimes g_1\otimes\dots\otimes g_d)\,T ,$$
--   and the same formula defines $(I\otimes A_1\otimes\dots\otimes A_d)T$ for any matrix tuple; $K=\mathrm U(n_1)\times\dots\times\mathrm U(n_d)$ acts by restriction.
--
--   For $T\ne0$ let $\rho=\sum_{i\in[n_0]}t_it_i^\dagger/\|T\|^2$ on $\mathbb C^{n_1}\otimes\dots\otimes\mathbb C^{n_d}$. For an operator $M$ on that space and $\ell\in[d]$, the **partial trace** over all factors but the $\ell$-th is
--   $$(\operatorname{tr}_{\check\ell}M)_{a,b}=\sum_{i_k,\,k\ne\ell}M_{(\dots,i_{\ell-1},a,i_{\ell+1},\dots),(\dots,i_{\ell-1},b,i_{\ell+1},\dots)} .$$
--   The **moment map** is $\mu(T)=(\rho_1,\dots,\rho_d)$ with $\rho_\ell=\operatorname{tr}_{\check\ell}\rho=T^{(\ell)}T^{(\ell)\dagger}/\|T\|^2$, the normalized one-body quantum marginals; each $\rho_\ell$ is positive semidefinite with trace one. $T$ is **concise** if every $\rho_\ell$ is nonsingular.
--
--   **Formalization Note** Modes are indexed by `Fin d` and entries of mode $\ell$ by `Fin (n ℓ)` (0-based). A tensor tuple is a function on `Fin n0 × ((ℓ : Fin d) → Fin (n ℓ))`. $\mu$ is defined through $\rho$ and the partial trace (6.30)–(6.31); it is applied only to $T\ne0$ (at $T=0$ it is the junk value $0$).
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), pp. 43–44, Definition 6.26 and eqs. (6.28)–(6.31); p. 54 (conciseness)

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra

set_option autoImplicit false

namespace MomentPolytopes.QuantumFunctionals

/-- Multi-indices `(i_1, …, i_d)` of `ℂ^{n_1} ⊗ ⋯ ⊗ ℂ^{n_d}`; the tensor modes are indexed by
`Fin d` (0-based) and the entries of mode `ℓ` by `Fin (n ℓ)`. -/
abbrev MIdx {d : ℕ} (n : Fin d → ℕ) : Type := (ℓ : Fin d) → Fin (n ℓ)

/-- Tensor tuples `Ten(n_0; n_1, …, n_d) = ℂ^{n_0} ⊗ ℂ^{n_1} ⊗ ⋯ ⊗ ℂ^{n_d}`
(§6.4, p. 43), as functions of `(i_0, (i_1, …, i_d))`. -/
abbrev Ten (d n0 : ℕ) (n : Fin d → ℕ) : Type := Fin n0 × MIdx n → ℂ

/-- Tuples `(X_1, …, X_d)` of square complex matrices, `X_ℓ ∈ ℂ^{n_ℓ × n_ℓ}`. -/
abbrev MatTuple {d : ℕ} (n : Fin d → ℕ) : Type := (ℓ : Fin d) → Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ

/-- The group `G = GL(n_1) × ⋯ × GL(n_d)` (Example 2.1, p. 15). -/
abbrev GTuple {d : ℕ} (n : Fin d → ℕ) : Type :=
  (ℓ : Fin d) → Matrix.GeneralLinearGroup (Fin (n ℓ)) ℂ

/-- Its maximal compact subgroup `K = U(n_1) × ⋯ × U(n_d)` (Example 2.1, p. 15). -/
abbrev UTuple {d : ℕ} (n : Fin d → ℕ) : Type :=
  (ℓ : Fin d) → Matrix.unitaryGroup (Fin (n ℓ)) ℂ

variable {d n0 : ℕ} {n : Fin d → ℕ}

/-- Standard (Hilbert–Schmidt) norm `‖T‖ = (∑ |T_{i_0 i_1 ⋯ i_d}|²)^{1/2}` of a tensor tuple. -/
noncomputable def tnorm (T : Ten d n0 n) : ℝ :=
  Real.sqrt (∑ x, ‖T x‖ ^ 2)

/-- Standard inner product `⟨S, T⟩ = ∑ conj(S_x) T_x`, antilinear in the first argument. -/
def tinner (S T : Ten d n0 n) : ℂ :=
  ∑ x, star (S x) * T x

/-- The Kronecker product `A_1 ⊗ ⋯ ⊗ A_d` as a matrix indexed by multi-indices. -/
def kron (A : MatTuple n) : Matrix (MIdx n) (MIdx n) ℂ :=
  fun j j' => ∏ ℓ, A ℓ (j ℓ) (j' ℓ)

/-- `(I ⊗ A_1 ⊗ ⋯ ⊗ A_d) T` for any matrix tuple `A` (eq. (6.28), p. 43). -/
def act (A : MatTuple n) (T : Ten d n0 n) : Ten d n0 n :=
  fun x => ∑ j', kron A x.2 j' * T (x.1, j')

/-- The tensor action `(g_1, …, g_d) · T := (I ⊗ g_1 ⊗ ⋯ ⊗ g_d) T` of `GL(n_1) × ⋯ × GL(n_d)`
(Definition 6.26, eq. (6.28), p. 43). -/
def gact (g : GTuple n) (T : Ten d n0 n) : Ten d n0 n :=
  act (fun ℓ => ((g ℓ : Matrix.GeneralLinearGroup (Fin (n ℓ)) ℂ) : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ)) T

/-- The restriction of the tensor action to `K = U(n_1) × ⋯ × U(n_d)`. -/
def uact (u : UTuple n) (T : Ten d n0 n) : Ten d n0 n :=
  act (fun ℓ => ((u ℓ : Matrix.unitaryGroup (Fin (n ℓ)) ℂ) : Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ)) T

/-- The density operator `ρ = ∑_{i ∈ [n_0]} t_i t_i† / ‖T‖²` on `ℂ^{n_1} ⊗ ⋯ ⊗ ℂ^{n_d}`
(p. 43). -/
noncomputable def densityOp (T : Ten d n0 n) : Matrix (MIdx n) (MIdx n) ℂ :=
  fun j j' => (∑ i, T (i, j) * star (T (i, j'))) / ((tnorm T ^ 2 : ℝ) : ℂ)

/-- The partial trace `tr_ℓ̌` over all tensor factors but the `ℓ`-th, defined for every operator
`M` (eq. (6.31), p. 43):
`(tr_ℓ̌ M)_{a,b} = ∑_{i_k, k ≠ ℓ} M_{(…,i_{ℓ-1},a,i_{ℓ+1},…),(…,i_{ℓ-1},b,i_{ℓ+1},…)}`. -/
def partialTrace (ℓ : Fin d) (M : Matrix (MIdx n) (MIdx n) ℂ) :
    Matrix (Fin (n ℓ)) (Fin (n ℓ)) ℂ :=
  fun a b => ∑ j : MIdx n, if j ℓ = a then M j (Function.update j ℓ b) else 0

/-- The moment map of the tensor action: the normalized one-body quantum marginals
`µ(T) = (ρ_1, …, ρ_d)`, `ρ_ℓ = tr_ℓ̌ ρ = T^{(ℓ)} T^{(ℓ)†} / ‖T‖²` (eqs. (6.29)–(6.30), p. 43).
Used only for `T ≠ 0`. -/
noncomputable def momentMap (T : Ten d n0 n) : MatTuple n :=
  fun ℓ => partialTrace ℓ (densityOp T)

/-- `T` is **concise**: every component `µ(T)_ℓ` of the moment map is nonsingular (p. 54). -/
def IsConcise (T : Ten d n0 n) : Prop :=
  ∀ ℓ, (momentMap T ℓ).det ≠ 0

end MomentPolytopes.QuantumFunctionals


