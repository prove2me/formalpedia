-- Prove2me | Definitions.Def_QDSGibbs_Op
-- name    : QDSGibbs_Op
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:32:27.455515+00:00
-- url     : https://prove2.me/theorems/ff4ae67e-5f03-4855-bd3e-1926bc324f38
-- title:
--   Configuration space, full-space operators, supports and partial traces
-- statement:
--   The system has $N$ sites $\Lambda=\{0,\dots,N-1\}$ with local Hilbert spaces $\mathcal H_i\simeq\mathbb C^{d_i}$. The **configuration space** is $\prod_{i\in\Lambda}\{0,\dots,d_i-1\}$, and an **operator** is a complex matrix indexed by configurations, i.e. an element of $\mathcal B(\mathcal H_\Lambda)$ with $\mathcal H_\Lambda=\bigotimes_i\mathcal H_i$.
--
--   An operator $A$ is **supported on** $S\subseteq\Lambda$ when $A=A_S\otimes\mathbb 1_{S^c}$: its matrix entry at $(x,y)$ vanishes unless $x$ and $y$ agree off $S$, and depends only on the restrictions $x_S,y_S$. The **re-embedded partial trace** is
--
--   $$
--   \mathrm{ptr}_S(X)=\mathbb 1_S\otimes\mathrm{Tr}_S X,\qquad \mathrm{ptr}_S(X)_{x,y}=[x_S=y_S]\sum_{z}X_{(z,x_{S^c}),(z,y_{S^c})},
--   $$
--
--   where $z$ ranges over configurations of $S$; $\mathrm{ptr}_\emptyset=\mathrm{id}$. The dimension of a region is $\dim\mathcal H_S=\prod_{i\in S}d_i$.
--
--   These objects carry the whole operator-algebraic layer of the mission: every operator "on a region" of the paper is represented on the full system, extended by the identity, as the paper itself does in full-system expressions.
--
--   **Formalization Note** Sites are 0-based (paper site $i$ is index $i-1$). "$\mathrm{Tr}_S X=0$" is $\mathrm{ptr}_S X=0$.
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), §2.1, p.10

import Mathlib

open scoped Matrix

namespace QDSGibbs

/-- The **configuration space** of a system of `N` sites with local dimensions `d i`: the basis of
`H_Λ = ⊗_{i ∈ Λ} ℂ^{d_i}`, `Λ = {0, …, N-1}` (Rouzé–Stilck França, arXiv:2610.03578, held file
sha256 ede55815…, §2.1, p.10).

**Formalization Note** Sites are 0-based: paper site `i` is index `i - 1`. -/
abbrev Cfg {N : ℕ} (d : Fin N → ℕ) : Type := (i : Fin N) → Fin (d i)

/-- Operators on the full system `B(H_Λ)` (arXiv:2610.03578, §2.1, p.10), as matrices over the
configuration space.

**Formalization Note** Every operator of the paper is represented on the full space: an operator on
a region `U` is `A ⊗ 1_{U^c}` ("Operators on U are extended by the identity on U^c whenever they
occur in a full-system expression", p.10). -/
abbrev Op {N : ℕ} (d : Fin N → ℕ) : Type := Matrix (Cfg d) (Cfg d) ℂ

/-- Configurations of the sites in a region `S`: the basis of `H_S`. -/
abbrev SubCfg {N : ℕ} (d : Fin N → ℕ) (S : Finset (Fin N)) : Type := (i : S) → Fin (d i)

/-- `glue S z x` overwrites the `S`-coordinates of the configuration `x` by `z`. -/
def glue {N : ℕ} {d : Fin N → ℕ} (S : Finset (Fin N)) (z : SubCfg d S) (x : Cfg d) : Cfg d :=
  fun i => if h : i ∈ S then z ⟨i, h⟩ else x i

/-- The restriction of a configuration to the sites of `S`. -/
def restr {N : ℕ} {d : Fin N → ℕ} (S : Finset (Fin N)) (x : Cfg d) : SubCfg d S :=
  fun i => x i

/-- `A` is **supported on** `S` (arXiv:2610.03578, §2.1, p.10, "supp A ⊆ S"): `A = A_S ⊗ 1_{S^c}`.
Entrywise: the matrix entry `A x y` vanishes unless `x` and `y` agree off `S`, and it depends only on
the restrictions of `x` and `y` to `S`. -/
def SupportedOn {N : ℕ} {d : Fin N → ℕ} (S : Finset (Fin N)) (A : Op d) : Prop :=
  (∀ x y : Cfg d, (∃ i, i ∉ S ∧ x i ≠ y i) → A x y = 0) ∧
  (∀ x y x' y' : Cfg d, (∀ i ∈ S, x i = x' i ∧ y i = y' i) → (∀ i, i ∉ S → x i = y i) →
    (∀ i, i ∉ S → x' i = y' i) → A x y = A x' y')

/-- The **re-embedded partial trace** `ptr S X = 1_S ⊗ Tr_S X` (arXiv:2610.03578, §2.1, p.10):
`(ptr S X) x y = [x_S = y_S] · Σ_z X (z, x_{S^c}) (z, y_{S^c})`.

**Formalization Note** The paper's `Tr_S X` is an operator on `H_{S^c}`; here it is tensored with
`1_S` so that it lives on the full space. "`Tr_S X = 0`" is `ptr S X = 0`, and the trace norm of
`Tr_S X` is `traceNorm (ptr S X) / dimOf d S`. `ptr ∅ X = X` (`Tr_∅ = id`). -/
def ptr {N : ℕ} {d : Fin N → ℕ} (S : Finset (Fin N)) (X : Op d) : Op d :=
  Matrix.of fun x y =>
    if (∀ i ∈ S, x i = y i) then ∑ z : SubCfg d S, X (glue S z x) (glue S z y) else 0

/-- The dimension `dim H_S = ∏_{i ∈ S} d_i` of a region. -/
def dimOf {N : ℕ} (d : Fin N → ℕ) (S : Finset (Fin N)) : ℕ := ∏ i ∈ S, d i

end QDSGibbs


