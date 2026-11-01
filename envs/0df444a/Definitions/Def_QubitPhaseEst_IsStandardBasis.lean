-- Prove2me | Definitions.Def_QubitPhaseEst_IsStandardBasis
-- name    : QubitPhaseEst_IsStandardBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:18:40.036403+00:00
-- url     : https://prove2.me/theorems/f2d9e5f4-9f1e-4819-8c3b-fb3465ead520
-- title:
--   Standard angular-momentum basis $|j,m,\alpha\rangle_z$ of $N$ qubits
-- statement:
--   Let $J_z=\tfrac12\sum_k\sigma_z^{(k)}$ and $J_+=\sum_k\sigma_+^{(k)}$ on $N$ qubits, with $\sigma_+=|0\rangle\langle1|$. A family of vectors $|j,m,\alpha\rangle$, indexed by the labels $(j,m,\alpha)$ with multiplicities $d_j$, is a **standard angular-momentum basis** when
--
--   1. the vectors are orthonormal (there are $2^N$ of them, so they form a basis);
--   2. $J_z|j,m,\alpha\rangle=m\,|j,m,\alpha\rangle$;
--   3. $J_+|j,m,\alpha\rangle=\sqrt{j(j+1)-m(m+1)}\,|j,m+1,\alpha\rangle$ for $m<j$, with the same $\alpha$;
--   4. $J_+|j,j,\alpha\rangle=0$.
--
--   Each $(j,\alpha)$ then spans an irreducible spin-$j$ subspace, and the vectors are the paper's $|m,j\alpha\rangle=|j,m,\alpha\rangle_z$. The paper fixes them only up to "a suitable set of unitary operators" $U_{j,\alpha}$; every family with these properties is admitted.
--
--   The module also defines the matrix element $\langle u|A|v\rangle=u^\dagger A v$.
--
--   **Formalization Note** $m$ is the eigenvalue of $J_z$; the paper's wording "eigenvalues of $\tfrac12 J_z$" on p. 2 is read this way, since $m$ runs over $-j,\dots,j$ in Eq. (12).
-- source:
--   D'Ariano, Macchiavello, Perinotti, Optimal phase estimation for qubit mixed states, arXiv:quant-ph/0411133v3, Sec. II, Eqs. (11)–(13), p. 2, and the notation |m,jα⟩ ≐ |j,m,α⟩_z after Eq. (15)

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_QubitPhaseEst_Qb
import Definitions.Def_QubitPhaseEst_SpinIdx

open scoped Matrix

namespace QubitPhaseEst

/-- The one-qubit operator `A` acting on qubit `k` of `N` (the `σ^{(k)}` of arXiv:quant-ph/0411133v3, Sec. II, p. 3, after Eq. (21)): `⟨x|A^{(k)}|y⟩ = ⟨x_k|A|y_k⟩` when `x`
and `y` agree off `k`, and `0` otherwise. -/
def siteOp {N : ℕ} (k : Fin N) (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Qb N) (Qb N) ℂ :=
  Matrix.of fun x y => if ∀ l, l ≠ k → x l = y l then A (x k) (y k) else 0

/-- `σ₊ = |0⟩⟨1|`: it raises `σ_z`, since bit `0` is spin up. Unnumbered; used for the ladder of the
angular-momentum basis of arXiv:quant-ph/0411133v3, Sec. II, Eqs. (11)–(13), p. 2. -/
def sigmaPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 0, 0]

/-- The total `J_z = ½ Σ_k σ_z^{(k)}`, arXiv:quant-ph/0411133v3, Sec. II, p. 1. -/
noncomputable def totalJz (N : ℕ) : Matrix (Qb N) (Qb N) ℂ :=
  ∑ k, (1 / 2 : ℂ) • siteOp k (BBPSSW.Distill.pauli .z)

/-- The total raising operator `J₊ = Σ_k σ₊^{(k)}` = `J_x + iJ_y`, unnumbered; the ladder operator of the
SU(2) representation on `N` qubits, arXiv:quant-ph/0411133v3, Sec. II, Eqs. (11)–(13), p. 2. -/
def totalJplus (N : ℕ) : Matrix (Qb N) (Qb N) ℂ :=
  ∑ k, siteOp k sigmaPlus

/-- The matrix element `⟨u|A|v⟩ = u† · (A v)`, antilinear in `u` (the brackets of arXiv:quant-ph/0411133v3, Sec. II, Eqs. (15)–(17),
pp. 2–3). -/
def braket {n : Type*} [Fintype n] (u : n → ℂ) (A : Matrix n n ℂ) (v : n → ℂ) : ℂ :=
  star u ⬝ᵥ (A *ᵥ v)

/-- **A standard angular-momentum basis of `N` qubits**: the paper's `|m, jα⟩ = |j, m, α⟩_z`,
arXiv:quant-ph/0411133v3, Sec. II, Eqs. (11)–(15), p. 2.

1. The vectors are orthonormal. There are `2^N` labels, so they form a basis (`QubitPhaseEst.eq_11_14`
   proves that such a family exists).
2. `|j, m, α⟩` is a `J_z` eigenvector with eigenvalue `m`.
3. `J₊|j, m, α⟩ = √(j(j+1) − m(m+1)) |j, m+1, α⟩` for `m < j` (the Condon–Shortley ladder), with the
   same `α`, and
4. `J₊|j, j, α⟩ = 0`.

**Formalization Note.** Index `i` means `m = j − i`, so `J₊` moves index `i + 1` to index `i`. The paper
fixes the `|j, m, α⟩` only through Eq. (13) and a "suitable set of unitary operators": every family with
these four properties is admitted; orthonormality and the ladder force each `(j, α)` to span a copy of
the spin-`j` representation. The label `m` is the eigenvalue of `J_z = ½ Σ_k σ_z^{(k)}`; the paper's p. 2
words "eigenvalues of ½J_z" are read as this (`m` runs over `−j, …, j` in Eq. (12)). -/
structure IsStandardBasis {N : ℕ} (b : SpinIdx N → Qb N → ℂ) : Prop where
  orthonormal : ∀ s t, star (b s) ⬝ᵥ b t = if s = t then 1 else 0
  eigen : ∀ s, totalJz N *ᵥ b s = ((SpinIdx.weight s : ℝ) : ℂ) • b s
  ladder : ∀ (k : Fin (N / 2 + 1)) (α : Fin (mult N k)) (i : Fin (N - 2 * (k : ℕ))),
    totalJplus N *ᵥ b (spinBot k α i) =
      (ladderCoeff (N - 2 * (k : ℕ)) ((i : ℕ) + 1) : ℂ) • b (spinTop k α i)
  highest : ∀ (k : Fin (N / 2 + 1)) (α : Fin (mult N k)),
    totalJplus N *ᵥ b ⟨k, (0, α)⟩ = 0

end QubitPhaseEst


