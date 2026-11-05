-- Prove2me | Definitions.Def_FermionModewise_normalForm
-- name    : FermionModewise_normalForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:00.451451+00:00
-- url     : https://prove2.me/theorems/167c4e22-132f-470c-82c2-d3e89be6416a
-- title:
--   Isotropic normal form (11)–(12) of a bipartite FCM
-- statement:
--   Let $A$-modes be indexed by $\alpha$ and $B$-modes by $\beta$, so that quadratures are indexed by $(\alpha\times\{0,1\})\sqcup(\beta\times\{0,1\})$. Given $s$ pairs, described by injective maps $p_A:\{0,\dots,s-1\}\to\alpha$ and $p_B:\{0,\dots,s-1\}\to\beta$, parameters $\lambda_k,\kappa_k$ for each pair, and a number $\lambda_0$, the **normal form** is the real matrix
--   $$\widetilde M=\widetilde M_{\tilde A_1\tilde B_1}\oplus\cdots\oplus\widetilde M_{\tilde A_s\tilde B_s}\oplus\widetilde M_{\tilde A_F}\oplus\widetilde M_{\tilde B_F}$$
--   of (11): on each pair $(\tilde A_{p_A(k)},\tilde B_{p_B(k)})$ it is the block (12) with parameters $\lambda_k,\kappa_k$; on every unpaired mode, of either side, it is $\lambda_0J_2$; all other entries are $0$.
--
--   Milestone `isotropic_normal_form` shows that every bipartite isotropic covariance matrix is brought to this form by local orthogonal transformations.
--
--   **Formalization Note.** Instead of re-ordering the modes, the pairing is given by the embeddings $p_A$, $p_B$. In block form, the $AA$ block has $\lambda_kJ_2$ at mode $p_A(k)$ and $\lambda_0J_2$ at unpaired modes, likewise the $BB$ block; the $AB$ block has $\kappa_k\begin{pmatrix}0&1\\1&0\end{pmatrix}$ at $(p_A(k),p_B(k))$, and the $BA$ block is minus its transpose. This is (12) entry by entry.
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eqs. (11)–(12), pp.5–6

import Mathlib
import Definitions.Def_FermionModewise_J2

open Matrix

namespace FermionModewise

/-- **Isotropic normal form** (Botero–Reznik, arXiv:quant-ph/0404176v3, eqs. (11)–(12), pp.5–6): the
covariance matrix on the quadratures `(α × Fin 2) ⊕ (β × Fin 2)` of the A-modes and B-modes which,
for `s` pairs `(pA k, pB k)`, has the `4 × 4` block (12) with parameters `λ_k, κ_k` on the pair
`(Ã_{pA k}, B̃_{pB k})`, the block `λ₀ J₂` on every unpaired mode, and `0` elsewhere.

**Formalization Note.** Instead of re-ordering the modes, the pairs are given by embeddings
`pA : Fin s ↪ α` and `pB : Fin s ↪ β`. In the AA block, entry `((a, x), (a', x'))` is
`λ_k J₂ x x'` when `a = a' = pA k`, `λ₀ J₂ x x'` when `a = a'` is unpaired, and `0` otherwise; the BB
block likewise. The AB block has `κ_k · [[0, 1], [1, 0]]` on the pair `(pA k, pB k)` (rows `A₁ A₂`,
columns `B₁ B₂` of (12)), and the BA block is minus its transpose. The sums over `k` have at most
one nonzero term since `pA`, `pB` are injective. -/
def normalForm {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {s : ℕ}
    (pA : Fin s ↪ α) (pB : Fin s ↪ β) (lam kap : Fin s → ℝ) (lam0 : ℝ) :
    Matrix ((α × Fin 2) ⊕ (β × Fin 2)) ((α × Fin 2) ⊕ (β × Fin 2)) ℝ :=
  let swap2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
  let AA : Matrix (α × Fin 2) (α × Fin 2) ℝ := Matrix.of fun p q =>
    (if p.1 = q.1 ∧ p.1 ∉ Finset.univ.map pA then lam0 * J2 p.2 q.2 else 0) +
      ∑ k, if p.1 = pA k ∧ q.1 = pA k then lam k * J2 p.2 q.2 else 0
  let BB : Matrix (β × Fin 2) (β × Fin 2) ℝ := Matrix.of fun p q =>
    (if p.1 = q.1 ∧ p.1 ∉ Finset.univ.map pB then lam0 * J2 p.2 q.2 else 0) +
      ∑ k, if p.1 = pB k ∧ q.1 = pB k then lam k * J2 p.2 q.2 else 0
  let AB : Matrix (α × Fin 2) (β × Fin 2) ℝ := Matrix.of fun p q =>
    ∑ k, if p.1 = pA k ∧ q.1 = pB k then kap k * swap2 p.2 q.2 else 0
  Matrix.fromBlocks AA AB (-ABᵀ) BB

end FermionModewise


