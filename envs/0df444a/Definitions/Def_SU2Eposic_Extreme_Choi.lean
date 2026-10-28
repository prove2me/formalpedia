-- Prove2me | Definitions.Def_SU2Eposic_Extreme_Choi
-- name    : SU2Eposic_Extreme_Choi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:42.058162+00:00
-- url     : https://prove2.me/theorems/de059b9c-0a5a-433f-b523-b1bd3a3ee6bf
-- title:
--   The maps J_k, the isometries η_{m,n,h} = (I ⊗ J_n) α_{m,n,h}, the projections q_{m,r,l} and the Choi matrix
-- statement:
--   This file adds the objects used to describe Choi matrices of SU(2)-covariant channels.
--
--   1. **$J_k$** (Definition 2.2, (2.4)). $J_k:P_k\to\bar P_k$ is the SU(2)-equivariant unitary with
--   $$J_k(f^k_l)=(-1)^l f^k_{k-l},\qquad 0\le l\le k.$$
--   Here $\bar P_k$ is the conjugate space of $P_k$, which carries the conjugate representation $\bar\rho_k$; for the unitary $\rho_k$ this coincides with the contragredient $\check\rho_k$.
--
--   2. **$\eta_{m,n,h}$** (Lemma 2.12). For $0\le h\le\min\{m,n\}$,
--   $$\eta_{m,n,h}=(I_{P_m}\otimes J_n)\,\alpha_{m,n,h}:P_{m+n-2h}\to P_m\otimes\bar P_n.$$
--
--   3. **$q_{m,r,l}$** (§3.2). For $0\le l\le\min\{m,r\}$, $q_{m,r,l}=\eta_{m,r,l}\eta_{m,r,l}^*$, an operator on $P_m\otimes\bar P_r$, with $\eta_{m,r,l}$ defined on $P_{m+r-2l}$.
--
--   4. **The Choi matrix** (Example 1.5(5)). For a map $\Phi:\mathrm{End}(H)\to\mathrm{End}(K)$,
--   $$C(\Phi)=\sum_{i,j}\Phi(E_{ij})\otimes E_{ij}\in\mathrm{End}(K\otimes H),$$
--   where $E_{ij}$ are the matrix units of $\mathrm{End}(H)$.
--
--   The projections $q_{m,r,l}$ decompose $P_m\otimes\bar P_r$ into SU(2)-irreducible pieces, and the Choi matrix of an EPOSIC channel is a multiple of one of them; this is how the paper identifies the vertices of the convex set of covariant channels.
--
--   **Formalization Note** In canonical coordinates $J_k$ is the matrix with entry $(k-l,l)$ equal to $(-1)^l$ and all other entries $0$; $\bar P_k$ has the coordinates of $P_k$. The Choi matrix is defined for any map on matrices, output factor first: its entry at $((k,i),(k',i'))$ is $\Phi(E_{ii'})_{kk'}$, with 0-based indices (the paper's $E_{lk}$ are 1-based).
-- source:
--   Al Nuwairan, SU(2)-irreducibly covariant and EPOSIC channels, arXiv:1306.5321v1, p. 5, Example 1.5(5); p. 9, Definition 2.2 and (2.4); p. 13, Lemma 2.12; p. 22, §3.2 (q_{m,r,l})

import Mathlib
import Definitions.Def_SU2Eposic_Extreme_Setup

/-!
# J_k, the isometries η_{m,n,h}, the projections q_{m,r,l} and the Choi matrix

M. Al Nuwairan, *SU(2)-irreducibly covariant and EPOSIC channels*, arXiv:1306.5321v1:
Example 1.5(5) (p. 5), Definition 2.2 and (2.4) (p. 9), Lemma 2.12 (p. 13), §3.2 (p. 22).
Same coordinates as `Def_SU2Eposic_Extreme_Setup`; `P̄_k` has the coordinates of `P_k` and
carries `rhoConj k`.
-/

namespace SU2Eposic.Extreme

open scoped Matrix ComplexConjugate Kronecker

/-- **Definition 2.2 and (2.4), p. 9.** `J_k : P_k → P̄_k`, `J_k(f^k_l) = (−1)^l f^k_{k−l}`: the
matrix with entry `(k − l, l)` equal to `(−1)^l` and all other entries `0`. -/
def J (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.of fun i l => if (i : ℕ) + l = k then (-1) ^ (l : ℕ) else 0

/-- **Lemma 2.12, p. 13.** `η_{m,n,h} = (I_{P_m} ⊗ J_n) α_{m,n,h} : P_r → P_m ⊗ P̄_n`
(`r = m + n − 2h` in every statement). -/
noncomputable def eta (r m n h : ℕ) : Matrix (Fin (m + 1) × Fin (n + 1)) (Fin (r + 1)) ℂ :=
  ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ⊗ₖ J n) * alpha r m n h

/-- **§3.2, p. 22.** `q_{m,r,l} = η_{m,r,l} η*_{m,r,l}` on `P_m ⊗ P̄_r`, with `η_{m,r,l}` defined
on `P_{m+r−2l}`. -/
noncomputable def q (m r l : ℕ) : Matrix (Fin (m + 1) × Fin (r + 1)) (Fin (m + 1) × Fin (r + 1)) ℂ :=
  eta (m + r - 2 * l) m r l * (eta (m + r - 2 * l) m r l)ᴴ

/-- **Example 1.5(5), p. 5.** The Choi matrix `C(Φ) = Σ_{ij} Φ(E_ij) ⊗ E_ij`, output factor
first: the entry at `((k, i), (k', i'))` is `Φ(E_{ii'})_{kk'}`, `E_{ii'}` the matrix unit
(0-based indices). -/
def choi {ι κ : Type*} [DecidableEq ι] (Φ : QAlgorithms.Superop ι κ) :
    Matrix (κ × ι) (κ × ι) ℂ :=
  Matrix.of fun ki ki' => Φ (Matrix.single ki.2 ki'.2 1) ki.1 ki'.1

end SU2Eposic.Extreme


