-- Prove2me | Definitions.Def_SparseTensorInj_Certify_OddCertificate
-- name    : SparseTensorInj_Certify_OddCertificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:37:27.281807+00:00
-- url     : https://prove2.me/theorems/28e7bb69-25c1-47f1-836a-f4b50eb115de
-- title:
--   Slices $P_e$, $A_i$, the centered Kroneckered sum $M$, $d_{\max}$ and the odd-order certificate (9) (§4.1, Definition 45, Construction 47)
-- statement:
--   Let $k=2q+1$ with $q\ge1$, fix the natural order $\prec$ on $[n]$, and let $I_q=[n]_q$ ($q$-subsets, $N_q=|I_q|=\binom nq$), each $J\in I_q$ identified with its increasing ordering. For a tensor $T$, $T^\circ$ is $T$ with every entry having a repeated index set to $0$, and for $e\in[n]_{2q+1}$, $T_e$ is the coefficient of $T$ at the distinct indices of $e$. Write $e=\{i,j_1,\dots,j_q,k_1,\dots,k_q\}$ with $i\prec j_1\prec\dots\prec j_q\prec k_1\prec\dots\prec k_q$, so $i=\min(e)$, $J_e=\{j_1,\dots,j_q\}$, $K_e=\{k_1,\dots,k_q\}$, and set
--   $$P_e=e_{J_e}e_{K_e}^\top+e_{K_e}e_{J_e}^\top\in\mathbb R^{N_q\times N_q},\qquad A_i=\sum_{e\in[n]_{2q+1},\ \min(e)=i}T_eP_e .$$
--   With the Kronecker product $(A\otimes B)[(a,b),(c,d)]=A[a,c]B[b,d]$ (Definition 14), Construction 47 defines
--   $$D=\sum_{e}T_e^2(P_e\otimes P_e),\quad d_{J,K}=\sum_{e:\{J_e,K_e\}=\{J,K\}}T_e^2,\quad d_{\max}=\max_{J,K\in I_q}d_{J,K},\quad M=\sum_{i=1}^nA_i\otimes A_i-D,$$
--   equivalently $M=\sum_{e\ne f,\ \min(e)=\min(f)}T_eT_f(P_e\otimes P_f)$. The **odd-order certificate**, eq. (9), is
--   $$u(T)=\|T-T^\circ\|_F+\frac{(2q+1)!}{2\cdot q!}\sqrt{\|M\|_{\mathrm{op}}+2d_{\max}} .$$
--   The same quadratic chaos $\sum_{e\ne f,\min e=\min f}x_ey_f(P_e\otimes P_f)$ with other coefficient families gives $M_{\mathrm{dec}}$, $M_{\mathrm{sym}}$ and $M_{\mathrm{comp}}$ of §4.3.
--
--   **Formalization Note.** $\prec$ is the order of `Fin n`; the increasing enumeration of $e$ is `Finset.orderEmbOfFin`, $J_e$ and $K_e$ are the images of positions $1..q$ and $q+1..2q$, and $T_e$ is $T$ at that enumeration (for symmetric $T$ any ordering gives the same value). $d_{\max}$ is `⨆ J, ⨆ K, dJK T J K`, the maximum when $I_q\neq\emptyset$ ($0$ otherwise). The printed constant "$(2q+1)!/2q!$" is read as $(2q+1)!/(2\cdot q!)$, the value the proof of Lemma 48 derives (p. 27). `chaosMatrix x y` is the chaos above; `oddM T` is $\sum_iA_i\otimes A_i-D$.
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), pp. 25–26, §4.1, Definition 45, Construction 47 and eq. (9)

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_Tensor

open Matrix

namespace SparseTensorInj.Certify

/-- `I_q = [n]_q`, the `q`-element subsets of `[n]` (§4.1, p. 25); `N_q = |I_q| = C(n, q)`. A set
`J ∈ I_q` is identified with its increasing ordering. -/
abbrev QSet (n q : ℕ) : Type := KSubset n q

/-- The increasing enumeration `v_0 ≺ v_1 ≺ ⋯ ≺ v_{2q}` of a `(2q+1)`-set `e`, for the fixed
order `≺` on `[n]` taken to be the order of `Fin n` (§4.1, p. 25). -/
noncomputable def sortedElt {n q : ℕ} (e : KSubset n (2 * q + 1)) : Fin (2 * q + 1) ↪o Fin n :=
  e.1.orderEmbOfFin e.2

/-- Positions `1, …, q` of `Fin (2q+1)` (the `j`-block of `e = {i, j_1, …, j_q, k_1, …, k_q}`). -/
def posJ (q : ℕ) : Fin q ↪ Fin (2 * q + 1) :=
  ⟨fun j => ⟨j.val + 1, by omega⟩, by
    intro a b h
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)⟩

/-- Positions `q+1, …, 2q` of `Fin (2q+1)` (the `k`-block of `e`). -/
def posK (q : ℕ) : Fin q ↪ Fin (2 * q + 1) :=
  ⟨fun j => ⟨q + 1 + j.val, by omega⟩, by
    intro a b h
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)⟩

/-- `min_≺(e)`, the smallest element `i` of `e` (§4.1, p. 25). -/
noncomputable def minElt {n q : ℕ} (e : KSubset n (2 * q + 1)) : Fin n :=
  sortedElt e ⟨0, by omega⟩

/-- `J_e = {j_1, …, j_q}`, the 2nd to `(q+1)`-th smallest elements of `e` (Definition 45, p. 26). -/
noncomputable def Jset {n q : ℕ} (e : KSubset n (2 * q + 1)) : QSet n q :=
  ⟨Finset.univ.map ((posJ q).trans (sortedElt e).toEmbedding), by simp⟩

/-- `K_e = {k_1, …, k_q}`, the `(q+2)`-th to `(2q+1)`-th smallest elements of `e`
(Definition 45, p. 26). -/
noncomputable def Kset {n q : ℕ} (e : KSubset n (2 * q + 1)) : QSet n q :=
  ⟨Finset.univ.map ((posK q).trans (sortedElt e).toEmbedding), by simp⟩

/-- `T_e`, the coefficient of `T` at the distinct indices of `e` (§4.1, p. 25), read at the
increasing enumeration of `e`; for a symmetric tensor every ordering gives the same value. -/
noncomputable def coef {n q : ℕ} (T : Tensor (2 * q + 1) n) (e : KSubset n (2 * q + 1)) : ℝ :=
  T (fun m => sortedElt e m)

/-- `P_e = e_{J_e} e_{K_e}^⊤ + e_{K_e} e_{J_e}^⊤ ∈ ℝ^{N_q × N_q}` (Definition 45, p. 26). -/
noncomputable def Pmat {n q : ℕ} (e : KSubset n (2 * q + 1)) : Matrix (QSet n q) (QSet n q) ℝ :=
  fun a b => (if a = Jset e ∧ b = Kset e then 1 else 0) + (if a = Kset e ∧ b = Jset e then 1 else 0)

/-- The slice `A_i = Σ_{e ∈ [n]_{2q+1}, min(e) = i} T_e P_e` (Definition 45, p. 26). -/
noncomputable def slice {n q : ℕ} (T : Tensor (2 * q + 1) n) (i : Fin n) :
    Matrix (QSet n q) (QSet n q) ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e : KSubset n (2 * q + 1) => minElt e = i), coef T e • Pmat e

/-- `D = Σ_{e ∈ [n]_{2q+1}} T_e^2 (P_e ⊗ P_e)` (Construction 47, p. 26). -/
noncomputable def Dmat {n q : ℕ} (T : Tensor (2 * q + 1) n) :
    Matrix (QSet n q × QSet n q) (QSet n q × QSet n q) ℝ :=
  ∑ e : KSubset n (2 * q + 1), coef T e ^ 2 • kronecker (Pmat e) (Pmat e)

/-- `d_{J,K} = Σ_{e : {J_e, K_e} = {J, K}} T_e^2` (Construction 47, p. 26); `{J_e, K_e} = {J, K}`
is equality of unordered pairs. -/
noncomputable def dJK {n q : ℕ} (T : Tensor (2 * q + 1) n) (J K : QSet n q) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e : KSubset n (2 * q + 1) =>
      (Jset e = J ∧ Kset e = K) ∨ (Jset e = K ∧ Kset e = J)), coef T e ^ 2

/-- `d_max = max_{J, K ∈ I_q} d_{J,K}` (Construction 47, p. 26), as a supremum over a finite
index set (the maximum when `I_q` is nonempty). -/
noncomputable def dmax {n q : ℕ} (T : Tensor (2 * q + 1) n) : ℝ :=
  ⨆ J : QSet n q, ⨆ K : QSet n q, dJK T J K

/-- `M = M̃ − D` with `M̃ = Σ_{i=1}^n A_i ⊗ A_i` (Construction 47, p. 26), an
`N_q^2 × N_q^2` matrix indexed by `I_q × I_q`; `⊗` is the Kronecker product,
`(A ⊗ B)[(a, b), (c, d)] = A[a, c] B[b, d]` (Definition 14). -/
noncomputable def oddM {n q : ℕ} (T : Tensor (2 * q + 1) n) :
    Matrix (QSet n q × QSet n q) (QSet n q × QSet n q) ℝ :=
  (∑ i : Fin n, kronecker (slice T i) (slice T i)) - Dmat T

/-- The quadratic matrix chaos `Σ_{e ≠ f, min(e) = min(f)} x_e y_f (P_e ⊗ P_f)` built from two
coefficient families `x, y` indexed by `E = [n]_{2q+1}` (eq. (13), p. 30). With `x = y = (T_e)`
it is `M` (Construction 47); with independent copies it is `M_dec` (Lemma 57), with symmetrized
variables `M_sym` (Lemma 64), with sparse Rademacher variables `M_comp` (Definition 65). -/
noncomputable def chaosMatrix {n q : ℕ} (x y : KSubset n (2 * q + 1) → ℝ) :
    Matrix (QSet n q × QSet n q) (QSet n q × QSet n q) ℝ :=
  ∑ e : KSubset n (2 * q + 1), ∑ f : KSubset n (2 * q + 1),
    if e ≠ f ∧ minElt e = minElt f then (x e * y f) • kronecker (Pmat e) (Pmat f) else 0

/-- `T°`: the tensor `T` with every entry having a repeated index set to zero (§4.1, p. 25). -/
noncomputable def zeroRepeated {k n : ℕ} (T : Tensor k n) : Tensor k n :=
  fun i => if (Finset.univ.image i).card = k then T i else 0

/-- The odd-order certificate, eq. (9) (p. 26), for `k = 2q + 1`:
`u(T) = ‖T − T°‖_F + ((2q+1)!/(2·q!)) · √(‖M‖_op + 2 d_max)`. The printed constant
"(2q + 1)!/2q!" is read as `(2q+1)!/(2·q!)`, the value derived in the proof of Lemma 48 (p. 27). -/
noncomputable def oddCert {n q : ℕ} (T : Tensor (2 * q + 1) n) : ℝ :=
  frobNorm (T - zeroRepeated T) +
    ((Nat.factorial (2 * q + 1) : ℝ) / (2 * (Nat.factorial q : ℝ))) *
      Real.sqrt (opNorm (oddM T) + 2 * dmax T)

end SparseTensorInj.Certify


