-- Prove2me | Definitions.Def_SymThrWires_Main_Sampling
-- name    : SymThrWires_Main_Sampling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:15:42.523984+00:00
-- url     : https://prove2.me/theorems/54e6df57-9cdd-41e9-a0a7-b87a9c732c16
-- title:
--   Sample lists, the error matrix E_D, the dilation H(E), closed alternating walks and κ_σ
-- statement:
--   Let $[N]$ index the rows and columns of real $N\times N$ matrices. A **sample list** is a list $S=(S_1,\dots,S_Q)$ of pairs $S_t=(U_t,V_t)\in[N]^2$, repetitions allowed, and
--   $$\Gamma(x)=Q-N^2\,\#\{t: S_t=x\}\qquad(x\in[N]^2).$$
--   The **error matrix** of a real matrix $D$ is $E_D=QD-N^2\sum_t D(U_t,V_t)e_{U_t}e_{V_t}^{\mathsf T}$, so $E_D[x]=D[x]\Gamma(x)$. The **dilation** of a real $N\times N$ matrix is the $2N\times 2N$ matrix $H(E)=\begin{pmatrix}0&E\\E^{\mathsf T}&0\end{pmatrix}$.
--
--   A **closed alternating walk** is $w=(u_1,\dots,u_m,v_1,\dots,v_m)\in[N]^{2m}$ with edges $e_{2i-1}=(u_i,v_i)$, $e_{2i}=(u_{i+1},v_i)$ and $u_{m+1}=u_1$. For a sign pattern $\sigma\in\{\pm1\}^{2m}$, $\kappa_\sigma=1+(-1)^m\prod_l\sigma_l\in\{0,2\}$.
--
--   These are the objects of §4 (sampling bounds, Lemmas 4.1 and 4.3) and §5 (the cycle-sum identity, Lemma 5.1).
--
--   **Formalization Note.** A sample list is `Fin Q → Fin N × Fin N`. `errorMatrix` is written entrywise as $Q\,D(u,v)-N^2\sum_t[S_t=(u,v)]D(u,v)$, which is the displayed sum of rank-one terms. `dilation` is `Matrix.fromBlocks 0 E Eᵀ 0`, indexed by `Fin N ⊕ Fin N`. Walk edges are indexed from $0$: `walkEdge u v (2i) = (u i, v i)` and `walkEdge u v (2i+1) = (u (i+1 mod m), v i)`, the paper's $e_{2i+1}, e_{2i+2}$. Signs are units of ℤ (`ℤˣ = {±1}`).
-- source:
--   Dev Nag, Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits, STOC 2027 submission, Zenodo doi:10.5281/zenodo.23847026 (sha256 02f54f02…), p. 15, §4 (Γ, E_D, H(E)); p. 17, §5 (closed walks, κ_σ)

import Mathlib

/-!
# Sample lists, error matrices, the Hermitian dilation, and closed alternating walks

Dev Nag, *Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits*, STOC 2027
submission, Zenodo doi:10.5281/zenodo.23847026, p. 15 (§4: Γ, E_D, H(E)) and p. 17 (§5: closed
walks, edges, sign patterns, κ_σ, walk sums).

`[N]` is `Fin N`; a sample list of `Q` pairs is a function `Fin Q → Fin N × Fin N` (repetitions
allowed).
-/

namespace SymThrWires.Main

open Classical in
/-- `Γ(x) = Q − N² · #{j : (U_j, V_j) = x}` for a list `S` of `Q` sample pairs. -/
noncomputable def sampleGamma {N Q : ℕ} (S : Fin Q → Fin N × Fin N) (x : Fin N × Fin N) : ℝ :=
  (Q : ℝ) - (N : ℝ) ^ 2 * ((Finset.univ.filter (fun j => S j = x)).card : ℝ)

open Classical in
/-- The **error matrix** `E_D = Q D − N² Σ_j D(U_j, V_j) e_{U_j} e_{V_j}ᵀ` of a real `N × N`
matrix `D` and a sample list `S` (§4), written entrywise. -/
noncomputable def errorMatrix {N Q : ℕ} (D : Matrix (Fin N) (Fin N) ℝ) (S : Fin Q → Fin N × Fin N) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun u v =>
    (Q : ℝ) * D u v - (N : ℝ) ^ 2 * ∑ j : Fin Q, (if S j = (u, v) then D u v else 0)

/-- The **Hermitian dilation** `H(E) = [[0, E], [Eᵀ, 0]]` of a real `N × N` matrix. -/
def dilation {N : ℕ} (E : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks 0 E E.transpose 0

/-- The edges of the closed alternating walk `w = (u_1, …, u_m, v_1, …, v_m)` (§5), indexed from
`0`: edge `2i` is `(u_i, v_i)` and edge `2i + 1` is `(u_{i+1}, v_i)`, with `u_m = u_0` (the paper's
`e_{2i−1} = (u_i, v_i)`, `e_{2i} = (u_{i+1}, v_i)`, `u_{m+1} = u_1`, shifted to base `0`). -/
def walkEdge {N m : ℕ} (u v : Fin m → Fin N) (l : Fin (2 * m)) : Fin N × Fin N :=
  have hi : l.val / 2 < m := by have := l.isLt; omega
  if l.val % 2 = 0 then (u ⟨l.val / 2, hi⟩, v ⟨l.val / 2, hi⟩)
  else (u ⟨(l.val / 2 + 1) % m, Nat.mod_lt _ (by omega)⟩, v ⟨l.val / 2, hi⟩)

/-- `κ_σ = 1 + (−1)^m Π_l σ_l` for a sign pattern `σ ∈ {±1}^{2m}` (`ℤˣ = {±1}`). -/
def kappa {m : ℕ} (σ : Fin (2 * m) → ℤˣ) : ℤ :=
  1 + (-1) ^ m * ∏ l, ((σ l : ℤˣ) : ℤ)

end SymThrWires.Main


