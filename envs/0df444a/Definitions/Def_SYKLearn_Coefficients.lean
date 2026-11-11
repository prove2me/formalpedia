-- Prove2me | Definitions.Def_SYKLearn_Coefficients
-- name    : SYKLearn_Coefficients
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:17:43.704776+00:00
-- url     : https://prove2.me/theorems/173847d4-8fe2-4e87-bd1d-d363715b2d34
-- title:
--   $H^2|_{\mathbb M_4}$, $H^2|_{\mathbb M_8}$, $T_{\rm dis}$, $T_{\rm conn}$ and the coefficients $c_{1,4},c_{2,4},c_{2,8},c^{\rm conn}_{3,8},c^{\rm dis}_{3,8}$ of Lemma 3.3
-- statement:
--   The low-degree Hermite components of the annealed Gibbs components are expressed through four explicit tensors of the coupling vector $g\in\mathbb M_4$:
--
--   $$H^2|_{\mathbb M_4},\qquad H^2|_{\mathbb M_8},\qquad T_{\rm dis}=g\wedge(H^2|_{\mathbb M_4}),\qquad T_{\rm conn}=\sum_{i,j}a_ig\wedge a_ja_ig\wedge a_jg,$$
--
--   where $H^2|_{\mathbb M_k}$ is the degree-$k$ part of $H_g^2$. Lemma 3.3 asserts that $\Pi_1\bar\rho_4$, $\Pi_2\bar\rho_4$, $\Pi_2\bar\rho_8$, $\Pi_3\bar\rho_8$ are combinations of these with coefficients depending only on $n,\beta$. This module names those coefficients, as $L^2$ projection coefficients over the coupling law (with $\langle u,v\rangle=\sum_Su_Sv_S$):
--
--   1. $c_{1,4}=-\mathbb E\langle g,\bar\rho_4\rangle/\mathbb E\|g\|^2$ (the paper's identity $c_{1,4}\sigma_n^2m=-\mathbb E\langle g,\bar\rho_4\rangle$, p.32);
--   2. $c_{2,4}=\mathbb E\langle u,\Pi_2\bar\rho_4\rangle/\mathbb E\|u\|^2$ with $u=H^2|_{\mathbb M_4}$, and $c_{2,8}=\mathbb E\langle v,\Pi_2\bar\rho_8\rangle/\mathbb E\|v\|^2$ with $v=H^2|_{\mathbb M_8}$;
--   3. $(c^{\rm conn}_{3,8},c^{\rm dis}_{3,8})$ is the minimum-norm least-squares solution of $\Pi_3\bar\rho_8\approx-c\,T_{\rm conn}+c'\,T_{\rm dis}$: with the Gram matrix $G$ of $(-T_{\rm conn},T_{\rm dis})$ and the vector $r$ of their inner products with $\Pi_3\bar\rho_8$, it is $G^+r$.
--
--   Whenever an identity of Lemma 3.3 holds with some coefficient and its regressors are linearly independent, that coefficient is the one defined here; Lemma 3.11 is a statement about $c_{1,4}$ and $c^{\rm conn}_{3,8}$.
--
--   **Formalization Note** A ratio with zero denominator is $0$. The Moore–Penrose inverse of the $2\times2$ symmetric positive semidefinite $G$ is $G^{-1}$ if $\det G\neq0$, $G/(\mathrm{tr}\,G)^2$ if $G\neq0=\det G$, and $0$ if $G=0$. The coefficients of $H_g^2$ in the basis $\Gamma_S$ are real, and their real parts are taken.
-- source:
--   Anshu–Arunachalam–Chen–Hwang, Efficiently Learning SYK Hamiltonians, STOC 2027 submission (held file sha256 5d7d199a…), Lemma 3.3, p.20; T_dis and T_conn, p.21; c_{1,4}σ_n²m = −E⟨g, ρ̄_4⟩, p.32

import Mathlib
import Definitions.Def_SYKLearn_Exterior
import Definitions.Def_SYKLearn_Hermite

noncomputable section
open Matrix MeasureTheory

namespace SYKLearn

/-!
# The low-degree objects of Lemma 3.3 and their canonical coefficients

A. Anshu, S. Arunachalam, S. Chen, Y. Hwang, *Efficiently Learning SYK Hamiltonians*, STOC 2027
submission (held file sha256 5d7d199a…), Lemma 3.3, p.20; `T_dis`, `T_conn`, p.21; the identity
`c_{1,4} σ_n² m = −E⟨g, ρ_4⟩`, p.32.

**Formalization Note.**
* `Hsq4 Q w = H²|M_4` and `Hsq8 Q w = H²|M_8` are the degree-4 and degree-8 parts of `H_g²`
  (`g = w`), as real vectors of `M_4`, `M_8` (the coefficients of `H_g²` in the basis `Γ_S` are
  real for a real coupling vector).
* `Tdis Q w = g ∧ (H²|M_4)` and `Tconn w = Σ_{i,j} a_i g ∧ a_j a_i g ∧ a_j g` (p.21), with
  `g = emb4 w ∈ M_4`; the wedge is associative and is taken left to right.
* Lemma 3.3 asserts that there are coefficients `c_{1,4}, c_{2,4}, c_{2,8}, c^conn_{3,8}, c^dis_{3,8}`
  depending only on `n, β`; Lemma 3.11 is a statement about two of them, so they are named here.
  Each is the canonical (least-squares) coefficient, computed in `L²(disorderLaw Q)` with the
  Euclidean inner product `extInner` on `Ext N`:
  - `c14 = −E⟨g, ρ_4⟩ / E‖g‖²` — the paper's own identity (p.32), the `L²` projection of `Π_1 ρ_4`
    on `−g` (`g` has Hermite degree `1`);
  - `c24 = E⟨u, Π_2 ρ_4⟩ / E‖u‖²`, `u = H²|M_4`; `c28 = E⟨v, Π_2 ρ_8⟩ / E‖v‖²`, `v = H²|M_8`;
  - `(cconn, cdis)` is the minimum-norm least-squares solution of
    `Π_3 ρ_8 ≈ −c·T_conn + c′·T_dis`: with `A = −T_conn`, `B = T_dis`, the Gram matrix
    `G = (E⟨X, Y⟩)_{X,Y ∈ {A,B}}` and `r = (E⟨A, Π_3ρ_8⟩, E⟨B, Π_3ρ_8⟩)`, it is `G⁺ r` with the
    Moore–Penrose inverse of the `2 × 2` symmetric positive semidefinite `G`
    (`pinv2`: `G⁻¹` if `det G ≠ 0`, `G/(tr G)²` if `G ≠ 0 = det G`, `0` if `G = 0`).
  A ratio with denominator `0` is `0`. Whenever the identities of Lemma 3.3 hold with some
  coefficients and the functions in each identity are linearly independent in `L²`, those
  coefficients are exactly these.
* `ρ_k` is the annealed component `rhoK`; `Π_d` is `hermProj (sigma N) (disorderLaw Q) d`.
-/

open SYKFastMix.FastMixing

/-- `H²|M_4`, the degree-4 part of `H_g²` (p.20). -/
def Hsq4 {N : ℕ} (Q : Model N) (w : Disorder N) : Ext N :=
  resReal Q 4 (hamiltonian Q w * hamiltonian Q w)

/-- `H²|M_8`, the degree-8 part of `H_g²` (p.20). -/
def Hsq8 {N : ℕ} (Q : Model N) (w : Disorder N) : Ext N :=
  resReal Q 8 (hamiltonian Q w * hamiltonian Q w)

/-- `T_dis = g ∧ (H²|M_4)` (p.21). -/
def Tdis {N : ℕ} (Q : Model N) (w : Disorder N) : Ext N :=
  wedge (emb4 w) (Hsq4 Q w)

/-- `T_conn = Σ_{i,j} a_i g ∧ a_j a_i g ∧ a_j g` (p.21). -/
def Tconn {N : ℕ} (w : Disorder N) : Ext N :=
  ∑ i : Fin N, ∑ j : Fin N,
    wedge (wedge (ann i (emb4 w)) (ann j (ann i (emb4 w)))) (ann j (emb4 w))

/-- The `L²(disorderLaw Q)` inner product `E⟨X(g), Y(g)⟩` of two `Ext N`-valued functions. -/
def eInner {N : ℕ} (Q : Model N) (X Y : Disorder N → Ext N) : ℝ :=
  ∫ w, extInner (X w) (Y w) ∂(disorderLaw Q)

/-- `Π_d` in the SYK couplings, `σ = σ_N`, law `disorderLaw Q`. -/
def proj {N : ℕ} (Q : Model N) (d : ℕ) (f : Disorder N → Ext N) : Disorder N → Ext N :=
  hermProj (sigma N) (disorderLaw Q) d f

/-- `c_{1,4} = −E⟨g, ρ_4⟩ / E‖g‖²` (Lemma 3.3, p.20; p.32). -/
def c14 {N : ℕ} (β : ℝ) (Q : Model N) : ℝ :=
  -eInner Q emb4 (rhoK β Q 4) / eInner Q emb4 emb4

/-- `c_{2,4} = E⟨H²|M_4, Π_2ρ_4⟩ / E‖H²|M_4‖²` (Lemma 3.3, p.20). -/
def c24 {N : ℕ} (β : ℝ) (Q : Model N) : ℝ :=
  eInner Q (Hsq4 Q) (proj Q 2 (rhoK β Q 4)) / eInner Q (Hsq4 Q) (Hsq4 Q)

/-- `c_{2,8} = E⟨H²|M_8, Π_2ρ_8⟩ / E‖H²|M_8‖²` (Lemma 3.3, p.20). -/
def c28 {N : ℕ} (β : ℝ) (Q : Model N) : ℝ :=
  eInner Q (Hsq8 Q) (proj Q 2 (rhoK β Q 8)) / eInner Q (Hsq8 Q) (Hsq8 Q)

/-- The Moore–Penrose inverse of a symmetric positive semidefinite `2 × 2` matrix. -/
def pinv2 (G : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if G.det ≠ 0 then G⁻¹ else (G.trace ^ 2)⁻¹ • G

/-- The two regressors `(−T_conn, T_dis)` of the degree-3 identity. -/
def deg3Basis {N : ℕ} (Q : Model N) : Fin 2 → Disorder N → Ext N :=
  ![fun w => -Tconn w, Tdis Q]

/-- `(c^conn_{3,8}, c^dis_{3,8})`: the minimum-norm least-squares solution of
`Π_3ρ_8 ≈ −c·T_conn + c′·T_dis` in `L²(disorderLaw Q)`. -/
def c3pair {N : ℕ} (β : ℝ) (Q : Model N) : Fin 2 → ℝ :=
  pinv2 (Matrix.of fun a b => eInner Q (deg3Basis Q a) (deg3Basis Q b)) *ᵥ
    (fun a => eInner Q (deg3Basis Q a) (proj Q 3 (rhoK β Q 8)))

/-- `c^conn_{3,8}` (Lemma 3.3, p.20). -/
def cconn {N : ℕ} (β : ℝ) (Q : Model N) : ℝ := c3pair β Q 0

/-- `c^dis_{3,8}` (Lemma 3.3, p.20). -/
def cdis {N : ℕ} (β : ℝ) (Q : Model N) : ℝ := c3pair β Q 1

end SYKLearn


