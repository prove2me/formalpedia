-- Prove2me | Definitions.Def_PALM_ProxNMF_Setting
-- name    : PALM_ProxNMF_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:20.751953+00:00
-- url     : https://prove2.me/theorems/0d30f355-a0a1-47e9-b16b-989c70a6769e
-- title:
--   The proximal map (2.2), $\|X\|_0$, $\delta_{X\ge 0}+\delta_{\|X\|_0\le s}$, $T_s$ (Definition 4.1), $P_+$, and $\|X\|^2_\pm$ on $\mathbb R^{m\times n}$
-- statement:
--   This file fixes the objects of §4.2 of Bolte, Sabach and Teboulle on the space $\mathbb R^{m\times n}$ of real $m\times n$ matrices, with the squared Frobenius norm
--   $$\|M\|_F^2=\sum_{i,j}M_{ij}^2=\langle M,M\rangle .$$
--
--   1. **Indicator.** For a set $C$, $\delta_C(X)=0$ if $X\in C$ and $\delta_C(X)=+\infty$ otherwise.
--   2. **Argmin set.** For $\varphi:\mathbb R^{m\times n}\to\mathbb R$ and a set $C$, $\operatorname{argmin}\{\varphi(X):X\in C\}$ is the set of all $X\in C$ with $\varphi(X)\le\varphi(W)$ for every $W\in C$. It may be empty or contain several points.
--   3. **Proximal map (2.2).** For $\sigma:\mathbb R^{m\times n}\to(-\infty,+\infty]$, $t\in\mathbb R$ and $U\in\mathbb R^{m\times n}$,
--   $$\operatorname{prox}^\sigma_t(U)=\operatorname{argmin}\Big\{\sigma(X)+\frac t2\|X-U\|_F^2 : X\in\mathbb R^{m\times n}\Big\},$$
--   the set of all minimizers; note the weight $t/2$.
--   4. **Sparsity.** $\|X\|_0$ is the number of nonzero entries of $X$; $X\ge 0$ means $X_{ij}\ge0$ for all $i,j$.
--   5. **The function** $f:=\delta_{X\ge0}+\delta_{\|X\|_0\le s}$ for a natural number $s$: it is $0$ on nonnegative matrices with at most $s$ nonzero entries and $+\infty$ elsewhere.
--   6. **Hard thresholding (Definition 4.1).** $T_s(U)=\operatorname{argmin}_{V}\{\|U-V\|_F^2:\|V\|_0\le s\}$, a set (the operator is in general multi-valued).
--   7. **Projection onto the nonnegative orthant.** $P_+(U)=\max\{0,U\}$, taken componentwise; the paper introduces it as $\operatorname{argmin}_V\{\|U-V\|_F^2 : V\ge0\}$, whose unique element is this matrix.
--   8. **Splitting relative to $U$.** $\mathcal I^+=\{(i,j):U_{ij}\ge0\}$, $\mathcal I^-=\{(i,j):U_{ij}<0\}$, and
--   $$\|X\|_+^2=\sum_{(i,j)\in\mathcal I^+}X_{ij}^2,\qquad \|X\|_-^2=\sum_{(i,j)\in\mathcal I^-}X_{ij}^2 .$$
--
--   These are the objects in which the proximal map of the nonnegative sparsity constraint, needed to run PALM on sparse nonnegative matrix factorization, is computed.
--
--   **Formalization Note** Matrices are `Matrix (Fin m) (Fin n) ℝ`, with 0-based indices. $\|M\|_F^2$ is the Frobenius inner product $\langle M,M\rangle$ of the referenced definition `CaiCandesShen.ProximalLimit.Basic` (`frobInner M M`). Indicator and $f$ take values in `EReal`, with $+\infty=\top$. $P_+$ is defined by the componentwise formula; the paper's argmin description of it is not restated.
-- source:
--   Bolte, Sabach, Teboulle, Proximal alternating linearized minimization for nonconvex and nonsmooth problems, Math. Program. 146 (2014), doi:10.1007/s10107-013-0701-9 (source: author version), pp. 7, 27–28, (2.2), δ_X, ‖·‖_F, ‖·‖_0, Definition 4.1, P_+, and the notation of the proof of Proposition 4.1

import Mathlib
import Definitions.Def_CaiCandesShen_ProximalLimit_Basic

open CaiCandesShen.ProximalLimit

namespace PALM.ProxNMF

/-- The indicator `δ_C` of a set `C` (p. 7): `0` on `C` and `+∞` off `C`, valued in `EReal`. -/
noncomputable def indicator {α : Type*} (C : Set α) (x : α) : EReal :=
  open Classical in if x ∈ C then 0 else ⊤

/-- The argmin set `argmin {φ(X) : X ∈ C}`: the points of `C` at which `φ` is smallest over `C`. -/
def argminOn {α : Type*} (φ : α → ℝ) (C : Set α) : Set α :=
  {X | X ∈ C ∧ ∀ W ∈ C, φ X ≤ φ W}

/-- The proximal map (2.2), p. 7, on `ℝ^{m×n}` with the Frobenius norm, as a set:
`prox^σ_t(U) = argmin {σ(X) + (t/2)‖X − U‖²_F}`, with `‖M‖²_F = ⟨M, M⟩` (p. 27). -/
def proxSet {m n : ℕ} (σ : Matrix (Fin m) (Fin n) ℝ → EReal) (t : ℝ)
    (U : Matrix (Fin m) (Fin n) ℝ) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  {X | ∀ W, σ X + ((t / 2 * frobInner (X - U) (X - U) : ℝ) : EReal)
          ≤ σ W + ((t / 2 * frobInner (W - U) (W - U) : ℝ) : EReal)}

/-- `‖X‖₀`, the number of nonzero entries of `X` (pp. 27–28). -/
noncomputable def l0 {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) : ℕ :=
  (Finset.univ.filter (fun p : Fin m × Fin n => X p.1 p.2 ≠ 0)).card

/-- The nonnegative matrices `{X : X ≥ 0}` (entrywise), i.e. `ℝ^{m×n}_+`. -/
def NonnegSet (m n : ℕ) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  {X | ∀ i j, 0 ≤ X i j}

/-- The sparse matrices `{X : ‖X‖₀ ≤ s}`. -/
def SparseSet (m n s : ℕ) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  {X | l0 X ≤ s}

/-- `f := δ_{X ≥ 0} + δ_{‖X‖₀ ≤ s}` (Proposition 4.1, p. 28). -/
noncomputable def f {m n : ℕ} (s : ℕ) (X : Matrix (Fin m) (Fin n) ℝ) : EReal :=
  indicator (NonnegSet m n) X + indicator (SparseSet m n s) X

/-- The operator `T_s` of Definition 4.1 (p. 28), as the full (in general multi-valued) set
`T_s(U) = argmin_{V} {‖U − V‖²_F : ‖V‖₀ ≤ s}`. -/
def Ts {m n : ℕ} (s : ℕ) (U : Matrix (Fin m) (Fin n) ℝ) : Set (Matrix (Fin m) (Fin n) ℝ) :=
  argminOn (fun V => frobInner (U - V) (U - V)) (SparseSet m n s)

/-- The projection onto `ℝ^{m×n}_+` (p. 28): `P_+(U) = max {0, U}` componentwise. -/
noncomputable def Pplus {m n : ℕ} (U : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j => max 0 (U i j)

/-- `I⁺ = {(i, j) : U_ij ≥ 0}` (proof of Proposition 4.1, p. 28). -/
noncomputable def Iplus {m n : ℕ} (U : Matrix (Fin m) (Fin n) ℝ) : Finset (Fin m × Fin n) :=
  Finset.univ.filter (fun p => 0 ≤ U p.1 p.2)

/-- `I⁻ = {(i, j) : U_ij < 0}` (proof of Proposition 4.1, p. 28). -/
noncomputable def Iminus {m n : ℕ} (U : Matrix (Fin m) (Fin n) ℝ) : Finset (Fin m × Fin n) :=
  Finset.univ.filter (fun p => U p.1 p.2 < 0)

/-- `‖X‖²_+ = ∑_{(i,j) ∈ I⁺} X_ij²`, relative to the fixed `U` (p. 28). -/
noncomputable def normSqPlus {m n : ℕ} (U X : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ p ∈ Iplus U, X p.1 p.2 ^ 2

/-- `‖X‖²_− = ∑_{(i,j) ∈ I⁻} X_ij²`, relative to the fixed `U` (p. 28). -/
noncomputable def normSqMinus {m n : ℕ} (U X : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ p ∈ Iminus U, X p.1 p.2 ^ 2

end PALM.ProxNMF


