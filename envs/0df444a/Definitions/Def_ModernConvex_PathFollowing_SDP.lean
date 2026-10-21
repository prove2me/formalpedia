-- Prove2me | Definitions.Def_ModernConvex_PathFollowing_SDP
-- name    : ModernConvex_PathFollowing_SDP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:19.805474+00:00
-- url     : https://prove2.me/theorems/039d50fb-f4cf-4087-8c0f-4424c8b86620
-- title:
--   The primal-dual SDP pair (P), (D), the distance to the central path, N_κ, and the updating (U)
-- statement:
--   Fix $k \ge 1$ and let $\mathbf S^k$ be the space of real symmetric $k \times k$ matrices with the Frobenius inner product $\langle X, Y\rangle_F = \operatorname{Tr}(XY)$ and the Frobenius norm $\|A\|_2 = \sqrt{\sum_{i,j} A_{ij}^2}$. For a positive semidefinite $X$, $X^{1/2}$ is its positive semidefinite square root. The file defines the objects of §§6.4–6.5 of the book in the semidefinite case $\mathbf K = \mathbf S^k_+$.
--
--   1. **The primal-dual pair** (p. 389): a linear subspace $\mathcal L \subseteq \mathbf S^k$ and matrices $B, C \in \mathbf S^k$ define
--   $$\text{(P)}\ \min_X\{\langle C, X\rangle_F : X \in (\mathcal L - B) \cap \mathbf S^k_+\},\qquad \text{(D)}\ \max_S\{\langle B, S\rangle_F : S \in (\mathcal L^\perp + C) \cap \mathbf S^k_+\},$$
--   where $\mathcal L^\perp = \{S \in \mathbf S^k : \operatorname{Tr}(XS) = 0\ \forall X \in \mathcal L\}$. $X$ is **strictly primal feasible** if $X + B \in \mathcal L$ and $X \succ 0$; $S$ is **strictly dual feasible** if $S - C \in \mathcal L^\perp$ and $S \succ 0$. The **duality gap** of a primal-dual feasible pair is $\operatorname{DualityGap}(X, S) = \langle C, X\rangle_F - \langle B, S\rangle_F + \langle C, B\rangle_F$ (p. 393).
--   2. **Distance to the central path** in the SDP case, (6.4.11): for $t \in \mathbb R$ and $X, S \succ 0$, $\operatorname{dist}((X,S), Z_*(t)) = \|tX^{1/2}SX^{1/2} - I\|_2$.
--   3. **The neighbourhood** $\mathcal N_\kappa$ (6.4.13): $(t, X, S) \in \mathcal N_\kappa$ iff $X \in \mathcal L - B$, $S \in \mathcal L^\perp + C$, $t > 0$, $X \succ 0$, $S \succ 0$ and $\operatorname{dist}((X,S), Z_*(t)) \le \kappa$.
--   4. **The updating (U)** (pp. 411–412): the penalty $\bar t = k/\operatorname{Tr}(\bar X\bar S)$ (6.5.38), the new penalty $t_+ = (1 - \chi/\sqrt k)^{-1}\bar t$ (6.5.40); a **commuting scaling** is a $Q \succ 0$ such that $Q\bar XQ$ and $Q^{-1}\bar SQ^{-1}$ commute; a **search direction** is a pair $(\Delta X, \Delta S)$ with $\Delta X \in \mathcal L$, $\Delta S \in \mathcal L^\perp$ (6.5.42) and
--   $$Q[\Delta X\cdot\bar S + \bar X\cdot\Delta S]Q^{-1} + Q^{-1}[\Delta S\cdot\bar X + \bar S\cdot\Delta X]Q = \frac{2}{t_+}I - [Q\bar X\bar SQ^{-1} + Q^{-1}\bar S\bar XQ]. \qquad (6.5.41)$$
--   5. **The objects of the proof of Theorem 6.5.2** (pp. 413–421): $\mu_+ = 1 - \chi k^{-1/2}$; $\rho = \sqrt{\chi^2+\kappa^2}/(1-\kappa)$ (6.5.64); the bound
--   $$\mathrm{bound}(k,\kappa,\chi) = \frac{\rho(1+\rho)}{1-\chi k^{-1/2}}\Big[\frac{\chi}{\sqrt k} + \frac{\rho}{1-\rho} + \frac{\kappa}{1-\kappa}\Big] \qquad (6.5.73);$$
--   a solution of system (6.5.46) at $(X, S)$ is a pair $(\Delta X, \Delta S)$ with $\Delta X \in \mathcal L$, $\Delta S \in \mathcal L^\perp$ and $\Delta X\cdot S + X\cdot\Delta S + \Delta S\cdot X + S\cdot\Delta X = 2\mu_+I - 2XS$; and the **normalized situation of step 2∗**: $X = \operatorname{Diag}(x)$, $S = \operatorname{Diag}(s)$ with all $x_i, s_i > 0$, $X \in \mathcal L - B$, $S \in \mathcal L^\perp + C$, $\sum_i x_is_i = k$ (6.5.49), $\sum_i (x_is_i - 1)^2 \le \kappa^2$ (6.5.50), and $0 < \chi \le \kappa \le 0.1$ (6.5.44).
--
--   **Formalization Note** Matrices are `Matrix (Fin k) (Fin k) ℝ`; $\mathcal L$ is a submodule of real matrices all of whose elements are symmetric, and $\mathcal L^\perp$ is taken inside the symmetric matrices, so the unknowns of the linear systems are symmetric. $X^{1/2}$ is Mathlib's `CFC.sqrt`. The book's $(P)$ comes from $(CP)$ $\min\{c^Tx : \mathcal Ax - B \in \mathbf K\}$ with Assumption A ($\mathcal A$ injective) and $\mathcal L = \operatorname{Im}\mathcal A$; every subspace of $\mathbf S^k$ is the image of an injective linear map, so quantifying over subspaces is the same as quantifying over such $\mathcal A$. The distance is defined directly by its SDP closed form (6.4.11), without the central path. Strict feasibility of both problems, assumed on p. 389, is supplied in every theorem by the strictly feasible pair it is about.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 389 ((P), (D)), p. 393 (DualityGap), p. 395 ((6.4.11)), p. 396 ((6.4.13)), pp. 411–412 (updating (U), (6.5.38)–(6.5.42)), pp. 413–421 ((6.5.44)–(6.5.50), (6.5.64), (6.5.73))

import Mathlib

open Matrix
open scoped MatrixOrder

namespace ModernConvex.PathFollowing

/-- The Frobenius norm `‖A‖₂ = √(Tr(AᵀA)) = √(∑ᵢⱼ Aᵢⱼ²)` of a real `k × k` matrix
(Ben-Tal–Nemirovski write `‖·‖₂` for it in Lecture 6). -/
noncomputable def frobNorm {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, A i j ^ 2)

/-- `ℒ⊥`: the orthogonal complement of a set `ℒ` of symmetric matrices inside the space `Sᵏ` of
real symmetric `k × k` matrices, with respect to the Frobenius inner product
`⟨X, Y⟩_F = Tr(XY)`. -/
def orthSym {k : ℕ} (L : Submodule ℝ (Matrix (Fin k) (Fin k) ℝ)) :
    Set (Matrix (Fin k) (Fin k) ℝ) :=
  {S | S.IsHermitian ∧ ∀ X ∈ L, (X * S).trace = 0}

/-- The data of a primal-dual pair of semidefinite programs in the geometric form of
Ben-Tal–Nemirovski, p. 389, with `K = Sᵏ₊`:
`(P) min_X {Tr(CX) : X ∈ (ℒ − B) ∩ Sᵏ₊}` and `(D) max_S {Tr(BS) : S ∈ (ℒ⊥ + C) ∩ Sᵏ₊}`,
where `ℒ` is a linear subspace of `Sᵏ` and `B, C ∈ Sᵏ`. -/
structure SDPPair (k : ℕ) where
  /-- the linear subspace `ℒ ⊆ Sᵏ` -/
  L : Submodule ℝ (Matrix (Fin k) (Fin k) ℝ)
  /-- the primal shift `B` -/
  B : Matrix (Fin k) (Fin k) ℝ
  /-- the dual shift `C` (the primal objective) -/
  C : Matrix (Fin k) (Fin k) ℝ
  L_sym : ∀ X ∈ L, X.IsHermitian
  B_sym : B.IsHermitian
  C_sym : C.IsHermitian

namespace SDPPair

variable {k : ℕ}

/-- `X` is a strictly feasible solution of `(P)`: `X ∈ ℒ − B` and `X ≻ 0`. -/
def StrictlyPrimalFeasible (P : SDPPair k) (X : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  X + P.B ∈ P.L ∧ X.PosDef

/-- `S` is a strictly feasible solution of `(D)`: `S ∈ ℒ⊥ + C` and `S ≻ 0`. -/
def StrictlyDualFeasible (P : SDPPair k) (S : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  S - P.C ∈ orthSym P.L ∧ S.PosDef

/-- The duality gap `DualityGap(X, S) = ⟨C, X⟩_F − ⟨B, S⟩_F + ⟨C, B⟩_F` of a primal-dual
feasible pair (p. 393). -/
def dualityGap (P : SDPPair k) (X S : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  (P.C * X).trace - (P.B * S).trace + (P.C * P.B).trace

end SDPPair

/-- The distance `dist((X, S), Z∗(t))` from a pair of positive definite matrices to the point
`Z∗(t)` of the primal-dual central path, in the explicit SDP form of (6.4.11), p. 395:
`dist((X, S), Z∗(t)) = ‖t X^{1/2} S X^{1/2} − I‖₂`, where `X^{1/2}` is the positive semidefinite
square root of `X` and `‖·‖₂` the Frobenius norm. -/
noncomputable def centralPathDist {k : ℕ} (t : ℝ) (X S : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  frobNorm (t • (CFC.sqrt X * S * CFC.sqrt X) - 1)

/-- Membership of a triple `(t, X, S)` in the neighbourhood `N_κ` of the primal-dual central path,
(6.4.13), p. 396, for `K = Sᵏ₊`: `X ∈ ℒ − B`, `S ∈ ℒ⊥ + C`, `t > 0`, and
`dist((X, S), Z∗(t)) ≤ κ`; the distance is defined only for `X, S` in the interior of the cone,
so `X ≻ 0` and `S ≻ 0` are part of the membership. -/
def SDPPair.InNbhd {k : ℕ} (P : SDPPair k) (κ t : ℝ) (X S : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  X + P.B ∈ P.L ∧ S - P.C ∈ orthSym P.L ∧ 0 < t ∧ X.PosDef ∧ S.PosDef ∧
    centralPathDist t X S ≤ κ

/-- The penalty parameter attached to a primal-dual pair by (6.5.38)/(6.5.43):
`t̄ = k / Tr(X̄ S̄)`. -/
noncomputable def penaltyOf {k : ℕ} (X S : Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  (k : ℝ) / (X * S).trace

/-- The new penalty parameter of step 1 of the updating (U), (6.5.40):
`t₊ = (1 − χ/√k)⁻¹ t̄`. -/
noncomputable def nextPenalty (k : ℕ) (χ tbar : ℝ) : ℝ :=
  (1 - χ / Real.sqrt k)⁻¹ * tbar

/-- Step 2 of the updating (U): `Q ≻ 0` is a scaling matrix such that `X̃ = Q X̄ Q` and
`S̃ = Q⁻¹ S̄ Q⁻¹` commute. -/
def IsCommutingScaling {k : ℕ} (Q X S : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  Q.PosDef ∧ Commute (Q * X * Q) (Q⁻¹ * S * Q⁻¹)

/-- Steps 3–5 of the updating (U): `(ΔX, ΔS)` is a solution, in symmetric matrices, of the
linearized system (6.5.41), (6.5.42) at `(X̄, S̄)` with scaling matrix `Q` and new penalty `t₊`:
`ΔX ∈ ℒ`, `ΔS ∈ ℒ⊥`, and
`Q[ΔX·S̄ + X̄·ΔS]Q⁻¹ + Q⁻¹[ΔS·X̄ + S̄·ΔX]Q = (2/t₊)I − [QX̄S̄Q⁻¹ + Q⁻¹S̄X̄Q]`. -/
def SDPPair.IsSearchDirection {k : ℕ} (P : SDPPair k) (Q X S : Matrix (Fin k) (Fin k) ℝ)
    (tplus : ℝ) (dX dS : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  dX ∈ P.L ∧ dS ∈ orthSym P.L ∧
    Q * (dX * S + X * dS) * Q⁻¹ + Q⁻¹ * (dS * X + S * dX) * Q =
      (2 / tplus) • (1 : Matrix (Fin k) (Fin k) ℝ) - (Q * X * S * Q⁻¹ + Q⁻¹ * S * X * Q)

/-- `μ₊ = 1 − χ k^{-1/2}`, (6.5.45) after the normalization `μ = 1` (p. 414). -/
noncomputable def muPlus (k : ℕ) (χ : ℝ) : ℝ :=
  1 - χ / Real.sqrt k

/-- `ρ = √(χ² + κ²)/(1 − κ)`, (6.5.64). -/
noncomputable def rho (κ χ : ℝ) : ℝ :=
  Real.sqrt (χ ^ 2 + κ ^ 2) / (1 - κ)

/-- The right-hand side of (6.5.73):
`ρ(1 + ρ)/(1 − χk^{-1/2}) · (χ/√k + ρ/(1 − ρ) + κ/(1 − κ))` with `ρ = √(χ² + κ²)/(1 − κ)`. -/
noncomputable def closenessBound (k : ℕ) (κ χ : ℝ) : ℝ :=
  rho κ χ * (1 + rho κ χ) / (1 - χ / Real.sqrt k) *
    (χ / Real.sqrt k + rho κ χ / (1 - rho κ χ) + κ / (1 - κ))

/-- `(ΔX, ΔS)` is a solution, in symmetric matrices, of system (6.5.46) of the proof of
Theorem 6.5.2 (p. 413): `ΔX ∈ ℒ`, `ΔS ∈ ℒ⊥`, `ΔX·S + X·ΔS + ΔS·X + S·ΔX = 2μ₊I − 2XS`. -/
def SDPPair.IsReducedDirection {k : ℕ} (P : SDPPair k) (X S : Matrix (Fin k) (Fin k) ℝ)
    (μplus : ℝ) (dX dS : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  dX ∈ P.L ∧ dS ∈ orthSym P.L ∧
    dX * S + X * dS + dS * X + S * dX =
      (2 * μplus) • (1 : Matrix (Fin k) (Fin k) ℝ) - (2 : ℝ) • (X * S)

/-- The situation of step 2∗ of the proof of Theorem 6.5.2 after the normalization `μ = 1`
(pp. 413–415): `X = Diag(x)`, `S = Diag(s)` are positive definite diagonal matrices with
`X ∈ ℒ − B`, `S ∈ ℒ⊥ + C`, `∑ᵢ xᵢsᵢ = k` (6.5.49), `∑ᵢ (xᵢsᵢ − 1)² ≤ κ²` (6.5.50), and the
parameters satisfy `0 < χ ≤ κ ≤ 0.1` (6.5.44). -/
structure SDPPair.ReducedSituation {k : ℕ} (P : SDPPair k) (κ χ : ℝ) (x s : Fin k → ℝ) :
    Prop where
  x_pos : ∀ i, 0 < x i
  s_pos : ∀ i, 0 < s i
  primal : diagonal x + P.B ∈ P.L
  dual : diagonal s - P.C ∈ orthSym P.L
  trace_eq : ∑ i, x i * s i = k
  close : ∑ i, (x i * s i - 1) ^ 2 ≤ κ ^ 2
  chi_pos : 0 < χ
  chi_le_kappa : χ ≤ κ
  kappa_le : κ ≤ 0.1

end ModernConvex.PathFollowing


