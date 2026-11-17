-- Prove2me | Definitions.Def_TwoBoxMemory_Supplement_Certificate
-- name    : TwoBoxMemory_Supplement_Certificate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:12:39.556862+00:00
-- url     : https://prove2.me/theorems/2810b717-0588-441d-8728-7292bdfe023f
-- title:
--   Completion allowance $E_T$ and rational certificates $(L,U)$ of §C.3
-- statement:
--   Fix failure probabilities $r,s\in(0,1)$, $p=1-r$, $t=1-s$, and costs $C,D>0$. The constants of the completed game are
--
--   $$A_z=\frac{C+rD}{p},\qquad B_z=\frac{C+D}{t},\qquad \ell=\frac{s^3}{4},\quad h=\frac{4}{r^3},\quad a_0=\min(\ell,r),\quad b_0=\max(h,1/s),$$
--
--   and, for a horizon $T\in\mathbb N$,
--
--   $$a_T=\min\{i\in\{0,\dots,T\}:\ell r^i/s^{T-i}\le b_0\},\qquad b_T=\min\{j\in\{0,\dots,T\}:h r^{T-j}/s^j\ge a_0\},$$
--
--   $$E_T=\max\bigl(A_z r^{a_T},\,B_z s^{b_T}\bigr).$$
--
--   A **rational certificate** consists of a rational candidate controller $(\mu,K_A,K_B)$ with $m$ labels, nonnegative rational vectors $v_A,v_B$ with $v_A\ge c+Q_Av_A$ and $v_B\ge c+Q_Bv_B$ componentwise (where $Q_A=rK_A+K_B$, $Q_B=K_A+sK_B$, $c=CK_A\mathbf 1+DK_B\mathbf 1$), a horizon $T$, a rational prior $\pi\in[0,1]$, and a rational triangular array $(Y_{i,j})_{i+j\le T}$ with
--
--   $$Y_{i,j}\le \pi r^iA_z+(1-\pi)s^jB_z\quad(i+j=T),$$
--
--   $$Y_{i,j}\le C[\pi r^i+(1-\pi)s^j]+Y_{i+1,j},\qquad Y_{i,j}\le D[\pi r^i+(1-\pi)s^j]+Y_{i,j+1}\quad(i+j<T).$$
--
--   Its endpoints are
--
--   $$L=\max(0,\,Y_{0,0}-E_T),\qquad U=\max(\mu v_A,\mu v_B).$$
--
--   The module also names the three conditions of Theorem C.6 for given $(r,s,C,D,M,\varepsilon)$: (1) some controller with at most $M$ labels has worst risk $<V+\varepsilon$; (2) some rational controller with at most $M$ labels does; (3) some valid rational certificate with at most $M$ labels has $U-L<\varepsilon$; and the coded input range $0<r,s<1$, $C,D>0$, $M\ge1$, $\varepsilon>0$.
--
--   **Formalization Note** $a_T,b_T$ are infima of subsets of $\mathbb N$; for $r,s\in(0,1)$ both sets contain $T$, so these are the minima. The array is a function $\mathbb N\times\mathbb N\to\mathbb R$ of which only the entries with $i+j\le T$ are used.
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), (A.2), p.13 (PDF 15); (A.4)–(A.5), p.14 (PDF 16); (A.8), p.15 (PDF 17); (A.20)–(A.21), pp.18–19 (PDF 20–21); §C.3 and Theorem C.6, p.31 (PDF 33)

import Mathlib
import Definitions.Def_TwoBoxMemory_Controller
import Definitions.Def_TwoBoxMemory_Supplement_Rational

namespace TwoBoxMemory.Supplement

/-!
# The completion allowance `E_T` and rational certificates of Appendices A.2, A.7 and C.3

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
(A.2), p.13 (PDF 15); (A.4)–(A.5), p.14 (PDF 16); (A.8), p.15 (PDF 17); (A.20)–(A.21),
pp.18–19 (PDF 20–21); §C.3, p.31 (PDF 33).

With `p = 1 − r`, `t = 1 − s`:
* (A.2) `A_z = (C + r D)/p`, `B_z = (C + D)/t`;
* (A.4) `ℓ = s³/4`, `h = 4/r³`, `a₀ = min(ℓ, r)`, `b₀ = max(h, 1/s)`;
* (A.5) `a_T = min{i ∈ {0,…,T} : ℓ r^i / s^{T−i} ≤ b₀}`,
  `b_T = min{j ∈ {0,…,T} : h r^{T−j} / s^j ≥ a₀}`;
* (A.8) `E_T = max(A_z r^{a_T}, B_z s^{b_T})`.

A **rational certificate** (§C.3) consists of a rational candidate controller, nonnegative rational
Bellman supersolutions `v_A`, `v_B` with `v_A ≥ c + Q_A v_A`, `v_B ≥ c + Q_B v_B` componentwise
(A.21), a horizon `T`, a rational prior `π ∈ [0, 1]` and a rational triangular array `Y_{i,j}`
(`i + j ≤ T`) satisfying (A.20):
`Y_{i,j} ≤ π r^i A_z + (1 − π) s^j B_z` for `i + j = T`, and for `i + j < T`
`Y_{i,j} ≤ C[π r^i + (1 − π) s^j] + Y_{i+1,j}`, `Y_{i,j} ≤ D[π r^i + (1 − π) s^j] + Y_{i,j+1}`.
Its endpoints are `L = max(0, Y_{0,0} − E_T)` and `U = max(µ v_A, µ v_B)`.

**Formalization Note.**
* `a_T`, `b_T` are `sInf` of subsets of `ℕ`. For `0 < r, s < 1` both sets contain `T`
  (`ℓ r^T ≤ ℓ ≤ b₀` and `h ≥ a₀`), so the infimum is the minimum of (A.5); the empty-set value
  `0` of `sInf` never arises under the hypotheses of the theorems. `T − i` is natural subtraction
  with `i ≤ T`.
* The array `Y` is a function `ℕ → ℕ → ℝ`; only its entries with `i + j ≤ T` are constrained or
  used.
* `C6Cond1`–`C6Cond3` are the three conditions of Theorem C.6 (p.31); `C6Input` codes an input
  `(r, s, C, D, M, ε)` with each rational as a `RatCode`, and `C6Valid` is the input range
  `0 < r, s < 1`, `C, D > 0`, `M ≥ 1`, `ε > 0`.
* The certificate's controller has `m` labels (`Fin m`), the supersolutions are vectors
  `Fin m → ℝ`, and `µ v` is `dotProduct`.
-/

open TwoBoxMemory

noncomputable section

/-- `A_z = (C + r D)/p` of (A.2): the exact risk at location `A` of the cycle `(AB)^∞` started at
its `A` label. -/
def Az (r C D : ℝ) : ℝ := (C + r * D) / (1 - r)

/-- `B_z = (C + D)/t` of (A.2). -/
def Bz (s C D : ℝ) : ℝ := (C + D) / (1 - s)

/-- `ℓ = s³/4` of (A.4). -/
def envL (s : ℝ) : ℝ := s ^ 3 / 4

/-- `h = 4/r³` of (A.4). -/
def envH (r : ℝ) : ℝ := 4 / r ^ 3

/-- `a₀ = min(ℓ, r)` of (A.4). -/
def envA0 (r s : ℝ) : ℝ := min (envL s) r

/-- `b₀ = max(h, 1/s)` of (A.4). -/
def envB0 (r s : ℝ) : ℝ := max (envH r) (1 / s)

/-- `a_T = min{i ∈ {0,…,T} : ℓ r^i / s^{T−i} ≤ b₀}` of (A.5). -/
def aT (r s : ℝ) (T : ℕ) : ℕ :=
  sInf {i : ℕ | i ≤ T ∧ envL s * r ^ i / s ^ (T - i) ≤ envB0 r s}

/-- `b_T = min{j ∈ {0,…,T} : h r^{T−j} / s^j ≥ a₀}` of (A.5). -/
def bT (r s : ℝ) (T : ℕ) : ℕ :=
  sInf {j : ℕ | j ≤ T ∧ envA0 r s ≤ envH r * r ^ (T - j) / s ^ j}

/-- The completion allowance `E_T = max(A_z r^{a_T}, B_z s^{b_T})` of (A.8). -/
def ET (r s C D : ℝ) (T : ℕ) : ℝ :=
  max (Az r C D * r ^ aT r s T) (Bz s C D * s ^ bT r s T)

/-- The data of a certificate with an `m`-label candidate controller (§C.3, p.31). -/
structure Certificate (m : ℕ) where
  /-- the candidate controller -/
  κ : TwoBoxMemory.Controller m
  /-- the Bellman supersolution for location `A` -/
  vA : Fin m → ℝ
  /-- the Bellman supersolution for location `B` -/
  vB : Fin m → ℝ
  /-- the horizon -/
  T : ℕ
  /-- the prior -/
  π : ℝ
  /-- the completed-prefix dual array `Y_{i,j}` (`i + j ≤ T` used) -/
  Y : ℕ → ℕ → ℝ

variable {m : ℕ}

/-- The dual-array inequalities (A.20) at prior `π` and horizon `T`. -/
def DualArray (r s C D : ℝ) (T : ℕ) (π : ℝ) (Y : ℕ → ℕ → ℝ) : Prop :=
  (∀ i j : ℕ, i + j = T →
      Y i j ≤ π * r ^ i * Az r C D + (1 - π) * s ^ j * Bz s C D) ∧
  (∀ i j : ℕ, i + j < T →
      Y i j ≤ C * (π * r ^ i + (1 - π) * s ^ j) + Y (i + 1) j ∧
      Y i j ≤ D * (π * r ^ i + (1 - π) * s ^ j) + Y i (j + 1))

/-- The certificate conditions of §C.3: rational candidate controller; nonnegative rational
supersolutions satisfying (A.21); rational prior in `[0, 1]`; rational array satisfying (A.20). -/
def Certificate.Valid (r s C D : ℝ) (Z : Certificate m) : Prop :=
  IsRationalCtrl Z.κ ∧
  (∀ i, IsRat (Z.vA i) ∧ IsRat (Z.vB i) ∧ 0 ≤ Z.vA i ∧ 0 ≤ Z.vB i) ∧
  (∀ i, cvec C D Z.κ i + Matrix.mulVec (Qmat r s Z.κ 0) Z.vA i ≤ Z.vA i) ∧
  (∀ i, cvec C D Z.κ i + Matrix.mulVec (Qmat r s Z.κ 1) Z.vB i ≤ Z.vB i) ∧
  IsRat Z.π ∧ 0 ≤ Z.π ∧ Z.π ≤ 1 ∧
  (∀ i j : ℕ, i + j ≤ Z.T → IsRat (Z.Y i j)) ∧
  DualArray r s C D Z.T Z.π Z.Y

/-- The lower endpoint `L = max(0, Y_{0,0} − E_T)`. -/
def Certificate.lower (r s C D : ℝ) (Z : Certificate m) : ℝ :=
  max 0 (Z.Y 0 0 - ET r s C D Z.T)

/-- The upper endpoint `U = max(µ v_A, µ v_B)`. -/
def Certificate.upper (Z : Certificate m) : ℝ :=
  max (dotProduct Z.κ.μ Z.vA) (dotProduct Z.κ.μ Z.vB)

/-- Condition 1 of Theorem C.6: some real controller with at most `M` labels has worst risk
strictly less than `V + ε`. -/
def C6Cond1 (r s C D : ℝ) (M : ℕ) (ε : ℝ) : Prop :=
  ∃ (m : ℕ) (κ : Controller m), m ≤ M ∧
    worstRisk r s C D κ < value r s C D + ENNReal.ofReal ε

/-- Condition 2 of Theorem C.6: some **rational** controller with at most `M` labels has worst risk
strictly less than `V + ε`. -/
def C6Cond2 (r s C D : ℝ) (M : ℕ) (ε : ℝ) : Prop :=
  ∃ (m : ℕ) (κ : Controller m), m ≤ M ∧ IsRationalCtrl κ ∧
    worstRisk r s C D κ < value r s C D + ENNReal.ofReal ε

/-- Condition 3 of Theorem C.6: a rational certificate with at most `M` controller labels has
`U − L < ε`. -/
def C6Cond3 (r s C D : ℝ) (M : ℕ) (ε : ℝ) : Prop :=
  ∃ (m : ℕ) (Z : Certificate m), m ≤ M ∧ Z.Valid r s C D ∧
    Z.upper - Z.lower r s C D < ε

/-- The input codes of Theorem C.6: codes of `r, s, C, D`, the budget `M`, and a code of `ε`. -/
abbrev C6Input : Type := RatCode × RatCode × RatCode × RatCode × ℕ × RatCode

/-- The input is valid: `0 < r, s < 1`, `C, D > 0`, `M ≥ 1`, `ε > 0`. -/
def C6Valid (x : C6Input) : Prop :=
  0 < x.1.val ∧ x.1.val < 1 ∧ 0 < x.2.1.val ∧ x.2.1.val < 1 ∧ 0 < x.2.2.1.val ∧
    0 < x.2.2.2.1.val ∧ 1 ≤ x.2.2.2.2.1 ∧ 0 < x.2.2.2.2.2.val

end

end TwoBoxMemory.Supplement


