-- Prove2me | Definitions.Def_LeeYangGap_SpectralGap_Model
-- name    : LeeYangGap_SpectralGap_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:16.091167+00:00
-- url     : https://prove2.me/theorems/db94c9c6-da93-48a3-bda3-c19f203f60a0
-- title:
--   The full Lee–Yang coefficient model and uniform-field Hamiltonian
-- statement:
--   A configuration of $n$ qubits is $x\in\{0,1\}^n$, and the Hilbert space is $\mathbb C^{\{0,1\}^n}$. The standard Pauli matrices are reused from the published definition DrezetGHZ_Quantum with exactly the same signs and basis ordering. Their lifts $X_i,Y_i,Z_i$ act on site $i$ and as identity elsewhere. A bond has two distinct ordered endpoints and five real coefficients. A system is a finite ordered list of bonds, with zero coefficients and repeated pairs allowed. Define
--   $$H_{ij}=-w^z_{ij}Z_iZ_j+w^x_{ij}X_iX_j+w^y_{ij}Y_iY_j+w^{xy}_{ij}X_iY_j+w^{yx}_{ij}Y_iX_j,$$
--   $$H=\sum_{ij}H_{ij},\qquad H_h=H-h\sum_iZ_i,$$
--   and define Lee–Yang admissibility solely by
--   $$w^z_{ij}\ge\tfrac12\sqrt{(w^x_{ij}-w^y_{ij})^2+(w^{xy}_{ij}+w^{yx}_{ij})^2}+\tfrac12\sqrt{(w^x_{ij}+w^y_{ij})^2+(w^{xy}_{ij}-w^{yx}_{ij})^2}.$$
--   There are no other local fields or graph restrictions. Also $W=\sum_{ij}w^z_{ij}$ and $\Gamma=3W+nh$. For $S\subseteq[n]$, define $Z_S=\prod_{i\in S}Z_i$ and $f_S(t)=\langle Z_S(0)Z_S(t)\rangle_\beta-\langle Z_S\rangle_\beta^2$. The empty product is the identity. The explicit decay constants are $C_\star=\max(n,6\beta W)$, $C_T=48(\beta\Gamma^2+W)$, $G=2\max(C_T,\Gamma,h,1)$ and $K=256C_\star G/h+2$. These definitions retain the whole coefficient class and compute every quantity from its physical data.
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Spectral gap of Lee-Yang Hamiltonians, STOC 2027 submission #575 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/575.pdf, pp. 4–6, Definition 1, Eqs. (1)–(2), (6)–(7), (11); p. 10, Eq. (30)

import Mathlib
import Definitions.Def_DrezetGHZ_Quantum
import Definitions.Def_LeeYangGap_SpectralGap_MatrixTools
open scoped BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false
noncomputable section

namespace LeeYangGap.SpectralGap
abbrev Config (n : ℕ) := Fin n → Fin 2
abbrev QOp (n : ℕ) := Operator (Config n)

/-- Identity on all tensor factors except the chosen site. -/
def atSite {n : ℕ} (i : Fin n) (A : Operator (Fin 2)) : QOp n :=
  fun x y => A (x i) (y i) * ∏ j : Fin n, if j = i then 1 else if x j = y j then 1 else 0

def X {n : ℕ} (i : Fin n) : QOp n := atSite i DrezetGHZ.pauliX
def Y {n : ℕ} (i : Fin n) : QOp n := atSite i DrezetGHZ.pauliY
def Z {n : ℕ} (i : Fin n) : QOp n := atSite i DrezetGHZ.pauliZ

/-- Ordered endpoints of a genuine two-site interaction; all coefficients real. -/
structure Bond (n : ℕ) where
  left : Fin n
  right : Fin n
  distinct : left ≠ right
  wz : ℝ
  wx : ℝ
  wy : ℝ
  wxy : ℝ
  wyx : ℝ

/-- Definition 1, Eq. (2); no analytic or spectral condition is bundled here. -/
def Bond.Admissible {n : ℕ} (b : Bond n) : Prop :=
  (1 / 2 : ℝ) * Real.sqrt ((b.wx - b.wy)^2 + (b.wxy + b.wyx)^2) +
  (1 / 2 : ℝ) * Real.sqrt ((b.wx + b.wy)^2 + (b.wxy - b.wyx)^2) ≤ b.wz

/-- The source's Eq. (1), with both independent cross couplings. -/
def bondHamiltonian {n : ℕ} (b : Bond n) : QOp n :=
  (-b.wz : ℂ) • (Z b.left * Z b.right) +
  (b.wx : ℂ) • (X b.left * X b.right) +
  (b.wy : ℂ) • (Y b.left * Y b.right) +
  (b.wxy : ℂ) • (X b.left * Y b.right) +
  (b.wyx : ℂ) • (Y b.left * X b.right)

/-- Finite ordered bond list; repeated pairs and zero coefficients allowed. -/
abbrev System (n : ℕ) := List (Bond n)
def IsLeeYang {n : ℕ} (B : System n) : Prop := ∀ b ∈ B, b.Admissible
def hamiltonian {n : ℕ} (B : System n) : QOp n := (B.map bondHamiltonian).sum
def fieldSum (n : ℕ) : QOp n := ∑ i : Fin n, Z i
def fieldHamiltonian {n : ℕ} (B : System n) (h : ℝ) : QOp n :=
  hamiltonian B - (h : ℂ) • fieldSum n
def weight {n : ℕ} (B : System n) : ℝ := (B.map Bond.wz).sum
def gamma {n : ℕ} (B : System n) (h : ℝ) : ℝ := 3 * weight B + n * h

/-- The product of diagonal Z operators, including the identity for the empty set. -/
def zProduct {n : ℕ} (S : Finset (Fin n)) : QOp n :=
  Matrix.diagonal (fun x => ∏ i ∈ S, if x i = 0 then (1 : ℂ) else -1)

def connected {n : ℕ} (B : System n) (h β : ℝ) (S : Finset (Fin n)) (t : ℝ) : ℂ :=
  twoPoint (fieldHamiltonian B h) (zProduct S) (zProduct S) β t -
    (mean (fieldHamiltonian B h) (zProduct S) β)^2

def cStar {n : ℕ} (B : System n) (β : ℝ) : ℝ := max n (6 * β * weight B)
def cT {n : ℕ} (B : System n) (h β : ℝ) : ℝ := 48 * (β * (gamma B h)^2 + weight B)
def decayG {n : ℕ} (B : System n) (h β : ℝ) : ℝ :=
  2 * max (max (cT B h β) (gamma B h)) (max h 1)
def decayK {n : ℕ} (B : System n) (h β : ℝ) : ℝ :=
  256 * cStar B β * decayG B h β / h + 2
end LeeYangGap.SpectralGap


