-- Prove2me | Definitions.Def_QMCTied_Defs
-- name    : QMCTied_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T10:12:15.637386+00:00
-- url     : https://prove2.me/theorems/a36fba44-953c-4094-a81c-d497579d67e6
-- title:
--   Tied-entry semidefinite programs and an integer penalty supergradient iteration
-- statement:
--   An instance consists of $N\times N$ Gram matrices $\Gamma(\ell)_{ij}=s_{ij}\,\ell(c_{ij})$ whose entries are tied together in classes $c_{ij}$ with signs $s_{ij}\in\{-1,0,1\}$, the normalization $\ell(c_0)=1$, the constraint $\Gamma(\ell)\succeq0$ and an affine objective. The iteration keeps $\lambda=D\ell$ in integers inside the box $[-D,D]$. Each step forms $M=ND-D\Gamma(\ell)\succeq0$, the exact power $Q=M^{2K}$, and moves along the objective gradient plus, when the certified bound on $\lambda_{\min}(\Gamma)$ is negative, twice the class sums of $Q/\operatorname{tr}Q$. It also records the objective at an exactly feasible point obtained by mixing in a certified multiple of the identity.
-- source:
--   Supporting library for QuantumMaxCutEnergy.PauliSDP.uniform_value_lower_approximation_compiler (Prove2me Quantum Max-Cut campaign; level-k Pauli moment relaxation as in Gribling, Sinjorgo and Sotirov, arXiv:2504.11120, Section 2). Method: integer penalty supergradient iteration with matrix-power certificates.

import Mathlib
import Definitions.Def_QMCSub_LinAlg
import Definitions.Def_QMCSub_Iter

/-!
Semidefinite programs over Gram matrices whose entries are tied together in classes, and an
integer penalty supergradient iteration for them.

An instance has `N × N` Gram matrices `Γ(ℓ)[i,j] = sgn i j * ℓ (cls i j)` for a vector `ℓ` of
class values, the constraint `ℓ k0 = 1`, `Γ(ℓ) ⪰ 0`, and an affine objective. The iteration keeps
`lam = D * ℓ` in integers inside the box `[-D, D]`.
-/

namespace QMCTied
open Matrix
open scoped BigOperators

/-- A tied-entry SDP instance on `N × N` Gram matrices with classes `κ`. -/
structure Inst (N : ℕ) (κ : Type) where
  cls : Fin N → Fin N → κ
  sgn : Fin N → Fin N → ℤ
  k0 : κ
  Cs : Fin N → Fin N → ℚ
  c0 : ℚ

variable {N : ℕ} {κ : Type} [DecidableEq κ]

/-- Structural hypotheses on an instance. The objective is normalized. -/
structure Inst.Good (I : Inst N κ) : Prop where
  cls_symm : ∀ i j, I.cls i j = I.cls j i
  sgn_symm : ∀ i j, I.sgn i j = I.sgn j i
  sgn_abs : ∀ i j, |I.sgn i j| ≤ 1
  cls_diag : ∀ i j, I.cls i j = I.k0 ↔ i = j
  sgn_diag : ∀ i, I.sgn i i = 1
  Cs_diag : ∀ i, I.Cs i i = 0
  Cs_sum : ∑ i, ∑ j, |I.Cs i j| ≤ 3 / 2
  Cs_sgn : ∀ i j, I.Cs i j ≠ 0 → I.sgn i j ≠ 0
  c0_nonneg : 0 ≤ I.c0
  c0_le : I.c0 ≤ 1 / 2

/-- The Gram matrix of a vector of class values. -/
noncomputable def Gam (I : Inst N κ) (ℓ : κ → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j => (I.sgn i j : ℝ) * ℓ (I.cls i j)

/-- Feasibility: normalized and positive semidefinite. -/
def Feas (I : Inst N κ) (ℓ : κ → ℝ) : Prop := ℓ I.k0 = 1 ∧ (Gam I ℓ).PosSemidef

/-- The affine objective. -/
noncomputable def obj (I : Inst N κ) (ℓ : κ → ℝ) : ℝ :=
  (I.c0 : ℝ) + ∑ i, ∑ j, (I.Cs i j : ℝ) * ℓ (I.cls i j)

/-- Parameters of the iteration: grid `D`, step `eta` in grid units, exponent `K`,
`δ = 1 / dN`, and output resolution `D2`. -/
structure Par where
  D : ℤ
  eta : ℚ
  K : ℕ
  dN : ℕ
  D2 : ℕ

/-- `D * Γ(ℓ)` in integers. -/
def Ghat (I : Inst N κ) (lam : κ → ℤ) : Matrix (Fin N) (Fin N) ℤ :=
  Matrix.of fun i j => I.sgn i j * lam (I.cls i j)

/-- The shifted matrix `N D - D Γ(ℓ)`, positive semidefinite on the box. -/
def Mz (I : Inst N κ) (D : ℤ) (lam : κ → ℤ) : Matrix (Fin N) (Fin N) ℤ :=
  ((N : ℤ) * D) • (1 : Matrix (Fin N) (Fin N) ℤ) - Ghat I lam

def Qz (I : Inst N κ) (D : ℤ) (K : ℕ) (lam : κ → ℤ) : Matrix (Fin N) (Fin N) ℤ :=
  (Mz I D lam) ^ (2 * K)

def tau (I : Inst N κ) (D : ℤ) (K : ℕ) (lam : κ → ℤ) : ℤ := (Qz I D K lam).trace

/-- `tr(M^(2K+1))`, as an entrywise sum. -/
def rnum (I : Inst N κ) (D : ℤ) (K : ℕ) (lam : κ → ℤ) : ℤ :=
  ∑ i, ∑ j, Mz I D lam i j * Qz I D K lam i j

/-- The penalty is active when the certified upper bound on `λ_min(Γ)` is negative. -/
def active (I : Inst N κ) (D : ℤ) (K : ℕ) (lam : κ → ℤ) : Bool :=
  decide ((N : ℤ) * D * tau I D K lam < rnum I D K lam)

/-- Class sums of the objective coefficients. -/
def gC (I : Inst N κ) (k : κ) : ℚ := ∑ i, ∑ j, if I.cls i j = k then I.Cs i j else 0

/-- Class sums of the signed power matrix. -/
def gQ (I : Inst N κ) (D : ℤ) (K : ℕ) (lam : κ → ℤ) (k : κ) : ℤ :=
  ∑ i, ∑ j, if I.cls i j = k then I.sgn i j * Qz I D K lam i j else 0

/-- Rounding toward zero. -/
def rnd (q : ℚ) : ℤ := if q < 0 then -⌊-q⌋ else ⌊q⌋

def clampZ (D x : ℤ) : ℤ := max (-D) (min D x)

/-- The supergradient step for a class, in grid units, before rounding. -/
def stepv (I : Inst N κ) (P : Par) (lam : κ → ℤ) (k : κ) : ℚ :=
  P.eta * (gC I k +
    if active I P.D P.K lam then
      2 * (gQ I P.D P.K lam k : ℚ) / (tau I P.D P.K lam : ℚ) else 0)

/-- One step of the iteration. -/
def next (I : Inst N κ) (P : Par) (lam : κ → ℤ) : κ → ℤ :=
  fun k => if k = I.k0 then lam k else clampZ P.D (lam k + rnd (stepv I P lam k))

/-- The certified amount of the identity to mix in. -/
def aq (I : Inst N κ) (P : Par) (lam : κ → ℤ) : ℚ :=
  max 0 ((rnum I P.D P.K lam : ℚ) * ((P.dN : ℚ) + 1) /
    ((tau I P.D P.K lam : ℚ) * ((P.dN : ℚ) - 1)) - (N : ℚ) * (P.D : ℚ)) / (P.D : ℚ)

/-- The objective at the current point. -/
def objq (I : Inst N κ) (P : Par) (lam : κ → ℤ) : ℚ :=
  I.c0 + ∑ i, ∑ j, I.Cs i j * (lam (I.cls i j) : ℚ) / (P.D : ℚ)

/-- The objective at the repaired, exactly feasible point. -/
def valq (I : Inst N κ) (P : Par) (lam : κ → ℤ) : ℚ :=
  (objq I P lam + aq I P lam * I.c0) / (1 + aq I P lam)

def lam0 (I : Inst N κ) (P : Par) : κ → ℤ := fun k => if k = I.k0 then P.D else 0

def lamSeq (I : Inst N κ) (P : Par) (k : ℕ) : κ → ℤ := (next I P)^[k] (lam0 I P)

def bestStep (I : Inst N κ) (P : Par) (lam : κ → ℤ) (b : ℤ) : ℤ :=
  max b ⌊(P.D2 : ℚ) * max 0 (valq I P lam)⌋

/-- The best certified value so far, in units of `1 / D2`. -/
def bestSeq (I : Inst N κ) (P : Par) : ℕ → ℤ
  | 0 => 0
  | k + 1 => bestStep I P (lamSeq I P k) (bestSeq I P k)

end QMCTied


