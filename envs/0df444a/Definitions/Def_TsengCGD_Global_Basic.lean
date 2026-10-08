-- Prove2me | Definitions.Def_TsengCGD_Global_Basic
-- name    : TsengCGD_Global_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:00.48832+00:00
-- url     : https://prove2.me/theorems/dcbb9815-8541-4c69-894a-f3d5b03c01e0
-- title:
--   Problem (1), direction (6), the CGD method, Armijo rule (9)–(10), index rules (11), (14), (16), block separability (20), and Assumption 1
-- statement:
--   Let $D=\operatorname{dom}P$ be the effective domain of a proper closed convex penalty $P$, and let $f$ be continuously differentiable on an open neighborhood of $D$. For $c>0$, define the composite objective, on $D$, by
--
--   $$F_c(x)=f(x)+cP(x).$$
--
--   The bundle defines the exact coordinate-restricted quadratic direction $d_H(x;\mathcal J)$ from (6), the resulting CGD iteration, the Armijo decrease $\Delta$ and first accepted geometric trial from (9)–(10), stationary points through one-sided directional derivatives, the generalized Gauss–Seidel rule (11), and the two Gauss–Southwell rules (14) and (16). It also defines block separability (20), uniform matrix bounds of Assumption 1, and the Rayleigh-quotient extrema used in Lemma 3. These objects provide the common model for the global-convergence statements.
--
--   **Formalization Note** Vectors have the Euclidean norm and coordinates in `Fin n`; the paper numbers the same coordinates from one. The pair $(D,P)$ gives $+\infty$ outside $D$, so every finite objective comparison requires membership in $D$. The exact direction uses a choice among minimizers and is used only for valid inputs. Armijo takes the first accepted exponent. Eigenvalue extrema use Rayleigh quotients on nonempty coordinate blocks.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), pp. 388–399, §§1–4, equations (1), (6), (9)–(16), (20), Assumption 1, https://doi.org/10.1007/s10107-007-0170-0

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep

namespace TsengCGD.Global

open Filter Topology Finset Matrix
open scoped RealInnerProductSpace

variable {n : ℕ}

abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The hypotheses of problem (1). -/
structure Standing (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ) (c : ℝ) : Prop where
  c_pos : 0 < c
  properConvexLsc : ProxNewton.Inexact.IsProperClosedConvex D P
  smooth : ∃ U : Set (Vec n), IsOpen U ∧ D ⊆ U ∧ ContDiffOn ℝ 1 f U

/-- Finite value of F_c on the effective domain D. -/
def Fc (f : Vec n → ℝ) (P : Vec n → ℝ) (c : ℝ) (x : Vec n) : ℝ :=
  f x + c * P x

/-- Quadratic form dᵀHd. -/
def qf (H : Matrix (Fin n) (Fin n) ℝ) (d : Vec n) : ℝ :=
  (WithLp.ofLp d) ⬝ᵥ (H *ᵥ WithLp.ofLp d)

def SupportedOn (J : Finset (Fin n)) (d : Vec n) : Prop :=
  ∀ j, j ∉ J → d j = 0

noncomputable def subObj (f : Vec n → ℝ) (P : Vec n → ℝ) (c : ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (x d : Vec n) : ℝ :=
  ⟪gradient f x, d⟫ + qf H d / 2 + c * P (x + d)

def IsDir (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ) (c : ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) (J : Finset (Fin n)) (d : Vec n) : Prop :=
  SupportedOn J d ∧ x + d ∈ D ∧
    ∀ d', SupportedOn J d' → x + d' ∈ D → subObj f P c H x d ≤ subObj f P c H x d'

noncomputable def dH (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ) (c : ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) (J : Finset (Fin n)) : Vec n :=
  Classical.epsilon (IsDir f D P c H x J)

noncomputable def dI (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ) (c : ℝ)
    (x : Vec n) : Vec n := dH f D P c 1 x Finset.univ

noncomputable def qH (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ) (c : ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (x : Vec n) (J : Finset (Fin n)) : ℝ :=
  subObj f P c H x (dH f D P c H x J) - c * P x

noncomputable def Delta (f : Vec n → ℝ) (P : Vec n → ℝ) (c γ : ℝ)
    (H : Matrix (Fin n) (Fin n) ℝ) (x d : Vec n) : ℝ :=
  ⟪gradient f x, d⟫ + γ * qf H d + c * P (x + d) - c * P x

/-- Limiting directional derivative of the extended-valued F_c is nonnegative in every direction. -/
def IsStationary (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c : ℝ) (x : Vec n) : Prop :=
  x ∈ D ∧ ∀ d : Vec n, ∀ ε : ℝ, 0 < ε →
    ∀ᶠ α in 𝓝[>] (0 : ℝ), x + α • d ∈ D →
      -ε ≤ (Fc f P c (x + α • d) - Fc f P c x) / α

/-- A run uses the exact direction from (6) and any positive step size. -/
structure IsCGDRun (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ) (c : ℝ)
    (J : ℕ → Finset (Fin n)) (H : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x d : ℕ → Vec n) (α : ℕ → ℝ) : Prop where
  start : x 0 ∈ D
  iterate_mem : ∀ k, x k ∈ D
  J_nonempty : ∀ k, (J k).Nonempty
  H_posDef : ∀ k, (H k).PosDef
  dir : ∀ k, IsDir f D P c (H k) (x k) (J k) (d k)
  step_pos : ∀ k, 0 < α k
  step : ∀ k, x (k + 1) = x k + α k • d k

structure ArmijoParams (β σ γ : ℝ) : Prop where
  beta_pos : 0 < β
  beta_lt_one : β < 1
  sigma_pos : 0 < σ
  sigma_lt_one : σ < 1
  gamma_nonneg : 0 ≤ γ
  gamma_lt_one : γ < 1

def ArmijoTest (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c σ γ : ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (x d : Vec n) (a : ℝ) : Prop :=
  x + a • d ∈ D ∧
    Fc f P c (x + a • d) ≤ Fc f P c x + a * σ * Delta f P c γ H x d

/-- First accepted exponent j, equivalently the largest Armijo trial step. -/
def IsArmijo (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ)
    (c β σ γ : ℝ) (αinit : ℕ → ℝ)
    (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (x d : ℕ → Vec n) (α : ℕ → ℝ) : Prop :=
  ArmijoParams β σ γ ∧ (∀ k, 0 < αinit k) ∧
    ∀ k, ∃ j : ℕ, α k = αinit k * β ^ j ∧
      ArmijoTest f D P c σ γ (H k) (x k) (d k) (α k) ∧
      ∀ j' < j, ¬ ArmijoTest f D P c σ γ (H k) (x k) (d k) (αinit k * β ^ j')

/-- Assumption 1, represented by quadratic-form bounds. -/
def Assumption1 (H : ℕ → Matrix (Fin n) (Fin n) ℝ) (lam lamBar : ℝ) : Prop :=
  0 < lam ∧ lam ≤ lamBar ∧
    ∀ k (z : Vec n), lam * ‖z‖ ^ 2 ≤ qf (H k) z ∧
      qf (H k) z ≤ lamBar * ‖z‖ ^ 2

/-- Rule (11): every T consecutive coordinate sets cover all coordinates. -/
def GaussSeidel (J : ℕ → Finset (Fin n)) : Prop :=
  ∃ T : ℕ, 1 ≤ T ∧ ∀ k, (Finset.range T).biUnion (fun i => J (k + i)) = Finset.univ

/-- The infinity norm of a direction. -/
def supNorm (d : Vec n) : ℝ := ‖(WithLp.ofLp d : Fin n → ℝ)‖

def IsPosDiag (Dm : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Dm.PosDef ∧ ∀ i j, i ≠ j → Dm i j = 0

def GaussSouthwellR (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ) (c : ℝ)
    (J : ℕ → Finset (Fin n)) (Dk : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x : ℕ → Vec n) (υ : ℝ) : Prop :=
  0 < υ ∧ υ ≤ 1 ∧ ∀ k, IsPosDiag (Dk k) ∧
    υ * supNorm (dH f D P c (Dk k) (x k) Finset.univ) ≤
      supNorm (dH f D P c (Dk k) (x k) (J k))

def GaussSouthwellQ (f : Vec n → ℝ) (D : Set (Vec n)) (P : Vec n → ℝ) (c : ℝ)
    (J : ℕ → Finset (Fin n)) (Dk : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (x : ℕ → Vec n) (υ : ℝ) : Prop :=
  0 < υ ∧ υ ≤ 1 ∧ ∀ k, IsPosDiag (Dk k) ∧
    qH f D P c (Dk k) (x k) (J k) ≤ υ * qH f D P c (Dk k) (x k) Finset.univ

/-- The two extended-valued block functions in (20), expressed as domain-value pairs. -/
def IsBlockSepWitness (D : Set (Vec n)) (P : Vec n → ℝ) (J : Finset (Fin n))
    (DJ : Set (Vec n)) (PJ : Vec n → ℝ) (DJC : Set (Vec n)) (PJC : Vec n → ℝ) : Prop :=
  ProxNewton.Inexact.IsProperClosedConvex DJ PJ ∧
  ProxNewton.Inexact.IsProperClosedConvex DJC PJC ∧
  (∀ x y : Vec n, (∀ j ∈ J, x j = y j) → ((x ∈ DJ ↔ y ∈ DJ) ∧ PJ x = PJ y)) ∧
  (∀ x y : Vec n, (∀ j, j ∉ J → x j = y j) → ((x ∈ DJC ↔ y ∈ DJC) ∧ PJC x = PJC y)) ∧
  (∀ x, x ∈ D ↔ (x ∈ DJ ∧ x ∈ DJC)) ∧
  ∀ x ∈ D, P x = PJ x + PJC x

def BlockSeparable (D : Set (Vec n)) (P : Vec n → ℝ) (J : Finset (Fin n)) : Prop :=
  ∃ DJ PJ DJC PJC, IsBlockSepWitness D P J DJ PJ DJC PJC

/-- Rayleigh quotient extrema of the principal submatrix. -/
noncomputable def lamMax (A : Matrix (Fin n) (Fin n) ℝ) (J : Finset (Fin n)) : ℝ :=
  sSup {r | ∃ u : Vec n, SupportedOn J u ∧ u ≠ 0 ∧ r = qf A u / ‖u‖ ^ 2}

noncomputable def lamMin (A : Matrix (Fin n) (Fin n) ℝ) (J : Finset (Fin n)) : ℝ :=
  sInf {r | ∃ u : Vec n, SupportedOn J u ∧ u ≠ 0 ∧ r = qf A u / ‖u‖ ^ 2}

/-- Extremes of the generalized spectrum of (Ht_JJ,H_JJ). -/
noncomputable def genMax (H Ht : Matrix (Fin n) (Fin n) ℝ)
    (J : Finset (Fin n)) : ℝ :=
  sSup {r | ∃ u : Vec n, SupportedOn J u ∧ u ≠ 0 ∧ r = qf Ht u / qf H u}

noncomputable def genMin (H Ht : Matrix (Fin n) (Fin n) ℝ)
    (J : Finset (Fin n)) : ℝ :=
  sInf {r | ∃ u : Vec n, SupportedOn J u ∧ u ≠ 0 ∧ r = qf Ht u / qf H u}

end TsengCGD.Global


