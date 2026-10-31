-- Prove2me | Definitions.Def_IndefPOMFG_Coeffs
-- name    : IndefPOMFG_Coeffs
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:50.159481+00:00
-- url     : https://prove2.me/theorems/8087e938-a914-484d-a3b4-905379ceff0d
-- title:
--   Model data of the indefinite LQ partially observed mean-field game and Assumptions (H1)–(H2)
-- statement:
--   The model of Chen–Nie–Wu is driven by deterministic, time-dependent coefficients on a horizon $[0,T]$. The state of each agent lives in $\mathbb R^n$, controls in $\mathbb R^m$, and the individual noises $W^i,\bar W^i$ are $d$-dimensional.
--
--   The **data** consist of the state coefficients $A,\bar A,D,\bar D\in\mathbb R^{n\times n}$, $B,\bar B,F,\bar F\in\mathbb R^{n\times m}$, $b,\bar b\in\mathbb R^n$, $\sigma,\bar\sigma\in\mathbb R^{n\times d}$; the private-observation coefficients $G,\bar G\in\mathbb R^{n\times n}$, $H,\bar H\in\mathbb R^{n\times m}$, $\tilde b\in\mathbb R^n$, $\tilde\sigma\in\mathbb R^{n\times d}$; the common-observation coefficients $I,\check b,\check\sigma\in\mathbb R$; the initial state $x\in\mathbb R^n$; and the cost weights $Q,R,S,q,r,L_T,l_T$ and constants $\alpha_1,\alpha_2,\alpha_3,\beta_1,\beta_2$.
--
--   **Assumption (H1).** $A,\bar A,D,\bar D,G,\bar G,b,\bar b,\tilde b,B,\bar B,F,\bar F,H,\bar H,I,\check b,\check\sigma$ are uniformly bounded on $[0,T]$, $\sigma,\bar\sigma,\tilde\sigma$ are square integrable on $[0,T]$, and $\check\sigma$ is non-degenerate.
--
--   **Assumption (H2).** $Q$ and $R$ are bounded and symmetric ($Q\in\mathbb S^n$, $R\in\mathbb S^m$), $S,q,r$ are bounded, $L_T\in\mathbb S^n$, $l_T\in\mathbb R^n$. No sign condition is imposed on $Q$, $R$ or $L_T$: the problem is **indefinite**.
--
--   The module also fixes the notation used throughout: $M\gg0$ (uniformly positive definite: $\langle M_tv,v\rangle\ge\lambda_0|v|^2$ for all $t\in[0,T]$), the quadratic-form order $M\ge0$, and absolutely continuous functions $P_t=P_0+\int_0^t\dot P_s\,ds$.
--
--   **Formalization Note** $L^\infty([0,T];\cdot)$ is the paper's "deterministic uniformly bounded functions" (p.5), taken Borel. "$\check\sigma$ non-degenerate" is read as $|\check\sigma_t|\ge\kappa>0$ for all $t\in[0,T]$. (H2) prints $q\in l^\infty$, read as $L^\infty$.
-- source:
--   Chen, Nie & Wu, Indefinite Linear-Quadratic Partially Observed Mean-Field Game, arXiv:2508.01568v1, §2.3 p.5 (notation), (H1) p.6, (H2) p.7

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal Matrix

namespace IndefPOMFG

/-- `M ∈ L^∞([0, T]; ℝ^{k×l})` in the paper's sense (p.5: "deterministic uniformly bounded
functions"): every entry is a Borel function of time and `|M_t(i, j)| ≤ K` for every `t ∈ [0, T]`.
Chen–Nie–Wu, arXiv:2508.01568v1, §2.3, p.5.

**Formalization Note** Time is `ℝ≥0`; only `[0, T]` enters. Borel measurability fixes a
representative, so that coefficient-times-process integrands are progressively measurable. -/
def MatBdd {k l : ℕ} (T : ℝ≥0) (M : ℝ≥0 → Matrix (Fin k) (Fin l) ℝ) : Prop :=
  (∀ i j, Measurable fun s => M s i j) ∧ ∃ K : ℝ, ∀ s ≤ T, ∀ i j, |M s i j| ≤ K

/-- `v ∈ L^∞([0, T]; ℝᵏ)` (uniformly bounded Borel vector function), p.5. -/
def VecBdd {k : ℕ} (T : ℝ≥0) (v : ℝ≥0 → Fin k → ℝ) : Prop :=
  (∀ i, Measurable fun s => v s i) ∧ ∃ K : ℝ, ∀ s ≤ T, ∀ i, |v s i| ≤ K

/-- `f ∈ L^∞([0, T]; ℝ)` (uniformly bounded Borel scalar function), p.5. -/
def ScalBdd (T : ℝ≥0) (f : ℝ≥0 → ℝ) : Prop :=
  Measurable f ∧ ∃ K : ℝ, ∀ s ≤ T, |f s| ≤ K

/-- `M ∈ L²([0, T]; ℝ^{k×l})`: Borel entries, each square integrable on `[0, T]`. (H1), p.6. -/
def MatL2 {k l : ℕ} (T : ℝ≥0) (M : ℝ≥0 → Matrix (Fin k) (Fin l) ℝ) : Prop :=
  (∀ i j, Measurable fun s => M s i j) ∧
    ∀ i j, MemLp (fun s : ℝ => M s.toNNReal i j) 2 (volume.restrict (Icc (0 : ℝ) T))

/-- `M ≫ 0` (p.5): uniformly positive definite on `[0, T]`, i.e. there is `λ₀ > 0` with
`⟨M_t v, v⟩ ≥ λ₀ |v|²` for every `t ∈ [0, T]` and every `v`. -/
def UnifPD {k : ℕ} (T : ℝ≥0) (M : ℝ≥0 → Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ s ≤ T, ∀ v : Fin k → ℝ, lam₀ * (v ⬝ᵥ v) ≤ v ⬝ᵥ (M s *ᵥ v)

/-- `M ≥ 0` as a quadratic form: `⟨M v, v⟩ ≥ 0` for every `v` (for a symmetric `M` this is
positive semidefiniteness, p.5).

**Formalization Note** Stated as a quadratic form so that it also applies to the
compensated weights of (23), which involve the derivative `Ṗ` and are symmetric only almost
everywhere. -/
def QNonneg {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) : Prop :=
  ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (M *ᵥ v)

/-- `P` is absolutely continuous on `[0, T]` with derivative `Ṗ`: `Ṗ` is integrable on `[0, T]`
and `P_t = P_0 + ∫₀ᵗ Ṗ_s ds` for every `t ∈ [0, T]` (componentwise). This is the form of
`Υ([0, T]; 𝕊ⁿ)` (p.10) and of the solutions of (34)–(36) (p.23: "absolutely continuous
functions"). -/
def IsACRep {ι : Type*} (T : ℝ≥0) (P Pdot : ℝ≥0 → ι → ℝ) : Prop :=
  (∀ k, IntegrableOn (fun s : ℝ => Pdot s.toNNReal k) (Icc (0 : ℝ) T)) ∧
    ∀ t ≤ T, ∀ k, P t k = P 0 k + ∫ s in Icc (0 : ℝ) t, Pdot s.toNNReal k

/-- `IsACRep` for matrix-valued functions, entrywise. -/
def IsACMat {k l : ℕ} (T : ℝ≥0) (P Pdot : ℝ≥0 → Matrix (Fin k) (Fin l) ℝ) : Prop :=
  IsACRep T (fun t (ij : Fin k × Fin l) => P t ij.1 ij.2) (fun t ij => Pdot t ij.1 ij.2)

/-- The data of the model (2)–(5) (p.3): horizon `T`, state dimension `n`, control dimension `m`,
dimension `d` of the individual noises `Wⁱ, W̄ⁱ`, the coefficients of the state (2), of the
private observation (3) and of the common observation (4), the initial state `x`, and the
weights of the cost (5).

Field names: `Ab = Ā`, `Db = D̄`, `Gb = Ḡ`, `Bb = B̄`, `Fb = F̄`, `Hb = H̄`, `bb = b̄`,
`bt = b̃`, `σb = σ̄`, `σt = σ̃`, `bc = b̌`, `σc = σ̌`, `LT = L_T`, `lT = l_T`. -/
structure Coeffs (n m d : ℕ) where
  T : ℝ≥0
  A : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  Ab : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  D : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  Db : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  G : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  Gb : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  b : ℝ≥0 → Fin n → ℝ
  bb : ℝ≥0 → Fin n → ℝ
  bt : ℝ≥0 → Fin n → ℝ
  σ : ℝ≥0 → Matrix (Fin n) (Fin d) ℝ
  σb : ℝ≥0 → Matrix (Fin n) (Fin d) ℝ
  σt : ℝ≥0 → Matrix (Fin n) (Fin d) ℝ
  B : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ
  Bb : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ
  F : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ
  Fb : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ
  H : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ
  Hb : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ
  I : ℝ≥0 → ℝ
  bc : ℝ≥0 → ℝ
  σc : ℝ≥0 → ℝ
  x : Fin n → ℝ
  Q : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ
  R : ℝ≥0 → Matrix (Fin m) (Fin m) ℝ
  S : ℝ≥0 → Matrix (Fin n) (Fin m) ℝ
  q : ℝ≥0 → Fin n → ℝ
  r : ℝ≥0 → Fin m → ℝ
  LT : Matrix (Fin n) (Fin n) ℝ
  lT : Fin n → ℝ
  α₁ : ℝ
  α₂ : ℝ
  α₃ : ℝ
  β₁ : ℝ
  β₂ : ℝ

variable {n m d : ℕ}

/-- Assumption (H1), p.6: `A, Ā, D, D̄, G, Ḡ ∈ L^∞([0, T]; ℝ^{n×n})`, `b, b̄, b̃ ∈ L^∞([0, T]; ℝⁿ)`,
`σ, σ̄, σ̃ ∈ L²([0, T]; ℝ^{n×d})`, `B, B̄, F, F̄, H, H̄ ∈ L^∞([0, T]; ℝ^{n×m})`,
`I, b̌, σ̌ ∈ L^∞([0, T]; ℝ)`, `σ̌` non-degenerate, `x` a constant.

**Formalization Note** "σ̌ is non-degenerate" is read as `|σ̌_t| ≥ κ > 0` for every
`t ∈ [0, T]` (the scalar case of [19, Thm 7.16], which the paper invokes on p.3 to get
`𝓕^θ = 𝓕^{W⁰}`). -/
structure H1 (c : Coeffs n m d) : Prop where
  A : MatBdd c.T c.A
  Ab : MatBdd c.T c.Ab
  D : MatBdd c.T c.D
  Db : MatBdd c.T c.Db
  G : MatBdd c.T c.G
  Gb : MatBdd c.T c.Gb
  b : VecBdd c.T c.b
  bb : VecBdd c.T c.bb
  bt : VecBdd c.T c.bt
  σ : MatL2 c.T c.σ
  σb : MatL2 c.T c.σb
  σt : MatL2 c.T c.σt
  B : MatBdd c.T c.B
  Bb : MatBdd c.T c.Bb
  F : MatBdd c.T c.F
  Fb : MatBdd c.T c.Fb
  H : MatBdd c.T c.H
  Hb : MatBdd c.T c.Hb
  I : ScalBdd c.T c.I
  bc : ScalBdd c.T c.bc
  σc : ScalBdd c.T c.σc
  σc_nondeg : ∃ κ : ℝ, 0 < κ ∧ ∀ s ≤ c.T, κ ≤ |c.σc s|

/-- Assumption (H2), p.7: `Q ∈ L^∞([0, T]; 𝕊ⁿ)`, `R ∈ L^∞([0, T]; 𝕊ᵐ)`, `S ∈ L^∞([0, T]; ℝ^{n×m})`,
`q ∈ L^∞([0, T]; ℝⁿ)` (printed "l^∞"), `r ∈ L^∞([0, T]; ℝᵐ)`, `L_T ∈ 𝕊ⁿ`, `l_T ∈ ℝⁿ`; the
`α`'s and `β`'s are constants. No sign condition is imposed on `Q, R, L_T` (Remark 3.4). -/
structure H2 (c : Coeffs n m d) : Prop where
  Q : MatBdd c.T c.Q
  Q_symm : ∀ s ≤ c.T, (c.Q s).IsSymm
  R : MatBdd c.T c.R
  R_symm : ∀ s ≤ c.T, (c.R s).IsSymm
  S : MatBdd c.T c.S
  q : VecBdd c.T c.q
  r : VecBdd c.T c.r
  LT_symm : c.LT.IsSymm

end IndefPOMFG


