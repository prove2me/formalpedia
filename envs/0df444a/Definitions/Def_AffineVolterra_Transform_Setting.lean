-- Prove2me | Definitions.Def_AffineVolterra_Transform_Setting
-- name    : AffineVolterra_Transform_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:54:52.682988+00:00
-- url     : https://prove2.me/theorems/05f44032-25be-4be3-91cb-fa54fa83e0e0
-- title:
--   §4 — affine Volterra coefficients and process; Riccati–Volterra equation (4.3)
-- statement:
--   Fix a positive dimension $d$. The affine covariance and drift are $a(x)=A^0+\sum_i x_iA^i$ and $b(x)=b^0+\sum_i x_i b^i$, with symmetric $A^i$ and with $B$ having $b^i$ as its columns. For a complex row $u$, the row $A(u)$ has entries $uA^iu^\top$; there is no complex conjugation.
--
--   An affine Volterra process is a continuous, adapted, $E$-valued solution of
--
--   $$
--   X_t=x_0+\int_0^t K(t-s)b(X_s)\,ds+\int_0^t K(t-s)\sigma(X_s)\,dW_s,
--   $$
--
--   on a usual stochastic basis, where $K$ is locally square integrable, $a(x)$ is positive semidefinite on $E$, and the continuous coefficient $\sigma$ satisfies $\sigma(x)\sigma(x)^\top=a(x)$ there. The definition also records the $L^2$ Riccati–Volterra equation (4.3), its resolvent form (4.8), the terminal payoff, and the process $Y$ defined by (4.4)–(4.5).
--
--   **Formalization Note** The Itô terms are witnessed by Brownian integral relations, so no stochastic integral is an unconstrained variable. Deterministic drift integrals are required to be integrable. Process time is $\mathbb R_{\ge0}$ and kernel time is $\mathbb R$. Equalities of the stochastic equation hold almost surely for each fixed time; $Y$ is the continuous adapted version of its Itô construction.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, (1.1), p. 2; (4.1), Definition 4.1, p. 17; (4.3)–(4.5), (4.8), p. 19

import Mathlib
import Definitions.Def_AffineVolterra_Transform_Core
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsSourceLocalMartingale
import Definitions.Def_AffineVolterra_Existence_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace AffineVolterra.Transform

/-- The coefficients A⁰,…,Aᵈ and b⁰,…,bᵈ of (4.1). -/
structure AffineData (d : ℕ) where
  A : Fin (d + 1) → Matrix (Fin d) (Fin d) ℝ
  bv : Fin (d + 1) → RVec d
  A_symm : ∀ i j k, A i j k = A i k j

def affA {d : ℕ} (D : AffineData d) (x : State d) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k => D.A 0 j k + ∑ i, x i * D.A (Fin.succ i) j k

def affB {d : ℕ} (D : AffineData d) (x : State d) : RVec d :=
  fun j => D.bv 0 j + ∑ i, x i * D.bv (Fin.succ i) j

/-- B has b¹,…,bᵈ as columns. -/
def Bmat {d : ℕ} (D : AffineData d) : Matrix (Fin d) (Fin d) ℝ :=
  fun j i => D.bv (Fin.succ i) j

/-- A(u) uses ordinary transpose, without complex conjugation. -/
def Aquad {d : ℕ} (D : AffineData d) (u : CVec d) : CVec d :=
  fun i => ∑ j, ∑ k, u j * (D.A (Fin.succ i) j k : ℂ) * u k

def quad {d : ℕ} (u : CVec d) (M : Matrix (Fin d) (Fin d) ℝ) : ℂ :=
  ∑ i, ∑ j, u i * (M i j : ℂ) * u j

def pair {d : ℕ} (u : CVec d) (x : State d) : ℂ :=
  ∑ i, u i * (x i : ℂ)

def IsFBrownian {Ω : Type} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (W : ℝ≥0 → Ω → State d) : Prop :=
  EthierKurtz.IsStandardBrownian P W ∧
  (∀ t, Measurable[ℱ t] (W t)) ∧
  ∀ t, Indep (ℱ t)
    (MeasurableSpace.comap (fun ω (r : Set.Ici t) => W r.val ω - W t ω)
      inferInstance) P

/-- A fixed-terminal-time stochastic convolution is given by actual Brownian Itô relations. -/
def StochConv {Ω : Type} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (K : RKernel d)
    (σ : State d → Matrix (Fin d) (Fin d) ℝ)
    (W X : ℝ≥0 → Ω → State d)
    (J : ℝ≥0 → Fin d → Fin d → Fin d → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ t i j k, EthierKurtz.HasBrownianItoIntegral P ℱ
    (fun r ω => W r ω k)
    (fun r ω => if r < t then K ((t : ℝ) - (r : ℝ)) i j * σ (X r ω) j k else 0)
    (J t i j k)

/-- The version-wise stochastic Volterra equation (1.1). -/
def IsSolution {Ω : Type} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (K : RKernel d)
    (b : State d → RVec d) (σ : State d → Matrix (Fin d) (Fin d) ℝ)
    (x₀ : State d) (W X : ℝ≥0 → Ω → State d) : Prop :=
  (∀ t, Measurable[ℱ t] (X t)) ∧
  (∀ ω, Continuous (fun t => X t ω)) ∧
  (∀ (t : ℝ≥0) ω i j, IntervalIntegrable
    (fun s : ℝ => K ((t : ℝ) - s) i j * b (X s.toNNReal ω) j)
      volume 0 t.val) ∧
  ∃ J : ℝ≥0 → Fin d → Fin d → Fin d → ℝ≥0 → Ω → ℝ,
    StochConv P ℱ K σ W X J ∧
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ∀ i,
      X t ω i = x₀ i +
        (∑ j, ∫ s in (0 : ℝ)..t.val,
          K ((t : ℝ) - s) i j * b (X s.toNNReal ω) j) +
        ∑ j, ∑ k, J t i j k t ω

/-- Definition 4.1 together with the standing hypotheses at the start of §4. -/
def IsAffineVolterra {Ω : Type} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (K : RKernel d)
    (D : AffineData d) (σ : State d → Matrix (Fin d) (Fin d) ℝ)
    (E : Set (State d)) (x₀ : State d)
    (W X : ℝ≥0 → Ω → State d) : Prop :=
  0 < d ∧ KernelLpLoc 2 K ∧ AffineVolterra.Existence.IsUsualBasis P ℱ ∧ IsFBrownian P ℱ W ∧
  Continuous σ ∧
  (∀ x ∈ E, (∀ v : RVec d, 0 ≤ ∑ i, ∑ j, v i * affA D x i j * v j) ∧
    ∀ i j, (∑ k, σ x i k * σ x j k) = affA D x i j) ∧
  IsSolution P ℱ K (affB D) σ x₀ W X ∧
  (∀ᵐ ω ∂P, ∀ t, X t ω ∈ E) ∧
  (∀ᵐ ω ∂P, X 0 ω = x₀)

/-- The L² Riccati–Volterra equation (4.3), with integrable convolution terms. -/
def IsRiccati43 {d : ℕ} (K : RKernel d) (D : AffineData d)
    (T : ℝ) (u : CVec d) (f ψ : ℝ → CVec d) : Prop :=
  (∀ i, MemLp (fun t => f t i) 1 (volume.restrict (Set.Ioc 0 T))) ∧
  (∀ i, MemLp (fun t => ψ t i) 2 (volume.restrict (Set.Ioc 0 T))) ∧
  ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)),
    (∀ i j, IntegrableOn
      (fun s => (f s i + rowMul (ψ s) (Bmat D) i + (1 / 2 : ℂ) * Aquad D (ψ s) i) *
        (K (t - s) i j : ℂ)) (Set.Ioc 0 t)) ∧
    ψ t = rowMul u (K t) + rowKernelConv
      (fun s i => f s i + rowMul (ψ s) (Bmat D) i + (1 / 2 : ℂ) * Aquad D (ψ s) i) K t

/-- The resolvent version (4.8) of the same Riccati equation. -/
def IsRiccati48 {d : ℕ} (K R : RKernel d) (D : AffineData d)
    (T : ℝ) (u : CVec d) (f ψ : ℝ → CVec d) : Prop :=
  (∀ i, MemLp (fun t => f t i) 1 (volume.restrict (Set.Ioc 0 T))) ∧
  (∀ i, MemLp (fun t => ψ t i) 2 (volume.restrict (Set.Ioc 0 T))) ∧
  ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)),
    (∀ i j, IntegrableOn
      (fun s => (f s i + (1 / 2 : ℂ) * Aquad D (ψ s) i) *
        (EKernel K R (t - s) i j : ℂ)) (Set.Ioc 0 t)) ∧
    ψ t = rowMul u (EKernel K R t) + rowKernelConv
      (fun s i => f s i + (1 / 2 : ℂ) * Aquad D (ψ s) i) (EKernel K R) t

/-- The terminal payoff uX_T + (f * X)_T. -/
noncomputable def payoff {Ω : Type} {d : ℕ} (u : CVec d) (f : ℝ → CVec d)
    (X : ℝ≥0 → Ω → State d) (T : ℝ≥0) (ω : Ω) : ℂ :=
  pair u (X T ω) + ∑ i, ∫ s in (0 : ℝ)..T.val,
    f s i * (X (T.val - s).toNNReal ω i : ℂ)

/-- The deterministic initial value (4.5). -/
noncomputable def Yinitial {d : ℕ} (D : AffineData d) (x₀ : State d)
    (T : ℝ≥0) (u : CVec d) (f ψ : ℝ → CVec d) : ℂ :=
  pair u x₀ + ∫ s in (0 : ℝ)..T.val,
    pair (f s) x₀ + (∑ i, ψ s i * (affB D x₀ i : ℂ)) +
      (1 / 2 : ℂ) * quad (ψ s) (affA D x₀)

/-- Equation (4.4) with real and imaginary Itô integrals, using (4.5) for Y₀. -/
def IsY43 {Ω : Type} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω)
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (W X : ℝ≥0 → Ω → State d)
    (D : AffineData d) (σ : State d → Matrix (Fin d) (Fin d) ℝ)
    (x₀ : State d) (T : ℝ≥0) (u : CVec d) (f ψ : ℝ → CVec d)
    (Y : ℝ≥0 → Ω → ℂ) : Prop :=
  (∀ t, t ≤ T → Measurable[ℱ t] (Y t)) ∧
  (∀ ω, ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) ∧
  ∃ Jre Jim : Fin d → ℝ≥0 → Ω → ℝ,
    (∀ k, EthierKurtz.HasBrownianItoIntegral P ℱ (fun r ω => W r ω k)
      (fun r ω => if r ≤ T then
        (∑ j, ψ (T.val - (r : ℝ)) j * (σ (X r ω) j k : ℂ)).re else 0) (Jre k)) ∧
    (∀ k, EthierKurtz.HasBrownianItoIntegral P ℱ (fun r ω => W r ω k)
      (fun r ω => if r ≤ T then
        (∑ j, ψ (T.val - (r : ℝ)) j * (σ (X r ω) j k : ℂ)).im else 0) (Jim k)) ∧
    ∀ t : ℝ≥0, t ≤ T → ∀ᵐ ω ∂P,
      Y t ω = Yinitial D x₀ T u f ψ +
        (∑ k, ((Jre k t ω : ℂ) + Complex.I * (Jim k t ω : ℂ))) -
        (1 / 2 : ℂ) * (∫ s in (0 : ℝ)..t.val,
          quad (ψ (T.val - s)) (affA D (X s.toNNReal ω)))

end AffineVolterra.Transform


