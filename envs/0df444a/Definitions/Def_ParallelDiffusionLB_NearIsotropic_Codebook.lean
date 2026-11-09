-- Prove2me | Definitions.Def_ParallelDiffusionLB_NearIsotropic_Codebook
-- name    : ParallelDiffusionLB_NearIsotropic_Codebook
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:48.450303+00:00
-- url     : https://prove2.me/theorems/507da277-934c-4d0f-9c38-cddf3758461e
-- title:
--   Cube codebooks, information density, gates and public budgets
-- statement:
--   Write $V_m=\{-1,+1\}^m$, $U_m=\operatorname{Unif}(V_m)$, and for a finite nonempty codebook $S\subseteq V_m$ let $p_\tau^S=\operatorname{Unif}(S)*N(0,\tau^2I_m)$ and $q_\tau=U_m*N(0,\tau^2I_m)$. Let $s_\tau^S$ and $s_\tau^0$ be their scores. A random size-$n$ codebook is uniform among all $n$-element subsets, without replacement.
--
--   For $y\in V_m$ and $x\in\mathbb R^m$, set $L_\tau(y,x)=\varphi_\tau(x-y)/q_\tau(x)$, $\ell_\tau=\log L_\tau$, and $\alpha_\tau=m^{-1}E\ell_\tau(Y,Y+\tau Z)$ under independent $Y\sim U_m$ and standard Gaussian $Z$. Put $F_\tau(S)=E_{p_\tau^S}\|s_\tau^S-s_\tau^0\|^2$ and $\tilde\tau=\tau\sqrt{1-\gamma^2/m^2}$.
--
--   For public $d,B,P,\varepsilon,\rho$, define
--   $$\delta=\frac{\rho^2}{100Pd^3},\quad\eta=\frac{\varepsilon}{8B},\quad\zeta(\tau)=\min\left\{\frac{\rho^2}{100},\frac{\eta^2\tau^2}{16m}\right\},\quad t_\tau=m\alpha_\tau-\tau^{-1}\sqrt{8m\log(1/\zeta(\tau))}.$$
--   The gate is $a_\tau^S(x)=\min\{1,\max\{0,1+\max_{y\in S}\ell_\tau(y,x)-t_\tau\}\}$. The local answer $b_\tau^S$ is $s_\tau^0$ if $F_\tau(S)\le\eta^2/(4\tau^2)$ and $s_\tau^S$ otherwise. The thresholds are $\kappa^-(\tau)=(t_\tau-\log(1/\delta)-1)/m$ and $\kappa^+(\tau)=\alpha_{\tilde\tau}+H/m+\tilde\tau^{-1}\sqrt{8H/m}$. The recognizing event is $E(S)=\{x:a_\gamma^S(x)=1\}$.
--
--   These are the one-block objects of the appendix, not alternative oracle assumptions. The four explicit sufficient bounds on $H$ are grouped in `LargeH`.
-- source:
--   Yimeng Wang, Yiwen Kou, Lower Bounds for Parallel Diffusion Sampling, STOC 2027 submission #660 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/660.pdf, (12)–(13), p. 18; Appendix A.2, pp. 20–21; (27)–(29), p. 23; (38)–(39), p. 25; (45), p. 27

import Definitions.Def_ParallelDiffusionLB_NearIsotropic_Gaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

namespace ParallelDiffusionLB.NearIsotropic

/-- Boolean labels enumerate the `2^m` distinct signed cube vertices. -/
abbrev Cube (m : ℕ) := Fin m → Bool

def vertex {m : ℕ} (y : Cube m) : E m :=
  WithLp.toLp 2 (fun i => if y i then 1 else -1)

def cubePrior (m : ℕ) : Measure (E m) :=
  (uniformFinset (Finset.univ : Finset (Cube m))).map vertex

def codePrior {m : ℕ} (S : Finset (Cube m)) : Measure (E m) :=
  (uniformFinset S).map vertex

def blockLaw {m : ℕ} (S : Finset (Cube m)) (τ : ℝ) : Measure (E m) :=
  smoothLaw (codePrior S) τ

def nullLaw (m : ℕ) (τ : ℝ) : Measure (E m) := smoothLaw (cubePrior m) τ

def blockScore {m : ℕ} (S : Finset (Cube m)) (τ : ℝ) : E m → E m :=
  score (codePrior S) τ

def nullScore (m : ℕ) (τ : ℝ) : E m → E m := score (cubePrior m) τ

def likelihood {m : ℕ} (τ : ℝ) (y : Cube m) (x : E m) : ℝ :=
  gaussianDensity m τ (x - vertex y) / smoothDensity (cubePrior m) τ x

def logLikelihood {m : ℕ} (τ : ℝ) (y : Cube m) (x : E m) : ℝ :=
  Real.log (likelihood τ y x)

/-- Per-coordinate expectation of the planted information density (p. 20). -/
def informationLevel (m : ℕ) (τ : ℝ) : ℝ :=
  (∫ yz, logLikelihood τ yz.1 (vertex yz.1 + τ • yz.2)
    ∂((uniformFinset (Finset.univ : Finset (Cube m))).prod (stdGaussian (E m)))) / m

/-- Uniform sampling without replacement: the law on all n-element subsets. -/
def codebookLaw (m n : ℕ) : Measure (Finset (Cube m)) :=
  uniformFinset ((Finset.univ : Finset (Cube m)).powersetCard n)

/-- The null-score Fisher error, with extended nonnegative values. -/
def fisherError {m : ℕ} (S : Finset (Cube m)) (τ : ℝ) : ℝ≥0∞ :=
  squaredError (blockLaw S τ) (blockScore S τ) (nullScore m τ)

/-- Noise used by the KL–Fisher comparison. -/
def nearbyNoise (m : ℕ) (γ τ : ℝ) : ℝ := τ * Real.sqrt (1 - γ ^ 2 / (m : ℝ) ^ 2)

/-- Public budgets (12); d, B and m remain arguments, not implicit constants. -/
def hidingBudget (d P : ℕ) (ρ : ℝ) : ℝ := ρ ^ 2 / (100 * P * (d : ℝ) ^ 3)
def localBudget (B : ℕ) (ε : ℝ) : ℝ := ε / (8 * B)
def gateBudget (m B : ℕ) (ε ρ τ : ℝ) : ℝ :=
  min (ρ ^ 2 / 100) (localBudget B ε ^ 2 * τ ^ 2 / (16 * m))

def cutoff (m B : ℕ) (ε ρ τ : ℝ) : ℝ :=
  m * informationLevel m τ - Real.sqrt (8 * m * Real.log (1 / gateBudget m B ε ρ τ)) / τ

/-- Maximum over a finite codebook; the empty codebook is assigned zero and is excluded in lemmas. -/
def evidence {m : ℕ} (S : Finset (Cube m)) (τ : ℝ) (x : E m) : ℝ :=
  sSup ((fun y => logLikelihood τ y x) '' (S : Set (Cube m)))

def gate {m : ℕ} (B : ℕ) (ε ρ : ℝ) (S : Finset (Cube m)) (τ : ℝ) (x : E m) : ℝ :=
  min 1 (max 0 (1 + evidence S τ x - cutoff m B ε ρ τ))

def localAnswer {m : ℕ} (B : ℕ) (ε : ℝ) (S : Finset (Cube m)) (τ : ℝ) : E m → E m :=
  if fisherError S τ ≤ ENNReal.ofReal (localBudget B ε ^ 2 / (4 * τ ^ 2))
  then nullScore m τ else blockScore S τ

def lowerRate (d m B P : ℕ) (ε ρ τ : ℝ) : ℝ :=
  (cutoff m B ε ρ τ - Real.log (1 / hidingBudget d P ρ) - 1) / m

def upperRate (m : ℕ) (γ H τ : ℝ) : ℝ :=
  informationLevel m (nearbyNoise m γ τ) + H / m +
    Real.sqrt (8 * H / m) / nearbyNoise m γ τ

def rate (m n : ℕ) : ℝ := Real.log n / m

def transitionScale (m : ℕ) (H : ℝ) : ℝ := Real.sqrt (H / m) + H / m

/-- Explicit sufficient inequalities used for H in the proof, pp. 25–26. -/
def LargeH (d m B P : ℕ) (γ ε ρ H : ℝ) : Prop :=
  1 ≤ H ∧ Real.log (1 / hidingBudget d P ρ) ≤ H ∧
  Real.log (1 / gateBudget m B ε ρ γ) ≤ H ∧
  2 * Real.log (1 + (2 : ℝ) ^ m) * Real.exp (-H) ≤
    hidingBudget d P ρ * γ ^ 2 * localBudget B ε ^ 2 / (8 * Real.exp 1 * (m : ℝ) ^ 2)

/-- Target-level recognizing event (45). -/
def recognizingEvent {m : ℕ} (B : ℕ) (ε ρ γ : ℝ) (S : Finset (Cube m)) : Set (E m) :=
  {x | gate B ε ρ S γ x = 1}

end ParallelDiffusionLB.NearIsotropic


