-- Prove2me | Definitions.Def_SingleCopyMoments_Adaptive_Pilot
-- name    : SingleCopyMoments_Adaptive_Pilot
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T09:46:21.083393+00:00
-- url     : https://prove2.me/theorems/549cfcc2-cc09-4204-92bb-04eb5ece9ec6
-- title:
--   Pilot mixture and the conditional Kraus filter
-- statement:
--   Let $\nu_H$ be normalized Haar measure on unit vectors, $P_v=vv^\dagger$, and $\rho$ a state. The covariant law has density $d\langle v,\rho v\rangle$ against $\nu_H$. A pilot uses that law with probability $\gamma_x=x(d+1)/(d+x)$ and Haar sampling otherwise, for $0\le x\le1$. Independent trials define
--
--   $$S_x=\sum_{i=1}^nP_{v_i},\quad B_x=\frac{d+x}{n}\sqrt\rho S_x\sqrt\rho,\quad H_x=\rho+x\rho^2,\quad K_x=\sqrt{S_x/L}.$$
--
--   The filtering success probability is $s_x=\operatorname{Tr}(S_x\rho)/L$. Its conditional output is the normalization of $\sqrt{S_x}\rho\sqrt{S_x}$, with the original input state as the explicit zero-success dummy. The implementation $K_x$ depends only on pilot data. The state-dependent $B_x,H_x$ are analysis quantities.
--
--   The simulator interface asks for a measurable decoder and a measurable completion event. The decoded successful transcript submeasure, including the seed, equals $q$ times the intended inner transcript law, with $1-\beta\le q\le1$, uniformly over all inputs with success at least $s_0$. The simulator's fixed budget counts failures. This expresses exact transcript simulation on completion and an additional failure of at most $\beta$.
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), §6.2, (6.1) and (6.4), printed pp. 22–23 (PDF pp. 24–25); Lemma 23 and its successful-transcript construction, printed p. 25 (PDF p. 27). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_SingleCopyMoments_Adaptive_Estimation
import Definitions.Def_IncoherentPurity_Adaptive_Estimators

open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder
noncomputable section

namespace SingleCopyMoments.Adaptive

abbrev HaarBasis := IncoherentPurity.Adaptive.HaarBasis
abbrev outer := @IncoherentPurity.Adaptive.outer
abbrev pureHaar := @IncoherentPurity.Adaptive.pureHaar
abbrev covariantLaw := @IncoherentPurity.Adaptive.uniformLaw

def pilotMixing (d : ℕ) (x : ℝ) : ℝ := x * ((d : ℝ) + 1) / ((d : ℝ) + x)

def pilotTrial {d : ℕ} (H : HaarBasis d) (ρ : State d) (x : ℝ) : Measure (Fin d → ℂ) :=
  ENNReal.ofReal (1 - pilotMixing d x) • pureHaar H +
    ENNReal.ofReal (pilotMixing d x) • covariantLaw H ρ.val

def pilotLaw {d : ℕ} (H : HaarBasis d) (ρ : State d) (x : ℝ) (n : ℕ) :=
  Measure.pi (fun _ : Fin n => pilotTrial H ρ x)

def pilotS {d n : ℕ} (v : Fin n → (Fin d → ℂ)) : Op d := ∑ i, outer (v i)

def pilotB {d n : ℕ} (ρ : State d) (x : ℝ) (v : Fin n → (Fin d → ℂ)) : Op d :=
  (((d : ℝ) + x) / (n : ℝ)) • (cfc Real.sqrt ρ.val * pilotS v * cfc Real.sqrt ρ.val)

def pilotH {d : ℕ} (ρ : State d) (x : ℝ) : Op d := ρ.val + x • (ρ.val ^ 2)

def filterK {d n : ℕ} (v : Fin n → (Fin d → ℂ)) (L : ℝ) : Op d :=
  cfc Real.sqrt ((1/L) • pilotS v)

def filterSuccess {d n : ℕ} (ρ : State d) (v : Fin n → (Fin d → ℂ)) (L : ℝ) : ℝ :=
  (pilotS v * ρ.val).trace.re / L

def filterState {d n : ℕ} (ρ : State d) (v : Fin n → (Fin d → ℂ)) : State d :=
  normalizedState (cfc Real.sqrt (pilotS v) * ρ.val * cfc Real.sqrt (pilotS v)) ρ

/-- Normalized Kraus output; all simulator guarantees require a positive success probability. -/
def krausOutput {d : ℕ} (K : Op d) (ρ : State d) : State d :=
  normalizedState (K * ρ.val * K.conjTranspose) ρ

/-- Equality of the successful decoded transcript submeasure to a scalar multiple of
its intended law, including the seed. Exhaustion remains an observed failure. -/
def Simulates {d : ℕ} (K : Op d) (s₀ β : ℝ) (P Q : Protocol d) (N M : ℕ)
    (decode : Record Q → Record P) (good : Set (Record Q)) : Prop :=
  Measurable decode ∧ MeasurableSet good ∧
  ∀ ρ : State d, s₀ ≤ (K * ρ.val * K.conjTranspose).trace.re →
    IsProbabilityMeasure (law Q ρ M) ∧
    ∃ q ∈ Set.Icc (1 - β) 1,
      ((law Q ρ M).restrict good).map decode =
        ENNReal.ofReal q • law P (krausOutput K ρ) N

end SingleCopyMoments.Adaptive


