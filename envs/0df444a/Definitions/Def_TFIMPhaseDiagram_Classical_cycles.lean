-- Prove2me | Definitions.Def_TFIMPhaseDiagram_Classical_cycles
-- name    : TFIMPhaseDiagram_Classical_cycles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:01:37.511342+00:00
-- url     : https://prove2.me/theorems/5bf1fed9-c470-4e04-902c-6bf72fc01623
-- title:
--   Poisson paths and signed open and closed Ising cycles
-- statement:
--   A spin is a Boolean, encoded as $+1$ for false and $-1$ for true. A closed cycle of $M$ spins has weight
--   $$\exp\!\left(\sum_{k=0}^{M-1}K_k s_k s_{k+1}+\sum_k w_k s_k\right),\qquad s_M=s_0.$$
--   Finite weights are normalized by their actual finite sum. Infinite external fields are compatible pinning conditions. The parity-cycle family uses $K_M(\eta)=\frac12\log\coth(\eta/M)$ and a last-edge sign $(-1)^p$ when $\eta>0$. At $\eta=0$ it uses the two constant configurations for $p=0$ and the uniform one-jump construction for $p=1$, before reweighting or pinning.
--
--   The Poisson path law stores its jump count, initial sign, and uniform jump-time tape, retaining evaluations at zero. Its parity mass is $\eta^d/(d!Z_{\eta,p})$, with $Z_{\eta,0}=\cosh\eta$, $Z_{\eta,1}=\sinh\eta$, and $D=p$ at zero. The open chain has $M-1$ edges and no closing edge. Covariance, its two cycle arcs, exponential tilts on arbitrary measurable spaces, and the two-spin log parameters are also defined here.
--
--   These laws provide the common classical objects for the trace identities and covariance results. Theorems use only well-defined positive normalizers.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, Definitions 5–6, pp.5–6; (7), p.7; (13), p.12; zero-field sampler, p.29

import Definitions.Def_TFIMPhaseDiagram_Classical_quantum

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
attribute [local instance] Classical.propDecidable

abbrev Spins (M : ℕ) := Fin M → Bool
def spin (b : Bool) : ℝ := if b then -1 else 1
/-- Finite Gibbs normalization. Valid source data always have a positive normalizer. -/
def normalize {A : Type} [Fintype A] (w : A → ℝ) (x : A) : ℝ := w x / ∑ y, w y
def finiteLaw {A : Type} [Fintype A] [MeasurableSpace A] (p : A → ℝ) : Measure A :=
  ∑ x, ENNReal.ofReal (p x) • Measure.dirac x
/-- ±infinite fields are pinning flags, never infinity arithmetic. -/
inductive Field where
  | finite (w : ℝ) | plus | minus

def compatible {M : ℕ} (w : Fin M → Field) (s : Spins M) : Prop :=
  ∀ k, match w k with
    | .finite _ => True
    | .plus => s k = false
    | .minus => s k = true

def fieldEnergy {M : ℕ} (w : Fin M → Field) (s : Spins M) : ℝ :=
  ∑ k, match w k with | .finite a => a * spin (s k) | _ => 0

def next {M : ℕ} (k : Fin M) : Fin M := ⟨(k.val + 1) % M, Nat.mod_lt _ k.pos⟩
def cycleEnergy {M : ℕ} (K : Fin M → ℝ) (w : Fin M → Field) (s : Spins M) : ℝ :=
  (∑ k, K k * spin (s k) * spin (s (next k))) + fieldEnergy w s

def cycleWeight {M : ℕ} (K : Fin M → ℝ) (w : Fin M → Field) (s : Spins M) : ℝ :=
  if compatible w s then Real.exp (cycleEnergy K w s) else 0

def cycleProb {M : ℕ} (K : Fin M → ℝ) (w : Fin M → Field) : Spins M → ℝ :=
  normalize (cycleWeight K w)
def cycleLaw {M : ℕ} (K : Fin M → ℝ) (w : Fin M → Field) : Measure (Spins M) :=
  finiteLaw (cycleProb K w)

def coupling (M : ℕ) (η : ℝ) : ℝ := (1/2) * Real.log (Real.cosh (η/M) / Real.sinh (η/M))
def signedCoupling {M : ℕ} (η : ℝ) (p : Bool) (k : Fin M) : ℝ :=
  if k.val + 1 = M ∧ p = true then -coupling M η else coupling M η
/-- One-jump vector: r ranges over 1,...,M; r=M gives a constant vector. -/
def oneJump {M : ℕ} (u : Bool) (r : Fin M) (k : Fin M) : Bool :=
  if k.val < r.val + 1 then u else !u

def zeroCycleBase {M : ℕ} (p : Bool) (s : Spins M) : ℝ :=
  if p then (∑ u : Bool, ∑ r : Fin M, if s = oneJump u r then (1 : ℝ) else 0) / (2*M)
  else (∑ u : Bool, if s = fun _ => u then (1 : ℝ) else 0) / 2

def pathCycleWeight {M : ℕ} (η : ℝ) (p : Bool) (w : Fin M → Field) (s : Spins M) : ℝ :=
  if η = 0 then
    if compatible w s then zeroCycleBase p s * Real.exp (fieldEnergy w s) else 0
  else cycleWeight (signedCoupling η p) w s

def pathCycleProb {M : ℕ} (η : ℝ) (p : Bool) (w : Fin M → Field) :=
  normalize (pathCycleWeight η p w)
def pathCycleLaw {M : ℕ} (η : ℝ) (p : Bool) (w : Fin M → Field) : Measure (Spins M) :=
  finiteLaw (pathCycleProb η p w)
/-- Open chain: exactly M-1 edges and no closing edge. -/
def openProb {M : ℕ} (K : Fin (M-1) → ℝ) (w : Fin M → ℝ) : Spins M → ℝ :=
  normalize (fun s => Real.exp
    ((∑ k : Fin (M-1), K k * spin (s ⟨k.val, by omega⟩) * spin (s ⟨k.val+1, by omega⟩)) +
      ∑ k, w k * spin (s k)))
def covariance {A : Type} [Fintype A] (p : A → ℝ) (f g : A → ℝ) : ℝ :=
  (∑ x, p x * f x * g x) - (∑ x, p x * f x) * (∑ x, p x * g x)
def spinCov {M : ℕ} (p : Spins M → ℝ) (i j : Fin M) : ℝ :=
  covariance p (fun s => spin (s i)) (fun s => spin (s j))
def arcProduct {M : ℕ} (K : Fin M → ℝ) (i j : Fin M) : ℝ :=
  ∏ k ∈ Finset.univ.filter (fun k : Fin M => i.val ≤ k.val ∧ k.val < j.val), Real.tanh (K k)
def otherArcProduct {M : ℕ} (K : Fin M → ℝ) (i j : Fin M) : ℝ :=
  ∏ k ∈ Finset.univ.filter (fun k : Fin M => k.val < i.val ∨ j.val ≤ k.val), Real.tanh (K k)
def finiteCovNorm {M : ℕ} (p : Spins M → ℝ) : ℝ :=
  sSup {r | ∃ x : EuclideanSpace ℝ (Fin M), ‖x‖ = 1 ∧
    r = ∑ i, ∑ j, x i * spinCov p i j * x j}

/-- Generic exponential tilt on an arbitrary measurable sample space. -/
def tilt {A : Type} [MeasurableSpace A] (μ : Measure A) (V : A → ℝ) : Measure A :=
  (∫⁻ x, ENNReal.ofReal (Real.exp (V x)) ∂μ)⁻¹ •
    μ.withDensity (fun x => ENNReal.ofReal (Real.exp (V x)))
def cycleInteraction {n M : ℕ} (J : Matrix (Fin n) (Fin n) ℝ)
    (s : Fin n → Spins M) : ℝ :=
  (1 / (2 * (M : ℝ))) * ∑ i, ∑ j, J i j * ∑ k, spin (s i k) * spin (s j k)
def spinProductLaw {n M : ℕ} (p : Fin n → Spins M → ℝ) : Measure (Fin n → Spins M) :=
  finiteLaw (fun s => ∏ i, p i (s i))
/-- TV defined by all measurable events, with values in [0,1] for probability measures. -/
def tv {A : Type} [MeasurableSpace A] (μ ν : Measure A) : ℝ :=
  sSup {r | ∃ E : Set A, MeasurableSet E ∧ r = |μ.real E - ν.real E|}

/-- Actual jump data preserve evaluation at 0. -/
abbrev PathData := ℕ × Bool × (ℕ → ℝ)
def uniform01 : Measure ℝ := volume.restrict (Set.Icc 0 1)
def parityMass (η : ℝ) (p : Bool) (d : ℕ) : ℝ :=
  if η = 0 then if d = (if p then 1 else 0) then 1 else 0
  else if d % 2 = (if p then 1 else 0) then
    η^d / ((d.factorial : ℝ) * (if p then Real.sinh η else Real.cosh η)) else 0
def parityLaw (η : ℝ) (p : Bool) : Measure ℕ :=
  Measure.sum (fun d => ENNReal.ofReal (parityMass η p d) • Measure.dirac d)
def pathLaw (η : ℝ) (p : Bool) : Measure PathData :=
  (parityLaw η p).prod ((finiteLaw (fun _ : Bool => (1/2 : ℝ))).prod
    (Measure.infinitePi (fun _ : ℕ => uniform01)))
def pathValue (σ : PathData) (t : ℝ) : ℝ :=
  spin σ.2.1 * (-1 : ℝ)^((Finset.range σ.1).filter (fun k => σ.2.2 k ≤ t)).card
def pathBits (σ : PathData) (t : ℝ) : Bool := decide (pathValue σ t < 0)
def discretize (M : ℕ) (σ : PathData) : Spins M := fun k => pathBits σ (k.val / (M : ℝ))
def pathPotential {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ)
    (σ : Fin n → PathData) : ℝ :=
  ∫ t in Set.Icc (0 : ℝ) 1, potential J h (fun i => pathValue (σ i) t)
def meshPotential {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ)
    (M : ℕ) (σ : Fin n → PathData) : ℝ :=
  (1/(M : ℝ)) * ∑ k : Fin M, potential J h (fun i => pathValue (σ i) (k.val / (M : ℝ)))
def hasFlip (P : Pauli) : Bool := match P with | .X | .Y => true | _ => false
def pathSign {n : ℕ} (P : Fin n → Pauli) (σ : Fin n → PathData) : ℝ :=
  ∏ i, if P i = .Y ∨ P i = .Z then pathValue (σ i) 0 else 1
def meshSign {n M : ℕ} (P : Fin n → Pauli) (s : Fin n → Spins M) : ℝ :=
  ∏ i, if P i = .Y ∨ P i = .Z then (∑ k : Fin M, if k.val = 0 then spin (s i k) else 0) else 1
/-- Positive two-spin Fourier/log parameters, Proposition 19. -/
def pairJ (r : Bool × Bool → ℝ) : ℝ :=
  (1/4) * Real.log (r (false,false) * r (true,true) / (r (false,true) * r (true,false)))
def pairV1 (r : Bool × Bool → ℝ) : ℝ :=
  (1/4) * Real.log (r (false,false) * r (false,true) / (r (true,false) * r (true,true)))
def pairV2 (r : Bool × Bool → ℝ) : ℝ :=
  (1/4) * Real.log (r (false,false) * r (true,false) / (r (false,true) * r (true,true)))
def pairC (r : Bool × Bool → ℝ) : ℝ := Real.rpow (∏ s, r s) (1/4)
def pairProb (r : Bool × Bool → ℝ) (w : ℝ × ℝ) : Bool × Bool → ℝ :=
  normalize (fun s => r s * Real.exp (w.1 * spin s.1 + w.2 * spin s.2))
def pairCov (r : Bool × Bool → ℝ) (w : ℝ × ℝ) : ℝ :=
  covariance (pairProb r w) (fun s => spin s.1) (fun s => spin s.2)
end TFIMPhaseDiagram.Classical


