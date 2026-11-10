-- Prove2me | Definitions.Def_BooleanHiddenPartition_LowerBounds_Posteriors
-- name    : BooleanHiddenPartition_LowerBounds_Posteriors
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:22:15.042209+00:00
-- url     : https://prove2.me/theorems/aad4424c-2d7c-46d3-86ad-1f21c5cc3094
-- title:
--   Actual injection and message posteriors and conditional quantum states
-- statement:
--   For an ordered injection pi:[k]→[t], define N(pi)=E_uniform[q(x_pi)nu(x)], and define the posterior mass p_pi(x)=q(x_pi)nu(x)/(2^t N(pi)) when N is nonzero, with zero mass otherwise. injectionBias is E_pi[N(pi)(E_p f(x_pi))^2], including the weight N inside the injection expectation.
--
--   $$p_\pi(x)=\frac{q(x_\pi)\nu(x)}{2^tN(\pi)},\qquad m_{\sigma,z}=\mathbb E_{Q_\sigma\mid F_z}[g(x)].$$
--
--   Prefix events constrain the outputs of the preceding blocks. messagePosterior is computed from the hard law, the actual encoder output, sigma, and the prefix. classicalBias averages its squared block bias using the joint conditional weights of sigma and the message, divided by the prefix mass. prefixState is the entrywise conditional average of the actual density encoder, and quantumIncrement averages the unhalved trace norm of two successive such states under the actual (sigma,y) hard-law marginal. Every null conditioning returns zero. matrixFourier uses the same 2^(-n) normalization as the scalar transform. No posterior or state is an arbitrary object assumed to satisfy an estimate.
-- source:
--   Mark Bun, Joao F. Doriguello, John Kallaugher, Nadezhda Voronova, STOC 2027 submission #1085 (October 2026), pp. 17–19, 22–24, definitions and conventions.

import Definitions.Def_BooleanHiddenPartition_LowerBounds_Problem
import Definitions.Def_WildeQIT_traceNorm

open scoped BigOperators ENNReal
open Classical
set_option autoImplicit false

namespace BooleanHiddenPartition.LowerBounds

noncomputable section

/-- Restriction along an actual ordered injection. -/
def injected {k t : ℕ} (π : Fin k ↪ Fin t) (x : Cube t) : Cube k := fun j => x (π j)

def injectionMean {k t : ℕ} (h : (Fin k ↪ Fin t) → ℝ) : ℝ :=
  (Fintype.card (Fin k ↪ Fin t) : ℝ)⁻¹ * ∑ π, h π

def injectionN {k t : ℕ} (q : Cube k → ℝ) (ν : Cube t → ℝ)
    (π : Fin k ↪ Fin t) : ℝ := cubeMean (fun x => q (injected π x) * ν x)

def injectionPosterior {k t : ℕ} (q : Cube k → ℝ) (ν : Cube t → ℝ)
    (π : Fin k ↪ Fin t) (x : Cube t) : ℝ :=
  if injectionN q ν π = 0 then 0
  else q (injected π x) * ν x / ((2 : ℝ)^t * injectionN q ν π)

def injectionBias {k t : ℕ} (f : Cube k → Bool) (q : Cube k → ℝ)
    (ν : Cube t → ℝ) : ℝ :=
  injectionMean (fun π => injectionN q ν π *
    (∑ x, injectionPosterior q ν π x * sign (f (injected π x))) ^ 2)

/-- Prefix length ℓ is explicit and ranges only up to m in the theorems. -/
def prefixEvent {k n m ℓ : ℕ} {α : ℝ} (L : Layout k n m α)
    (f : Cube k → Bool) (σ : Equiv.Perm (Fin n)) (z : Cube ℓ) (x : Cube n) : Prop :=
  ∀ (j : Fin ℓ) (h : j.val < m), f (block L σ x ⟨j.val, h⟩) = z j

def prefixMass {k n m ℓ : ℕ} {α : ℝ} (L : Layout k n m α)
    (f : Cube k → Bool) (q : Cube k → ℝ) (σ : Equiv.Perm (Fin n))
    (z : Cube ℓ) (x : Cube n) : ℝ :=
  if prefixEvent L f σ z x then hardMass L q σ x else 0

/-- Joint mass of x and the actually received message after a fixed prefix. -/
def messageMass {k n m ℓ c : ℕ} {α : ℝ} (L : Layout k n m α)
    (f : Cube k → Bool) (q : Cube k → ℝ) (e : Cube n → Fin (2^c))
    (σ : Equiv.Perm (Fin n)) (z : Cube ℓ) (a : Fin (2^c)) (x : Cube n) : ℝ :=
  if e x = a then prefixMass L f q σ z x else 0

/-- Zero on a zero-mass conditioning event. -/
def messagePosterior {k n m ℓ c : ℕ} {α : ℝ} (L : Layout k n m α)
    (f : Cube k → Bool) (q : Cube k → ℝ) (e : Cube n → Fin (2^c))
    (σ : Equiv.Perm (Fin n)) (z : Cube ℓ) (a : Fin (2^c)) (x : Cube n) : ℝ :=
  let w := messageMass L f q e σ z a
  if (∑ u, w u) = 0 then 0 else w x / ∑ u, w u

/-- Average of squared actual posterior biases under (σ,a)|F_z. -/
def classicalBias {k n m c : ℕ} {α : ℝ} (L : Layout k n m α)
    (f : Cube k → Bool) (q : Cube k → ℝ) (e : Cube n → Fin (2^c))
    (i : Fin m) (z : Cube i.val) : ℝ :=
  let den := permMean (fun σ => ∑ x, prefixMass L f q σ z x)
  if den = 0 then 0 else
    permMean (fun σ => ∑ a : Fin (2^c),
      (∑ x, messageMass L f q e σ z a x) *
      (∑ x, messagePosterior L f q e σ z a x * sign (f (block L σ x i)))^2) / den

/-- Entrywise Fourier coefficient with the same 2⁻ⁿ normalization. -/
def matrixFourier {n c : ℕ} (g : Cube n → QMat c) (S : Finset (Fin n)) : QMat c :=
  fun a b => ((2 : ℂ)^n)⁻¹ * ∑ x, (parity S x : ℂ) * g x a b

/-- The computed conditional average state m_{σ,z}; zero on null prefixes. -/
def prefixState {k n m ℓ c : ℕ} {α : ℝ} (L : Layout k n m α)
    (f : Cube k → Bool) (q : Cube k → ℝ) (g : Cube n → QMat c)
    (σ : Equiv.Perm (Fin n)) (z : Cube ℓ) : QMat c :=
  let w := prefixMass L f q σ z
  if (∑ x, w x) = 0 then 0 else
    fun a b => (∑ x, (w x : ℂ) * g x a b) / (∑ x, w x : ℝ)

def takePrefix {m : ℕ} (y : Cube m) (ℓ : ℕ) (h : ℓ ≤ m) : Cube ℓ :=
  fun j => y ⟨j.val, lt_of_lt_of_le j.isLt h⟩

/-- Expectation over the actual (σ,y) marginal of the hard input law. -/
def quantumIncrement {k n m c : ℕ} {α : ℝ} (L : Layout k n m α)
    (f : Cube k → Bool) (q : Cube k → ℝ) (g : Cube n → QMat c) (i : Fin m) : ℝ :=
  permMean (fun σ => ∑ x, hardMass L q σ x *
    ((∑ b : Bool, let y := labels L f σ x b
      WildeQIT.traceNorm
        (prefixState L f q g σ (takePrefix y (i.val+1) i.isLt) -
         prefixState L f q g σ (takePrefix y i.val (Nat.le_of_lt i.isLt)))) / 2))

end

end BooleanHiddenPartition.LowerBounds


