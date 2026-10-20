-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P17
-- name    : QAlgorithms_Papers_Independent_Dependency50_P17
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T13:48:30.002452+00:00
-- url     : https://prove2.me/theorems/2d3b68fe-7e31-4752-9c64-a831f67eb45b
-- title:
--   Definitions for Computation-aided classical-quantum multiple access to boost network communication speeds
-- statement:
--   The objects the formalized statements of *Computation-aided classical-quantum multiple access to boost network communication speeds* (arXiv:2105.14505) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsDensityKernel`: PDF pp.3,10: coefficients of a density operator in an arbitrary orthonormal basis. A countable convex decomposition into unit vectors represents a positive trace-class operator of trace one. The basis index type need not be finite or countable.
--   - `CQMAC`: PDF p.3, Section II.A: a memoryless two-sender cq-MAC, specified by its single-use positive trace-one output kernels. Both alphabets are the same field.
--   - `degradedOutput`: PDF pp.12–13: W^d_s = (1/|F|) sum_a W_(a,s-a). Subtraction is field subtraction, not a subtraction of optical amplitudes.
--   - `degradedProduct`: PDF p.13, (38): the n-fold product of the single-use degraded channel.
--   - `aliceEncoder`: PDF p.13: Alice's constructed encoder for a fixed invertible extension L and a shared random seed z that is not given to the receiver. Write n = ell + k.
--   - `bobEncoder`: PDF p.13: Bob uses the negative of Alice's shared seed and the fixed affine shift e. These are separate encoders; their maps are not required to coincide.
--   - `sumEncoder`: PDF p.13: the affine encoder g(m)=F(m)+e, where F is the restriction of L to its first ell coordinates, constructed here as m ↦ L(m,0).
--   - `conditionalSumOutput`: PDF p.13, left side of (38): average over independent uniform M_A and z, conditional on M_A+M_B=m. The receiver does not receive z. There are |F|^(ell+k) equiprobable pairs. The printed q in the normalization is read as |F|=p.
--   - `UniformMessagePair`: PDF pp.3–6: independent uniform messages of a fixed common length. The underlying probability space may include encoder randomness, quantum measurement outcomes and link noise; no independence among those errors is imposed.
--   - `quadratureGaussian`: PDF p.10, (25): a normal density with mean m and variance 1/4. This is a density relative to Lebesgue measure, including its normalization factor.
--   - `bpskSign`: PDF p.10, (25): the BPSK sign associated with an input bit in F_2.
--   - `homodyneSingle`: PDF p.10, (25): homodyne output density given the two input bits. The Gaussian noise is independent of both inputs, and the quadrature is aligned with alpha, so its displacement uses the complex modulus of alpha.
--   - `homodyneSumDensity`: PDF p.10, first line of (26): conditional output density for S=A+B in F_2 under independent uniform input bits. At S=0 the two displacements are ±2|alpha|; at S=1 the output is vacuum noise.
--   - `homodyneMeanDensity`: PDF p.10: unconditional Gaussian mixture with weights 1/4,1/4,1/2.
--   - `homodyneRate`: PDF p.10, valid mutual-information rate in bits, written as a fully specified integral. Every denominator is a strictly positive Gaussian mixture; the theorem also records integrability of the entropy terms used to rewrite this integral.
--   - `HomodyneCode`: PDF pp.3–4,10: a block computation code after fixed, identical single-use homodyne measurements. Each encoder sees only its own message; decoding acts on all real-valued outcomes, with measurable fibers. No quantum memory is used.
--   - `homodyneError`: PDF pp.3–4,10: average decoding error over the two independent uniform ell-bit messages and the product Gaussian channel. The encoders and decoder are fixed before this average. F_2 has two symbols, so the pair has 2^(2 ell) values.
--   - `HomodyneAchievable`: PDF pp.3–4,10: an asymptotically achievable computation rate in bits/use. There is one code sequence, independent of the messages, with convergent rate ell/n and vanishing average error. The n=0 quotient is immaterial at atTop.
-- source:
--   Computation-aided classical-quantum multiple access to boost network communication speeds, arXiv:2105.14505v1, https://arxiv.org/abs/2105.14505v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

/-!
Paper-local statements from arXiv:2105.14505v1. Rates requiring additional analytic or
operational interfaces are explicitly deferred in this unit's HARD.md and GAPS.json.
The density-kernel interface below permits arbitrary orthonormal-basis index types;
there is no finite Fock cutoff. Only the four source statements are admitted.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Dependency50.P17

open QAlgorithms.Papers.Independent.Information100.P56 (productOutput)

/-- PDF pp.3,10: coefficients of a density operator in an arbitrary orthonormal basis.
A countable convex decomposition into unit vectors represents a positive trace-class
operator of trace one. The basis index type need not be finite or countable. -/
def IsDensityKernel {I : Type*} (rho : I → I → ℂ) : Prop :=
  ∃ (w : ℕ → ℝ) (psi : ℕ → RealRegisters.Hilbert I),
    (∀ r, 0 ≤ w r) ∧ Summable w ∧ (∑' r, w r) = 1 ∧
      (∀ r, ‖psi r‖ = 1) ∧
      ∀ i j, rho i j = ∑' r, (w r : ℂ) * psi r i * star (psi r j)

/-- PDF p.3, Section II.A: a memoryless two-sender cq-MAC, specified by its
single-use positive trace-one output kernels. Both alphabets are the same field. -/
structure CQMAC (F I : Type*) where
  output : F → F → I → I → ℂ
  density : ∀ a b, IsDensityKernel (output a b)

/-- PDF pp.12–13: W^d_s = (1/|F|) sum_a W_(a,s-a).
Subtraction is field subtraction, not a subtraction of optical amplitudes. -/
def degradedOutput {F I : Type*} [Field F] [Fintype F]
    (W : CQMAC F I) (s : F) (i j : I) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ * ∑ a, W.output a (s - a) i j

/-- PDF p.13, (38): the n-fold product of the single-use degraded channel. -/
def degradedProduct {F I : Type*} [Field F] [Fintype F]
    (W : CQMAC F I) {n : ℕ} (s : Fin n → F) (i j : Fin n → I) : ℂ :=
  productOutput n (degradedOutput W) s i j

/-- PDF p.13: Alice's constructed encoder for a fixed invertible extension L
and a shared random seed z that is not given to the receiver. Write n = ell + k. -/
def aliceEncoder {F : Type*} [Field F] {ell k : ℕ}
    (L : ((Fin ell → F) × (Fin k → F)) ≃ₗ[F] (Fin (ell + k) → F))
    (z : Fin k → F) (m : Fin ell → F) : Fin (ell + k) → F :=
  L (m, z)

/-- PDF p.13: Bob uses the negative of Alice's shared seed and the fixed affine
shift e. These are separate encoders; their maps are not required to coincide. -/
def bobEncoder {F : Type*} [Field F] {ell k : ℕ}
    (L : ((Fin ell → F) × (Fin k → F)) ≃ₗ[F] (Fin (ell + k) → F))
    (e : Fin (ell + k) → F) (z : Fin k → F) (m : Fin ell → F) :
    Fin (ell + k) → F :=
  L (m, -z) + e

/-- PDF p.13: the affine encoder g(m)=F(m)+e, where F is the restriction of
L to its first ell coordinates, constructed here as m ↦ L(m,0). -/
def sumEncoder {F : Type*} [Field F] {ell k : ℕ}
    (L : ((Fin ell → F) × (Fin k → F)) ≃ₗ[F] (Fin (ell + k) → F))
    (e : Fin (ell + k) → F) (m : Fin ell → F) : Fin (ell + k) → F :=
  L (m, 0) + e

/-- PDF p.13, left side of (38): average over independent uniform M_A and z,
conditional on M_A+M_B=m. The receiver does not receive z. There are |F|^(ell+k)
equiprobable pairs. The printed q in the normalization is read as |F|=p. -/
def conditionalSumOutput {F I : Type*} [Field F] [Fintype F] (W : CQMAC F I)
    {ell k : ℕ}
    (L : ((Fin ell → F) × (Fin k → F)) ≃ₗ[F] (Fin (ell + k) → F))
    (e : Fin (ell + k) → F) (m : Fin ell → F)
    (i j : Fin (ell + k) → I) : ℂ :=
  ((Fintype.card F : ℂ) ^ (ell + k))⁻¹ *
    ∑ a : Fin ell → F, ∑ z : Fin k → F,
      productOutput (ell + k) (fun ab : F × F => W.output ab.1 ab.2)
        (fun t => (aliceEncoder L z a t, bobEncoder L e z (m - a) t)) i j

/-- PDF pp.3–6: independent uniform messages of a fixed common length.
The underlying probability space may include encoder randomness, quantum measurement
outcomes and link noise; no independence among those errors is imposed. -/
def UniformMessagePair {F Omega : Type*} [Fintype F] [MeasurableSpace Omega]
    {ell : ℕ} (mu : Measure Omega) (a b : Omega → (Fin ell → F)) : Prop :=
  ∀ x y : Fin ell → F,
    mu {w | a w = x ∧ b w = y} = ((Fintype.card F : ℝ≥0∞) ^ (2 * ell))⁻¹

/-- A pure unit vector is a genuine instance of the local trace-one interface. -/
example {I : Type*} (psi : RealRegisters.Hilbert I) (hpsi : ‖psi‖ = 1) :
    IsDensityKernel (fun i j => psi i * star (psi j)) := by
  refine ⟨fun r => if r = 0 then 1 else 0, fun _ => psi, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    change 0 ≤ if r = 0 then (1 : ℝ) else 0
    exact ite_nonneg zero_le_one le_rfl
  · exact (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).summable
  · simp
  · intro r
    exact hpsi
  · intro i j
    calc
      _ = ∑' r : ℕ, if r = 0 then psi i * star (psi j) else 0 := by simp
      _ = _ := by
        apply tsum_congr
        intro r
        by_cases hr : r = 0 <;> simp [hr]

/-- The physical vacuum is a unit vector in the infinite single-mode lp register. -/
example : ‖(lp.single (E := fun _ : ℕ => ℂ) 2 (0 : ℕ) (1 : ℂ))‖ = 1 := by
  simp

/-- A zero-length uniform message pair imposes no nontrivial message data. -/
example {F Omega : Type*} [Field F] [Fintype F] [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu] :
    UniformMessagePair (F := F) (ell := 0) mu (fun _ => 0) (fun _ => 0) := by
  intro x y
  have hx : x = 0 := Subsingleton.elim _ _
  have hy : y = 0 := Subsingleton.elim _ _
  simp [hx, hy]

/-- The empty block is the scalar identity, including for arbitrary output dimension. -/
example {F I : Type*} (W : CQMAC F I) (a b : Fin 0 → F) (i j : Fin 0 → I) :
    productOutput 0 (fun ab : F × F => W.output ab.1 ab.2)
      (fun t => (a t, b t)) i j = 1 := by
  simp [productOutput]

/-- Degrading one use means averaging precisely the source's conditional pairs. -/
example {F I : Type*} [Field F] [Fintype F] (W : CQMAC F I)
    (s : F) (i j : Fin 1 → I) :
    degradedProduct W (fun _ : Fin 1 => s) i j =
      (Fintype.card F : ℂ)⁻¹ * ∑ a, W.output a (s - a) (i 0) (j 0) := by
  simp [degradedProduct, degradedOutput, productOutput]

/-- The zero-message, zero-seed encoder still carries the affine shift. -/
example {F : Type*} [Field F]
    (L : ((Fin 0 → F) × (Fin 0 → F)) ≃ₗ[F] (Fin 0 → F))
    (e : Fin 0 → F) : sumEncoder L e 0 = e := by
  funext i
  exact Fin.elim0 i

/-- PDF p.10, (25): a normal density with mean m and variance 1/4.
This is a density relative to Lebesgue measure, including its normalization factor. -/
def quadratureGaussian (m y : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) * Real.exp (-2 * (y - m) ^ 2)

/-- PDF p.10, (25): the BPSK sign associated with an input bit in F_2. -/
def bpskSign (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

/-- PDF p.10, (25): homodyne output density given the two input bits.
The Gaussian noise is independent of both inputs, and the quadrature is aligned
with alpha, so its displacement uses the complex modulus of alpha. -/
def homodyneSingle (alpha : ℂ) (a b : ZMod 2) (y : ℝ) : ℝ :=
  quadratureGaussian ((bpskSign a + bpskSign b) * ‖alpha‖) y

/-- PDF p.10, first line of (26): conditional output density for S=A+B in F_2
under independent uniform input bits. At S=0 the two displacements are ±2|alpha|;
at S=1 the output is vacuum noise. -/
def homodyneSumDensity (alpha : ℂ) (s : ZMod 2) (y : ℝ) : ℝ :=
  if s = 0 then
    (quadratureGaussian (2 * ‖alpha‖) y + quadratureGaussian (-2 * ‖alpha‖) y) / 2
  else quadratureGaussian 0 y

/-- PDF p.10: unconditional Gaussian mixture with weights 1/4,1/4,1/2. -/
def homodyneMeanDensity (alpha : ℂ) (y : ℝ) : ℝ :=
  (homodyneSumDensity alpha 0 y + homodyneSumDensity alpha 1 y) / 2

/-- PDF p.10, valid mutual-information rate in bits, written as a fully specified
integral. Every denominator is a strictly positive Gaussian mixture; the theorem
also records integrability of the entropy terms used to rewrite this integral. -/
def homodyneRate (alpha : ℂ) : ℝ :=
  ∫ y : ℝ,
    homodyneSumDensity alpha 0 y / 2 *
        Real.logb 2 (homodyneSumDensity alpha 0 y / homodyneMeanDensity alpha y) +
      homodyneSumDensity alpha 1 y / 2 *
        Real.logb 2 (homodyneSumDensity alpha 1 y / homodyneMeanDensity alpha y)

/-- PDF pp.3–4,10: a block computation code after fixed, identical single-use
homodyne measurements. Each encoder sees only its own message; decoding acts on
all real-valued outcomes, with measurable fibers. No quantum memory is used. -/
structure HomodyneCode (n ell : ℕ) where
  encodeA : (Fin ell → ZMod 2) → (Fin n → ZMod 2)
  encodeB : (Fin ell → ZMod 2) → (Fin n → ZMod 2)
  decode : (Fin n → ℝ) → (Fin ell → ZMod 2)
  decoder_fibers : ∀ m, MeasurableSet {y | decode y = m}

/-- PDF pp.3–4,10: average decoding error over the two independent uniform
ell-bit messages and the product Gaussian channel. The encoders and decoder are
fixed before this average. F_2 has two symbols, so the pair has 2^(2 ell) values. -/
def homodyneError (alpha : ℂ) {n ell : ℕ} (C : HomodyneCode n ell) : ℝ :=
  ((2 : ℝ) ^ (2 * ell))⁻¹ *
    ∑ a : Fin ell → ZMod 2, ∑ b : Fin ell → ZMod 2,
      ∫ y : Fin n → ℝ,
        (if C.decode y = a + b then 0 else
          ∏ t, homodyneSingle alpha (C.encodeA a t) (C.encodeB b t) (y t))
        ∂Measure.pi (fun _ : Fin n => (volume : Measure ℝ))

/-- PDF pp.3–4,10: an asymptotically achievable computation rate in bits/use.
There is one code sequence, independent of the messages, with convergent rate
ell/n and vanishing average error. The n=0 quotient is immaterial at atTop. -/
def HomodyneAchievable (alpha : ℂ) (R : ℝ) : Prop :=
  ∃ (ell : ℕ → ℕ) (C : ∀ n, HomodyneCode n (ell n)),
    Filter.Tendsto (fun n => (ell n : ℝ) / (n : ℝ)) Filter.atTop (nhds R) ∧
      Filter.Tendsto (fun n => homodyneError alpha (C n)) Filter.atTop (nhds 0)

/-- Zero quadrature displacement gives the same Gaussian at either sum bit. -/
example (s : ZMod 2) (y : ℝ) :
    homodyneSumDensity 0 s y = quadratureGaussian 0 y := by
  by_cases h : s = 0 <;> simp [homodyneSumDensity, h] <;> ring

/-- Opposite input bits give the vacuum-noise density. -/
example (alpha : ℂ) (y : ℝ) :
    homodyneSingle alpha 0 1 y = quadratureGaussian 0 y := by
  norm_num [homodyneSingle, bpskSign]

end QAlgorithms.Papers.Independent.Dependency50.P17


