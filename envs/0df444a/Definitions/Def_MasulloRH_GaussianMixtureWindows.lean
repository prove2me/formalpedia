-- Prove2me | Definitions.Def_MasulloRH_GaussianMixtureWindows
-- name    : MasulloRH_GaussianMixtureWindows
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T20:16:25.540746+00:00
-- url     : https://prove2.me/theorems/4f37f242-d888-587e-9bb9-016694227b76
-- title:
--   Gaussian overlaps and rational data for seven translated height-two approximants
-- statement:
--   Define the normalized shifted Gaussian, its exponential-weighted overlap kernel, seven rational shifts and amplitudes, and the 77 coefficient-shift pairs obtained by multiplying and translating the published eleven-term array.
-- source:
--   Finite approximation for the Masullo fixed-Gaussian criterion on expanding windows. https://prove2.me/theorems/5b5a3819-6fdf-5ee5-ba13-5cfaec0d1147 The base array is the published height-two witness. https://prove2.me/definitions/d1967a7a-bf7f-42bd-8ad5-820a7680a39d

import Definitions.Def_MasulloRH_FixedGaussianTest
import Definitions.Def_MasulloRH_HeightTwoWitness
import Mathlib.Logic.Equiv.Fin.Basic

namespace MasulloRH.GaussianMixture

noncomputable def bell (p y x : ℝ) : ℝ := p / Real.sqrt Real.pi * Real.exp (-(p^2)*(x-y)^2)

def exponent {K : Type*} [Field K] (p q y z t : K) : K :=
  (2*p^2*y + 2*q^2*z + t)^2 / (4*(p^2+q^2)) - p^2*y^2 - q^2*z^2

noncomputable def ratio (d : ℝ) : ℝ := Real.sqrt (Real.pi/d)/Real.pi
noncomputable def kernel (p q y z t : ℝ) : ℝ :=
  p*q*ratio (p^2+q^2)*Real.exp (exponent p q y z t)

def amplitude (i : Fin 7) : ℚ := (![3,12,29,38,29,12,3] i : ℚ)/128
def offset : Fin 7 → ℚ := ![-3/2,-1,-1/2,0,1/2,1,3/2]
def scale8 : Fin 8 → ℚ := Fin.cons 1 (fun _ : Fin 7 => 3)
def weight8 : Fin 8 → ℚ := Fin.cons 1 (fun i : Fin 7 => -(amplitude i))
def shift8 : Fin 8 → ℚ := Fin.cons 0 offset

noncomputable def difference (x : ℝ) : ℂ :=
  ((bell 1 0 x - ∑ i : Fin 7, (amplitude i : ℝ)*bell 3 (offset i : ℝ) x : ℝ) : ℂ)

def coefficient77 (n : Fin 77) : ℚ :=
  let ij := (finProdFinEquiv : (Fin 7 × Fin 11) ≃ Fin 77).symm n
  amplitude ij.1 * MasulloRH.HeightTwoWitness.coeffsQ ij.2

def shift77 (n : Fin 77) : ℚ :=
  let ij := (finProdFinEquiv : (Fin 7 × Fin 11) ≃ Fin 77).symm n
  offset ij.1 + MasulloRH.HeightTwoWitness.shiftsQ ij.2

end MasulloRH.GaussianMixture


