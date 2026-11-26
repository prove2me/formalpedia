-- Prove2me | Definitions.Def_FourierJacobi_Analysis_CoreParameters
-- name    : FourierJacobi_Analysis_CoreParameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:17:16.572804+00:00
-- url     : https://prove2.me/theorems/490c7c8e-2a75-5e09-82be-a22d33edba7f
-- title:
--   Core Parameters
-- statement:
--   Definitions and structural lemmas for Core Parameters, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CoreParameters.lean

import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra
def satakeTuple (a b : ℂ) : Fin 4 → ℂ := ![a, a⁻¹, b, b⁻¹]
def paperC (q : ℝ) : ℂ :=
  1 + 2 * (q : ℂ)⁻¹ + 2 * ((q : ℂ)⁻¹) ^ 2 +
    2 * ((q : ℂ)⁻¹) ^ 3 + ((q : ℂ)⁻¹) ^ 4
def paperN1 (q : ℝ) (a b : ℂ) : ℂ :=
  ∏ i : Fin 4, (1 - satakeTuple a b i * (q : ℂ)⁻¹)
def paperN2 (q : ℝ) (a b : ℂ) : ℂ :=
  (1 - a * b * (q : ℂ)⁻¹) * (1 - a⁻¹ * b * (q : ℂ)⁻¹) *
    (1 - a * b⁻¹ * (q : ℂ)⁻¹) * (1 - a⁻¹ * b⁻¹ * (q : ℂ)⁻¹)
def paperD1 (q : ℝ) (a b d : ℂ) : ℂ :=
  ∏ i : Fin 4, (1 - satakeTuple a b i * d * (inverseSqrt q : ℂ))
def paperD2 (q : ℝ) (a b d : ℂ) : ℂ :=
  ∏ i : Fin 4, (1 - satakeTuple a b i * d⁻¹ * (inverseSqrt q : ℂ))
def paperE (q : ℝ) (a b d : ℂ) : ℂ :=
  (((1 + a) ^ 2 * (1 + b) ^ 2 / (a * b)) * (1 - (q : ℂ)⁻¹) *
    paperN1 q a b * paperN2 q a b) /
      (paperC q * paperD1 q a b d * paperD2 q a b d)
structure GeometricRange (t d U V T : ℂ) : Prop where
  t2 : ‖t ^ 2‖ < 1
  p : ‖d * T * V * t‖ < 1
  n : ‖T * V * t / d‖ < 1
  e : ‖(T * V) ^ 2 * t ^ 2‖ < 1
  f : ‖T * U * t ^ 2‖ < 1
  g : ‖T * U * t ^ 4‖ < 1
end FourierJacobi.Analysis


