-- Prove2me | Definitions.Def_FourierJacobi_Analysis_MasterSeries
-- name    : FourierJacobi_Analysis_MasterSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:15:57.416645+00:00
-- url     : https://prove2.me/theorems/2fc5f9aa-1cf0-48df-8da0-8bf405b6a693
-- title:
--   Master Series
-- statement:
--   Definitions and structural lemmas for Master Series, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterSeries.lean

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Definitions.Def_FourierJacobi_Algebra_WeylSum
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations
abbrev LatticeIndex := ℤ × ℤ × ℤ × ℕ
def shellCoeff (q : ℂ) (r : ℤ) : ℂ :=
  if r = 0 then 1 else if r = 1 then q * (1 - q⁻¹) else -q
def collisionProbability (q : ℂ) (c : ℕ) : ℂ :=
  if c = 0 then (q - 2) / (q - 1) else q ^ (-(c : ℤ))
def collisionWeight (q : ℂ) (r j h : ℤ) (c : ℕ) : ℂ :=
  if r = 0 ∨ 2 * h ≠ j - r then (if c = 0 then 1 else 0)
  else collisionProbability q c
def shellMonomial (t d U V T : ℂ) (r : ℤ) (p : ℤ × ℤ × ℤ) (c : ℕ) : ℂ :=
  let ell := (cartanIndices r p.1 p.2.1 p.2.2 c).1
  let b := (cartanIndices r p.1 p.2.1 p.2.2 c).2
  (1 - t ^ 2) ^ 2 * d ^ p.1 *
    t ^ (3 * p.1 + 2 * p.2.1 + 2 * p.2.2 + 3 * ell + 4 * b) *
    (T * U) ^ (ell / 2) * (T * V) ^ b
def masterTerm (q t d U V T : ℂ) (r : ℤ) (p : LatticeIndex) : ℂ :=
  shellCoeff q r * shellMonomial t d U V T r (p.1, p.2.1, p.2.2.1) p.2.2.2 *
    collisionWeight q r p.2.1 p.2.2.1 p.2.2.2
def depthMajorant (q : ℂ) (c : ℕ) : ℝ :=
  (if c = 0 then 1 else 0) + ‖collisionProbability q c‖
end FourierJacobi.Analysis


