-- Prove2me | Definitions.Def_FD1D_V5_LocalBellman
-- name    : FD1D_V5_LocalBellman
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:25:17.710421+00:00
-- url     : https://prove2.me/theorems/a065d53c-ac31-4586-a2cc-b22588032260
-- title:
--   Local Bellman
-- statement:
--   Definitions and structural lemmas for Local Bellman, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/V5/LocalBellman.lean

import Definitions.Def_FD1D_V5_LocalInvariants
set_option autoImplicit true
namespace FD1D.V5.LocalBellman
noncomputable section
open LocalPolicy
namespace Normalized
def lambda (ρ : ℝ) : ℝ := ρ ^ 2
def A (s ρ : ℝ) : ℝ := s * (1 - lambda ρ)
def g (s r : ℝ) : ℝ := s + r
def d (s ρ : ℝ) : ℝ := s * (A s ρ + 2) + 1
def hPlus (s ρ z : ℝ) : ℝ :=
  (s + z) / (s * (1 + ρ))
def hMinus (s ρ z : ℝ) : ℝ :=
  (s - z) / (s * (1 - ρ))
def tPlus (r z : ℝ) : ℝ := (r - z) / 2
def tMinus (r z : ℝ) : ℝ := (r + z) / 2
def ZParent (s r : ℝ) : ℝ :=
  g s r / (s + 1 / 2)
def ZPlus (s r ρ : ℝ) : ℝ :=
  g s r / (s * (1 + ρ) + 1)
def ZMinus (s r ρ : ℝ) : ℝ :=
  g s r / (s * (1 - ρ) + 1)
def residual (s r ρ z : ℝ) : ℝ :=
  ((tPlus r z * ZPlus s r ρ +
        bellman (hPlus s ρ z) (tPlus r z) (ZPlus s r ρ)) +
      (tMinus r z * ZMinus s r ρ +
        bellman (hMinus s ρ z) (tMinus r z) (ZMinus s r ρ))) / 2 -
    bellman 1 r (ZParent s r)
def rateIncrement (s ρ z : ℝ) : ℝ :=
  (hPlus s ρ z ^ 2 + hMinus s ρ z ^ 2) / 2 - 1
def feedback (s ρ : ℝ) : ℝ :=
  8 * s * ρ / A s ρ
def uniform (s ρ : ℝ) : ℝ :=
  s * ρ
def floorCap (s r ρ : ℝ) : ℝ :=
  (s - s * (1 - ρ) * r) / (s * (1 - ρ) + 1)
def J (s ρ k : ℝ) : ℝ :=
  (s - k) / A s ρ
def bracket (s r ρ k : ℝ) : ℝ :=
  s * k - J s ρ k * (s + 1 / 2) -
    (1 / 2 - r) * s ^ 2 / (s + 1 / 2)
def floorEll (u v K : ℝ) : ℝ :=
  1 - u * (K - 1) / (2 * v)
def floorW (u v K : ℝ) : ℝ :=
  (K + 1) * (u + 1) / (2 * (v + 1))
def floorEta (u v : ℝ) : ℝ :=
  (v + 1 - u) / (v + 1 + u)
def floorR (K e u v : ℝ) : ℝ :=
  (5 * K ^ 2 + 12 * K + 9 + 2 * e ^ 2 - 2 * K * e - 6 * e) / 96 +
    floorW u v K / 2 *
      (e * floorEta u v - (K - 1 + floorEll u v K) / 2)
def floorJ (K e : ℝ) : ℝ :=
  5 * K ^ 2 - 3 + 2 * e ^ 2 - (2 * K + 6) * e +
    24 * (K + 1) * e * (K + e) / (K * (16 + K + e))
def floorU (s ρ : ℝ) : ℝ :=
  s * (1 - ρ)
def floorV (s ρ : ℝ) : ℝ :=
  s * (1 + ρ)
def floorE (r : ℝ) : ℝ :=
  1 - 2 * r
def floorK (s r ρ : ℝ) : ℝ :=
  (floorV s ρ - floorE r) / (floorU s ρ + 1)
def emptyResidual (s r emptyRate : ℝ) : ℝ :=
  let total := g s r
  let occupiedDrift := (r - s) / 2
  let occupiedZ := total / (2 * s + 1)
  let emptyDrift := total / 2
  ((occupiedDrift * occupiedZ +
        bellman 1 occupiedDrift occupiedZ) +
      (emptyDrift * total +
        bellman emptyRate emptyDrift total)) / 2 -
    bellman 1 r (total / (s + 1 / 2))
def emptyRateIncrement (emptyRate : ℝ) : ℝ :=
  (1 + emptyRate ^ 2) / 2 - 1
end Normalized
def localResidual (a p h : ℝ) (x y : ℕ) : ℝ :=
  ((discrepancyLeft a p h x y * regularizedMassLeft a p x y +
        bellman (rateLeft a p h x y) (discrepancyLeft a p h x y)
          (regularizedMassLeft a p x y)) +
      (discrepancyRight a p h x y * regularizedMassRight a p x y +
        bellman (rateRight a p h x y) (discrepancyRight a p h x y)
          (regularizedMassRight a p x y))) / 2 -
    bellman h (discrepancy a p h x y) (regularizedMass a p x y)
def localEnergy (a p h : ℝ) (x y : ℕ) : ℝ :=
  (rateLeft a p h x y ^ 2 + rateRight a p h x y ^ 2) / 2 -
    h ^ 2 + bias a p h x y ^ 2 / a ^ 2
end
end FD1D.V5.LocalBellman


