-- Prove2me | Definitions.Def_FD1D_Hazard
-- name    : FD1D_Hazard
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:51:17.090355+00:00
-- url     : https://prove2.me/theorems/d2bee337-957b-5513-8708-d1d4349c84f7
-- title:
--   Hazard
-- statement:
--   Definitions and structural lemmas for Hazard, from Yash Kanoria (ykanoria/FD1d-Lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Tight upper bound for fully dynamic matching on the line development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Hazard.lean

import Definitions.Def_FD1D_Basic
set_option autoImplicit true
namespace FD1D
noncomputable section
namespace LocalHazard
def N (x y : ℕ) : ℝ := (x : ℝ) + (y : ℝ)
def D (a : ℝ) (x y : ℕ) : ℝ :=
  2 * (x : ℝ) * (y : ℝ) + a * N x y
def dL (a : ℝ) (x y : ℕ) : ℝ :=
  if x + y = 0 then 1 / 2 else (x : ℝ) * ((y : ℝ) + a) / D a x y
def dR (a : ℝ) (x y : ℕ) : ℝ :=
  if x + y = 0 then 1 / 2 else (y : ℝ) * ((x : ℝ) + a) / D a x y
def hL (a h : ℝ) (x y : ℕ) : ℝ :=
  if x + y = 0 then h else h * N x y * ((y : ℝ) + a) / D a x y
def hR (a h : ℝ) (x y : ℕ) : ℝ :=
  if x + y = 0 then h else h * N x y * ((x : ℝ) + a) / D a x y
def q (h : ℝ) (x y : ℕ) : ℝ := N x y * h
def qL (a h : ℝ) (x y : ℕ) : ℝ := q h x y * dL a x y
def qR (a h : ℝ) (x y : ℕ) : ℝ := q h x y * dR a x y
def b (a h : ℝ) (x y : ℕ) : ℝ := qL a h x y - qR a h x y
def V (a h : ℝ) (x y : ℕ) : ℝ := (hL a h x y + hR a h x y) / 2 - h
def w (a h : ℝ) (x y : ℕ) : ℝ := (hL a h x y - hR a h x y) / 2
def rho (x y : ℕ) : ℝ := ((x : ℝ) - (y : ℝ)) / N x y
def t (a p h : ℝ) (x y : ℕ) : ℝ := (p - q h x y) / a
def tL (a p h : ℝ) (x y : ℕ) : ℝ := (p / 2 - qL a h x y) / a
def tR (a p h : ℝ) (x y : ℕ) : ℝ := (p / 2 - qR a h x y) / a
end LocalHazard
end
end FD1D


