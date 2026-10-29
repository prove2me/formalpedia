-- Prove2me | Definitions.Def_CloseGaps_DPA_Parameters
-- name    : CloseGaps_DPA_Parameters
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:36.412542+00:00
-- url     : https://prove2.me/theorems/6dad868d-a6f2-475a-841d-46bc39211b71
-- title:
--   The theoretical DPA parameters
-- statement:
--   The printed stage durations, real grid counts and nominal interval widths, indexed from one.
-- source:
--   Wang, Deng, and Ye (2014), Operations Research 62(2), 318–331, DOI 10.1287/opre.2013.1245, §4.2, equations (22)–(27), p. 324 (PDF 7)

import Mathlib

noncomputable section
open scoped Classical

namespace CloseGaps.DPA

/-- Source stage indices start at one. -/
def tauU (n : ℝ) (i : ℕ) : ℝ :=
  if i = 1 then n ^ (-(1 / 2 : ℝ)) * (Real.log n) ^ (7 / 2 : ℝ)
  else n ^ (-(1 / 2 : ℝ) * (3 / 5 : ℝ) ^ (i - 1)) * (Real.log n) ^ 5

def tauC (n : ℝ) (i : ℕ) : ℝ :=
  if i = 1 then n ^ (-(1 / 2 : ℝ)) * (Real.log n) ^ (5 / 2 : ℝ)
  else n ^ (-(1 / 2 : ℝ) * (2 / 3 : ℝ) ^ (i - 1)) * (Real.log n) ^ 3

def kappaU (n : ℝ) (i : ℕ) : ℝ :=
  n ^ ((1 / 10 : ℝ) * (3 / 5 : ℝ) ^ (i - 1)) * Real.log n

def kappaC (n : ℝ) (i : ℕ) : ℝ :=
  n ^ ((1 / 6 : ℝ) * (2 / 3 : ℝ) ^ (i - 1)) * Real.log n

def timeU (n : ℝ) (i : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 i, tauU n j

def timeC (n : ℝ) (i : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 i, tauC n j

/-- These nominal widths are not constraints on the truncated, realized intervals. -/
def nominalWidthU (n : ℝ) (i : ℕ) : ℝ :=
  n ^ (-(1 / 4 : ℝ) * (1 - (3 / 5 : ℝ) ^ (i - 1)))
def nominalWidthC (n : ℝ) (i : ℕ) : ℝ :=
  n ^ (-(1 / 2 : ℝ) * (1 - (2 / 3 : ℝ) ^ (i - 1)))

end CloseGaps.DPA


