-- Prove2me | Definitions.Def_PolyhedralPacking1261_Packing_Geometry
-- name    : PolyhedralPacking1261_Packing_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:35:48.399027+00:00
-- url     : https://prove2.me/theorems/26801210-889e-4052-a3c3-e207dac2a1ff
-- title:
--   Finite polyhedral inputs, feasible translations, box volume and the attained optimum
-- statement:
--   An input is a nonempty finite list of nonempty finite real vertex lists in three-space. Each piece is the convex hull of its vertices; repetitions and all affine dimensions are allowed. A packing specifies one translation per input position and lower and upper corners of a closed axis-parallel containing box. Lower coordinates do not exceed upper coordinates. The translated bodies are contained in that box and have pairwise disjoint ambient three-dimensional interiors; boundary contact is allowed. Box volume is the product of the three side lengths.
--   The feasible-volume set consists of exactly the volumes of these packings. optimumVolume is its real infimum. HasAttainedOptimum asserts that this set is nonempty and bounded below and that the infimum belongs to the set and is its least element. This is an obligation in the goal's conclusion, not an assumption on the input. No arbitrary optimum value or packing oracle is supplied. On the malformed empty input the empty packing is feasible and the minimum is zero; empty vertex lists also have empty convex hulls, but are excluded by AdmissibleInput. For admissible inputs the theorem explicitly asserts attainment, including zero optima.
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, §1 problem definition and Theorem 1, PDF p.2 = printed p.1

import Mathlib

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing

/-- Coordinates with the usual product topology on real three-space. -/
abbrev Point3 := Fin 3 → ℝ

/-- Piece indices and vertex multiplicities are retained by the two lists. -/
abbrev PackingInput := List (List Point3)

/-- The headline domain includes every affine dimension, with at least one piece
and at least one vertex in each piece. No coordinate is required to be rational. -/
def AdmissibleInput (K : PackingInput) : Prop :=
  K ≠ [] ∧ ∀ vertices ∈ K, vertices ≠ []

def inputBody (K : PackingInput) (i : Fin K.length) : Set Point3 :=
  convexHull ℝ {x | x ∈ K[i]}

structure PackingOutput (n : ℕ) where
  lower : Point3
  upper : Point3
  translation : Fin n → Point3

def closedContainer {n : ℕ} (out : PackingOutput n) : Set Point3 :=
  {x | ∀ r, out.lower r ≤ x r ∧ x r ≤ out.upper r}

def translatedBody (K : PackingInput) (out : PackingOutput K.length)
    (i : Fin K.length) : Set Point3 :=
  (fun x => x + out.translation i) '' inputBody K i

/-- Ambient interiors are disjoint; contact on the boundary is allowed. -/
def FeasiblePacking (K : PackingInput) (out : PackingOutput K.length) : Prop :=
  (∀ r, out.lower r ≤ out.upper r) ∧
  (∀ i, translatedBody K out i ⊆ closedContainer out) ∧
  ∀ i j, i ≠ j → Disjoint (interior (translatedBody K out i))
    (interior (translatedBody K out j))

def containerVolume {n : ℕ} (out : PackingOutput n) : ℝ :=
  ∏ r : Fin 3, (out.upper r - out.lower r)

def feasibleVolumes (K : PackingInput) : Set ℝ :=
  {v | ∃ out : PackingOutput K.length, FeasiblePacking K out ∧
    containerVolume out = v}

noncomputable def optimumVolume (K : PackingInput) : ℝ :=
  sInf (feasibleVolumes K)

/-- An assertion to prove, never an admissibility assumption: the infimum is
taken over a nonempty bounded-below set and is an attained minimum. -/
def HasAttainedOptimum (K : PackingInput) : Prop :=
  (feasibleVolumes K).Nonempty ∧ BddBelow (feasibleVolumes K) ∧
    IsLeast (feasibleVolumes K) (optimumVolume K)

end PolyhedralPacking1261.Packing


