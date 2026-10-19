-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
-- name    : OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T10:07:13.943491+00:00
-- url     : https://prove2.me/theorems/3ad93c0e-5f95-491f-9a91-ab3b34918b66
-- title:
--   Elementary identities for flips, sign coordinates and the threshold sign
-- statement:
--   On the Boolean cube $\{0,1\}^n$, write $x^{\oplus i}$ for $x$ with coordinate $i$ flipped and $x_i^\pm\in\{\pm1\}$ for the sign of coordinate $i$. Let $\operatorname{sgn}(t)=1$ for $t\ge0$ and $-1$ otherwise. The following identities hold.
--
--   1. Flipping twice is the identity, $(x^{\oplus i})^{\oplus i}=x$, and the flipped coordinate is negated: $(x^{\oplus i})_i=\neg x_i$, $(x^{\oplus i})_i^\pm=-x_i^\pm$.
--   2. $(x_i^\pm)^2=1$.
--   3. $\operatorname{sgn}(0)=1$, $\operatorname{sgn}(t)\in\{1,-1\}$ and $\operatorname{sgn}(t)^2=1$.
--   4. The cube has $2^n$ vertices.
--
--   These simplification rules are used throughout computations of averages over the cube.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/Statement.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/Statement.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CourtadeKumar mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar

namespace OAI

open scoped BigOperators

namespace LeanBlast.GotsmanLinial

@[simp] theorem flip_apply_same {n : ℕ} (i : Fin n) (x : Cube n) :
    flip i x i = !(x i) := by
  simp [flip]

@[simp] theorem flip_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    flip i (flip i x) = x := by
  funext j
  by_cases h : j = i
  · subst j
    simp [flip]
  · simp [flip, h]

@[simp] theorem cubeCoord_flip_same {n : ℕ} (x : Cube n) (i : Fin n) :
    cubeCoord (flip i x) i = -cubeCoord x i := by
  cases hxi : x i <;> simp [cubeCoord, flip, hxi]

@[simp] theorem cubeCoord_sq {n : ℕ} (x : Cube n) (i : Fin n) :
    (cubeCoord x i) ^ 2 = 1 := by
  cases hxi : x i <;> simp [cubeCoord, hxi]

@[simp] theorem thresholdSign_zero : thresholdSign 0 = 1 := by
  simp [thresholdSign]

theorem thresholdSign_cases (t : ℝ) : thresholdSign t = 1 ∨ thresholdSign t = -1 := by
  unfold thresholdSign
  split <;> simp

@[simp] theorem thresholdSign_sq (t : ℝ) : thresholdSign t ^ 2 = 1 := by
  rcases thresholdSign_cases t with h | h <;> simp [h]

@[simp] theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]

end LeanBlast.GotsmanLinial

end OAI


