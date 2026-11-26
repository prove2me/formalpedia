-- Prove2me | Definitions.Def_KnotsInsideFractals_fractals
-- name    : KnotsInsideFractals_fractals
-- status  : Definition
-- author  : @LG
-- created : 2026-11-26T15:06:51.964945+00:00
-- url     : https://prove2.me/theorems/f9281398-7472-487b-88a3-650fd02c3a76
-- title:
--   Fractal iterations and 1-skeleta
-- statement:
--   The fractal iterations and their $1$-skeleta for *Knots Inside Fractals* (arXiv:2409.03639), in the ambient space $\mathbb{R}^3$.
--
--   The **Menger iteration** $M_n$ (`menger n`) is the union of the $20^n$ closed cubes of side $3^{-n}$ surviving $n$ rounds of the rule that deletes, from each cube, the subcubes whose position in $\{0,1,2\}^3$ has at least two coordinates equal to $1$ (the six face-centres and the body-centre). The **Menger sponge** is $M=\bigcap_n M_n$ (`mengerSet`). The **$1$-skeleton** of $M_n$ (`mengerSkeleton n`) is the union of the edges of its cubes, where a box edge is the locus of points with at least two coordinates at an endpoint.
--
--   The **Sierpinski iteration** $S_n$ (`sierpinski n`) is the union of $4^n$ closed tetrahedra of side $2^{-n}$, obtained from a regular tetrahedron by repeatedly keeping the four corner homothetic copies scaled by $1/2$; the **Sierpinski tetrahedron** is $S=\bigcap_n S_n$ (`sierpinskiSet`), and its $1$-skeleton (`sierpinskiSkeleton n`) is the union of the edges of its tetrahedra.
--
--   The **Cantor set** $C$ (`cantorSet`) is the middle-third Cantor set, and the **Cantor dust** $C\times C$ (`cantorDust`) is its square.
--
--   **Formalization Note.** $\mathbb{R}^3$ is represented as `Fin 3 → ℝ` with the product (Euclidean) topology; cubes and tetrahedra are tracked explicitly as finite sets so their edges can be taken.
-- source:
--   Broden–Espinosa–Nazareth–Voth, Knots Inside Fractals, https://arxiv.org/abs/2409.03639, §2.1

import Mathlib
open Set
namespace KnotsInsideFractals
noncomputable section
abbrev R3 := Fin 3 → ℝ
local instance : DecidableEq (R3 × ℝ) := Classical.decEq _
local instance : DecidableEq (Fin 4 → R3) := Classical.decEq _
def box (c : R3) (s : ℝ) : Set R3 := Set.pi Set.univ (fun i => Set.Icc (c i) (c i + s))
def keptPos (c : Fin 3 → Fin 3) : Prop := (Finset.univ.filter (fun i => c i = 1)).card ≤ 1
instance keptPos_dec (c : Fin 3 → Fin 3) : Decidable (keptPos c) := by unfold keptPos; infer_instance
def keptPositions : Finset (Fin 3 → Fin 3) := Finset.univ.filter keptPos
def posVec (c : Fin 3 → Fin 3) : R3 := fun i => ((c i : ℕ) : ℝ)
def mengerCubes : ℕ → Finset (R3 × ℝ)
  | 0 => {(0, 1)}
  | n + 1 => (mengerCubes n).biUnion (fun cs => keptPositions.image (fun p => (cs.1 + (cs.2 / 3) • posVec p, cs.2 / 3)))
def menger (n : ℕ) : Set R3 := ⋃ cs ∈ mengerCubes n, box cs.1 cs.2
def mengerSet : Set R3 := ⋂ n, menger n
def boxSkeleton (c : R3) (s : ℝ) : Set R3 := {x ∈ box c s | (Finset.univ.filter (fun i => x i = c i ∨ x i = c i + s)).card ≥ 2}
def mengerSkeleton (n : ℕ) : Set R3 := ⋃ cs ∈ mengerCubes n, boxSkeleton cs.1 cs.2
def tetV : Fin 4 → R3
  | 0 => ![0, 0, 0] | 1 => ![1, 0, 0] | 2 => ![1 / 2, Real.sqrt 3 / 2, 0] | 3 => ![1 / 2, Real.sqrt 3 / 6, Real.sqrt 6 / 3]
def sierpinskiTets : ℕ → Finset (Fin 4 → R3)
  | 0 => {tetV}
  | n + 1 => (sierpinskiTets n).biUnion (fun vs => (Finset.univ : Finset (Fin 4)).image (fun i => fun j => (1 / 2 : ℝ) • (vs j + tetV i)))
def sierpinski (n : ℕ) : Set R3 := ⋃ vs ∈ sierpinskiTets n, convexHull ℝ (Set.range vs)
def sierpinskiSet : Set R3 := ⋂ n, sierpinski n
def sierpinskiSkeleton (n : ℕ) : Set R3 := ⋃ vs ∈ sierpinskiTets n, ⋃ j : Fin 4, ⋃ k : Fin 4, segment ℝ (vs j) (vs k)
def cantor : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | n + 1 => (fun x => x / 3) '' cantor n ∪ (fun x => (x + 2) / 3) '' cantor n
def cantorSet : Set ℝ := ⋂ n, cantor n
def cantorDust : Set (ℝ × ℝ) := {p | p.1 ∈ cantorSet ∧ p.2 ∈ cantorSet}
end
end KnotsInsideFractals


