-- Prove2me | Definitions.Def_KnotsInsideFractals_knots
-- name    : KnotsInsideFractals_knots
-- status  : Definition
-- author  : @LG
-- created : 2026-11-26T15:07:29.298616+00:00
-- url     : https://prove2.me/theorems/d2db947d-98ff-4ec9-8da4-b85b6b5eedec
-- title:
--   Polygonal knots, ambient isotopy, embedding indices
-- statement:
--   Polygonal (tame) knots, ambient isotopy, and the fractal-embedding indices for *Knots Inside Fractals*.
--
--   A **polygonal knot** (`PolygonalKnot`) is an embedded simple closed polygon in $\mathbb{R}^3$: at least three distinct vertices $v_0,\dots,v_{m-1}$, with consecutive edges (cyclically) meeting only at their shared endpoint and non-adjacent edges disjoint. Its image is `K.set`. This faithfully represents tame knots.
--
--   Two sets $A,B\subseteq\mathbb{R}^3$ are **ambient isotopic** (`AmbientIsotopic A B`) when there is a continuous $F:\mathbb{R}^3\times\mathbb{R}\to\mathbb{R}^3$ with each $F_t$ a homeomorphism, $F_0=\mathrm{id}$, and $F_1(A)=B$.
--
--   A knot $K$ **embeds in** $M_n$ (`EmbedsInMenger K n`) when an ambient-isotopic copy lies in the $1$-skeleton of the $n$-th Menger iteration; similarly for $S_n$ (`EmbedsInSierpinski K n`). The indices $M(K)$ and $S(K)$ are the least such iterations (as $\mathrm{sInf}$); $S(K)$ is meaningful only when $K$ embeds in some $S_n$.
--
--   **Formalization Note.** Ambient isotopy is encoded by a jointly continuous family of bijective slices with continuous inverses. The minima use $\mathrm{sInf}$ on $\mathbb{N}$; Theorem 1 guarantees the Menger set is nonempty.
-- source:
--   Broden–Espinosa–Nazareth–Voth, Knots Inside Fractals, https://arxiv.org/abs/2409.03639, §3, §5 Definition 1

import Mathlib
import Definitions.Def_KnotsInsideFractals_fractals
open Set KnotsInsideFractals
namespace KnotsInsideFractals
noncomputable section
def next {m : ℕ} (hm : 0 < m) (i : Fin m) : Fin m := ⟨(i.val + 1) % m, Nat.mod_lt _ hm⟩
def edge {m : ℕ} (v : Fin m → R3) (hm : 0 < m) (i : Fin m) : Set R3 := segment ℝ (v i) (v (next hm i))
def polygon {m : ℕ} (v : Fin m → R3) (hm : 0 < m) : Set R3 := ⋃ i : Fin m, edge v hm i
structure PolygonalKnot where
  m : ℕ
  hm : 3 ≤ m
  v : Fin m → R3
  inj : Function.Injective v
  simple : ∀ i j : Fin m, i ≠ j →
    edge v (by omega) i ∩ edge v (by omega) j ⊆
      if next (by omega) i = j then {v j} else if next (by omega) j = i then {v i} else ∅
def PolygonalKnot.set (K : PolygonalKnot) : Set R3 := polygon K.v (lt_of_lt_of_le (by norm_num : (0:ℕ) < 3) K.hm)
def AmbientIsotopic (A B : Set R3) : Prop :=
  ∃ F : R3 × ℝ → R3,
    Continuous F ∧
    (∀ t, Function.Bijective (fun x => F (x, t))) ∧
    (∀ t, Continuous (Function.invFun (fun x => F (x, t)))) ∧
    (∀ x, F (x, 0) = x) ∧
    (fun x => F (x, 1)) '' A = B
def EmbedsInMenger (K : PolygonalKnot) (n : ℕ) : Prop :=
  ∃ L : PolygonalKnot, L.set ⊆ mengerSkeleton n ∧ AmbientIsotopic K.set L.set
def EmbedsInSierpinski (K : PolygonalKnot) (n : ℕ) : Prop :=
  ∃ L : PolygonalKnot, L.set ⊆ sierpinskiSkeleton n ∧ AmbientIsotopic K.set L.set
def M (K : PolygonalKnot) : ℕ := sInf {n | EmbedsInMenger K n}
def S (K : PolygonalKnot) : ℕ := sInf {n | EmbedsInSierpinski K n}
end
end KnotsInsideFractals


