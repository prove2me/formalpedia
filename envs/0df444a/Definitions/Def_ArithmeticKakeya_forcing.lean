-- Prove2me | Definitions.Def_ArithmeticKakeya_forcing
-- name    : ArithmeticKakeya_forcing
-- status  : Definition
-- author  : @LG
-- created : 2026-11-16T21:54:53.254543+00:00
-- url     : https://prove2.me/theorems/840146bc-2a78-46ac-83fa-75f9091d538b
-- title:
--   Forcing pairs for arithmetic Kakeya
-- statement:
--   `IsXSet G R T` says $(R,T)$ is an $X$-set: $R$ is a duplicate-free list of single-site functions $\mathbf{x}g$ (value $\mathbf{x}\in X\setminus\{0\}$ at one vertex $g$, zero elsewhere) and $T$ a duplicate-free list of vertices. `Forces G R T` is the backward-inductive closure expressing that finitely many forcing operations from $(R,T)$ eventually know every vertex: add an edge function, add a vertex $e$ when some $f\in R$ equals $(a,-a)$ ($a\ne0$) at $e$ and vanishes off $T\cup\{e\}$, or add a difference $f-g$. This matches the source's forcing-pair definition; the duplicate-free convention gives set semantics for the score.
-- source:
--   https://epoch.ai/frontiermath/open-problems/arithmetic-kakeya (Verifiable Set-up / Introduction)

import Mathlib
import Definitions.Def_ArithmeticKakeya_grid

namespace ArithmeticKakeya

/-- An `X`-set for `G`: `R` is a duplicate-free list of single-site functions `x·g`
(value `x ∈ X \ {0}` at one vertex `g`, zero elsewhere), and `T` is a duplicate-free
list of vertices. -/
def IsXSet {X : Finset (ℤ × ℤ)} (G : ConstructibleGraph X)
    (R : List (List ℕ → ℤ × ℤ)) (T : List (List ℕ)) : Prop :=
  R.Nodup ∧ T.Nodup ∧
  (∀ f ∈ R, ∃ (x : ℤ × ℤ) (g : List ℕ),
      x ∈ X ∧ x ≠ (0, 0) ∧ g ∈ grid G.dims ∧
      f = fun e => if e = g then x else (0, 0)) ∧
  (∀ e ∈ T, e ∈ grid G.dims)

/-- `Forces G R T`: from `(R,T)`, finitely many forcing operations eventually make `T`
contain every vertex. Backward-inductive: `done` = all vertices known; each rule peels
one operation (add an edge function, add a vertex, add a difference). -/
inductive Forces {X : Finset (ℤ × ℤ)} (G : ConstructibleGraph X) :
    List (List ℕ → ℤ × ℤ) → List (List ℕ) → Prop
  | done {R T} (hT : ∀ e ∈ grid G.dims, e ∈ T) : Forces G R T
  | edge {R T} (i : Fin G.dims.length) (a c : List ℕ)
      (ha : a ∈ grid (domainDims G.dims i))
      (hc : c ∈ grid (G.dims.drop (i.val + 1))) :
      Forces G (edgeFn G i a c :: R) T → Forces G R T
  | vertex {R T} (f : List ℕ → ℤ × ℤ) (hf : f ∈ R) (e : List ℕ)
      (he : e ∈ grid G.dims) (a : ℤ) (ha : a ≠ 0) (hfe : f e = (a, -a))
      (hsupp : ∀ g ∈ grid G.dims, g ∉ T → g ≠ e → f g = (0, 0)) :
      Forces G R (e :: T) → Forces G R T
  | diff {R T} (f g : List ℕ → ℤ × ℤ) (hf : f ∈ R) (hg : g ∈ R) :
      Forces G ((f - g) :: R) T → Forces G R T

end ArithmeticKakeya


