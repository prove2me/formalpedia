-- Prove2me | Definitions.Def_RamseyDisambig_Spherical_Torus
-- name    : RamseyDisambig_Spherical_Torus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:25:22.361501+00:00
-- url     : https://prove2.me/theorems/b7f89974-07fe-4fe1-a85e-26334e396961
-- title:
--   Cyclic distance, discrete tori and distance-profile canonicality
-- statement:
--   Let $R\ge1$ be a positive integer, and use representatives $0,\ldots,R-1$ for the residues in $\mathbb Z_R$. Define
--   $$d_{\mathbb Z_R}(x,y)=\min\{|x-y|,R-|x-y|\}.$$
--   For $x,y\in(\mathbb Z_R)^n$, set
--   $$\delta(x,y)_i=d_{\mathbb Z_R}(x_i,y_i),\qquad d_T(x,y)=\sum_{i=0}^{n-1}\delta(x,y)_i.$$
--   A binary coloring $c$ is distance-profile-canonical if
--   $$\delta(x,y)=\delta(x',y')\ \Longrightarrow\ c(x,y)=c(x',y').$$
--   This is equivalent to factorization through a function on $\{0,\ldots,\lfloor R/2\rfloor\}^n$. The metric has diameter $n\lfloor R/2\rfloor$. The finite-diameter definition computes that diameter; the value is not supplied as a hypothesis.
--
--   These definitions express the common geometry of Lemmas 8 and 12 and Theorem 13.
--
--   **Formalization Note** The side length has type `ℕ+`, the torus is `Fin n → ZMod R`, and representatives are `ZMod.val`. Coordinates of the profile are represented as real numbers with integer values. Positive dimensions are enforced in the theorem statements; a zero-dimensional torus is a singleton, so it admits no gap coloring.
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), §2.1, pp. 8–9 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_GapColoring

set_option autoImplicit false

noncomputable section

namespace RamseyDisambig.Spherical

/-- Positive side lengths exclude ZMod 0 = Z. The dimension is separately constrained. -/
abbrev Torus (R : ℕ+) (n : ℕ) := Fin n → ZMod (R : ℕ)

/-- Shorter arc using representatives in [0,R-1], p. 8. -/
def cyclicDistance {R : ℕ+} (x y : ZMod (R : ℕ)) : ℝ :=
  min (|(x.val : ℝ) - (y.val : ℝ)|) ((R : ℝ) - |(x.val : ℝ) - (y.val : ℝ)|)

def distanceProfile {R : ℕ+} {n : ℕ} (x y : Torus R n) : Fin n → ℝ :=
  fun i => cyclicDistance (x i) (y i)

def torusDistance {R : ℕ+} {n : ℕ} (x y : Torus R n) : ℝ :=
  ∑ i, distanceProfile x y i

/-- Equivalent factorization-free formulation of the definition on p. 8. -/
def DistanceProfileCanonical {R : ℕ+} {n : ℕ} (c : Torus R n → Torus R n → Bool) : Prop :=
  ∀ x y x' y', distanceProfile x y = distanceProfile x' y' → c x y = c x' y'

end RamseyDisambig.Spherical


