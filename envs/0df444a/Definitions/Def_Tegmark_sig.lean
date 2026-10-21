-- Prove2me | Definitions.Def_Tegmark_sig
-- name    : Tegmark_sig
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T04:09:41.359231+00:00
-- url     : https://prove2.me/theorems/1da0cbe4-1a20-4ffe-a3b5-35929bb4b2b3
-- title:
--   The signature layer: worlds, the quadratic form, the PDE classes, and the data hyperplanes
-- statement:
--   The signature layer of Max Tegmark's letter "On the dimensionality of spacetime" (Classical and Quantum Gravity 14 (1997) L69-L75). A world with n space and m time dimensions is the coordinate space over the disjoint union of the n space directions and the m time directions, carrying the quadratic form that counts space coordinates positively and time coordinates negatively: a single minus sign distinguishes time from space. The layer defines the spacelike and timelike classification of vectors and of submodules; the elliptic, hyperbolic, and ultrahyperbolic classification of the second-order covariant field equations by the signs of the eigenvalues of their principal symbol — for the covariant equations (the wave equation and the Klein-Gordon equation) these are the eigenvalue signs of the metric, so the class is read off the numbers n and m; and the hyperplanes, the kernels of nonzero linear functionals, on which initial data can be posed, with the spacelike and timelike definite ones singled out. The predictability requirement of the letter's pages L72-L74 is the conjunction: the field equations are hyperbolic, so that initial-value problems are well posed, and a spacelike hyperplane exists on which to pose the data. The intended model is the flat linear-algebra skeleton of the letter's discussion: the PDE classification, the Asgeirsson discussion, and the data-surface argument are pointwise and linear, and the coordinate model carries them exactly.
-- source:
--   M. Tegmark, On the dimensionality of spacetime, Class. Quantum Grav. 14 (1997) L69-L75, pp. L69, L72-L74 (after Courant and Hilbert 1962; Asgeirsson 1936).

import Mathlib

open scoped BigOperators

namespace Tegmark

/-!
# On the dimensionality of spacetime: the signature layer

The signature layer of Max Tegmark's letter "On the dimensionality of
spacetime" (Classical and Quantum Gravity 14 (1997) L69-L75). A world
with "n" space and "m" time dimensions is the coordinate space over
the disjoint union of the "n" space directions and the "m" time
directions, carrying the quadratic form that counts space coordinates
positively and time coordinates negatively. The layer defines the
spacelike and timelike classification of vectors and submodules, the
elliptic, hyperbolic, and ultrahyperbolic classification of the
second-order field equations by the eigenvalue signs of their
principal symbol, the hyperplanes on which initial data can be posed,
and the predictability requirement of pages L72 to L74.
-/

/-- The point space of a world with "n" space and "m" time dimensions:
the coordinate space over the disjoint union of the "n" space
directions and the "m" time directions (Tegmark 1997, p. L69). -/
abbrev World (n m : ℕ) : Type := (Fin n ⊕ Fin m) → ℝ

/-- The quadratic form of the signature "(n, m)": space coordinates
count positively and time coordinates negatively, so that a single
minus sign distinguishes time from space (Tegmark 1997, p. L73). -/
def teg (n m : ℕ) (v : World n m) : ℝ :=
  (∑ i, v (Sum.inl i) ^ 2) - ∑ j, v (Sum.inr j) ^ 2

/-- A vector is spacelike when the form is positive on it. -/
def Spacelike (n m : ℕ) (v : World n m) : Prop := 0 < teg n m v

/-- A vector is timelike when the form is negative on it. -/
def Timelike (n m : ℕ) (v : World n m) : Prop := teg n m v < 0

/-- The classification of a second-order linear partial differential
equation by the signs of the eigenvalues of its principal symbol
(Tegmark 1997, p. L72): elliptic when all the eigenvalues have the
same sign, hyperbolic when exactly one has one sign and the rest the
other, ultrahyperbolic in the remaining case where at least two have
each sign. -/
inductive PDEClass : Type
  | elliptic : PDEClass
  | hyperbolic : PDEClass
  | ultrahyperbolic : PDEClass

/-- For the covariant field equations of a world with "n" space and
"m" time dimensions, among them the wave equation and the
Klein-Gordon equation, the principal symbol has the same eigenvalue
signs as the metric (Tegmark 1997, p. L73), so the class of the field
equations is read off the numbers of positive and negative
eigenvalues. -/
def pdeClass (n m : ℕ) : PDEClass :=
  if n = 0 ∨ m = 0 then PDEClass.elliptic
  else if n = 1 ∨ m = 1 then PDEClass.hyperbolic
  else PDEClass.ultrahyperbolic

/-- A submodule of the point space is spacelike when the form is
positive on every nonzero vector of it: a positive-definite
subspace. -/
def SpacelikeSubmodule (n m : ℕ) (s : Submodule ℝ (World n m)) : Prop :=
  ∀ v ∈ s, v ≠ 0 → 0 < teg n m v

/-- A submodule of the point space is timelike when the form is
negative on every nonzero vector of it: a negative-definite
subspace. -/
def TimelikeSubmodule (n m : ℕ) (s : Submodule ℝ (World n m)) : Prop :=
  ∀ v ∈ s, v ≠ 0 → teg n m v < 0

/-- The world has a spacelike hyperplane: a codimension-one
subspace, presented as the kernel of a nonzero linear functional, on
which the form is positive definite; a hypersurface on which an
observer can record initial data (Tegmark 1997, pp. L73-L74). -/
def HasSpacelikeHyperplane (n m : ℕ) : Prop :=
  ∃ f : World n m →ₗ[ℝ] ℝ, f ≠ 0 ∧ SpacelikeSubmodule n m (LinearMap.ker f)

/-- The world has a timelike hyperplane: the kernel of a nonzero
linear functional on which the form is negative definite. -/
def HasTimelikeHyperplane (n m : ℕ) : Prop :=
  ∃ f : World n m →ₗ[ℝ] ℝ, f ≠ 0 ∧ TimelikeSubmodule n m (LinearMap.ker f)

/-- The predictability requirement (Tegmark 1997, pp. L72-L74): an
observer can make predictions only when the field equations are
hyperbolic, so that initial-value problems are well posed, and the
initial data can be posed on a spacelike hyperplane. -/
def Predictable (n m : ℕ) : Prop :=
  pdeClass n m = PDEClass.hyperbolic ∧ HasSpacelikeHyperplane n m

end Tegmark


