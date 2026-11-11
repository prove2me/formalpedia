-- Prove2me | Definitions.Def_DetTerminalEmbedding1373_Real_geometry
-- name    : DetTerminalEmbedding1373_Real_geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:23:32.472421+00:00
-- url     : https://prove2.me/theorems/6bf6560f-61c6-4c8b-b4b4-7d854cbc0da4
-- title:
--   Euclidean terminals, empirical tests and exact target dimension
-- statement:
--   Write $E_d=\mathbb R^d$ with its Euclidean norm and $B_2^d=\{z:\|z\|\le1\}$. Additive convex-hull distortion at most $\eta$ means $|\|Az\|-\|z\||\le\eta$ for every $z\in\operatorname{conv}(Y)$. Ordered samples with repetition define $E_s(Y)$, and
--
--   $$\delta_s=\tfrac18\min\{\eta\sqrt s,\eta^2 S\}.$$
--
--   The shared geometry also defines normalized signed directions, the terminal affine rank $r$, the test-count envelope $L=n\sum_{s=1}^S(2n-2)^s$, and the exact projection dimension
--
--   $$m_0=\left\lceil\frac{512}{(\varepsilon/6)^4S}\log(32n(n-1))\right\rceil.$$
--
--   For $n\ge2$ the final dimension is $M=m_0+1$; the singleton branch has $M=1$. These definitions supply the common model for every statement, using zero-based finite indices. Empty empirical samples have a totalized value but all tests use $s\ge1$.
-- source:
--   Vladimir Braverman, Kuan Cheng, Jiaqing Zhu, STOC 2027 submission #1373 (October 2026), pp. 8, 10–11, 20–22, Definition 3.1, Lemma 3.2, equations (38)–(39); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1373.pdf

import Mathlib

set_option autoImplicit false

namespace DetTerminalEmbedding1373.Real

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

def unitBall (d : ℕ) : Set (E d) := {x | ‖x‖ ≤ 1}

/-- Definition 3.1; a norm error, not a squared-norm error. -/
def ConvexHullDistortion {d m : ℕ} (A : E d →ₗ[ℝ] E m)
    (Y : Set (E d)) (η : ℝ) : Prop :=
  ∀ z ∈ convexHull ℝ Y, |‖A z‖ - ‖z‖| ≤ η

/-- Ordered samples, with repetitions. Only positive s is used in Lemma 3.2. -/
def empiricalSet {d : ℕ} (Y : Set (E d)) (s : ℕ) : Set (E d) :=
  {z | ∃ y : Fin s → E d, (∀ i, y i ∈ Y) ∧ z = (s : ℝ)⁻¹ • ∑ i, y i}

noncomputable def tolerance (η : ℝ) (S s : ℕ) : ℝ :=
  min (η * Real.sqrt (s : ℝ)) (η ^ 2 * (S : ℝ)) / 8

noncomputable def direction {d : ℕ} (v : E d) : E d := ‖v‖⁻¹ • v

def signedDirections {n d : ℕ} (x : Fin n → E d) : Set (E d) :=
  {v | ∃ i, v = direction (x i) ∨ v = -direction (x i)}

def terminalDirections {n d : ℕ} (x : Fin n → E d) (k : Fin n) : Set (E d) :=
  {v | ∃ i, i ≠ k ∧ (v = direction (x i - x k) ∨ v = -direction (x i - x k))}

def baseTerminal {n d : ℕ} (x : Fin n → E d) : E d :=
  if h : 0 < n then x ⟨0, h⟩ else 0

noncomputable def affineRank {n d : ℕ} (x : Fin n → E d) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i => x i - baseTerminal x)))

def maxTests (n S : ℕ) : ℕ := n * ∑ s ∈ Finset.Icc 1 S, (2 * n - 2) ^ s

/-- Equation (38): projection dimension. The machine computes this by exp comparisons. -/
noncomputable def projectionDimension (n : ℕ) (ε : ℝ) (S : ℕ) : ℕ :=
  ⌈512 / ((ε / 6) ^ 4 * (S : ℝ)) * Real.log (32 * (n : ℝ) * ((n : ℝ) - 1))⌉₊

/-- Final dimension; the literal singleton case has the exact radial map into ℝ. -/
noncomputable def targetDimension (n : ℕ) (ε : ℝ) (S : ℕ) : ℕ :=
  if n = 1 then 1 else projectionDimension n ε S + 1

end DetTerminalEmbedding1373.Real


