-- Prove2me | Definitions.Def_RegMT_Classif_Supplement_Architecture
-- name    : RegMT_Classif_Supplement_Architecture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:28:34.623568+00:00
-- url     : https://prove2.me/theorems/24ea2396-f020-4d56-9eba-257882b73704
-- title:
--   General normed feedforward architecture
-- statement:
--   For $M$ layers, each layer has its own finite-dimensional real normed space, activation $\sigma_m$, and arbitrary continuous linear weight map $W_m$. The weight parameter space includes every such collection. Recursively apply $x_{m+1}=\sigma_m(W_mx_m)$, and read the scalar output with the coordinate isomorphism $o:E_M\to\mathbb R$.
--   $$a(W)=\prod_{m=1}^M\operatorname{lip}(\sigma_m)\|W_m\|.$$
--   The vector activation modulus is its supremum of norm ratios, possibly $+\infty$. The induced norms are the actual continuous-linear-map operator norms for the adjacent layer norms. The scalar-output Lipschitz estimate uses $\|o\|a(W)$ when the final scalar norm differs from absolute value. Under the usual absolute-value output norm, $\|o\|=1$. This is an independent architecture definition, not a restriction to coordinatewise scalar activations or to any selected weight collection.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p.17, §3.4, architecture and layer moduli; p.18 Theorem 3.30; p.41 (48); output-norm correction documented in DISPROOF.md

import Mathlib

open scoped ENNReal

noncomputable section

namespace RegMT.Classif.Supplement
attribute [local instance] Classical.propDecidable

/-- General layered architecture: all finite-dimensional layer norms are independent. -/
structure Layers (M : ℕ) where
  Space : ℕ → Type
  [group : ∀ m, NormedAddCommGroup (Space m)]
  [scalar : ∀ m, NormedSpace ℝ (Space m)]
  [finite : ∀ m, FiniteDimensional ℝ (Space m)]
  activation : (m : Fin M) → Space (m.val + 1) → Space (m.val + 1)
  continuous_activation : ∀ m, Continuous (activation m)
  output : Space M ≃L[ℝ] ℝ

attribute [instance] Layers.group Layers.scalar Layers.finite

variable {M : ℕ}

def Weights (A : Layers M) := (m : Fin M) → A.Space m.val →L[ℝ] A.Space (m.val + 1)

def netState (A : Layers M) (W : Weights A) : (m : ℕ) → A.Space 0 → A.Space m
  | 0 => fun x => x
  | m + 1 => fun x => if hm : m < M then
      A.activation ⟨m, hm⟩ (W ⟨m, hm⟩ (netState A W m x)) else 0

def network (A : Layers M) (W : Weights A) (x : A.Space 0) : ℝ :=
  A.output (netState A W M x)

/-- p.17: vector-valued norm-ratio Lipschitz modulus, including +∞. -/
def activationModulus (A : Layers M) (m : Fin M) : ℝ≥0∞ :=
  ⨆ z : A.Space (m.val + 1), ⨆ z' : A.Space (m.val + 1), ⨆ (_ : z ≠ z'),
    ENNReal.ofReal (‖A.activation m z - A.activation m z'‖ / ‖z - z'‖)

def layerProduct (A : Layers M) (W : Weights A) : ℝ≥0∞ :=
  ∏ m, activationModulus A m * ENNReal.ofReal ‖W m‖

/-- Conversion needed when the last layer's scalar norm is not absolute value. -/
def outputProduct (A : Layers M) (W : Weights A) : ℝ≥0∞ :=
  ENNReal.ofReal ‖(A.output : A.Space M →L[ℝ] ℝ)‖ * layerProduct A W


end RegMT.Classif.Supplement


