-- Prove2me | Definitions.Def_VlasovMaxwell
-- name    : VlasovMaxwell
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:13.801779+00:00
-- url     : https://prove2.me/theorems/31a34db3-7556-4fed-a1f9-ea41adc24e6e
-- statement:
--   This block sets up the relativistic Vlasov–Maxwell system in three space dimensions. Vec is Euclidean 3-space, Phase is pairs (x,v) of position and momentum, a Particle density is a real function of (t,x,v), and a Field is a vector-valued function of (t,x). With q(v)=√(1+|v|²), velocity(v)=v/q(v). The block defines the dot and cross products, spatial partial derivatives via the Fréchet derivative along coordinate basis vectors, divergence, and curl, together with the charge density rho(g)(x)=∫g(x,v)dv and current(g)(x)=∫g(x,v)·velocity(v)dv. A Datum consists of an initial density f₀ and initial fields E₀, B₀. BoundedSmooth F means F is C^∞ and each iterated derivative is uniformly bounded. Admissible(d) requires f₀ to be C^∞, compactly supported and nonnegative, E₀ and B₀ to be bounded smooth and in L², div E₀ = rho(f₀), and div B₀ = 0. A Solution is a triple (f,E,B). TimeContinuousL2 F says that F agrees almost everywhere at each t≥0 with an L² (Lp) valued function continuous on [0,∞). Equations(s) requires, for every t≥0, the Vlasov equation ∂ₜf + velocity(v)·∇ₓf + (E + velocity(v)×B)·∇ᵥf = 0 (time derivative taken within [0,∞)), together with ∂ₜE − curl B = −current(f), ∂ₜB + curl E = 0, div E = rho(f), and div B = 0. CompactOnFiniteHorizons says that for each T≥0 the topological supports of f(t,·), t in [0,T], lie in a single compact set of phase space. Classical(d,s) bundles: f is C¹ on the half-space t≥0 and E and B are C¹ on t≥0; f is nonnegative for t≥0; E and B are time-continuous in L²; compact support on finite horizons; the equations hold; and the initial values equal f₀, E₀, B₀ at t=0. SmoothOnFiniteHorizons says f, E, B are C^∞ on each slab 0≤t≤T. SameNonnegativeTime(s,s') says two solutions agree pointwise in f, E, B for all t≥0. These are definitions only; no existence, uniqueness or regularity theorem is stated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/VlasovMaxwell.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/VlasovMaxwell.lean; bytes 16..4060
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace RVM

abbrev Vec := EuclideanSpace ℝ (Fin 3)
abbrev Phase := Vec × Vec
abbrev Particle := ℝ × Phase → ℝ
abbrev Field := ℝ × Vec → Vec

def q (v : Vec) : ℝ := Real.sqrt (1 + ‖v‖ ^ 2)
def velocity (v : Vec) : Vec := (q v)⁻¹ • v

def basis (i : Fin 3) : Vec := WithLp.toLp 2 (Pi.single i (1 : ℝ))
def dot (a b : Vec) : ℝ := ∑ i : Fin 3, a i * b i
def cross (a b : Vec) : Vec := WithLp.toLp 2
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0]

def spatialPartial (g : Vec → ℝ) (x : Vec) (i : Fin 3) : ℝ :=
  fderiv ℝ g x (basis i)
def divergence (F : Vec → Vec) (x : Vec) : ℝ :=
  ∑ i : Fin 3, spatialPartial (fun y => F y i) x i

def curl (F : Vec → Vec) (x : Vec) : Vec := WithLp.toLp 2
  ![spatialPartial (fun y => F y 2) x 1 - spatialPartial (fun y => F y 1) x 2,
    spatialPartial (fun y => F y 0) x 2 - spatialPartial (fun y => F y 2) x 0,
    spatialPartial (fun y => F y 1) x 0 - spatialPartial (fun y => F y 0) x 1]

def rho (g : Phase → ℝ) (x : Vec) : ℝ := ∫ v : Vec, g (x, v)
def current (g : Phase → ℝ) (x : Vec) : Vec :=
  ∫ v : Vec, g (x, v) • velocity v

structure Datum where
  f₀ : Phase → ℝ
  E₀ : Vec → Vec
  B₀ : Vec → Vec

def BoundedSmooth (F : Vec → Vec) : Prop :=
  ContDiff ℝ ∞ F ∧ ∀ n : ℕ, ∃ C : ℝ, ∀ x : Vec,
    ‖iteratedFDeriv ℝ n F x‖ ≤ C

def Admissible (d : Datum) : Prop :=
  ContDiff ℝ ∞ d.f₀ ∧ HasCompactSupport d.f₀ ∧ (∀ z, 0 ≤ d.f₀ z) ∧
  BoundedSmooth d.E₀ ∧ BoundedSmooth d.B₀ ∧
  MemLp d.E₀ 2 volume ∧ MemLp d.B₀ 2 volume ∧
  (∀ x, divergence d.E₀ x = rho d.f₀ x) ∧
  (∀ x, divergence d.B₀ x = 0)

structure Solution where
  f : Particle
  E : Field
  B : Field

def particleHalfSpace : Set (ℝ × Phase) := {z | 0 ≤ z.1}
def fieldHalfSpace : Set (ℝ × Vec) := {z | 0 ≤ z.1}
def particleSlab (T : ℝ) : Set (ℝ × Phase) := {z | z.1 ∈ Icc 0 T}
def fieldSlab (T : ℝ) : Set (ℝ × Vec) := {z | z.1 ∈ Icc 0 T}

def TimeContinuousL2 (F : Field) : Prop :=
  ∃ F₂ : ℝ → Lp Vec 2 (volume : Measure Vec),
    ContinuousOn F₂ (Ici 0) ∧
    ∀ t, 0 ≤ t → (F₂ t : Vec → Vec) =ᵐ[volume] (fun x => F (t, x))

def Equations (s : Solution) : Prop := ∀ t, 0 ≤ t →
  (∀ x v,
    derivWithin (fun t' => s.f (t', x, v)) (Ici 0) t +
    (∑ i : Fin 3, velocity v i * spatialPartial (fun y => s.f (t, y, v)) x i) +
    (∑ i : Fin 3, (s.E (t, x) + cross (velocity v) (s.B (t, x))) i *
      spatialPartial (fun v' => s.f (t, x, v')) v i) = 0) ∧
  (∀ x, derivWithin (fun t' => s.E (t', x)) (Ici 0) t -
    curl (fun y => s.B (t, y)) x = -current (fun z => s.f (t, z)) x) ∧
  (∀ x, derivWithin (fun t' => s.B (t', x)) (Ici 0) t +
    curl (fun y => s.E (t, y)) x = 0) ∧
  (∀ x, divergence (fun y => s.E (t, y)) x = rho (fun z => s.f (t, z)) x) ∧
  (∀ x, divergence (fun y => s.B (t, y)) x = 0)

def CompactOnFiniteHorizons (s : Solution) : Prop :=
  ∀ T : ℝ, 0 ≤ T → ∃ K : Set Phase, IsCompact K ∧
    ∀ t ∈ Icc 0 T, tsupport (fun z => s.f (t, z)) ⊆ K

def Classical (d : Datum) (s : Solution) : Prop :=
  ContDiffOn ℝ 1 s.f particleHalfSpace ∧
  ContDiffOn ℝ 1 s.E fieldHalfSpace ∧ ContDiffOn ℝ 1 s.B fieldHalfSpace ∧
  (∀ t, 0 ≤ t → ∀ z, 0 ≤ s.f (t, z)) ∧
  TimeContinuousL2 s.E ∧ TimeContinuousL2 s.B ∧
  CompactOnFiniteHorizons s ∧ Equations s ∧
  (∀ z, s.f (0, z) = d.f₀ z) ∧
  (∀ x, s.E (0, x) = d.E₀ x) ∧ (∀ x, s.B (0, x) = d.B₀ x)

def SmoothOnFiniteHorizons (s : Solution) : Prop := ∀ T : ℝ, 0 ≤ T →
  ContDiffOn ℝ ∞ s.f (particleSlab T) ∧
  ContDiffOn ℝ ∞ s.E (fieldSlab T) ∧ ContDiffOn ℝ ∞ s.B (fieldSlab T)

def SameNonnegativeTime (s s' : Solution) : Prop := ∀ t, 0 ≤ t →
  (∀ z, s.f (t, z) = s'.f (t, z)) ∧
  (∀ x, s.E (t, x) = s'.E (t, x)) ∧ (∀ x, s.B (t, x) = s'.B (t, x))



end RVM
end
end OAI


