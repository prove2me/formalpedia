-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P07
-- name    : QAlgorithms_Papers_Independent_Gap48_P07
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T21:11:16.332725+00:00
-- url     : https://prove2.me/theorems/a4d2624f-9647-4ff4-9ba3-4a78bb1fa7ef
-- title:
--   Definitions for Bernstein functions and rates in mean ergodic theorems for operator semigroups
-- statement:
--   The objects the formalized statements of *Bernstein functions and rates in mean ergodic theorems for operator semigroups* (arXiv:1112.0286) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BoundedC0`: PDF pp.2,4: strong continuity includes zero; negative times are unused.
--   - `semigroupBound`: PDF p.16: bounded, nonempty norm range under BoundedC0, including time zero.
--   - `continuousCesaro`: PDF p.2, (1.1): vectorwise strong integral, used for t>0. Distinct from the accepted discrete matrix Cesaro average.
--   - `MeanErgodic`: PDF p.2: strong convergence on every vector.
--   - `FiniteRep`: PDF pp.4–5: witnesses for the accepted finite Laplace image, retaining its measure and density for vector integration.
--   - `laplaceNorm`: PDF p.4, (2.1): total variation norm, used only under LaplaceImage. Uniqueness of Laplace transforms makes every representing density give the same integral of its norm. The defining set is then nonempty and bounded below by 0.
--   - `hpEval`: PDF pp.4–5: concrete HP integral on this T. Independence of the selected finite representation and genuine vector integrability are theorem conclusions.
--   - `HPRegularizer`: PDF p.5: injective regularizer for the concrete evaluation.
--   - `HPRegularizable`: PDF p.5: holomorphic regularizable symbols; outside C+ values are unused.
--   - `hpGraph`: PDF p.5: natural graph, with an injective regularizer selected from Reg(f). The empty fallback is used only outside the regularizable class.
--   - `SpectralAccumulation`: PDF p.20: nonzero spectral points tending to zero; isolated zero is excluded.
--   - `VanishingFactor`: PDF pp.20–21: positive nonincreasing factors tending to zero.
--   - `BernsteinData`: PDF pp.7–8: Levy data, extended by zero off (0,infinity). Local finiteness is imposed away from zero; infinite mass near zero is allowed.
--   - `bernsteinValue`: PDF p.8, (2.7): canonical analytic and continuous boundary values.
--   - `bernsteinRate`: PDF p.13, (3.2): associated rate, used only at positive times. Distinct from accepted coding and channel-testing rates.
--   - `CompleteBernstein`: PDF p.10: complete Bernstein functions have a completely monotone Levy density.
--   - `NonzeroBernstein`: PDF pp.8,10: nonzero on the positive real axis.
--   - `cesaroSymbol`: PDF p.13: scalar Cesaro symbol, with its continuous value at zero.
--   - `LaplaceRadon`: PDF p.4: polar representation of a complex Radon measure; its locally finite positive variation and unit-modulus phase also cover positive measures.
--   - `radonLaplace`: PDF p.4: the source Laplace transform.
--   - `abelIntegral`: PDF p.6, (2.4): the actual damped vector integral.
--   - `WeakAbel`: PDF p.6: weak Abel convergence, explicitly including genuine integrability for every positive damping. Weak means every continuous linear functional.
--   - `improperIntegral`: PDF p.7, (2.5): actual truncated integral on [0,r].
--   - `WeakImproper`: PDF p.7: improper weak convergence, with locally genuine integrals.
--   - `GeneralRateConclusion`: PDF pp.16–17: all (a)–(c) of Theorem 3.4, expanded once for Corollary 3.5.
--   - `SharpRate`: PDF p.21: full sharpness, with unbounded real quotients rather than junk suprema.
--   - `logarithmicRateSymbol`: PDF p.22: removable logarithmic quotient, g(0)=0 and g(1)=1.
--   - `logarithmicStieltjes`: PDF pp.11–12: removable Stieltjes quotient, equal to one at z=1.
--   - `logRegularizer`: PDF p.22: the specific regularizer from this source.
--   - `constantBernstein`: PDF p.8: constant Bernstein data, including the allowed zero function.
-- source:
--   Bernstein functions and rates in mean ergodic theorems for operator semigroups, arXiv:1112.0286v1, https://arxiv.org/abs/1112.0286v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11

/-! arXiv:1112.0286v1, Gomilko–Haase–Tomilov. Statements only.
Same-semigroup constructions; no supplied abstract calculus. Compilation pending.
See HARD.md for whole-node deferrals, including three printed source defects. -/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace QAlgorithms.Papers.Independent.Gap48.P07

open QAlgorithms.Papers.Independent.Next46.P06
open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore graphPower)
open QAlgorithms.Papers.Independent.Renew46.P11
  (LaplaceImage Bernstein CompletelyMonotone SpecialBernstein StieltjesClass PositiveReal)

attribute [local instance] Classical.propDecidable

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- PDF pp.2,4: strong continuity includes zero; negative times are unused. -/
def BoundedC0 (T : ℝ → X →L[ℂ] X) : Prop :=
  BoundedSemigroup T ∧ ∀ x : X, ContinuousOn (fun t => T t x) (Ici 0)

/-- PDF p.16: bounded, nonempty norm range under BoundedC0, including time zero. -/
def semigroupBound (T : ℝ → X →L[ℂ] X) : ℝ :=
  sSup {r | ∃ t : ℝ, 0 ≤ t ∧ r = ‖T t‖}

/-- PDF p.2, (1.1): vectorwise strong integral, used for t>0.
Distinct from the accepted discrete matrix Cesaro average. -/
def continuousCesaro (T : ℝ → X →L[ℂ] X) (t : ℝ) (x : X) : X :=
  ((t : ℂ)⁻¹) • ∫ s in Icc (0 : ℝ) t, T s x

/-- PDF p.2: strong convergence on every vector. -/
def MeanErgodic (T : ℝ → X →L[ℂ] X) : Prop :=
  ∀ x : X, ∃ y : X, Tendsto (fun t => continuousCesaro T t x) atTop (𝓝 y)

/-- PDF pp.4–5: witnesses for the accepted finite Laplace image, retaining
its measure and density for vector integration. -/
def FiniteRep (f : ℂ → ℂ) (d : Measure NNReal × (NNReal → ℂ)) : Prop :=
  IsFiniteMeasure d.1 ∧ Integrable d.2 d.1 ∧ ∀ z : ℂ, 0 < z.re →
    Integrable (fun s : NNReal => Complex.exp (-((s : ℝ) : ℂ) * z) * d.2 s) d.1 ∧
    f z = ∫ s, Complex.exp (-((s : ℝ) : ℂ) * z) * d.2 s ∂d.1

/-- PDF p.4, (2.1): total variation norm, used only under LaplaceImage.
Uniqueness of Laplace transforms makes every representing density give the same
integral of its norm. The defining set is then nonempty and bounded below by 0. -/
def laplaceNorm (f : ℂ → ℂ) : ℝ :=
  sInf {r | ∃ d, FiniteRep f d ∧ r = ∫ s, ‖d.2 s‖ ∂d.1}

/-- PDF pp.4–5: concrete HP integral on this T. Independence of the selected
finite representation and genuine vector integrability are theorem conclusions. -/
def hpEval (T : ℝ → X →L[ℂ] X) (f : ℂ → ℂ) (x : X) : X :=
  if h : ∃ d, FiniteRep f d then
    let d := Classical.choose h
    ∫ s, d.2 s • T (s : ℝ) x ∂d.1
  else 0

/-- PDF p.5: injective regularizer for the concrete evaluation. -/
def HPRegularizer (T : ℝ → X →L[ℂ] X) (f e : ℂ → ℂ) : Prop :=
  LaplaceImage e ∧ LaplaceImage (e * f) ∧ Function.Injective (hpEval T e)

/-- PDF p.5: holomorphic regularizable symbols; outside C+ values are unused. -/
def HPRegularizable (T : ℝ → X →L[ℂ] X) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f {z | 0 < z.re} ∧ ∃ e, HPRegularizer T f e

/-- PDF p.5: natural graph, with an injective regularizer selected from Reg(f).
The empty fallback is used only outside the regularizable class. -/
def hpGraph (T : ℝ → X →L[ℂ] X) (f : ℂ → ℂ) : Graph X :=
  if h : HPRegularizable T f then
    let e := Classical.choose h.2
    {p | hpEval T (e * f) p.1 = hpEval T e p.2}
  else ∅

/-- PDF p.20: nonzero spectral points tending to zero; isolated zero is excluded. -/
def SpectralAccumulation (T : ℝ → X →L[ℂ] X) (S : Set ℂ := univ) : Prop :=
  ∃ z : ℕ → ℂ, (∀ n, z n ≠ 0 ∧ z n ∉ banachResolventSet (negativeGenerator T) ∧
    z n ∈ S) ∧ Tendsto z atTop (𝓝 0)

/-- PDF pp.20–21: positive nonincreasing factors tending to zero. -/
def VanishingFactor (e : ℝ → ℝ) : Prop :=
  (∀ t, 0 < t → 0 < e t) ∧ AntitoneOn e (Ioi 0) ∧ Tendsto e atTop (𝓝 0)

/-- PDF pp.7–8: Levy data, extended by zero off (0,infinity). Local finiteness
is imposed away from zero; infinite mass near zero is allowed. -/
structure BernsteinData where
  a : ℝ
  b : ℝ
  mu : Measure ℝ
  a_nonneg : 0 ≤ a
  b_nonneg : 0 ≤ b
  support_positive : mu (Iic 0) = 0
  locally_finite_positive : ∀ l r : ℝ, 0 < l → mu (Icc l r) < ⊤
  levy_integrable : Integrable (fun s => s / (1 + s)) mu

/-- PDF p.8, (2.7): canonical analytic and continuous boundary values. -/
def bernsteinValue (g : BernsteinData) (z : ℂ) : ℂ :=
  (g.a : ℂ) + (g.b : ℂ) * z + ∫ s, 1 - Complex.exp (-(s : ℂ) * z) ∂g.mu

/-- PDF p.13, (3.2): associated rate, used only at positive times.
Distinct from accepted coding and channel-testing rates. -/
def bernsteinRate (g : BernsteinData) (t : ℝ) : ℝ :=
  g.a / 2 + g.b / t + ∫ s, min (s / t) 1 ∂g.mu

/-- PDF p.10: complete Bernstein functions have a completely monotone Levy density. -/
def CompleteBernstein (g : BernsteinData) : Prop :=
  ∃ m : ℝ → ℝ, CompletelyMonotone m ∧
    g.mu = volume.withDensity (fun s => ENNReal.ofReal (if 0 < s then m s else 0))

/-- PDF pp.8,10: nonzero on the positive real axis. -/
def NonzeroBernstein (g : BernsteinData) : Prop :=
  ∃ t : ℝ, 0 < t ∧ bernsteinValue g (t : ℂ) ≠ 0

/-- PDF p.13: scalar Cesaro symbol, with its continuous value at zero. -/
def cesaroSymbol (t : ℝ) (z : ℂ) : ℂ :=
  if z = 0 then 1 else (1 - Complex.exp (-(t : ℂ) * z)) / ((t : ℂ) * z)

/-- PDF p.4: polar representation of a complex Radon measure; its locally
finite positive variation and unit-modulus phase also cover positive measures. -/
structure LaplaceRadon where
  variation : Measure ℝ≥0
  locally_finite : IsLocallyFiniteMeasure variation
  phase : ℝ≥0 → ℂ
  phase_norm : ∀ᵐ s ∂variation, ‖phase s‖ = 1
  transformable : ∀ a : ℝ, 0 < a →
    Integrable (fun s : NNReal => Complex.exp (-(a : ℂ) * ((s : ℝ) : ℂ)) * phase s) variation

/-- PDF p.4: the source Laplace transform. -/
def radonLaplace (m : LaplaceRadon) (z : ℂ) : ℂ :=
  ∫ s, Complex.exp (-((s : ℝ) : ℂ) * z) * m.phase s ∂m.variation

/-- PDF p.6, (2.4): the actual damped vector integral. -/
def abelIntegral (T : ℝ → X →L[ℂ] X) (m : LaplaceRadon) (a : ℝ) (x : X) : X :=
  ∫ s, (Complex.exp (-(a : ℂ) * ((s : ℝ) : ℂ)) * m.phase s) • T (s : ℝ) x ∂m.variation

/-- PDF p.6: weak Abel convergence, explicitly including genuine integrability
for every positive damping. Weak means every continuous linear functional. -/
def WeakAbel (T : ℝ → X →L[ℂ] X) (m : LaplaceRadon) (x y : X) : Prop :=
  (∀ a : ℝ, 0 < a → Integrable
    (fun s : NNReal => (Complex.exp (-(a : ℂ) * ((s : ℝ) : ℂ)) * m.phase s) • T (s : ℝ) x)
    m.variation) ∧
  ∀ l : X →L[ℂ] ℂ, Tendsto (fun a => l (abelIntegral T m a x)) (𝓝[>] 0) (𝓝 (l y))

/-- PDF p.7, (2.5): actual truncated integral on [0,r]. -/
def improperIntegral (T : ℝ → X →L[ℂ] X) (m : LaplaceRadon) (r : ℝ) (x : X) : X :=
  ∫ s in {s : ℝ≥0 | (s : ℝ) ≤ r}, m.phase s • T (s : ℝ) x ∂m.variation

/-- PDF p.7: improper weak convergence, with locally genuine integrals. -/
def WeakImproper (T : ℝ → X →L[ℂ] X) (m : LaplaceRadon) (x y : X) : Prop :=
  (∀ r : ℝ, 0 < r → IntegrableOn (fun s => m.phase s • T (s : ℝ) x)
    {s : ℝ≥0 | (s : ℝ) ≤ r} m.variation) ∧
  ∀ l : X →L[ℂ] ℂ, Tendsto (fun r => l (improperIntegral T m r x)) atTop (𝓝 (l y))

/-- PDF pp.16–17: all (a)–(c) of Theorem 3.4, expanded once for Corollary 3.5. -/
def GeneralRateConclusion (g : BernsteinData) (T : ℝ → X →L[ℂ] X) : Prop :=
  (∀ x y : X, (x, y) ∈ hpGraph T (bernsteinValue g) → ∀ t : ℝ, 0 < t →
    ‖continuousCesaro T t y‖ ≤ 2 * semigroupBound T * bernsteinRate g t * ‖x‖) ∧
  ((Tendsto (fun t => t * bernsteinRate g t) atTop atTop ∧ g.a = 0 ∧ MeanErgodic T) →
    ∀ y ∈ graphRange (hpGraph T (bernsteinValue g)),
      Asymptotics.IsLittleO atTop (fun t => ‖continuousCesaro T t y‖) (bernsteinRate g)) ∧
  (Asymptotics.IsBigO atTop (fun t => t * bernsteinRate g t) (fun _ => (1 : ℝ)) →
    graphRange (hpGraph T (bernsteinValue g)) ⊆ graphRange (negativeGenerator T) ∧
    ∀ y ∈ graphRange (hpGraph T (bernsteinValue g)),
      Asymptotics.IsBigO atTop (fun t => ‖continuousCesaro T t y‖) (fun t : ℝ => t⁻¹))

/-- PDF p.21: full sharpness, with unbounded real quotients rather than junk suprema. -/
def SharpRate (T : ℝ → X →L[ℂ] X) (G : Graph X) (r : ℝ → ℝ) : Prop :=
  ∀ e : ℝ → ℝ, VanishingFactor e → ∃ y ∈ graphRange G,
    ∀ K : ℝ, ∃ t : ℝ, 1 ≤ t ∧ K < ‖continuousCesaro T t y‖ / (e t * r t)

/-- PDF p.22: removable logarithmic quotient, g(0)=0 and g(1)=1. -/
def logarithmicRateSymbol (z : ℂ) : ℂ :=
  if z = 0 then 0 else if z = 1 then 1 else (z - 1) / Complex.log z

/-- PDF pp.11–12: removable Stieltjes quotient, equal to one at z=1. -/
def logarithmicStieltjes (z : ℂ) : ℂ :=
  if z = 1 then 1 else Complex.log z / (z - 1)

/-- PDF p.22: the specific regularizer from this source. -/
def logRegularizer (z : ℂ) : ℂ := z / (1 + z) ^ 2

example (T : ℝ → X →L[ℂ] X) : graphPower (negativeGenerator T) 0 = identityGraph := rfl

example : logarithmicRateSymbol 0 = 0 := by simp [logarithmicRateSymbol]

example : logarithmicRateSymbol 1 = 1 := by simp [logarithmicRateSymbol]

example : logarithmicStieltjes 1 = 1 := by simp [logarithmicStieltjes]

example (g : BernsteinData) : bernsteinValue g 0 = (g.a : ℂ) := by simp [bernsteinValue]

example (T : ℝ → X →L[ℂ] X) (f : ℂ → ℂ) (h : ¬ HPRegularizable T f) :
    hpGraph T f = ∅ := by simp [hpGraph, h]

/-- PDF p.8: constant Bernstein data, including the allowed zero function. -/
def constantBernstein (a : ℝ) (ha : 0 ≤ a) : BernsteinData where
  a := a
  b := 0
  mu := 0
  a_nonneg := ha
  b_nonneg := le_rfl
  support_positive := by simp
  locally_finite_positive := by intro l r hl; simp
  levy_integrable := by simp

example (a : ℝ) (ha : 0 ≤ a) (z : ℂ) :
    bernsteinValue (constantBernstein a ha) z = (a : ℂ) := by
  simp [bernsteinValue, constantBernstein]

example (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    bernsteinRate (constantBernstein a ha) t = a / 2 := by
  simp [bernsteinRate, constantBernstein]

example (f : ℂ → ℂ) : LaplaceImage f ↔ ∃ d, FiniteRep f d := by
  constructor
  · rintro ⟨mu, h, hmu, hh, hrep⟩
    exact ⟨(mu, h), hmu, hh, hrep⟩
  · rintro ⟨⟨mu, h⟩, hmu, hh, hrep⟩
    exact ⟨mu, h, hmu, hh, hrep⟩

example (T : ℝ → X →L[ℂ] X) (f : ℂ → ℂ) (x : X)
    (h : ¬ ∃ d, FiniteRep f d) : hpEval T f x = 0 := by
  simp [hpEval, h]

example (T : ℝ → X →L[ℂ] X) (hT : BoundedC0 T) (x : X) :
    ContinuousOn (fun t => T t x) (Ici 0) := hT.2 x

example (T : ℝ → X →L[ℂ] X) (f e : ℂ → ℂ) (h : HPRegularizer T f e) :
    Function.Injective (hpEval T e) := h.2.2

example (T : ℝ → X →L[ℂ] X) (G : Graph X) (r : ℝ → ℝ)
    (h : SharpRate T G r) (e : ℝ → ℝ) (he : VanishingFactor e) :
    ∃ y ∈ graphRange G, ∀ K : ℝ, ∃ t : ℝ,
      1 ≤ t ∧ K < ‖continuousCesaro T t y‖ / (e t * r t) := h e he

end QAlgorithms.Papers.Independent.Gap48.P07


