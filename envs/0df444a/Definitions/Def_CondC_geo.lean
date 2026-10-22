-- Prove2me | Definitions.Def_CondC_geo
-- name    : CondC_geo
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-21T15:44:34.811453+00:00
-- url     : https://prove2.me/theorems/aa336f2e-4b44-4698-8ee4-cfd43aa9e881
-- title:
--   The geometric layer: discs, the structure sheaf, and the cohomological worlds
-- statement:
--   The geometric layer of Clausen and Scholze's "Condensed Mathematics and Complex Geometry" (lecture notes, May 2026 version): the propositional content of Lectures I, V, XII, XIII, and XIV. Disc is the type of open discs of the complex plane as center-radius pairs; DiscMem is point membership; SubDisc is containment of discs, reflexive and transitive. DiscModulePresheaf is the disc presheaf interface: an abstract family of fibres with restriction along containment, and bundled add, zero, neg, and scalar multiplication operations compatible with restriction. Covers2 is a cover of a disc by two sub-discs; AgreesOn2 is agreement of two sections on all discs contained in the overlap; SheafGlue2 is the sheaf condition in the two-disc form used in the paper's proof: locally agreeing sections glue uniquely. OIdentification is the power-series identification of the structure sheaf of Theorems 1.1 and 5.1: on each disc of positive radius, the expansion into power series satisfying the decay condition, bijective onto the decaying families. H1Vanishes is the vanishing of the first cohomology for two-disc covers: a pair of sections whose difference vanishes on the overlap is the pair of restrictions of a global section. CompactCxWorld abstracts a compact complex manifold for the cohomological theorems: the points with their topology and compactness, the complex dimension, the coherent cohomology groups as an abstract family with bundled operations, the coherence predicate, and the dualizing sheaf data. BundledFiniteDim presents finite-dimensionality through a finite basis with a spanning coordinate system; BundledLinearMap is the corresponding bundled linear map. HRRWorld collects the data of the Hirzebruch-Riemann-Roch theorem of Lecture XIV: the K-group with its operations, the Hodge cohomology, the Chern character, the Todd class, the integration functional, and the Euler characteristic.
--
--   **Formalization Note** The fibres carry bundled operations rather than instance-carrying module structures, and the algebraic axioms of the fibres are not part of the interface; both belong to the concrete construction that is the proposed work of the mission.
-- source:
--   D. Clausen, P. Scholze, Condensed Mathematics and Complex Geometry, lecture notes (May 2026 version), Lectures I, V, XII-XIV.

import Mathlib
import Definitions.Def_CondC_liq

/-!
# The geometric layer: discs, the structure sheaf, and the worlds of the cohomological theorems

The geometric layer of the CondC mission, carrying the propositional content
of Lectures I, V, XII, XIII, and XIV of Clausen and Scholze, "Condensed
Mathematics and Complex Geometry" (May 2026 version): the discs of the
complex plane with their membership and containment relations; the disc
presheaf interface with bundled fibre operations; the two-disc covers and the
two-disc sheaf condition; the power-series identification of the structure
sheaf of Theorems 1.1 and 5.1; the vanishing of the first cohomology on
discs; the world interface of a compact complex manifold with its coherent
cohomology groups; the bundled finite-dimensional spaces and linear maps; and
the world interface of the Hirzebruch-Riemann-Roch data of Lecture XIV.
-/

namespace CondC

/-- Open discs in the complex plane, represented as center-radius pairs: the
disc d is D(d.1, d.2) = {z in C | dist z d.1 < d.2}. -/
abbrev Disc : Type := ℂ × ℝ

/-- Membership of a point z in the open disc d. -/
def DiscMem (z : ℂ) (d : Disc) : Prop := dist z d.1 < d.2

/-- Containment of discs: the disc d is contained in the disc d' iff the
distance of the centers plus the radius of d is at most the radius of d'. -/
def SubDisc (d d' : Disc) : Prop := dist d.1 d'.1 + d.2 ≤ d'.2

lemma subDisc_refl (d : Disc) : SubDisc d d := by
  simp [SubDisc]

lemma subDisc_trans {d d' d'' : Disc} (h1 : SubDisc d d') (h2 : SubDisc d' d'') :
    SubDisc d d'' := by
  unfold SubDisc at h1 h2 ⊢
  have h3 := dist_triangle d.1 d'.1 d''.1
  linarith

/-- The disc presheaf interface: an abstract family of fibres over discs
with restriction along containment, and bundled add, zero, neg, and scalar
multiplication operations compatible with restriction. The algebraic axioms
of the fibres are not part of the interface; they belong to the concrete
construction. -/
structure DiscModulePresheaf where
  F : Disc → Type
  res : ∀ d d' : Disc, SubDisc d d' → F d' → F d
  res_refl : ∀ (d : Disc) (s : F d), res d d (subDisc_refl d) s = s
  res_trans : ∀ (d d' d'' : Disc) (h1 : SubDisc d d') (h2 : SubDisc d' d'')
      (s : F d''), res d d'' (subDisc_trans h1 h2) s = res d d' h1 (res d' d'' h2 s)
  add : ∀ d : Disc, F d → F d → F d
  zero : ∀ d : Disc, F d
  neg : ∀ d : Disc, F d → F d
  smul : ∀ d : Disc, ℂ → F d → F d
  add_res : ∀ (d d' : Disc) (h : SubDisc d d') (s t : F d'),
    res d d' h (add d' s t) = add d (res d d' h s) (res d d' h t)
  zero_res : ∀ (d d' : Disc) (h : SubDisc d d'), res d d' h (zero d') = zero d
  neg_res : ∀ (d d' : Disc) (h : SubDisc d d') (s : F d'),
    res d d' h (neg d' s) = neg d (res d d' h s)
  smul_res : ∀ (d d' : Disc) (h : SubDisc d d') (k : ℂ) (s : F d'),
    res d d' h (smul d' k s) = smul d k (res d d' h s)

/-- A cover of the disc d by two of its sub-discs. -/
structure Covers2 (d : Disc) where
  d₀ : Disc
  d₁ : Disc
  h₀ : SubDisc d₀ d
  h₁ : SubDisc d₁ d
  cover : ∀ z : ℂ, DiscMem z d → DiscMem z d₀ ∨ DiscMem z d₁

/-- Agreement of two sections on a two-disc cover: their restrictions agree
on every disc contained in the intersection of the cover elements. -/
def AgreesOn2 (P : DiscModulePresheaf) {d : Disc} (c : Covers2 d)
    (s₀ : P.F c.d₀) (s₁ : P.F c.d₁) : Prop :=
  ∀ e : Disc, ∀ h₀ : SubDisc e c.d₀, ∀ h₁ : SubDisc e c.d₁,
    P.res e c.d₀ h₀ s₀ = P.res e c.d₁ h₁ s₁

/-- The sheaf condition for the disc presheaf P, in the two-disc form used
in the paper's proof of Theorem 5.1: locally agreeing sections on a two-disc
cover glue uniquely. -/
def SheafGlue2 (P : DiscModulePresheaf) : Prop :=
  ∀ (d : Disc) (c : Covers2 d) (s₀ : P.F c.d₀) (s₁ : P.F c.d₁),
    AgreesOn2 P c s₀ s₁ →
    ∃! s : P.F d, P.res c.d₀ d c.h₀ s = s₀ ∧ P.res c.d₁ d c.h₁ s = s₁

/-- The identification of the presheaf P with the sheaf of holomorphic
functions of Theorems 1.1 and 5.1: on each disc of positive radius, the
expansion into power series with the convergence condition, bijective onto
the decaying families. -/
structure OIdentification (P : DiscModulePresheaf) where
  coeffs : ∀ d : Disc, P.F d → ℕ → ℂ
  decay : ∀ (d : Disc) (s : P.F d), 0 < d.2 → PowerDecay d.2 (coeffs d s)
  inj : ∀ (d : Disc) (s t : P.F d), coeffs d s = coeffs d t → s = t
  surj : ∀ (d : Disc), 0 < d.2 → ∀ f : ℕ → ℂ, PowerDecay d.2 f →
    ∃ s : P.F d, coeffs d s = f

/-- Vanishing of the first cohomology for two-disc covers: a pair of
sections whose difference vanishes on every disc contained in the overlap of
the cover is the pair of restrictions of a global section. -/
def H1Vanishes (P : DiscModulePresheaf) : Prop :=
  ∀ (d : Disc) (c : Covers2 d) (s₀ : P.F c.d₀) (s₁ : P.F c.d₁),
    (∀ e : Disc, ∀ h₀ : SubDisc e c.d₀, ∀ h₁ : SubDisc e c.d₁,
      P.add e (P.res e c.d₀ h₀ s₀) (P.neg e (P.res e c.d₁ h₁ s₁)) = P.zero e) →
    ∃ s : P.F d, P.res c.d₀ d c.h₀ s = s₀ ∧ P.res c.d₁ d c.h₁ s = s₁

/-- The world interface for the cohomological theorems on a compact complex
manifold X: the points with their topology and compactness, the complex
dimension, the coherent cohomology groups as an abstract family with bundled
operations, the coherence predicate on coefficients, and the dualizing
sheaf. -/
structure CompactCxWorld where
  pts : Type
  top : TopologicalSpace pts
  compact : @CompactSpace pts top
  dim : ℕ
  Coh : Type → ℕ → Type
  add : (F : Type) → (i : ℕ) → Coh F i → Coh F i → Coh F i
  zero : (F : Type) → (i : ℕ) → Coh F i
  smul : (F : Type) → (i : ℕ) → ℂ → Coh F i → Coh F i
  coherent : Type → Prop
  dualF : Type → Type

/-- A finite-dimensional space presented through bundled operations: a basis
with finite dimension, the spanning map from the coordinate space, the
coordinate inverse, and the injectivity of the span. -/
structure BundledFiniteDim (V : Type) (add : V → V → V) (zero : V) (smul : ℂ → V → V) where
  dim : ℕ
  span : (Fin dim → ℂ) → V
  coord : V → Fin dim → ℂ
  span_add : ∀ x y : Fin dim → ℂ, span (x + y) = add (span x) (span y)
  span_zero : span 0 = zero
  span_smul : ∀ (k : ℂ) (x : Fin dim → ℂ), span (k • x) = smul k (span x)
  span_inj : ∀ x y : Fin dim → ℂ, span x = span y → x = y
  span_coord : ∀ v : V, span (coord v) = v

/-- A bundled linear map between bundled spaces. -/
structure BundledLinearMap (V W : Type) (addV : V → V → V) (zeroV : V) (smulV : ℂ → V → V)
    (addW : W → W → W) (zeroW : W) (smulW : ℂ → W → W) where
  map : V → W
  map_add : ∀ x y : V, map (addV x y) = addW (map x) (map y)
  map_zero : map zeroV = zeroW
  map_smul : ∀ (k : ℂ) (x : V), map (smulV k x) = smulW k (map x)

/-- The world interface for the Hirzebruch-Riemann-Roch theorem of Lecture
XIV: the K-group of vector bundles with its operations, the Hodge cohomology
with its operations, the Chern character, the Todd class of the tangent
bundle, the integration functional, and the Euler characteristic. -/
structure HRRWorld where
  K : Type
  addK : K → K → K
  zeroK : K
  negK : K → K
  mulK : K → K → K
  oneK : K
  Hdg : Type
  addH : Hdg → Hdg → Hdg
  mulH : Hdg → Hdg → Hdg
  oneH : Hdg
  ch : K → Hdg
  td : Hdg
  integral : Hdg → ℂ
  chi : K → ℂ

end CondC


