-- Prove2me | Definitions.Def_KoebeCircleDomains
-- name    : KoebeCircleDomains
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:16.938643+00:00
-- url     : https://prove2.me/theorems/b4f5ecea-6e82-44a2-83c3-c4e835a88101
-- statement:
--   The block works on the Riemann sphere, modelled as the one-point compactification of ℂ, with Möbius transformations given by invertible 2×2 complex matrices acting on it. Inversion z↦1/z swaps 0 and ∞, and charts are defined so that coordinates near a point p are the usual coordinate z (or 1/z when p=∞). A map f of the sphere is conformal at p if it is continuous there and, written in these charts around p and f(p), has a nonzero complex derivative at p; it is conformal on a set if conformal at every point of it, and a conformal equivalence between sets U and V is a map conformal on U, sending U into V, with a map conformal on V sending V into U that is a two-sided inverse on the respective sets. A round closed disk is the image of the closed unit disk under a Möbius transformation. A circle domain is an open connected subset of the sphere whose complement has every connected component (taken in the complement) either a single point or a round closed disk. A homeomorphism of the sphere is orientation preserving if it is homotopic to the identity map. A set E is conformally removable if it is compact and every orientation-preserving homeomorphism of the sphere that is conformal on the complement of E is itself a Möbius transformation. These are only definitions; no uniformization or rigidity theorem is stated, and the Problem047 namespace is empty.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KoebeCircleDomains.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KoebeCircleDomains.lean; bytes 16..2028
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

/-! Circle-domain uniformization and rigidity under conformal removability. -/

noncomputable section
open Set Classical
open scoped OnePoint

namespace CircleDomainRigidity

abbrev Sphere := OnePoint ℂ
abbrev Mobius := Matrix.GeneralLinearGroup (Fin 2) ℂ

def sphereInv (p : Sphere) : Sphere :=
  p.elim (0 : ℂ) (fun z ↦ if z = 0 then ∞ else (z⁻¹ : ℂ))

def finiteCoord (p : Sphere) : ℂ := p.elim 0 id

def chart (p q : Sphere) : ℂ :=
  if p = ∞ then finiteCoord (sphereInv q) else finiteCoord q

def chartSymm (p : Sphere) (z : ℂ) : Sphere :=
  if p = ∞ then sphereInv (z : Sphere) else (z : Sphere)

def IsConformalAt (f : Sphere → Sphere) (p : Sphere) : Prop :=
  ContinuousAt f p ∧ ∃ d : ℂ, d ≠ 0 ∧
    HasDerivAt (fun z ↦ chart (f p) (f (chartSymm p z))) d (chart p p)

def IsConformalOn (f : Sphere → Sphere) (U : Set Sphere) : Prop :=
  ∀ p ∈ U, IsConformalAt f p

def IsConformalEquivalence (f : Sphere → Sphere) (U V : Set Sphere) : Prop :=
  IsConformalOn f U ∧ MapsTo f U V ∧ ∃ g : Sphere → Sphere,
    IsConformalOn g V ∧ MapsTo g V U ∧
    (∀ z ∈ U, g (f z) = z) ∧ (∀ w ∈ V, f (g w) = w)

def IsRoundClosedDisk (K : Set Sphere) : Prop :=
  ∃ M : Mobius,
    K = (fun p : Sphere ↦ M • p) ''
      (((↑) : ℂ → Sphere) '' Metric.closedBall (0 : ℂ) 1)

def IsCircleDomain (U : Set Sphere) : Prop :=
  IsOpen U ∧ IsConnected U ∧
    ∀ p ∈ Uᶜ, (∃ q : Sphere, connectedComponentIn Uᶜ p = {q}) ∨
      IsRoundClosedDisk (connectedComponentIn Uᶜ p)

def OrientationPreserving (h : Sphere ≃ₜ Sphere) : Prop :=
  ContinuousMap.Homotopic (⟨h, h.continuous⟩ : C(Sphere, Sphere)) (ContinuousMap.id Sphere)

def IsConformallyRemovable (E : Set Sphere) : Prop :=
  IsCompact E ∧ ∀ h : Sphere ≃ₜ Sphere, OrientationPreserving h →
    IsConformalOn h Eᶜ → ∃ M : Mobius, ∀ p : Sphere, h p = M • p

end CircleDomainRigidity

open CircleDomainRigidity

namespace Problem047



end Problem047
end
end OAI


