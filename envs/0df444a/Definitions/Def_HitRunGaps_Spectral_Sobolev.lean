-- Prove2me | Definitions.Def_HitRunGaps_Spectral_Sobolev
-- name    : HitRunGaps_Spectral_Sobolev
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:08:43.419922+00:00
-- url     : https://prove2.me/theorems/87fec04a-8d11-4488-aa2d-5afbe3880ad6
-- title:
--   Domain Sobolev spaces, zero trace and divergence
-- statement:
--   Let $\Omega\subset\mathbb R^n$ be a bounded open connected nonempty domain. Scalar functions and their derivatives are equivalence classes in $L^2(\Omega,dx)$. The graph space $H^1(\Omega)$ consists of $f$ and all of its weak first derivatives; weak differentiation uses the published integration-by-parts definition with all smooth compactly supported tests. Zero trace means approximation by such tests in the full $H^1$ norm. Set
--
--   $$Q=L^2_0(\Omega),\qquad V=H^1_0(\Omega;\mathbb R^n),\qquad \operatorname{div}u=\sum_i\partial_i u_i.$$
--
--   The field inner product uses the full Frobenius gradient. For the antisymmetric matrix $G_{ij}=\partial_j u_i-\partial_i u_j$, its energy sums only over $i<j$. The relation $\nabla h=\operatorname{div}G$ is distributional. The representative predicate is exactly the Riesz pairing, and the dual norm is the source's supremum over nonzero gradient norms. These definitions provide the shared domain interface for every Appendix B target; no regularity or target estimate is included in a domain.
-- source:
--   Yunbum Kook, Santosh Vempala, Spectral Gaps of Hit-and-Run and Coordinate Hit-and-Run, STOC 2027 submission #207 (October 2026), published basis, pinned PDF SHA256 a0cdd91dff374c90e51e64b6848852bf973795b9a3005c4f1ee37214f9d5a940, pp.4–5,13–15, §1.2.1 and Appendices A–B

import Mathlib
import Definitions.Def_HunterPDE_Shared_WeakDeriv

open MeasureTheory Filter
open scoped ContDiff Topology

noncomputable section

namespace HitRunGaps.Spectral

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev L2 {n : ℕ} (Ω : Set (Space n)) := Lp ℝ 2 (volume.restrict Ω)

/-- A bounded domain; no convexity or boundary regularity. PDF p.14. -/
def IsDomain {n : ℕ} (Ω : Set (Space n)) : Prop :=
  IsOpen Ω ∧ Bornology.IsBounded Ω ∧ IsConnected Ω

/-- The graph of all L² weak first derivatives, modulo a.e. equality. PDF pp.4–5,13. -/
structure H1 {n : ℕ} (Ω : Set (Space n)) where
  val : L2 Ω
  grad : Fin n → L2 Ω
  weak : ∀ i, HunterPDE.Shared.HasWeakDeriv Ω (Pi.single i 1) val (grad i)

/-- Closure in the full H¹ norm, expressed by componentwise L² convergence.
No pointwise boundary values are used. PDF pp.5,13. -/
def ZeroTrace {n : ℕ} {Ω : Set (Space n)} (f : H1 Ω) : Prop :=
  ∃ φ : ℕ → Space n → ℝ,
    (∀ k, HunterPDE.Shared.IsTestFunction Ω (φ k)) ∧
    Tendsto (fun k => eLpNorm (fun x => φ k x - f.val x) 2 (volume.restrict Ω)) atTop (𝓝 0) ∧
    ∀ i, Tendsto (fun k => eLpNorm
      (fun x => HunterPDE.Shared.partialDeriv (φ k) i x - f.grad i x)
      2 (volume.restrict Ω)) atTop (𝓝 0)

abbrev V {n : ℕ} (Ω : Set (Space n)) := {u : Fin n → H1 Ω // ∀ i, ZeroTrace (u i)}

noncomputable def divergence {n : ℕ} {Ω : Set (Space n)} (u : V Ω) : L2 Ω :=
  ∑ i, (u.val i).grad i

noncomputable def fieldEnergy {n : ℕ} {Ω : Set (Space n)} (u : V Ω) : ℝ :=
  ∑ i, ∑ j, ‖(u.val i).grad j‖ ^ 2

noncomputable def fieldPair {n : ℕ} {Ω : Set (Space n)} (u v : V Ω) : ℝ :=
  ∑ i, ∑ j, inner ℝ ((u.val i).grad j) ((v.val i).grad j)

noncomputable def centered {n : ℕ} {Ω : Set (Space n)} (f : L2 Ω) : Prop :=
  (∫ x in Ω, f x) = 0

abbrev Q {n : ℕ} (Ω : Set (Space n)) := {f : L2 Ω // centered f}

noncomputable def boundaryDistance {n : ℕ} (Ω : Set (Space n)) (x : Space n) : ℝ :=
  Metric.infDist x (frontier Ω)

noncomputable def antiGradient {n : ℕ} {Ω : Set (Space n)} (u : V Ω) : Fin n → Fin n → L2 Ω :=
  fun i j => (u.val i).grad j - (u.val j).grad i

/-- Half of the full Frobenius energy, exactly the source's i<j norm. PDF p.14. -/
noncomputable def antiEnergy {n : ℕ} {Ω : Set (Space n)} (G : Fin n → Fin n → L2 Ω) : ℝ :=
  ∑ i, ∑ j, if i < j then ‖G i j‖ ^ 2 else 0

/-- Distributional relation ∂ᵢh = ∑ⱼ∂ⱼGᵢⱼ; neither side needs a global L² derivative. -/
def GradEqDiv {n : ℕ} {Ω : Set (Space n)} (h : L2 Ω)
    (G : Fin n → Fin n → L2 Ω) : Prop :=
  ∀ φ : Space n → ℝ, HunterPDE.Shared.IsTestFunction Ω φ → ∀ i,
    (∫ x in Ω, h x * HunterPDE.Shared.partialDeriv φ i x) =
      ∑ j, ∫ x in Ω, G i j x * HunterPDE.Shared.partialDeriv φ j x

/-- The Riesz representative is specified only by its defining pairing. PDF p.14. -/
def Represents {n : ℕ} {Ω : Set (Space n)} (f : L2 Ω) (u : V Ω) : Prop :=
  ∀ v : V Ω, inner ℝ f (divergence v) = fieldPair u v

/-- Real supremum of a bounded functional's unit-direction ratios.
Zero fields are excluded using their gradient norm; the empty supremum is 0. -/
noncomputable def dualNorm {n : ℕ} {Ω : Set (Space n)} (f : L2 Ω) : ℝ :=
  sSup {r : ℝ | ∃ v : V Ω, 0 < fieldEnergy v ∧
    r = inner ℝ f (divergence v) / Real.sqrt (fieldEnergy v)}

end HitRunGaps.Spectral


