-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_StaticStructure
-- name    : JRCurvedQFT_SharpTime_StaticStructure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:44.564016+00:00
-- url     : https://prove2.me/theorems/811347a9-0580-4f10-ae0c-96d2a804b52f
-- title:
--   Static structure of a quantizable static spacetime: Killing flow $\phi_s$, time $t$, slice $\Sigma$, reflection $\theta$
-- statement:
--   Let $M$ be a smooth Riemannian manifold of dimension $d$. A **static structure** on $M$ consists of
--
--   1. a global smooth flow $\phi:\mathbb R\times M\to M$, $\phi_0=\mathrm{id}$, $\phi_{s+r}=\phi_s\circ\phi_r$, each $\phi_s$ an isometry of $M$; its velocity $\xi_p=\frac{d}{ds}\big|_{s=0}\phi_s(p)$ is the **static Killing field**, whose orbits are complete;
--   2. a smooth **time function** $t:M\to\mathbb R$ with $t(\phi_s(p))=t(p)+s$, so that every orbit meets $\Sigma=\{t=0\}$ exactly once;
--   3. orthogonality: at every $p\in\Sigma$, $\langle\xi_p,v\rangle_g=0$ for all $v$ with $dt_p(v)=0$, i.e. $\xi\perp T_p\Sigma$.
--
--   Derived objects: the **lapse** $F(p)=\langle\xi_p,\xi_p\rangle_g$ of (4.1); the slice $\Sigma=\{t=0\}$; $\Omega_+=\{t>0\}$, $\Omega_-=\{t<0\}$; the **time reflection** $\theta(p)=\phi_{-2t(p)}(p)$, the point of the trajectory of $p$ with $t(\theta(p))=-t(p)$; and the projection $p\mapsto\phi_{-t(p)}(p)\in\Sigma$.
--
--   Together with completeness and connectedness of $M$ this is the paper's quantizable static spacetime (Definition 4.1) with the time reflection of Example 1.1, and $M=\Omega_-\cup\Sigma\cup\Omega_+$, $\theta\Omega_\pm=\Omega_\mp$ (1.1).
--
--   **Formalization Note** The manifold is modeled on $\mathbb R^d$ with a smooth Riemannian metric (Mathlib's `RiemannianBundle` on the tangent bundle); completeness, connectedness and "distance = Riemannian distance" are typeclass hypotheses of the theorems. Encoding Definition 4.1 by the time function is equivalent to the paper's "each orbit intersects $\Sigma$ exactly once" (Reading 3).
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, Definition 4.1, p. 20; Example 1.1, pp. 3–4; Eq. (1.1), p. 4; Eq. (4.1), p. 21

import Mathlib

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- A **static structure** on a Riemannian manifold `M` (a quantizable static spacetime).

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, Definition 4.1, p. 20: "A quantizable static spacetime is a complete, connected Riemannian
manifold M with a globally defined (smooth) Killing field ξ which is orthogonal to a codimension
one hypersurface Σ ⊂ M, such that the orbits of ξ are complete and each orbit intersects Σ exactly
once", read together with Example 1.1, pp. 3–4 (the time function `t` and the reflection `θ`).

Fields: a global smooth flow `flow s` (the one-parameter group `φ_s` of the Killing field ξ;
orbits complete), each `flow s` an isometry of `M` (ξ is Killing), and a smooth time function
`time` with `time (φ_s p) = time p + s` (so `dt(ξ) = 1` and each orbit meets `Σ = time⁻¹(0)`
exactly once), with ξ orthogonal to `ker dt_p = T_pΣ` at every `p ∈ Σ`.

**Formalization Note** Reading 3: Definition 4.1 is encoded by the triple (ξ, φ, t). The Killing
field is the derived velocity `killing p = d/ds|_{s=0} φ_s p`. Completeness, connectedness and the
Riemannian distance are hypotheses on `M` in each theorem (`CompleteSpace M`, `ConnectedSpace M`,
`IsRiemannianManifold`), not fields here. The orthogonality field uses the Riemannian inner product
of `T_pM` (tangent vectors at `φ_0 p = p` are read at `p`). -/
structure StaticStructure (M : Type) [EMetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)] where
  /-- The flow `φ_s` of the static Killing field ξ. -/
  flow : ℝ → M → M
  flow_zero : ∀ p, flow 0 p = p
  flow_add : ∀ s r p, flow (s + r) p = flow s (flow r p)
  flow_smooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ (fun q : ℝ × M => flow q.1 q.2)
  flow_isometry : ∀ s, Isometry (flow s)
  /-- The static time function `t` of Example 1.1 (`t = 0` on `Σ`). -/
  time : M → ℝ
  time_smooth : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, ℝ) ∞ time
  time_flow : ∀ s p, time (flow s p) = time p + s
  orthogonal : ∀ p, time p = 0 → ∀ v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) p,
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, ℝ) time p v = 0 →
    inner ℝ (show TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) p from
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) (fun s => flow s p) 0 1) v = 0

namespace StaticStructure

variable (S : StaticStructure (d := d) M)

/-- The static Killing field `ξ_p = d/ds|_{s=0} φ_s(p)` (Example 1.1, p. 3). -/
noncomputable def killing (p : M) : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) p :=
  mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) (fun s => S.flow s p) 0 1

/-- The lapse `F = ⟨ξ, ξ⟩` of (4.1), p. 21: `g = F dt² + G_μν dx^μ dx^ν`. -/
noncomputable def lapse (p : M) : ℝ := ‖S.killing p‖ ^ 2

/-- The time-zero hypersurface `Σ = {t = 0}` (Example 1.1, p. 3). -/
def slice : Set M := {p | S.time p = 0}

/-- The positive-time region `Ω₊ = {t > 0}` of (1.1), p. 4 (an open set). -/
def positiveTime : Set M := {p | 0 < S.time p}

/-- The negative-time region `Ω₋ = {t < 0}` of (1.1), p. 4. -/
def negativeTime : Set M := {p | S.time p < 0}

/-- The time reflection `θ` of Example 1.1, p. 4: the point on the ξ-trajectory of `p` with
`t(θ(p)) = −t(p)`, i.e. `θ(p) = φ_{−2t(p)}(p)`. -/
def reflection (p : M) : M := S.flow (-2 * S.time p) p

/-- The projection `p ↦ φ_{−t(p)}(p) ∈ Σ` along the ξ-trajectory (p. 24: "a pair (p, t) where
p ∈ Σ and t ∈ ℝ uniquely specify a point in M"). -/
def sliceProj (p : M) : M := S.flow (-S.time p) p

end StaticStructure

end JRCurvedQFT.SharpTime


