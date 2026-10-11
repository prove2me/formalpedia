-- Prove2me | Definitions.Def_StabilityConjecture_Basic
-- name    : StabilityConjecture_Basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T08:57:22.371659+00:00
-- url     : https://prove2.me/theorems/86422a3c-7166-42b0-b0c5-887e0b7145bb
-- title:
--   Hyperbolic sets, Axiom A, structural and $\Omega$-stability of $C^r$ diffeomorphisms
-- statement:
--   Let $M$ be a smooth manifold modelled on $\mathbb R^n$ (without boundary), let $r\ge 0$ be an integer, and let $\mathrm{Diff}^r(M)$ be the set of $C^r$ diffeomorphisms of $M$ with the weak $C^r$ topology (published definition `ClosingLemma_DiffeoCrTopology`). Write $\Omega(f)$ for the nonwandering set of $f$ (published definition `PughClosingLemma_nonwandering`) and $\mathrm{Per}(f)$ for its set of periodic points. For $x\in M$, $T_xM$ is the tangent space and $Df_x\colon T_xM\to T_{f(x)}M$ the derivative of $f$ at $x$.
--
--   1. **Continuous Riemannian metric.** A family $g=(g_x)_{x\in M}$ of inner products on the tangent spaces $T_xM$ depending continuously on $x$. The length of $v\in T_xM$ is $\|v\|_g=\sqrt{g_x(v,v)}$.
--
--   2. **Hyperbolic set.** A set $\Lambda\subseteq M$ is a hyperbolic set of $f\in\mathrm{Diff}^r(M)$ if $\Lambda$ is compact, $f(\Lambda)=\Lambda$, and there are a continuous Riemannian metric $g$, linear subspaces $E^s(x),E^u(x)\subseteq T_xM$ and constants $C>0$, $0<\lambda<1$ such that for every $x\in\Lambda$:
--      - $T_xM=E^s(x)\oplus E^u(x)$;
--      - $Df_x\big(E^s(x)\big)=E^s(f(x))$ and $Df_x\big(E^u(x)\big)=E^u(f(x))$;
--      - for every $k\ge 0$,
--   $$\|D(f^k)_x v\|_g\le C\lambda^k\|v\|_g\quad (v\in E^s(x)),\qquad \|D(f^{-k})_x v\|_g\le C\lambda^k\|v\|_g\quad (v\in E^u(x)).$$
--
--   3. **Hyperbolic periodic point.** A periodic point $p$ of $f$ is hyperbolic if its orbit $\{f^k(p):k\ge 0\}$ is a hyperbolic set of $f$.
--
--   4. **Axiom A.** $f$ satisfies Axiom A if $\Omega(f)$ is a hyperbolic set of $f$ and
--   $$\overline{\mathrm{Per}(f)}=\Omega(f).$$
--
--   5. **Anosov diffeomorphism.** $f$ is Anosov if $M$ itself is a hyperbolic set of $f$.
--
--   6. **$C^r$ structural stability.** $f$ is $C^r$ structurally stable if there is a neighbourhood $\mathcal U$ of $f$ in $\mathrm{Diff}^r(M)$ such that for every $g\in\mathcal U$ there is a homeomorphism $h\colon M\to M$ with
--   $$h\circ f=g\circ h .$$
--
--   7. **$C^r$ $\Omega$-stability.** $f$ is $C^r$ $\Omega$-stable if there is a neighbourhood $\mathcal U$ of $f$ in $\mathrm{Diff}^r(M)$ such that for every $g\in\mathcal U$ there is a homeomorphism $h\colon\Omega(f)\to\Omega(g)$ with $h(f(x))=g(h(x))$ for all $x\in\Omega(f)$.
--
--   These are the notions in which the Palis–Smale stability conjecture is phrased: structural stability (item 6) is conjectured to imply Axiom A (item 4) in every regularity $r\ge 1$.
--
--   **Formalization Note** Derivatives are `mfderiv` for the model `𝓡 n`; they are the genuine derivatives when $r\ge 1$, which every statement of the mission assumes. Continuity of the splitting $E^s\oplus E^u$ is not required in item 2 because it follows from the estimates; on a compact manifold any two continuous Riemannian metrics are uniformly equivalent, so the existential choice of $g$ only affects $C$. Item 3 uses the orbit-is-a-hyperbolic-set form of the definition, equivalent to the condition that $D(f^m)_p$ has no eigenvalue of modulus $1$ when $p$ has period $m$. Structural stability does not ask for $h$ to be close to the identity.
-- source:
--   Open Problem Garden, "C^r Stability Conjecture" (Conjecture, author(s) J. Palis and S. Smale; posted by m n, December 20th, 2007), https://www.openproblemgarden.org/op/c_r_stability_conjecture (the definitions of structural stability and hyperbolicity linked from the conjecture). Standard definitions: S. Smale, Differentiable dynamical systems, Bull. Amer. Math. Soc. 73 (1967), Part I.6 (Axiom A) and Part II (hyperbolic sets, Omega-stability); J. Palis and W. de Melo, Geometric Theory of Dynamical Systems, Springer 1982 (structural stability).

import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering

/-!
# Hyperbolicity, Axiom A and structural stability of `C^r` diffeomorphisms

Setting for the Prove2Me mission "`C^r` Stability Conjecture" (Palis–Smale).

Throughout, `M` is a smooth manifold modelled on `ℝⁿ` (no boundary) and
`ClosingLemma.Diff n M r` is the space `Diff^r(M)` of `C^r` diffeomorphisms of `M`, carrying the
weak `C^r` topology `ClosingLemma.crTopology r` (published definition
`ClosingLemma_DiffeoCrTopology`). The nonwandering set `Ω(f)` is
`PughClosingLemma.nonwanderingSet` (published definition `PughClosingLemma_nonwandering`).

* `StabilityConjecture.TangentMetric n M` : continuous Riemannian metrics on `TM`.
* `StabilityConjecture.IsHyperbolicSet f Λ` : `Λ` is a hyperbolic set of `f`.
* `StabilityConjecture.SatisfiesAxiomA f` : Smale's Axiom A.
* `StabilityConjecture.IsAnosov f` : `f` is an Anosov diffeomorphism.
* `StabilityConjecture.IsStructurallyStable r f` : `C^r` structural stability.
* `StabilityConjecture.IsOmegaStable r f` : `C^r` `Ω`-stability.
-/

open scoped Manifold ContDiff Topology

namespace StabilityConjecture

open ClosingLemma

/-- A continuous Riemannian metric on the manifold `M`: a continuously varying inner product on
the tangent spaces `T_x M`. -/
abbrev TangentMetric (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] :=
  Bundle.ContinuousRiemannianMetric (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n) : M → Type)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- The length `‖v‖_g = √(g_x(v, v))` of a tangent vector `v ∈ T_x M` for the metric `g`. -/
noncomputable def TangentMetric.norm (g : TangentMetric n M) (x : M)
    (v : TangentSpace (𝓡 n) x) : ℝ :=
  Real.sqrt (g.inner x v v)

/-- `Λ` is a **hyperbolic set** of the `C^r` diffeomorphism `f`: `Λ` is compact and
`f`-invariant (`f(Λ) = Λ`), and there are a continuous Riemannian metric `g`, subspaces
`E^s(x), E^u(x) ⊆ T_x M` and constants `C > 0`, `0 < λ < 1` such that for every `x ∈ Λ`:
* `T_x M = E^s(x) ⊕ E^u(x)`;
* `Df_x(E^s(x)) = E^s(f x)` and `Df_x(E^u(x)) = E^u(f x)`;
* `‖D(f^k)_x v‖ ≤ C λ^k ‖v‖` for all `k ≥ 0` and `v ∈ E^s(x)`;
* `‖D(f^{-k})_x v‖ ≤ C λ^k ‖v‖` for all `k ≥ 0` and `v ∈ E^u(x)`.
(Continuity of the splitting is not required: it is a consequence of these estimates. On a
compact manifold all continuous Riemannian metrics are uniformly equivalent, so the choice of `g`
only affects the constant `C`.) -/
def IsHyperbolicSet {r : ℕ} (f : Diff n M r) (Λ : Set M) : Prop :=
  IsCompact Λ ∧ f '' Λ = Λ ∧
  ∃ (g : TangentMetric n M) (Es Eu : (x : M) → Submodule ℝ (TangentSpace (𝓡 n) x))
    (C lam : ℝ), 0 < C ∧ 0 < lam ∧ lam < 1 ∧ ∀ x ∈ Λ,
      IsCompl (Es x) (Eu x) ∧
      (Es x).map (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap = Es (f x) ∧
      (Eu x).map (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap = Eu (f x) ∧
      (∀ k : ℕ, ∀ v ∈ Es x,
        g.norm ((⇑f)^[k] x) (mfderiv (𝓡 n) (𝓡 n) (⇑f)^[k] x v) ≤ C * lam ^ k * g.norm x v) ∧
      (∀ k : ℕ, ∀ v ∈ Eu x,
        g.norm ((⇑f.symm)^[k] x) (mfderiv (𝓡 n) (𝓡 n) (⇑f.symm)^[k] x v)
          ≤ C * lam ^ k * g.norm x v)

/-- The periodic point `p` of `f` is **hyperbolic**: its (finite) orbit
`{f^k(p) : k ≥ 0}` is a hyperbolic set of `f`. (Equivalently, if `p` has period `m`, the
derivative `D(f^m)_p` has no eigenvalue of modulus one.) -/
def IsHyperbolicPeriodicPt {r : ℕ} (f : Diff n M r) (p : M) : Prop :=
  p ∈ Function.periodicPts f ∧ IsHyperbolicSet f (Set.range fun k : ℕ => (⇑f)^[k] p)

/-- `f` satisfies **Smale's Axiom A**: the nonwandering set `Ω(f)` is a hyperbolic set of `f`,
and the periodic points of `f` are dense in `Ω(f)`. -/
def SatisfiesAxiomA {r : ℕ} (f : Diff n M r) : Prop :=
  IsHyperbolicSet f (PughClosingLemma.nonwanderingSet f) ∧
    closure (Function.periodicPts f) = PughClosingLemma.nonwanderingSet f

/-- `f` is an **Anosov diffeomorphism**: the whole manifold `M` is a hyperbolic set of `f`. -/
def IsAnosov {r : ℕ} (f : Diff n M r) : Prop :=
  IsHyperbolicSet f Set.univ

/-- `f` is **`C^r` structurally stable**: there is a neighbourhood `U` of `f` in `Diff^r(M)`
(weak `C^r` topology) such that every `g ∈ U` is topologically conjugate to `f`, i.e. there is a
homeomorphism `h : M → M` with `h ∘ f = g ∘ h`. -/
def IsStructurallyStable (r : ℕ) (f : Diff n M r) : Prop :=
  ∃ U ∈ @nhds (Diff n M r) (crTopology r) f, ∀ g ∈ U,
    ∃ h : M ≃ₜ M, ∀ x : M, h (f x) = g (h x)

/-- `f` is **`C^r` `Ω`-stable**: there is a neighbourhood `U` of `f` in `Diff^r(M)` (weak `C^r`
topology) such that for every `g ∈ U` the restrictions `f|Ω(f)` and `g|Ω(g)` are topologically
conjugate, i.e. there is a homeomorphism `h : Ω(f) → Ω(g)` with `h(f x) = g(h x)` for all
`x ∈ Ω(f)`. -/
def IsOmegaStable (r : ℕ) (f : Diff n M r) : Prop :=
  ∃ U ∈ @nhds (Diff n M r) (crTopology r) f, ∀ g ∈ U,
    ∃ h : PughClosingLemma.nonwanderingSet f ≃ₜ PughClosingLemma.nonwanderingSet g,
      ∀ x y : PughClosingLemma.nonwanderingSet f, (y : M) = f x → (h y : M) = g (h x)

end StabilityConjecture


