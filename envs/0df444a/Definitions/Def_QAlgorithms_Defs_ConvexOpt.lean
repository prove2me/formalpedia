-- Prove2me | Definitions.Def_QAlgorithms_Defs_ConvexOpt
-- name    : QAlgorithms_Defs_ConvexOpt
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:40:13.077043+00:00
-- url     : https://prove2.me/theorems/cbf02648-57eb-492c-9257-bbf81d18102c
-- title:
--   Minimum width, separation oracles, expected query counts, Bregman divergences and mirror
-- statement:
--   # Minimum width, separation oracles, expected query counts, Bregman divergences and mirror
--   descent (shared definition layer)
--
--   * Y. T. Lee, A. Sidford, S. C. Wong, *A faster cutting plane method and its implications for
--     combinatorial and convex optimization* (arXiv:1508.04874v2), cited "LSW p.N" (PDF pages).
--   * N. Bansal, A. Gupta, *Potential-function proofs for gradient methods* (arXiv:1712.04581v3),
--     cited "Bansal–Gupta p.N" (PDF pages), §4.
--
--   Vectors of `ℝⁿ` are `Fin n → ℝ`, `⟨a, x⟩` is `dotProduct`, `‖·‖₂` is `euclidNorm`.
--   -/
--
--   namespace QAlgorithms
--
--   open scoped ENNReal
--
--   /-- LSW Definition 41 (p.54): `MinWidth(K) = min_{‖a‖₂ = 1} max_{x, y ∈ K} ⟨a, x − y⟩`, with real
--   `⨅`/`⨆`. For a nonempty compact `K` (the source's setting) and `n ≥ 1` this is the source's value;
--   on an empty or unbounded `K`, or for `n = 0`, it is the junk value `0` of Mathlib's real
--   `sSup`/`sInf` (such inputs are excluded by the statements' hypotheses).
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ConvexOpt.lean

import Definitions.Def_QAlgorithms_Defs_PhaseOracles
/-!
# Minimum width, separation oracles, expected query counts, Bregman divergences and mirror
descent (shared definition layer)

* Y. T. Lee, A. Sidford, S. C. Wong, *A faster cutting plane method and its implications for
  combinatorial and convex optimization* (arXiv:1508.04874v2), cited "LSW p.N" (PDF pages).
* N. Bansal, A. Gupta, *Potential-function proofs for gradient methods* (arXiv:1712.04581v3),
  cited "Bansal–Gupta p.N" (PDF pages), §4.

Vectors of `ℝⁿ` are `Fin n → ℝ`, `⟨a, x⟩` is `dotProduct`, `‖·‖₂` is `euclidNorm`.
-/

namespace QAlgorithms

open scoped ENNReal

/-- LSW Definition 41 (p.54): `MinWidth(K) = min_{‖a‖₂ = 1} max_{x, y ∈ K} ⟨a, x − y⟩`, with real
`⨅`/`⨆`. For a nonempty compact `K` (the source's setting) and `n ≥ 1` this is the source's value;
on an empty or unbounded `K`, or for `n = 0`, it is the junk value `0` of Mathlib's real
`sSup`/`sInf` (such inputs are excluded by the statements' hypotheses). -/
noncomputable def minWidth {n : ℕ} (K : Set (Fin n → ℝ)) : ℝ :=
  ⨅ a : {a : Fin n → ℝ // euclidNorm a = 1}, ⨆ p : K × K, a.1 ⬝ᵥ ((p.1 : Fin n → ℝ) - p.2)

/-- LSW Definition 2 (p.9): `O` is an `(η, δ)`-separation oracle on `Γ` for `f`: for every query
`x ∈ Γ` it either asserts `f(x) ≤ min_{y ∈ Γ} f(y) + η` (output `none`) or outputs a half space
`H = {z : cᵀz ≤ cᵀx + b} ⊇ {z ∈ Γ : f(z) ≤ f(x)}` with `c ≠ 0` and `b ≤ δ‖c‖₂`
(output `some (c, b)`). Queries outside `Γ` are unconstrained. The source's convexity of `f`, `Γ`
and `η, δ ≥ 0` are hypotheses of the statements. -/
def IsSeparationOracle {n : ℕ} (η δ : ℝ) (Γ : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (O : (Fin n → ℝ) → Option ((Fin n → ℝ) × ℝ)) : Prop :=
  ∀ x ∈ Γ, (O x = none → ∀ y ∈ Γ, f x ≤ f y + η) ∧
    ∀ c b, O x = some (c, b) → c ≠ 0 ∧ b ≤ δ * euclidNorm c ∧
      ∀ z ∈ Γ, f z ≤ f x → c ⬝ᵥ z ≤ c ⬝ᵥ x + b

/-- The expected number of oracle calls of a randomized decision tree `R` (a frozen distribution
over frozen deterministic trees) run against the oracle `x`, the expectation being over the
algorithm's randomness (LSW Theorem 42, p.54, "expected" oracle complexity). -/
noncomputable def expectedQueries {ι κ α : Type*} (R : RandDecisionTree ι κ α) (x : ι → κ) : ℝ≥0∞ :=
  ∑' t, R t * (t.queries x : ℝ≥0∞)

/-- Bansal–Gupta §4.1.2 (p.17): the Bregman divergence `D_h(y ‖ x) = h(y) − h(x) − ⟨∇h(x), y − x⟩`,
the gradient being the Fréchet derivative (an element of the dual `E →L[ℝ] ℝ`). -/
noncomputable def bregmanDiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : E → ℝ)
    (y x : E) : ℝ :=
  h y - h x - fderiv ℝ h x (y - x)

/-- Bansal–Gupta p.18: `b` is the Bregman projection `Π^h_K(x') = argmin_{y ∈ K} D_h(y ‖ x')`. -/
def IsBregmanProjection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : E → ℝ)
    (K : Set E) (x' b : E) : Prop :=
  b ∈ K ∧ ∀ y ∈ K, bregmanDiv h b x' ≤ bregmanDiv h y x'

/-- Bansal–Gupta §4.1 (p.16): `h` is `α`-strongly convex with respect to the norm of `E`, in the
source's first-order form `h(y) ≥ h(x) + ⟨∇h(x), y − x⟩ + (α/2)‖y − x‖²` for all `x, y`, `h`
differentiable. -/
def IsStronglyConvexWrt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : E → ℝ)
    (α : ℝ) : Prop :=
  Differentiable ℝ h ∧ ∀ x y, h x + fderiv ℝ h x (y - x) + α / 2 * ‖y - x‖ ^ 2 ≤ h y

/-- Bansal–Gupta (4.37) (p.17) and Theorem 4.2 (p.18): `x 1, …, x T` is a run of mirror descent
with mirror map `h`, constant step size `η`, losses `f t`, started at `x0`: `x_1 = Π^h_K(x_0)` and,
for `1 ≤ t < T`, `θ'_{t+1} = ∇h(x_t) − η∇f_t(x_t)`, `x'_{t+1} = (∇h)^{−1}(θ'_{t+1})`,
`x_{t+1} = Π^h_K(x'_{t+1})`. Gradients are Fréchet derivatives; differentiability of the `f t` is
a hypothesis of the statements. -/
def IsMirrorDescentRun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : E → ℝ)
    (K : Set E) (η : ℝ) (f : ℕ → E → ℝ) (x0 : E) (T : ℕ) (x : ℕ → E) : Prop :=
  IsBregmanProjection h K x0 (x 1) ∧
    ∀ t, 1 ≤ t → t < T → ∃ x' : E, fderiv ℝ h x' = fderiv ℝ h (x t) - η • fderiv ℝ (f t) (x t) ∧
      IsBregmanProjection h K x' (x (t + 1))

/-! ### Sanity tests -/

example {ι κ α : Type*} (a : α) (x : ι → κ) :
    expectedQueries (PMF.pure (DecisionTree.leaf a : DecisionTree ι κ α)) x = 0 := by
  simp [expectedQueries, DecisionTree.queries]

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : E → ℝ) (x : E) :
    bregmanDiv h x x = 0 := by
  simp [bregmanDiv]

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : E → ℝ) (K : Set E) (x : E)
    (hx : x ∈ K) (hD : ∀ y, 0 ≤ bregmanDiv h y x) : IsBregmanProjection h K x x :=
  ⟨hx, fun y _ => by simpa [bregmanDiv] using hD y⟩

example {n : ℕ} (f : (Fin n → ℝ) → ℝ) (η δ : ℝ) :
    IsSeparationOracle η δ ∅ f (fun _ => none) := fun x hx => absurd hx (Set.notMem_empty x)

example (K : Set (Fin 0 → ℝ)) : minWidth K = 0 := by
  have : IsEmpty {a : Fin 0 → ℝ // euclidNorm a = 1} :=
    ⟨fun a => by simp [euclidNorm] at a; exact absurd a.2 (by norm_num)⟩
  simp [minWidth]

end QAlgorithms


