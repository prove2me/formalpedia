-- Prove2me | Definitions.Def_DecodablePOMDP_Supplement_Observability
-- name    : DecodablePOMDP_Supplement_Observability
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:44:11.179651+00:00
-- url     : https://prove2.me/theorems/88087ed6-1e26-466b-822f-7f4b1300d37c
-- title:
--   $\ell_1$- and $\ell_2$-observability (Definitions 1–2) and the optimal $\ell_1$-observability parameter $\gamma(K)$
-- statement:
--   Let $K$ be an observation channel from a finite state space $\mathcal S$ to a finite observation space $\mathcal O$, viewed as the matrix $K\in\mathbb R^{\mathcal O\times\mathcal S}$ with entries $(K)_{y,s}=K(y\mid s)$, so that $(Kv)(y)=\sum_s K(y\mid s)\,v(s)$ for $v\in\mathbb R^{\mathcal S}$. Write $\Delta(\mathcal S)$ for the probability vectors on $\mathcal S$ and $\mathbf 1^\perp_{\mathcal S}$ for the zero-sum vectors.
--
--   1. For $\gamma>0$, $K$ is **$\gamma$-$\ell_1$-observable** if $\|Kp-Kq\|_1\ge\gamma\|p-q\|_1$ for all $p,q\in\Delta(\mathcal S)$.
--   2. For $\alpha>0$, $K$ is **$\alpha$-$\ell_2$-observable** if $\|Kp-Kq\|_2\ge\alpha\|p-q\|_2$ for all $p,q\in\Delta(\mathcal S)$.
--   3. The **optimal $\ell_1$-observability parameter** of $K$ is
--
--   $$\gamma(K)=\inf_{v\in\mathbf 1^\perp_{\mathcal S},\,v\ne0}\frac{\|Kv\|_1}{\|v\|_1}.$$
--
--   Observability is the reverse data-processing assumption of Golowich et al. under which quasipolynomial planning was first proved; Theorem 5 shows it implies decodability, Theorem 6 that constant $\ell_2$-observability does not give fast filter forgetting, and Theorem 7 that $\gamma(K)$ can encode the uniform sparsest cut.
--
--   **Formalization Note** The channel is stored as `Kc s y` $=K(y\mid s)$, the base mission's convention. The ranges $\gamma>0$, $\alpha>0$ are part of the predicates. $\gamma(K)$ is a real infimum over the nonzero zero-sum vectors; it is a genuine infimum when $|\mathcal S|\ge2$ (the ratios are nonnegative), and Lean returns $0$ when $|\mathcal S|\le1$, a case never used.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), Definition 1 and Definition 2, p.3; App. D, p.28 (definition of γ(K))

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist

namespace DecodablePOMDP.Supplement

open CalibratedCE.Forecast

/-- **The channel acting on a vector.** For a channel `Kc s y = K(y | s)` from `S` to `O` and a vector
`v ∈ ℝ^S`, `chanApply Kc v` is `Kv ∈ ℝ^O`, `(Kv)(y) = Σ_s K(y | s) v(s)` (the matrix
`K ∈ ℝ^{O×S}` with entries `(K)_{y,s} = K(y | s)` applied to `v`).

Dobson, Jog, Shiu, *Quasipolynomial-Time Planning for Decodable POMDPs* (preprint, sha256
c1256cbe…3584b), Definition 1, p.3: "The observation channel K ∈ R^{O×S} from the state space S to
the output space O is the matrix with entries (K)_{y,s} = K(y|s)."

**Formalization Note.** The base mission's convention `Kc s y = K(y | s)` is kept. -/
def chanApply {S O : Type} [Fintype S] (Kc : S → O → ℝ) (v : S → ℝ) : O → ℝ :=
  fun y => ∑ s, Kc s y * v s

/-- The ℓ1 norm `‖v‖₁ = Σ_a |v(a)|` on `ℝ^α`, `α` finite. -/
def l1norm {α : Type} [Fintype α] (v : α → ℝ) : ℝ :=
  ∑ a, |v a|

/-- The Euclidean norm `‖v‖₂ = (Σ_a v(a)²)^{1/2}` on `ℝ^α`, `α` finite. -/
noncomputable def l2norm {α : Type} [Fintype α] (v : α → ℝ) : ℝ :=
  Real.sqrt (∑ a, v a ^ 2)

/-- **γ-ℓ1-observability** (Definition 1, p.3). For `γ > 0`, a channel `K` is γ-ℓ1-observable if
`‖Kp − Kq‖₁ ≥ γ ‖p − q‖₁` for all state distributions `p, q ∈ Δ(S)`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Definition 1, p.3: "Let γ > 0. … This channel is
said to be γ-ℓ1-observable if, for any state distributions p, q ∈ ∆(S), ∥Kp − Kq∥1 ≥ γ∥p − q∥1. (1)"

**Formalization Note.** The standing range `γ > 0` is part of the predicate; `p, q` range over
probability vectors (`IsDist`), exactly as printed. -/
def IsL1Observable {S O : Type} [Fintype S] [Fintype O] (Kc : S → O → ℝ) (γ : ℝ) : Prop :=
  0 < γ ∧ ∀ p q : S → ℝ, IsDist p → IsDist q →
    γ * l1norm (fun s => p s - q s) ≤ l1norm (fun y => chanApply Kc p y - chanApply Kc q y)

/-- **α-ℓ2-observability** (Definition 2, p.3). For `α > 0`, a channel `K` satisfies
α-ℓ2-observability if `‖Kp − Kq‖₂ ≥ α ‖p − q‖₂` for all distributions `p, q ∈ Δ(S)`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), Definition 2, p.3: "Let α > 0. Let K be as in
Definition 1. We say that K satisfies α-ℓ2-observability if for any distributions p, q ∈ ∆(S),
∥Kp − Kq∥2 ≥ α∥p − q∥2. (2)"

**Formalization Note.** The standing range `α > 0` is part of the predicate; `p, q` range over
probability vectors, exactly as printed. -/
def IsL2Observable {S O : Type} [Fintype S] [Fintype O] (Kc : S → O → ℝ) (α : ℝ) : Prop :=
  0 < α ∧ ∀ p q : S → ℝ, IsDist p → IsDist q →
    α * l2norm (fun s => p s - q s) ≤ l2norm (fun y => chanApply Kc p y - chanApply Kc q y)

/-- **Optimal ℓ1-observability parameter** (App. D, p.28):
`γ(K) = inf_{v ≠ 0, v ∈ 1⊥_S} ‖Kv‖₁ / ‖v‖₁`, the infimum over nonzero zero-sum vectors.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. D, p.28: "Given an observation kernel
K ∈ R^{O×S}, define its optimal ℓ1-observability parameter as γ(K) := inf_{v≠0: v∈1⊥_S} ∥Kv∥1/∥v∥1."

**Formalization Note.** A real infimum (`⨅`) over the subtype of nonzero zero-sum vectors. Every
ratio is `≥ 0`, so the infimum is a genuine one whenever the index set is nonempty, i.e. whenever
`S` has at least two elements; on a one-point (or empty) `S` the index set is empty and Lean's value
is `0`. Every use in this mission assumes `|S| ≥ 2`. -/
noncomputable def optL1Obs {S O : Type} [Fintype S] [Fintype O] (Kc : S → O → ℝ) : ℝ :=
  ⨅ v : {v : S → ℝ // (∑ s, v s) = 0 ∧ v ≠ 0}, l1norm (chanApply Kc v.1) / l1norm v.1

end DecodablePOMDP.Supplement


