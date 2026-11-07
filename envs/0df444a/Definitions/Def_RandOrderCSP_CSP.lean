-- Prove2me | Definitions.Def_RandOrderCSP_CSP
-- name    : RandOrderCSP_CSP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:06:57.78561+00:00
-- url     : https://prove2.me/theorems/e143de15-718f-4bcc-b33f-78a9e99b67ae
-- title:
--   CSP instance, value and optimum
-- statement:
--   A **constraint satisfaction problem** with alphabet $\Sigma$ and arity $k$ is a $k$-uniform hypergraph $H$ with a predicate $f(j):\Sigma^k\to\{0,1\}$ on each edge $j$. For an assignment $x:\mathcal V_H\to\Sigma$,
--
--   $$\mathrm{val}_\Phi(x)=\mathbb E_{j\in\mathcal E_H}\big[f(j)(x(M_H(j,1)),\dots,x(M_H(j,k)))\big],\qquad \mathrm{opt}_\Phi=\max_x \mathrm{val}_\Phi(x).$$
--
--   $\Phi$ is an instance of $\mathrm{CSP}(\Gamma)$ when all its predicates lie in $\Gamma\subseteq\{0,1\}^{\Sigma^k}$. These are the values that the promise problem $\text{MAX-CSP}_{\beta,\gamma}(\Gamma)$ distinguishes.
--
--   **Formalization Note** The optimum is the supremum over the finite set of assignments; values are used only with a nonempty edge set, as on p.13.
-- source:
--   Singer, Tulsiani, Velusamy, A dichotomy theorem for approximating CSPs in random-order streams, STOC 2027 submission (manuscript sha256 3aca9d2f…), §3.3, p.14

import Mathlib
import Definitions.Def_RandOrderCSP_Hypergraph

namespace RandOrderCSP

/-- **CSP instance, value and optimum** (§3.3, p.14).

Singer, Tulsiani, Velusamy, *A dichotomy theorem for approximating CSPs in random-order streams*,
STOC 2027 submission (manuscript sha256 3aca9d2f…), §3.3, p.14: a CSP with alphabet `Σ` and arity
`k` is a `{0,1}^{Σ^k}`-edge-colored `k`-uniform hypergraph `Φ = (H, f)`;
`val_Φ(x) := E_{j∈ℰ_H}[(f(j))(x|_{𝒱_H(j)})]`, `opt_Φ := max_{x : 𝒱_H → Σ} val_Φ(x)`.

**Formalization Note.** A predicate `Σ^k → {0,1}` is a function `(Fin k → Σ) → Bool`, and
`x|_{𝒱_H(j)} = (x(M_H(j,1)), …, x(M_H(j,k)))` is `x ∘ H.M j`. The expectation over `j` is the
uniform average `(1/m_H) ∑_j`; theorems that use it assume `[Nonempty E]` (p.13: "Whenever we …
normalize a CSP value by its number of constraints, we assume that the edge set is nonempty").
`opt` is the supremum over the finite set of assignments; it is attained (and equals the maximum)
whenever that set is nonempty, which holds when `Σ` is nonempty. -/
structure CSP (k : ℕ) (Sig V E : Type) where
  /-- The underlying hypergraph. -/
  H : Hypergraph k V E
  /-- The predicate `f(j) : Σ^k → {0,1}` of the edge `j`. -/
  f : E → (Fin k → Sig) → Bool

namespace CSP

variable {k : ℕ} {Sig V E : Type}

/-- `val_Φ(x)`: the fraction of constraints satisfied by the assignment `x`. -/
noncomputable def val [Fintype E] (Φ : CSP k Sig V E) (x : V → Sig) : ℝ :=
  (1 / (Fintype.card E : ℝ)) * ∑ j, (if Φ.f j (x ∘ Φ.H.M j) then (1 : ℝ) else 0)

/-- `opt_Φ = opt^CSP(Φ) := max_x val_Φ(x)`. -/
noncomputable def opt [Fintype E] (Φ : CSP k Sig V E) : ℝ :=
  ⨆ x : V → Sig, Φ.val x

/-- `Φ` is an instance of `CSP(Γ)`: every predicate belongs to `Γ` (p.14). -/
def IsInstanceOf (Φ : CSP k Sig V E) (Γ : Set ((Fin k → Sig) → Bool)) : Prop :=
  ∀ j, Φ.f j ∈ Γ

end CSP

end RandOrderCSP


