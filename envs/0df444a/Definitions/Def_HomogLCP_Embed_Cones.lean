-- Prove2me | Definitions.Def_HomogLCP_Embed_Cones
-- name    : HomogLCP_Embed_Cones
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:09.945286+00:00
-- url     : https://prove2.me/theorems/558bb4e6-a0a6-4c1e-a51a-2136d8a79e6f
-- title:
--   pp. 4–8 — closed convex cones, dual cone, normal cone, LCP(M, q, C) (3.5) and certificates (4.4)
-- statement:
--   Let $\mathcal C\subseteq\mathbb R^d$, $M\in\mathbb R^{d\times d}$, $q\in\mathbb R^d$.
--
--   1. **Closed convex cone.** $\mathcal C$ is a nonempty, closed, convex cone: $\mathcal C\neq\emptyset$, $\mathcal C$ is closed and convex, and $tz\in\mathcal C$ for all $z\in\mathcal C$, $t\ge 0$.
--   2. **Dual cone.** $\mathcal C^*=\{w\mid w^\top z\ge 0\ \text{for all } z\in\mathcal C\}$.
--   3. **Normal cone.** $N_{\mathcal C}$ is the operator with graph $\{(z,x)\mid z\in\mathcal C,\ (y-z)^\top x\le 0\ \text{for all } y\in\mathcal C\}$.
--   4. **Linear complementarity problem (3.5).** $z$ solves $\mathrm{LCP}(M,q,\mathcal C)$ if
--   $$\mathcal C\ni z\perp (Mz+q)\in\mathcal C^*,$$
--   i.e. $z\in\mathcal C$, $Mz+q\in\mathcal C^*$ and $z^\top(Mz+q)=0$.
--   5. **Certificate of infeasibility (4.4).** $\lambda\in\mathbb R^d$ is a certificate of (strong) infeasibility of $\mathrm{LCP}(M,q,\mathcal C)$ if
--   $$\lambda^\top q<0,\qquad \sup_{(z,w)\in N_{\mathcal C}}\lambda^\top(Mz+w)\le 0 .$$
--
--   These objects state the companion results of the mission: the certificate form of Lemma 4.2, weak alternatives, and the decoding of solutions of the embedded problem.
--
--   **Formalization Note** The supremum in (4.4) is written pointwise, $\lambda^\top(Mz+w)\le 0$ for every $(z,w)$ in the graph of $N_{\mathcal C}$, so no real supremum of a possibly unbounded set appears. Orthogonality $a\perp b$ is $a^\top b=0$. The cone hypotheses are a separate predicate, imposed by the theorems that need them.
-- source:
--   O'Donoghue, Operator splitting for a homogeneous embedding of the linear complementarity problem, arXiv:2004.02177v4, p. 4 (cones, dual cone); p. 5 (normal cone, (3.5)); p. 8, (4.4)

import Mathlib

namespace HomogLCP.Embed

open Matrix

/-- `C ⊆ ℝ^d` is a nonempty, closed, convex cone (p. 4). -/
def IsClosedConvexCone {d : ℕ} (C : Set (Fin d → ℝ)) : Prop :=
  C.Nonempty ∧ IsClosed C ∧ Convex ℝ C ∧ ∀ z ∈ C, ∀ t : ℝ, 0 ≤ t → t • z ∈ C

/-- The dual cone `C* = {w | wᵀz ≥ 0 for all z ∈ C}` (p. 4). -/
def dualCone {d : ℕ} (C : Set (Fin d → ℝ)) : Set (Fin d → ℝ) :=
  {w | ∀ z ∈ C, 0 ≤ w ⬝ᵥ z}

/-- The graph of the normal cone operator `N_C` (p. 5): pairs `(z, x)` with `z ∈ C` and
`(y - z)ᵀx ≤ 0` for all `y ∈ C`. -/
def normalConeGraph {d : ℕ} (C : Set (Fin d → ℝ)) : Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {a | a.1 ∈ C ∧ ∀ y ∈ C, (y - a.1) ⬝ᵥ a.2 ≤ 0}

/-- `z` solves `LCP(M, q, C)`, (3.5), p. 5: `C ∋ z ⊥ (Mz + q) ∈ C*`. -/
def SolvesLCP {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ) (C : Set (Fin d → ℝ))
    (z : Fin d → ℝ) : Prop :=
  z ∈ C ∧ M *ᵥ z + q ∈ dualCone C ∧ z ⬝ᵥ (M *ᵥ z + q) = 0

/-- `lam` is a certificate of (strong) infeasibility of `LCP(M, q, C)`, (4.4), p. 8:
`lamᵀq < 0` and `sup_{(z, w) ∈ N_C} lamᵀ(Mz + w) ≤ 0`, the supremum bound written pointwise. -/
def IsInfeasCert {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℝ) (C : Set (Fin d → ℝ))
    (lam : Fin d → ℝ) : Prop :=
  lam ⬝ᵥ q < 0 ∧ ∀ a ∈ normalConeGraph C, lam ⬝ᵥ (M *ᵥ a.1 + a.2) ≤ 0

end HomogLCP.Embed


