-- Prove2me | Definitions.Def_ConvexRMDP_Supplement_Assumption61
-- name    : ConvexRMDP_Supplement_Assumption61
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:54:18.95699+00:00
-- url     : https://prove2.me/theorems/e48bdffd-0931-5821-a610-353a77877e22
-- title:
--   Assumption 6.1: $\mathcal U_s=\{P\in\Delta(S)^A\mid g_{s,i}(P)\le0\}$ with Slater (corrected: Slater point feasible)
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an s-rectangular robust MDP, $m \in \mathbb N$, and for each $s$ let $g_{s,1}, \dots, g_{s,m} : \mathbb R^{\mathcal S \times \mathcal A} \to \mathbb R$. **Assumption 6.1** holds when
--
--   1. every $g_{s,i}$ is (proper, closed) convex;
--   2. $\mathcal U_s = \{P \in \Delta(\mathcal S)^{\mathcal A} : g_{s,i}(P) \le 0 \text{ for all } i\}$ for every $s$;
--   3. (**Slater's condition**) for every $s$ there is $P$ in the relative interior of $\Delta(\mathcal S)^{\mathcal A}$ with $g_{s,i}(P) \le 0$ for every affine $g_{s,i}$ and $g_{s,i}(P) < 0$ for every $g_{s,i}$ that is not affine.
--
--   **Reading.** The page prints "$\mathcal U_{sa} = \{p \in \Delta(\mathcal S)^{\mathcal A} \mid g_s(p) \le 0, \forall i\}$"; in the s-rectangular model the set is $\mathcal U_s$ and the constraints are $g_{s,i}(P) \le 0$ for each $i$.
--
--   **Correction.** As printed, the Slater point need not satisfy the affine constraints. The proof relies on strong duality with dual attainment (Boyd–Vandenberghe §5.2.3), whose refined Slater condition requires the affine constraints at the point; item 3 adds them. Since the $g_{s,i}$ are finite everywhere, the relative-interior-of-domain part of that condition is automatic.
--
--   **Formalization Note** $\mathbb R^{\mathcal S \times \mathcal A}$ is `A → S → ℝ`. A finite convex function on a finite-dimensional space is automatically proper and continuous, so convexity on the whole space expresses "proper closed convex". "Affine" means $g = \varphi$ for an affine map $\varphi$.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, §6, Assumption 6.1, p.20; Slater condition corrected after Boyd & Vandenberghe (2004) §5.2.3

import Mathlib
import Definitions.Def_ConvexRMDP_Supplement_SRMDP

namespace ConvexRMDP

namespace Supplement

variable {S A : Type*} [Fintype S] [Fintype A]

/-- **Assumption 6.1, with Slater's condition corrected** (Grand-Clément & Petrik,
arXiv:2209.10187v2, p.20). For every `s` there are proper closed convex
`g_{s,1}, …, g_{s,m} : ℝ^{S×A} → ℝ` with `𝒰_s = {P ∈ Δ(S)^A | g_{s,i}(P) ≤ 0, ∀ i}`, and Slater's
condition holds: there is `P` in the relative interior of `Δ(S)^A` with `g_{s,i}(P) < 0` for every `i`
such that `g_{s,i}` is not affine.

**Reading.** The page prints `𝒰_{sa} = {p ∈ Δ(S)^A | g_s(p) ≤ 0, ∀ i ∈ {1,…,m}}`; the set is `𝒰_s`
(the model is s-rectangular) and the constraint is `g_{s,i}(P) ≤ 0` for every `i`.

**Correction.** As printed, the Slater point need not satisfy the affine constraints; the paper's proof
cites Boyd–Vandenberghe §5.2.3, whose refined Slater condition also requires `g_{s,i}(P) ≤ 0` at the
point for affine `g_{s,i}`. (The domains are all of `ℝ^{S×A}`, so the relative-interior-of-domain part
of that condition is automatic.)

**Formalization Note.** `ℝ^{S×A}` is `A → S → ℝ` (`P a s'`). A finite convex function on a
finite-dimensional space is automatically proper and closed (continuous), so `ConvexOn ℝ univ`
expresses "proper closed convex". `relint` is `intrinsicInterior`; "affine" means `g = ⇑φ` for an
affine map `φ`. -/
def Assumption61 (M : SRMDP S A) (m : ℕ) (g : S → Fin m → (A → S → ℝ) → ℝ) : Prop :=
  (∀ s i, ConvexOn ℝ Set.univ (g s i)) ∧
    (∀ s, M.U s = {P | (∀ a, P a ∈ stdSimplex ℝ S) ∧ ∀ i, g s i P ≤ 0}) ∧
    (∀ s, ∃ P ∈ intrinsicInterior ℝ {P : A → S → ℝ | ∀ a, P a ∈ stdSimplex ℝ S},
      ∀ i, ((∃ φ : (A → S → ℝ) →ᵃ[ℝ] ℝ, ⇑φ = g s i) → g s i P ≤ 0) ∧
        ((¬ ∃ φ : (A → S → ℝ) →ᵃ[ℝ] ℝ, ⇑φ = g s i) → g s i P < 0))

end Supplement

end ConvexRMDP


