-- Prove2me | Definitions.Def_KMSHolder_IsArakiContinuation
-- name    : KMSHolder_IsArakiContinuation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:40:16.762025+00:00
-- url     : https://prove2.me/theorems/1a5a5532-3f12-4afa-8b85-95986d1cefbb
-- title:
--   Araki's symbolic notation: a continuation of the real-time correlation to $I^{(n)}$
-- statement:
--   With the notation of the real-time correlation $F_A(s) = \langle \Omega, A_n\Delta^{is_n}\cdots A_1\Delta^{is_1}A_0\Omega\rangle$, a function $G : \mathbb C^n \to \mathbb C$ is an **analytic continuation of $F_A$ to the tube** $I^{(n)} = I^{(n)}_1$ if
--
--   1. $G$ is continuous on the closed tube $I^{(n)}$;
--   2. $G$ is holomorphic in the interior of $I^{(n)}$;
--   3. $G(is_1, \dots, is_n) = F_A(s_1, \dots, s_n)$ for all $s \in \mathbb R^n$.
--
--   The value $G(z)$ is what Araki's symbolic notation writes as $\omega(A_n \Delta^{z_n} \cdots A_1 \Delta^{z_1} A_0)$. It is not an operator composition: for $\Re z_1 > 1/2$ the vector $A_0\Omega$ need not lie in the domain of $\Delta^{z_1}$.
--
--   **Formalization Note** No boundedness or growth condition is imposed. The continuation exists and is unique on $I^{(n)}$ without one (milestone `KMSHolder.araki_continuation_exists_unique`), so a statement quantified over all such $G$ is a statement about the paper's value and is not vacuous.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, §2, sentence after eq. (2), p.3; eq. (5), p.5

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_KMSHolder_tube
import Definitions.Def_KMSHolder_realChain

open OAI.BoundedRecovery

namespace KMSHolder

/-- Jäkel–Robl, arXiv:1103.3608v2, §2, sentence after eq. (2), p.3, and eq. (5), p.5: Araki's
symbolic notation. `G` is *an* analytic continuation of the real-time correlation
`s ↦ ⟪Ω, Aₙ Δ^{isₙ} ⋯ A₁ Δ^{is₁} A₀ Ω⟫` to the tube `I⁽ⁿ⁾ = I⁽ⁿ⁾₁`:
1. `G` is continuous on the closed tube `I⁽ⁿ⁾`;
2. `G` is holomorphic (complex differentiable) in its interior;
3. on the edge `z = (is₁, …, isₙ)`, `s ∈ ℝⁿ`, `G` equals the real-time correlation.

The value `G z` is what the paper writes `ω(Aₙ Δ^{zₙ} ⋯ A₁ Δ^{z₁} A₀)`; it is not an operator
composition (for `ℜz₁ > 1/2`, `A₀Ω` need not lie in the domain of `Δ^{z₁}`).

**Formalization Note.** No boundedness or growth condition is imposed: the continuation is
unique without one (milestone `KMSHolder.araki_continuation_exists_unique`), so statements
"for every `G` with `IsArakiContinuation S A G`" are about the paper's value and are not vacuous.
Lean index `j` of `z` is the paper's `z_{j+1}`. -/
def IsArakiContinuation {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StandardModularData H) {n : ℕ} (A : Fin (n + 1) → H →L[ℂ] H)
    (G : (Fin n → ℂ) → ℂ) : Prop :=
  ContinuousOn G (tube n 1) ∧ DifferentiableOn ℂ G (interior (tube n 1)) ∧
    ∀ s : Fin n → ℝ, G (fun j => (s j : ℂ) * Complex.I) = realChain S A s

end KMSHolder


