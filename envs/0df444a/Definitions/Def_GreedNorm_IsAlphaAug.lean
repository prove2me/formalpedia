-- Prove2me | Definitions.Def_GreedNorm_IsAlphaAug
-- name    : GreedNorm_IsAlphaAug
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:36.951189+00:00
-- url     : https://prove2.me/theorems/fc515967-a47e-4474-840b-fbe97ba1e243
-- title:
--   $\alpha$-augmentation
-- statement:
--   For a set function $h$ and $A\subseteq E$, write $h_A(e)=h(A\cup\{e\})-h(A)$. An element $e\in F(A)$ is an **$\alpha$-augmentation** of $A$ if
--
--   $$
--   h_A(e)\ \ge\ \alpha\cdot\max_{e'\in F(A)} h_A(e').
--   $$
--
--   **Formalization Note** The maximum is written as "for every $e'\in F(A)$"; these agree because $F(A)$ is finite and contains $e$.
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.2 Augmentation, p.8 (PDF 10)

import Mathlib
import Definitions.Def_GreedNorm_Feasible

namespace GreedNorm

/-- **`α`-augmentation**: `e ∈ F(A)` whose marginal `h_A(e) = h(A ∪ {e}) − h(A)` is at least
`α` times every marginal `h_A(e')`, `e' ∈ F(A)`.
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), §3.2 "Augmentation", p.8 (PDF 10): "A configuration (i, S) ∈ F(A) is an α-augmentation of A
if hA((i, S)) ≥ α·max_{(i′,S′)∈F(A)} hA((i′, S′))."

**Formalization Note** "≥ α · max" is written as "≥ α · h_A(e') for every `e' ∈ F(A)`", which
is the same since `F(A)` is finite and contains `e`. -/
def IsAlphaAug {E : Type} [Fintype E] [DecidableEq E] {p : ℕ} (α : ℝ) (h : Finset E → ℝ)
    (M : Fin p → Matroid E) (A : Finset E) (e : E) : Prop :=
  e ∈ Feasible M A ∧ ∀ e' ∈ Feasible M A, α * (h (insert e' A) - h A) ≤ h (insert e A) - h A

end GreedNorm


