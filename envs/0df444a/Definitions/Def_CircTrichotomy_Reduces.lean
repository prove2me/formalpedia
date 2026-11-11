-- Prove2me | Definitions.Def_CircTrichotomy_Reduces
-- name    : CircTrichotomy_Reduces
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:04.10223+00:00
-- url     : https://prove2.me/theorems/f0f20cfc-074e-4930-a988-cf8dba8eddc0
-- title:
--   Rational truth-table reductions $K\le L$
-- statement:
--   For $K\subseteq\Gamma^+$ and $L\subseteq\Sigma^+$, $K\le L$ if there is a **length-multiplying** morphism $\varphi:\Gamma^+\to\Sigma^+$ (all letters are mapped to words of one length $\ell\ge1$) such that $K$ is a finite Boolean combination of languages
--   $$\varphi^{-1}(u^{-1}Lv^{-1})=\{z\in\Gamma^+ : u\,\varphi(z)\,v\in L\},\qquad u,v\in\Sigma^*.$$
--
--   These reductions preserve circuit complexity classes defined by mild functions.
--
--   **Formalization Note** Quotients are positive and the Boolean combination is taken inside $\Gamma^+$.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.4.3, pp.18–19; p.7

import Mathlib
import Definitions.Def_CircTrichotomy_BoolComb

set_option autoImplicit false

namespace CircTrichotomy

/-- **`K ≤ L`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.4.3, pp.18–19; p.7): "Let L₁ ⊆ Σ₁⁺ and L₂ ⊆ Σ₂⁺ be languages. We write
L₁ ≤ L₂ if there exists a length-multiplying morphism φ : Σ₁⁺ → Σ₂⁺ such that L₁ is a finite Boolean
combination over a finite set of languages all of the form φ⁻¹(u⁻¹L₂v⁻¹), where u and v range over
Σ₂*." A morphism is length-multiplying (p.16) "if there exists ℓ ∈ ℕ>0 such that φ(a) ∈ Γ^ℓ for each
a ∈ Σ".

The morphism is given by the images `h b` of the letters, all of length `ℓ ≥ 1`; it maps `z` to
`z.flatMap h`. The quotients are positive (p.16: "x⁻¹L = {w ∈ Σ⁺ | xw ∈ L}"), so
`φ⁻¹(u⁻¹Lv⁻¹) = {z ∈ Σ₁⁺ | u φ(z) v ∈ L}`, and the Boolean combination is taken inside `Σ₁⁺`. -/
def Reduces {β α : Type} (K : Language β) (L : Language α) : Prop :=
  ∃ h : β → List α, ∃ ℓ : ℕ, 0 < ℓ ∧ (∀ b, (h b).length = ℓ) ∧
    BoolComb {M | ∃ u v : List α, M = {z | z ≠ [] ∧ u ++ z.flatMap h ++ v ∈ L}} K

end CircTrichotomy


