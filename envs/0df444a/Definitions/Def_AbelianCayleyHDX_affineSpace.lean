-- Prove2me | Definitions.Def_AbelianCayleyHDX_affineSpace
-- name    : AbelianCayleyHDX_affineSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:34:35.417072+00:00
-- url     : https://prove2.me/theorems/c8679854-d4b0-48fc-8f45-2440e3c02a37
-- title:
--   The space $A(D)$ of functions affine along $D$
-- statement:
--   For $D \subseteq \mathrm{PG}(t-1, F)$, $A(D)$ is the set of functions $V_0 \to F$ that are affine in every direction of $D$; it is an $F$-linear subspace of $F^{V_0}$.
--
--   **Formalization Note** Each direction is tested at a chosen representative, which suffices since the condition depends only on the direction.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.1, p.11

import Mathlib
import Definitions.Def_AbelianCayleyHDX_PG
import Definitions.Def_AbelianCayleyHDX_IsAffineIn

namespace AbelianCayleyHDX

/-- **The space `A(D)`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.1, p.11): the functions `V₀ → F` affine in every
direction of `D`, an `F`-linear subspace of `F^{V₀}`.

**Formalization Note** Each direction is tested at its chosen representative
`Projectivization.rep`; the condition depends only on the direction (p.11). -/
def affineSpace {t : ℕ} {F : Type*} [Field F] (D : Finset (PG t F)) :
    Submodule F ((Fin t → F) → F) where
  carrier := {f | ∀ d ∈ D, IsAffineIn f d.rep}
  add_mem' := by
    intro f g hf hg d hd x
    obtain ⟨A₁, B₁, h₁⟩ := hf d hd x
    obtain ⟨A₂, B₂, h₂⟩ := hg d hd x
    exact ⟨A₁ + A₂, B₁ + B₂, fun α => by simp only [Pi.add_apply, h₁, h₂]; ring⟩
  zero_mem' := by
    intro d _ x
    exact ⟨0, 0, fun α => by simp⟩
  smul_mem' := by
    intro c f hf d hd x
    obtain ⟨A, B, h⟩ := hf d hd x
    exact ⟨c * A, c * B, fun α => by simp only [Pi.smul_apply, smul_eq_mul, h]; ring⟩

end AbelianCayleyHDX


