-- Prove2me | Definitions.Def_AbelianCayleyHDX_IsAffineIn
-- name    : AbelianCayleyHDX_IsAffineIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:12.717164+00:00
-- url     : https://prove2.me/theorems/faf11955-87ce-4e30-8f40-d02c0e89c546
-- title:
--   Function affine in a direction
-- statement:
--   For $a \in V_0 = F^t$, a function $f : V_0 \to F$ is **affine in direction $[a]$** if for every $x \in V_0$ there are $A, B \in F$ with
--   $$f(x + \alpha a) = A + B\alpha \qquad \text{for every } \alpha \in F.$$
--   Replacing $a$ by $ca$, $c \in F^\times$, does not change the condition.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.1, p.11

import Mathlib

namespace AbelianCayleyHDX

/-- **Affine in direction `[a]`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.1, p.11): `f : V₀ → F` is affine in
direction `[a]` if for every `x ∈ V₀` there exist `A, B ∈ F` with `f(x + αa) = A + Bα` for every
`α ∈ F`. (The condition is unchanged when `a` is replaced by `ca`, `c ∈ F^×`.) -/
def IsAffineIn {t : ℕ} {F : Type*} [Field F] (f : (Fin t → F) → F) (a : Fin t → F) : Prop :=
  ∀ x : Fin t → F, ∃ A B : F, ∀ α : F, f (x + α • a) = A + B * α

end AbelianCayleyHDX


