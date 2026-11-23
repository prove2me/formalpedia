-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:20:18.879911+00:00
-- url     : https://prove2.me/theorems/f3fc6c3e-fc52-402e-9508-bc818e87e550
-- title:
--   Exists Unitary Basis Same Flag
-- statement:
--   Definitions and structural lemmas for Exists Unitary Basis Same Flag, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ExistsUnitaryBasisSameFlag.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UbasisAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace Data
variable {r : ℕ} (X : Data E r)
def Jt (x : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) : Fin r → ℂ :=
  I • ((2 : ℂ) • X.ppos x τ v - v)
def UBasis (z0 : Frame X.Ψ r) (ξ : Fin r → E) (f : X.Ψ → Fin (r - 2) → Fin r → ℂ) : Prop :=
  ∀ τ : X.Ψ,
    (∀ k, hermC τ.1 X.Gm (f τ k) (emb τ.1 ξ) = 0 ∧ hermC τ.1 X.Gm (X.Jt z0 τ (f τ k)) (emb τ.1 ξ) = 0) ∧
    (∀ k, X.Jt z0 τ (f τ k) = (if (k : ℕ) < X.p0 - 1 then I else -I) • f τ k) ∧
    (∀ k l, hermC τ.1 X.Gm (f τ k) (f τ l) =
      if k = l then (if (k : ℕ) < X.p0 - 1 then 1 else -1) else 0) ∧
    (∀ c : Fin (r - 2) → ℂ, X.maj z0 τ (∑ k, c k • f τ k) = ∑ k, ‖c k‖ ^ 2) ∧
    (∀ v : Fin r → ℂ, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 → hermC τ.1 X.Gm (X.Jt z0 τ v) (emb τ.1 ξ) = 0 →
      v ∈ Submodule.span ℂ (Set.range (f τ)))
end Data
end
end ReciprocityTheory.ChartRestriction.G.FD


