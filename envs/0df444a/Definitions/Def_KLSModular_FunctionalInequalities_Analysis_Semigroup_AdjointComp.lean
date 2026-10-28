-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_AdjointComp
-- name    : KLSModular_FunctionalInequalities_Analysis_Semigroup_AdjointComp
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:09:16.658641+00:00
-- url     : https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a
-- title:
--   Maximal-domain composition of a partial operator with its adjoint
-- statement:
--   For partially defined real-linear operators $T:H_0\to H_1$ between real inner-product spaces, `adjointCompDomain T` is the submodule of $H_0$ consisting of those $x\in D(T)$ for which $Tx\in D(T^\dagger)$. `adjointComp T` is the partial operator $T^\dagger T$ on this maximal domain, constructed by restricting $T$ before composing with the adjoint. The accompanying results characterize domain membership, verify the required adjoint-domain side condition, and state the pointwise formula for `adjointComp`.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.InnerProductSpace.LinearPMap
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def adjointCompDomain (T : H₀ →ₗ.[ℝ] H₁) : Submodule ℝ H₀ :=
--     (Submodule.comap T.toFun T†.domain).map T.domain.subtype
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Semigroup/AdjointComp.lean) · `FunctionalInequalities.Analysis.Semigroup.AdjointComp` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/AdjointComp.lean#L27-L76 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.AdjointComp`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Semigroup_AdjointComp`; the repository is private at upload time).

import Mathlib.Analysis.InnerProductSpace.LinearPMap

noncomputable section
open scoped LinearPMap
namespace FunctionalInequalities
namespace Analysis
namespace Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
/-- The domain of `T†T`, as a submodule of `H₀`: those `x ∈ D(T)` with `T x ∈ D(T†)`. -/
def adjointCompDomain (T : H₀ →ₗ.[ℝ] H₁) : Submodule ℝ H₀ :=
  (Submodule.comap T.toFun T†.domain).map T.domain.subtype
/-- Membership in the domain of `T†T`. -/
theorem mem_adjointCompDomain {T : H₀ →ₗ.[ℝ] H₁} {x : H₀} :
    x ∈ adjointCompDomain T ↔ ∃ hx : x ∈ T.domain, T ⟨x, hx⟩ ∈ T†.domain := by
  constructor
  · rintro ⟨⟨y, hy⟩, h, rfl⟩
    exact ⟨hy, h⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩
/-- On the restricted domain, `T` takes values in `D(T†)`; this is the side condition that
`LinearPMap.comp` demands. -/
theorem domRestrict_mem_adjoint_domain (T : H₀ →ₗ.[ℝ] H₁)
    (x : ↥(adjointCompDomain T ⊓ T.domain)) :
    T.domRestrict (adjointCompDomain T) x ∈ T†.domain := by
  obtain ⟨hx, h⟩ := mem_adjointCompDomain.mp x.2.1
  rw [T.domRestrict_apply (y := ⟨x, hx⟩) rfl]
  exact h
/-- `T†T` with its maximal domain `{x ∈ D(T) | T x ∈ D(T†)}`. -/
def adjointComp (T : H₀ →ₗ.[ℝ] H₁) : H₀ →ₗ.[ℝ] H₀ :=
  T†.comp (T.domRestrict (adjointCompDomain T)) (domRestrict_mem_adjoint_domain T)
/-- `adjointComp T x = T† (T x)`. -/
theorem adjointComp_apply (T : H₀ →ₗ.[ℝ] H₁) (x : (adjointComp T).domain) :
    adjointComp T x = T† ⟨T ⟨x, x.2.2⟩,
      by simpa [T.domRestrict_apply (y := ⟨x, x.2.2⟩) rfl] using domRestrict_mem_adjoint_domain T x⟩ := by
  change T† ⟨T.domRestrict (adjointCompDomain T) x, _⟩ = _
  congr 1
end Semigroup
end Analysis
end FunctionalInequalities


