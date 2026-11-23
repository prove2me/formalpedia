-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:17:15.110007+00:00
-- url     : https://prove2.me/theorems/bf99b68f-c4a8-4dd4-b52c-b802613a4962
-- title:
--   Torus At Data
-- statement:
--   Definitions and structural lemmas for Torus At Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TorusAtData.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField ReciprocityTheory.ChartRestriction.G.FD
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
structure TorusAt (X : Data E r) (x : Frame X.Ψ r) where
  T : PT E
  φ : (Fin r → E) →+ Vsp T.dim
  sg : ℝ
  sg_pm : sg = 1 ∨ sg = -1

  dim_pos : ∀ τ : X.Ψ, T.dim τ.1 = X.p0
  dim_neg : ∀ τ : X.Ψ, T.dim (ComplexEmbedding.conjugate τ.1) = r - X.p0

  e : X.Ψ → Fin r → (Fin r → ℂ)
  e_orth : ∀ τ a b, hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0
  e_flag : ∀ τ (i : ℕ) (hi : i ≤ r),
    Submodule.span ℂ (Set.range fun a : Fin i => e τ (Fin.castLE hi a)) =
      Submodule.span ℂ (Set.range fun a : Fin i => col (mat x τ) (Fin.castLE hi a))

  coord_pos : ∀ (τ : X.Ψ) (a : Fin (T.dim τ.1)) (v : Fin r → E),
    (φ v) ⟨τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) *
      hermC τ.1 X.Gm (Data.emb τ.1 v) (e τ (Fin.castLE (by rw [dim_pos τ]; exact X.p0_le) a))
  coord_neg : ∀ (τ : X.Ψ) (a : Fin (T.dim (ComplexEmbedding.conjugate τ.1))) (v : Fin r → E),
    (φ v) ⟨ComplexEmbedding.conjugate τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) *
      (starRingEnd ℂ) (-hermC τ.1 X.Gm (Data.emb τ.1 v)
        (e τ ⟨X.p0 + a.1, by have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (dim_neg τ); have := X.p0_le; omega⟩))
  lat : ∀ y, y ∈ T.L ↔ ∃ v ∈ X.Λ, φ v = y
  act_eq : ∀ (α : 𝓞 E) (v : Fin r → E), φ ((α : E) • v) = act α (φ v)
  im_eq : ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, (Hf (φ u) (φ v)).im =
    sg * ((Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) : ℚ) : ℝ)

  w0 : 𝓞 E
  eps_eq : ∀ v ∈ X.Λ, (T.eps (φ v) : ℝ) = Real.cos (Real.pi * (Hf (φ v) (φ ((w0 : E) • v))).im)

  s : (Fin 1 → Vsp T.dim) → ℂ
  s_mem : s ∈ T.Sec 1 1
  s_ne : s ≠ 0
def TorusAtExistsStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ φ : X.Λ →+ ℤ, ∃ u ∈ X.Λ, ∀ v : X.Λ,
      (φ v : ℚ) = Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (v : Fin r → E))) →
    ∀ w0 : 𝓞 E, (∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ,
      Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) -
        Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) →
    ∀ x ∈ X.dom, ∃ A : TorusAt X x, A.w0 = w0
def thAn {X : Data E r} {x : Frame X.Ψ r} (A : TorusAt X x) (q n : ℕ)
    (π : Vsp A.T.dim →ₗ[ℂ] Vsp A.T.dim) (b : Fin n → Vsp A.T.dim)
    (P : MvPolynomial (Letter n A.T.dim) ℂ) : ℂ :=
  polyDeriv P dir (A.T.U q b (s0 A.T π A.s)) 0 / (Real.sqrt (A.T.l2 1 A.s) : ℂ) ^ n
def TorusAtIsStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r)
    (A : TorusAt X x), IsTorusAt X x A.T
end
end ReciprocityTheory.ChartRestriction.G.I2


