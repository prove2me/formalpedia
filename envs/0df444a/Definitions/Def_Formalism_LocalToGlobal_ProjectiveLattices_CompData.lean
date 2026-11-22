-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompData
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_CompData
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:51.250583+00:00
-- url     : https://prove2.me/theorems/d06c1776-dde1-4d37-925c-8f9bd6cf1381
-- title:
--   Comp Data
-- statement:
--   Definitions and structural lemmas for Comp Data, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CompData.lean

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
abbrev WTZ (E : Type) [Field E] : Type := ((E →+* ℂ) × ℕ → ℤ) × ℤ
def wtZ {E : Type} [Field E] (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : WTZ E := (fun x => (a x : ℤ), (n : ℤ))
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
abbrev AC (Z : Comp Xo c) : Type := AddMonoidAlgebra (Om Z) (WTZ E)
example (Z : Comp Xo c) : Algebra (𝓞 c.F) (AC Z) := inferInstance
example (Z : Comp Xo c) : IsScalarTower (𝓞 c.F) c.F (AC Z) := inferInstance
instance towKAC (Z : Comp Xo c) : IsScalarTower c.F (Om Z) (AC Z) := inferInstance
def AG (Z : Comp Xo c) (G : WTZ E) : Submodule (Om Z) (AC Z) :=
  Submodule.span (Om Z) {AddMonoidAlgebra.single G 1}
theorem mem_AG {Z : Comp Xo c} {G : WTZ E} {f : AC Z} : f ∈ AG Z G ↔ ∃ r : Om Z, f = AddMonoidAlgebra.single G r := by
  unfold AG
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [AddMonoidAlgebra.smul_single', mul_one]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, by rw [AddMonoidAlgebra.smul_single', mul_one]⟩
instance gradedAG (Z : Comp Xo c) : SetLike.GradedMonoid (AG Z) where
  one_mem := mem_AG.2 ⟨1, rfl⟩
  mul_mem := by
    intro G G' f g hf hg
    obtain ⟨r, rfl⟩ := mem_AG.1 hf
    obtain ⟨s, rfl⟩ := mem_AG.1 hg
    exact mem_AG.2 ⟨r * s, by rw [AddMonoidAlgebra.single_mul_single]⟩
def valC (h : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ∀ Z : Comp Xo c, AC Z :=
  fun Z => AddMonoidAlgebra.single (wtZ a n) (evC h Z f)
end Formalism.L2.Pj


