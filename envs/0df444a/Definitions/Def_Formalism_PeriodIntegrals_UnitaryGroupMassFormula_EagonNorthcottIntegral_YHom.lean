-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_YHom
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_YHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:05:07.064966+00:00
-- url     : https://prove2.me/theorems/b73c44b2-95a2-4c9d-a2f8-d062535444f0
-- title:
--   YHom
-- statement:
--   Definitions and structural lemmas for YHom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/YHom.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_EagonNorthcottZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EagonNorthcottZ
open MvPolynomial
def sgn {D : ℕ} (i : Fin D) (J : Finset (Fin D)) : ℤ := (-1) ^ (J.filter (· < i)).card
abbrev P (D : ℕ) : Type := MvPolynomial (Fin D ⊕ Fin D) ℤ
abbrev S (D : ℕ) : Type := MvPolynomial (Fin D) ℤ
abbrev W (D : ℕ) : Type := Finset (Fin D) → P D
def K {D : ℕ} (t : Fin D → P D) (ω : W D) : W D :=
  fun J => ∑ i ∈ Jᶜ, (sgn i J : P D) * t i * ω (insert i J)
def ct {D : ℕ} (i : Fin D) (ω : W D) : W D :=
  fun J => if i ∈ J then 0 else (sgn i J : P D) * ω (insert i J)
def xs {D : ℕ} : Fin D → P D := fun i => X (Sum.inl i)
def ys {D : ℕ} : Fin D → P D := fun i => X (Sum.inr i)
def YHom {D : ℕ} (a : ℕ) (f : P D) : Prop := ∀ m ∈ f.support, ∑ i, m (Sum.inr i) = a
def Gr {D : ℕ} (a j : ℕ) (ω : W D) : Prop := (∀ J, J.card ≠ j → ω J = 0) ∧ ∀ J, YHom a (ω J)
def inx {D : ℕ} : S D →ₐ[ℤ] P D := rename Sum.inl
def mu {D : ℕ} : P D →ₐ[ℤ] S D := aeval (Sum.elim X X)
def Dop {D : ℕ} (ι : Fin D → Fin D ⊕ Fin D) (i : Fin D) : P D →ₗ[ℤ] P D :=
  (basisMonomials (Fin D ⊕ Fin D) ℤ).constr ℤ fun m =>
    if 0 < m (ι i) ∧ ∀ l, l < i → m (ι l) = 0 then monomial (m - Finsupp.single (ι i) 1) (1 : ℤ) else 0
def hom {D : ℕ} (ι : Fin D → Fin D ⊕ Fin D) (ω : W D) : W D :=
  fun J => if h : J.Nonempty then Dop ι (J.min' h) (ω (J.erase (J.min' h))) else 0
end PI.EagonNorthcottZ


