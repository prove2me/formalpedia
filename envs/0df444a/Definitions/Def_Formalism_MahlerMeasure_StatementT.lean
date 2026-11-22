-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_StatementT
-- name    : Formalism_MahlerMeasure_StatementT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:11.826123+00:00
-- url     : https://prove2.me/theorems/7c982f63-11c1-4c35-bae2-5d381e9843f3
-- title:
--   Statement T
-- statement:
--   Definitions and structural lemmas for Statement T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/StatementT.lean

import Definitions.Def_Formalism_MahlerMeasure_CsSaturated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.M
open MvPolynomial Finset
def HypP (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (e1 : ℕ) : Prop :=
  (∀ j ≤ N, ∀ Cs : Finset (Fin r), (Cs = univ ∨ Cs = univ.erase ρ) → ∀ T : Set (Fin r → ℤ), CsSaturated Cs T →
    ∃ P, IsTypeProj p LL j Cs T P ∧ (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r)) ∧
  (∀ (j j' : ℕ) (Cs Cs' : Finset (Fin r)) (T T' : Set (Fin r → ℤ)) (P P'), j ≤ j' → Cs' ⊆ Cs →
    (Cs = univ ∨ Cs = univ.erase ρ) → (Cs' = univ ∨ Cs' = univ.erase ρ) →
    IsTypeProj p LL j Cs T P → IsTypeProj p LL j' Cs' T' P' → P ∘ₗ P' = P' ∘ₗ P)
def HypW (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (e1 : ℕ) : Prop :=
  ∀ j ≤ N, ∀ la : Fin r → ℤ, ∀ x ∈ IsoC p LL j univ la ⊓ Pol p r LL, x ∈ IntPol p (Fin N × Fin r) →
    ((p : ℚ_[p]) ^ e1) • x ∈ ⨆ (h : MvPolynomial (Fin N × Fin r) ℚ_[p])
      (_ : h ∈ HWC p LL j univ la ⊓ Pol p r LL ∧ h ∈ IntPol p (Fin N × Fin r)), WeylLat p LL j h
def HypE (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (ρ : Fin r) (e1 : ℕ) : Prop :=
  ∀ j ≤ N, ∀ la : Fin r → ℤ, ∃ P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
    P ∘ₗ P = P ∧ LinearMap.range P = HWC p LL j (univ.erase ρ) la ⊓ WtSpC p LL j univ la ∧
    LinearMap.ker P ⊓ WtSpC p LL j univ la =
      (⨆ (c : Fin r) (d : Fin r) (_ : c ∈ univ.erase ρ ∧ d ∈ univ.erase ρ ∧ d < c),
        Submodule.map (glAct p LL j c d) ⊤) ⊓ WtSpC p LL j univ la ∧
    (∀ F G, F ∈ WtSpC p LL j univ la → G ∈ WtSpC p LL j univ la → fock p (P F) G = fock p F (P G)) ∧
    ∀ F ∈ PolZ p r LL, F ∈ WtSpC p LL j univ la → ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin N × Fin r)
def GramDeterminantGradedHypothesis (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (κ : ℝ) : Prop :=
  ∀ (w : Fin r → ℤ) (e k : ℕ) (g : Fin k → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
    LinearIndependent ℤ_[p] g → Submodule.span ℤ_[p] (Set.range g) = grLat p LLw J M ρ w (Fin.last K, ρ) e →
    (p : ℝ) ^ (-(κ * k)) ≤ ‖(Matrix.of fun a b => fock p (g a) (g b) / ∏ i, ((LLw.deg i).factorial : ℚ_[p])).det‖
def BadCrit : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (Vs : Type) [AddCommGroup Vs] [Module ℚ_[p] Vs] [Module ℤ_[p] Vs]
    [IsScalarTower ℤ_[p] ℚ_[p] Vs]
    (be : Vs →ₗ[ℚ_[p]] Vs →ₗ[ℚ_[p]] ℚ_[p]) (L L₁ : Submodule ℤ_[p] Vs) (D : ℤ),
    Module.Finite ℤ_[p] L → L₁ ≤ L →
    (∀ (a : ℤ_[p]) (x : Vs), a ≠ 0 → x ∈ L → a • x ∈ L₁ → x ∈ L₁) →
    (∀ u ∈ L₁, (∀ (a : ℤ_[p]) (x : Vs), x ∈ L₁ → u = a • x → IsUnit a) →
      ∃ u' ∈ L, (p : ℝ) ^ (-D) ≤ ‖be u u'‖) →
    bad p (fun x y => be x y) L D ≤ Module.finrank ℤ_[p] L - Module.finrank ℤ_[p] L₁
end Formalism.GM.M


