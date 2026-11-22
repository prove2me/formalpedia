-- Prove2me | Definitions.Def_Formalism_CharacterColumnKernels_StatementNG
-- name    : Formalism_CharacterColumnKernels_StatementNG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:27:57.149534+00:00
-- url     : https://prove2.me/theorems/75efefb2-4f89-475b-b181-cecbc734474a
-- title:
--   Statement NG
-- statement:
--   Definitions and structural lemmas for Statement NG, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/StatementNG.lean

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.NG
def StatNGlobal : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X X' : Type)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (Z : Set X) (p : X' → X) (q : ℕ)
    (b : Fin q → (X' → O)),
    (∀ f' ∈ T', ∃ a : Fin q → (X → O), (∀ k, a k ∈ T) ∧ f' = ∑ k, (a k ∘ p) * b k) →
    (∀ x ∉ Z, ∀ a : Fin q → O, (∀ x', p x' = x → ∑ k, a k * b k x' = 0) → a = 0) →
    ∀ (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
      (m g : Type) [Fintype m] [Fintype g] [DecidableEq g] (P : Matrix m g R'),
    (∀ Θ : Matrix g g R', ∃ f ∈ T', ∀ x', algebraMap O (FractionRing O) (f x') =
      (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det) →
    (∀ x', p x' ∉ Z → ∃ φ : Coker P →ₗ[R'] EvalSp O d R' x', φ ≠ 0) →
    ∀ (π' : X') (ρπ : R' →ₐ[O] Matrix d d O),
      (∀ r : R', (ρπ r).map (algebraMap O (FractionRing O)) = (r : X' → Matrix d d (FractionRing O)) π') →
    ∀ (t : ℕ) (bl : d → Fin (t + 1)), (∀ r, (ρπ r).BlockTriangular bl) →
    ∀ (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O),
      (∀ k, Function.Surjective (ρk k)) → (∀ r k, (ρπ r).toSquareBlock bl k = ρk k r) →
      ((Fintype.card g * ∑ k : Fin (t + 1), Fintype.card {a // bl a = k} : ℕ) : Cardinal) <
        Cardinal.mk (IsLocalRing.ResidueField O) →
    ∀ (ℓ : ℕ) (what₂ cols Q : Finset ℕ) (lenRow : ℕ → ℕ∞) (e' : ℕ → ℕ) (j : ℕ → ℕ) (vδ : ℕ∞)
      (h0 : ℕ → ℕ∞) (s : ℕ∞) (Sha : ℕ → ℕ∞) (vhE : ℕ∞) (cB : ℕ) (deg : ℕ → ℕ) (H0 : ℕ∞)
      (vζ : ℕ → ℕ∞),
      let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
      Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρk 0) P))) ≤
        ∑ w ∈ what₂, lenRow w + ∑ w ∈ cols, ((j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + h0 w) + s +
          4 * (Fintype.card {a // bl a = 0} : ℕ∞) * ((cols.card : ℕ∞) + 1) * vδ →
      (∀ c : Fin (t + 1), c ≠ 0 →
        Module.length O (LinearMap.ker (relMap O (KO O) (bigRect (ρk c) P))) ≤
          (if (c : ℕ) = 1 then vhE + ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) else Sha ((c : ℕ) - 1)) +
            eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) + 4 * ((cols.card : ℕ∞) + 1) * vδ +
            (cols.card : ℕ∞) * H0 + ∑ z ∈ Q, vζ z) →
      vcc T Z (p π') ≤
        ∑ w ∈ what₂, lenRow w +
          ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
          ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
          (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
          4 * ((Fintype.card {a // bl a = 0} : ℕ∞) + t) * ((cols.card : ℕ∞) + 1) * vδ +
          (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ z ∈ Q, vζ z
def LocalSubalgebraEtaBound : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type*) [Finite X]
    (T : Subalgebra O (X → O)) [IsLocalRing T], (∀ x y : X, x ≠ y → ∃ f ∈ T, f x ≠ f y) →
    ∀ (V : Type*) [AddCommGroup V] [Module (FractionRing O) V] [FiniteDimensional (FractionRing O) V]
      [Module O V] [IsScalarTower O (FractionRing O) V]
      (act : T →+* Module.End (FractionRing O) V), (⨆ x, Vx T act x) = ⊤ →
    ∀ L : Submodule O V, L.FG → Submodule.span (FractionRing O) (L : Set V) = ⊤ →
      (∀ f : T, ∀ v ∈ L, act f v ∈ L) →
    ∀ (Z Zg : Finset X), Zg ⊆ Z → ∀ (a : Module.End (FractionRing O) V) (A : ℤ),
      (∀ v ∈ L, a v ∈ L) → (∀ f : T, a * act f = act f * a) →
      (∀ x ∈ Zg, ∀ v ∈ Vx T act x, a v = (A : FractionRing O) • v) →
      (∀ x ∈ Z, x ∉ Zg → ∀ v ∈ Vx T act x, a v = 0) →
    ∀ B : X → ℕ∞, (∀ x ∈ Zg, vcc T (Z : Set X) x ≤ B x) →
      Module.length O (CongMod T act L (Zg : Set X)) ≤
        ∑ x ∈ Zg, (Module.finrank (FractionRing O) (Vx T act x) : ℕ∞) *
          (B x + IsDiscreteValuationRing.addVal O (A : O))
end Formalism.NG


