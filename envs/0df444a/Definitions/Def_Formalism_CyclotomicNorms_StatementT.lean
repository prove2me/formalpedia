-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_StatementT
-- name    : Formalism_CyclotomicNorms_StatementT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:15:25.16531+00:00
-- url     : https://prove2.me/theorems/040dee50-1b85-4dd3-92ee-edf2341d4a99
-- title:
--   Statement T
-- statement:
--   Definitions and structural lemmas for Statement T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/StatementT.lean

import Definitions.Def_Formalism_CyclotomicNorms_StatementI
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
namespace Formalism.CyclotomicNorms
def primeToPart (ℓ : ℕ) {M : Type*} [Monoid M] (x : M) : M :=
  x ^ (ℓ ^ (orderOf x).factorization ℓ *
    (((ℓ ^ (orderOf x).factorization ℓ : ℕ) :
      ZMod (orderOf x / ℓ ^ (orderOf x).factorization ℓ))⁻¹).val)
abbrev Fbar (g : ℕ) [Fact g.Prime] : Type := AlgebraicClosure (ZMod g)
def rootsBar {g : ℕ} [Fact g.Prime] (f : (ZMod g)[X]) : Multiset (Fbar g) :=
  (f.map (algebraMap (ZMod g) (Fbar g))).roots
def IsGood (N g : ℕ) [Fact g.Prime] {PP J : Type} (f : PP → (ZMod g)[X])
    (χ : PP → J → (ZMod g)ˣ) : Prop :=
  (∀ v, (f v).Monic ∧ (f v).natDegree = N ∧ (f v).coeff 0 ≠ 0) ∧
  (∀ v, Squarefree (f v)) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ BB N g → ∀ v, ∀ x ∈ rootsBar (f v), ∀ y ∈ rootsBar (f v),
    primeToPart ℓ x = primeToPart ℓ y → x = y) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ g → ∀ v j, ∀ x ∈ rootsBar (f v),
    primeToPart ℓ x ≠ primeToPart ℓ (algebraMap (ZMod g) (Fbar g) (χ v j : ZMod g))) ∧
  (∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ ∃ q : (ZMod g)[X], q ∣ f v ∧ q.natDegree = a) ∧
  (∃ v, ∃ q : (ZMod g)[X], Irreducible q ∧ q ∣ f v ∧ q.natDegree.Prime ∧
    N < 2 * q.natDegree ∧ q.natDegree + 3 ≤ N)
def IrredOn {N ℓ : ℕ} [Fact ℓ.Prime] {G : Type} [Group G] (ρ : G →* GL (Fin N) (Fbar ℓ))
    (H : Subgroup G) : Prop :=
  ∀ W : Submodule (Fbar ℓ) (Fin N → Fbar ℓ),
    (∀ h ∈ H, ∀ x ∈ W, Matrix.mulVec (ρ h : Matrix (Fin N) (Fin N) (Fbar ℓ)) x ∈ W) → W = ⊥ ∨ W = ⊤
def IrreducibilityCriterion : Prop :=
  ∀ (N : ℕ) (g : Fin 2 → ℕ) [∀ i, Fact (g i).Prime] (PP : Fin 2 → Type) (J : Type)
    (f : ∀ i, PP i → (ZMod (g i))[X]) (χ : ∀ i, PP i → J → (ZMod (g i))ˣ),
    BB N (g 0) ∩ BB N (g 1) = ∅ → (∀ i, IsGood N (g i) (f i) (χ i)) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (i : Fin 2), ℓ ∉ BB N (g i) →
    ∀ (G : Type) [Group G] (ρ : G →* GL (Fin N) (Fbar ℓ)) (τ φ : PP i → G)
      (ι : PP i → Fbar (g i) →* Fbar ℓ),
      (∀ v, ρ (φ v * τ v * (φ v)⁻¹) = ρ (τ v) ^ (g i)) →
      (∀ v, ∀ x y : Fbar (g i), x ≠ 0 → y ≠ 0 → (orderOf x).Coprime ℓ → (orderOf y).Coprime ℓ →
        ι v x = ι v y → x = y) →
      (∀ v, Matrix.charpoly (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ)) =
        ((rootsBar (f i v)).map fun x => X - C (ι v (primeToPart ℓ x))).prod) →
      IrredOn ρ ⊤ ∧
      (∀ (H : Subgroup G) [H.Normal], Finite (G ⧸ H) → Group.IsSolvable (G ⧸ H) →
        (∀ v, τ v ∈ H) → IrredOn ρ H) ∧
      (∀ v j, ¬ (Matrix.charpoly (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ))).IsRoot
        (ι v (primeToPart ℓ (algebraMap (ZMod (g i)) (Fbar (g i)) (χ i v j : ZMod (g i))))))
end Formalism.CyclotomicNorms


