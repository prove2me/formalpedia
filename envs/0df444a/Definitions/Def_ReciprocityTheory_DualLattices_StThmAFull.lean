-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_StThmAFull
-- name    : ReciprocityTheory_DualLattices_StThmAFull
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:27.502534+00:00
-- url     : https://prove2.me/theorems/6ec59168-b096-4d9a-b91a-c9d16bedcd76
-- title:
--   St Thm AFull
-- statement:
--   Definitions and structural lemmas for St Thm AFull, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/StThmAFull.lean

import Definitions.Def_ReciprocityTheory_DualLattices_NsetExpInjectiveSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_SmallLevelClassSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Matrix
namespace ReciprocityTheory.PGsh
variable {R₀ : Type} [CommRing R₀]
def thmAPhi (B : BX R₀) {O : LAlg R₀} {g : ℕ} (gb : Module.Basis (Fin g) R₀ B.gg)
    (ht : Fin g ⊕ Fin g → B.gg →ₗ[R₀] (O : Type)) (bt : Fin g ⊕ Fin g → B.gg ⊗[R₀] (O : Type)) :
    Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) (O : Type) :=
  Matrix.of fun r i => Sum.elim (fun a => ht i (gb a))
    (fun a => B.ev (Algebra.linearMap R₀ (O : Type) ∘ₗ gb.coord a) (bt i)) r
def ThmAFullStatement (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) : Prop :=
  ∀ [IsDomain (Tw.O : Type)] (Dp : ∀ n, DualPair (Tw.R n)) (g : ℕ)
    (gb : Module.Basis (Fin g) R₀ B.gg) (τ : Fin g ⊕ Fin g → ℕ → B.G Tw.O)
    (E : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) (Tw.O : Type))
    (ht : Fin g ⊕ Fin g → B.gg →ₗ[R₀] (Tw.O : Type))
    (bt : Fin g ⊕ Fin g → B.gg ⊗[R₀] (Tw.O : Type)),
    Tw.c ≠ 0 → Eᵀ = -E → (∀ i, E i i = 0) → IsUnit E.det →
    (∀ i j n, ∃ k : ℕ, (Tw.q n).1 (E i j) = k ∧
      B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k)) →
    (∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i)) →
    (∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type)),
      B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) ∧
      LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w =
        LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap (bt i)) →
    let Φ := thmAPhi B gb ht bt
    let Ht : Matrix (Fin g) (Fin g ⊕ Fin g) (Tw.O : Type) := Φ.submatrix Sum.inl id
    let Bt : Matrix (Fin g) (Fin g ⊕ Fin g) (Tw.O : Type) := Φ.submatrix Sum.inr id
    let hb : Matrix (Fin g ⊕ Fin g) (Fin g) (Tw.O : Type) := (Eᵀ)⁻¹ * Htᵀ
    let ι := algebraMap (Tw.O : Type) (FractionRing (Tw.O : Type))
    Φᵀ * stdJ (Tw.O : Type) g * Φ = Tw.c • E ∧
    (∀ f : Fin g → (Tw.O : Type), ∃ t : Fin g ⊕ Fin g → (Tw.O : Type), Ht *ᵥ t = Tw.c • f) ∧
    Ht * hb = 0 ∧ Bt * hb = Tw.c • (1 : Matrix (Fin g) (Fin g) (Tw.O : Type)) ∧
    hbᵀ * E * hb = 0 ∧
    (∀ t : Fin g ⊕ Fin g → FractionRing (Tw.O : Type), Ht.map ι *ᵥ t = 0 →
      ∃ x : Fin g → FractionRing (Tw.O : Type), hb.map ι *ᵥ x = t) ∧
    (∀ x : Fin g → FractionRing (Tw.O : Type),
      (∃ w : Fin g ⊕ Fin g → (Tw.O : Type), hb.map ι *ᵥ x = ι ∘ w) →
      ∃ y : Fin g → (Tw.O : Type), Tw.c • x = ι ∘ y)
end ReciprocityTheory.PGsh


