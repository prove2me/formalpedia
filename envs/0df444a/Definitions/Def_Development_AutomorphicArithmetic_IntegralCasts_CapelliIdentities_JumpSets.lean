-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_JumpSets
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_JumpSets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:29:56.001393+00:00
-- url     : https://prove2.me/theorems/db52fbad-ee16-4838-a7c6-248008fc4799
-- title:
--   Jump Sets
-- statement:
--   Definitions and structural lemmas for Jump Sets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/JumpSets.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold
open scoped Classical
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.HypOdd :
    ℕ → ℕ → Prop :=
    fun (q d : ℕ) ↦ Nat.Prime q ∧ Nat.Prime d ∧ q ≠ d ∧ q ≠ (2 : ℕ) ∧ d ≠ (2 : ℕ)
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.IsLayer.{u_1} :
    ℕ → ℕ → ℕ → {L : Type u_1} → [inst : Field L] → [Algebra ℚ L] → L → L → L → Prop :=
    fun (n q d : ℕ) {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦
      IsPrimitiveRoot ζ ((2 : ℕ) ^ n) ∧ a ^ (2 : ℕ) = -(↑q : L) ∧ b ^ (2 : ℕ) = -(↑d : L) ∧ ℚ⟮ζ, a, b⟯ = ⊤
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.E0.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → L → L → IntermediateField ℚ L :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (a b : L) ↦ ℚ⟮a, b⟯
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.F1.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → L → IntermediateField ℚ L :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ : L) ↦ ℚ⟮ζ + ζ⁻¹⟯
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.hostE.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → L → L → L → IntermediateField ℚ L :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦ UpperTheory.Reformulated.B.JumpSetsAlt.E0 a b ⊔ UpperTheory.Reformulated.B.JumpSetsAlt.F1 ζ
@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.G0 :
    Type :=
    ℤˣ × ℤˣ
@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.HGrp :
    ℕ → Type :=
    fun (e : ℕ) ↦ (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ)
@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.GG :
    ℕ → Type :=
    fun (e : ℕ) ↦ UpperTheory.Reformulated.B.JumpSetsAlt.G0 × UpperTheory.Reformulated.B.JumpSetsAlt.HGrp e
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.sgn.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → Gal(L/ℚ) → L → ℤˣ :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (σ : Gal(L/ℚ)) (x : L) ↦ if (σ : L → L) x = x then (1 : ℤˣ) else (-1 : ℤˣ)
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.aE.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → (ζ a b : L) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦
      (⟨a, (show ∀ {L : Type _} [inst : Field L] [inst_1 : Algebra ℚ L] (ζ a b : L), a ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b from by
  intro L _ _ ζ a b
  exact (le_sup_left : UpperTheory.Reformulated.B.JumpSetsAlt.E0 a b ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))
) ζ a b⟩ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b))
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.bE.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → (ζ a b : L) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦
      (⟨b, (show ∀ {L : Type _} [inst : Field L] [inst_1 : Algebra ℚ L] (ζ a b : L), b ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b from by
  intro L _ _ ζ a b
  exact (le_sup_left : UpperTheory.Reformulated.B.JumpSetsAlt.E0 a b ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))
) ζ a b⟩ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b))
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.thE.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → (ζ a b : L) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦
      (⟨ζ + ζ⁻¹, (show ∀ {L : Type _} [inst : Field L] [inst_1 : Algebra ℚ L] (ζ a b : L), ζ + ζ⁻¹ ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b from by
  intro L _ _ ζ a b
  exact (le_sup_right : UpperTheory.Reformulated.B.JumpSetsAlt.F1 ζ ≤ _) (IntermediateField.subset_adjoin ℚ _ (by simp))
) ζ a b⟩ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b))
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.hcl :
    (e : ℕ) → (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ → UpperTheory.Reformulated.B.JumpSetsAlt.HGrp e :=
    fun (e : ℕ) (u : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ) ↦
      (↑u : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ ⧸ Subgroup.zpowers (-1 : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ))
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.hPart.{u_1} :
    {L : Type u_1} →
      [inst : Field L] →
        [inst_1 : Algebra ℚ L] → (e : ℕ) → (ζ a b : L) → Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ) → UpperTheory.Reformulated.B.JumpSetsAlt.HGrp e :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (e : ℕ) (ζ a b : L) (σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ)) ↦
      if h :
          ∃ (u : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ),
            (↑((σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) (UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b)) : L) =
              ζ ^ (↑u : ZMod ((2 : ℕ) ^ (e + (2 : ℕ)))).val + ζ⁻¹ ^ (↑u : ZMod ((2 : ℕ) ^ (e + (2 : ℕ)))).val then
        UpperTheory.Reformulated.B.JumpSetsAlt.hcl e (Classical.choose h)
      else (1 : UpperTheory.Reformulated.B.JumpSetsAlt.HGrp e)
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.galE.{u_1} :
    {L : Type u_1} →
      [inst : Field L] →
        [inst_1 : Algebra ℚ L] → (e : ℕ) → (ζ a b : L) → Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ) → UpperTheory.Reformulated.B.JumpSetsAlt.GG e :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (e : ℕ) (ζ a b : L) (σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ)) ↦
      ((UpperTheory.Reformulated.B.JumpSetsAlt.sgn σ (UpperTheory.Reformulated.B.JumpSetsAlt.aE ζ a b), UpperTheory.Reformulated.B.JumpSetsAlt.sgn σ (UpperTheory.Reformulated.B.JumpSetsAlt.bE ζ a b)),
        UpperTheory.Reformulated.B.JumpSetsAlt.hPart e ζ a b σ)
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.HostGalois :
    Prop :=
    ∀ (e q d : ℕ),
      UpperTheory.Reformulated.B.JumpSetsAlt.HypOdd q d →
        ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L),
          UpperTheory.Reformulated.B.JumpSetsAlt.IsLayer (e + (2 : ℕ)) q d ζ a b →
            IsGalois ℚ ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) ∧
              Module.finrank ℚ ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) = (2 : ℕ) ^ (e + (2 : ℕ)) ∧
                (∀ (σ τ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ)),
                    UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b (σ * τ) =
                      UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ * UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b τ) ∧
                  Function.Bijective (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b)
@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.GalL :
    ℕ → Type :=
    fun (n : ℕ) ↦ (ZMod ((2 : ℕ) ^ n))ˣ × ℤˣ × ℤˣ
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.galMap.{u_1} :
    {n : ℕ} →
      {L : Type u_1} →
        [inst : Field L] →
          [inst_1 : Algebra ℚ L] → {ζ : L} → IsPrimitiveRoot ζ ((2 : ℕ) ^ n) → L → L → Gal(L/ℚ) → UpperTheory.Reformulated.B.JumpSetsAlt.GalL n :=
    fun {n : ℕ} {L : Type u_1} [Field L] [Algebra ℚ L] {ζ : L} (hζ : IsPrimitiveRoot ζ ((2 : ℕ) ^ n)) (a b : L)
        (σ : Gal(L/ℚ)) ↦
      ((IsPrimitiveRoot.autToPow ℚ hζ : Gal(L/ℚ) → (ZMod ((2 : ℕ) ^ n))ˣ) σ, UpperTheory.Reformulated.B.JumpSetsAlt.sgn σ a,
        UpperTheory.Reformulated.B.JumpSetsAlt.sgn σ b)
theorem UpperTheory.Reformulated.B.JumpSetsAlt.glEmbMat_one_eq_one :
    ∀ (e q d : ℕ) (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L),
      UpperTheory.Reformulated.B.JumpSetsAlt.IsLayer (e + (2 : ℕ)) q d ζ a b → IsPrimitiveRoot ζ ((2 : ℕ) ^ (e + (2 : ℕ))) := by
  intro e q d L _ _ ζ a b h
  exact h.1
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.HostGalSpec :
    Prop :=
    ∀ (e q d : ℕ),
      UpperTheory.Reformulated.B.JumpSetsAlt.HypOdd q d →
        ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L)
          (h : UpperTheory.Reformulated.B.JumpSetsAlt.IsLayer (e + (2 : ℕ)) q d ζ a b) (σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ)),
          (↑((σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) (UpperTheory.Reformulated.B.JumpSetsAlt.aE ζ a b)) : L) =
              (↑(↑(UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.1 : ℤ) : L) * a ∧
            (↑((σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) (UpperTheory.Reformulated.B.JumpSetsAlt.bE ζ a b)) : L) =
                (↑(↑(UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).1.2 : ℤ) : L) * b ∧
              (∀ (u : (ZMod ((2 : ℕ) ^ (e + (2 : ℕ))))ˣ),
                  (UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ).2 = UpperTheory.Reformulated.B.JumpSetsAlt.hcl e u ↔
                    (↑((σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) (UpperTheory.Reformulated.B.JumpSetsAlt.thE ζ a b)) :
                        L) =
                      ζ ^ (↑u : ZMod ((2 : ℕ) ^ (e + (2 : ℕ)))).val + ζ⁻¹ ^ (↑u : ZMod ((2 : ℕ) ^ (e + (2 : ℕ)))).val) ∧
                ∀ (τ : Gal(L/ℚ)),
                  (∀ (x : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)),
                      (↑((σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) x) : L) =
                        (τ : L → L) (↑x : L)) →
                    UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ =
                      (((UpperTheory.Reformulated.B.JumpSetsAlt.galMap (UpperTheory.Reformulated.B.JumpSetsAlt.glEmbMat_one_eq_one e q d L ζ a b h) a b τ).2.1,
                          (UpperTheory.Reformulated.B.JumpSetsAlt.galMap (UpperTheory.Reformulated.B.JumpSetsAlt.glEmbMat_one_eq_one e q d L ζ a b h) a b τ).2.2),
                        UpperTheory.Reformulated.B.JumpSetsAlt.hcl e (UpperTheory.Reformulated.B.JumpSetsAlt.galMap (UpperTheory.Reformulated.B.JumpSetsAlt.glEmbMat_one_eq_one e q d L ζ a b h) a b τ).1)
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.c0 :
    UpperTheory.Reformulated.B.JumpSetsAlt.G0 :=
    ((-1 : ℤˣ), (-1 : ℤˣ))
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.cc :
    (e : ℕ) → UpperTheory.Reformulated.B.JumpSetsAlt.GG e :=
    fun (e : ℕ) ↦ (UpperTheory.Reformulated.B.JumpSetsAlt.c0, (1 : UpperTheory.Reformulated.B.JumpSetsAlt.HGrp e))
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.HostConj :
    Prop :=
    ∀ (e q d : ℕ),
      UpperTheory.Reformulated.B.JumpSetsAlt.HypOdd q d →
        ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L),
          UpperTheory.Reformulated.B.JumpSetsAlt.IsLayer (e + (2 : ℕ)) q d ζ a b →
            NumberField.IsCMField ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) ∧
              ∀ (φ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) →+* ℂ) (σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ)),
                (∀ (x : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)),
                    (φ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ℂ)
                        ((σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) x) =
                      (starRingEnd ℂ : ℂ → ℂ) ((φ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ℂ) x)) ↔
                  UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ = UpperTheory.Reformulated.B.JumpSetsAlt.cc e
@[reducible] noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.hostF.{u_1} :
    {L : Type u_1} → [inst : Field L] → [inst_1 : Algebra ℚ L] → (ζ a b : L) → Subfield ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) :=
    fun {L : Type u_1} [Field L] [Algebra ℚ L] (ζ a b : L) ↦ NumberField.maximalRealSubfield ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)
noncomputable def UpperTheory.Reformulated.B.JumpSetsAlt.HostReal :
    Prop :=
    ∀ (e q d : ℕ),
      UpperTheory.Reformulated.B.JumpSetsAlt.HypOdd q d →
        ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] (ζ a b : L),
          UpperTheory.Reformulated.B.JumpSetsAlt.IsLayer (e + (2 : ℕ)) q d ζ a b →
            Module.finrank ℚ ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostF ζ a b) = (2 : ℕ) ^ (e + (1 : ℕ)) ∧
              ∀ (x : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)),
                (x ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostF ζ a b ↔
                    ∀ (σ : Gal(↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)/ℚ)),
                      UpperTheory.Reformulated.B.JumpSetsAlt.galE e ζ a b σ = UpperTheory.Reformulated.B.JumpSetsAlt.cc e →
                        (σ : ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b) → ↥(UpperTheory.Reformulated.B.JumpSetsAlt.hostE ζ a b)) x = x) ∧
                  (x ∈ UpperTheory.Reformulated.B.JumpSetsAlt.hostF ζ a b ↔ (↑x : L) ∈ ℚ⟮a * b, ζ + ζ⁻¹⟯)


