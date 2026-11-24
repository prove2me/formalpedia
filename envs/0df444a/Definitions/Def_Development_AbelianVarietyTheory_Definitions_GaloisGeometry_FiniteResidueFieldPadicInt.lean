-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt
-- name    : Development_AbelianVarietyTheory_Definitions_GaloisGeometry_FiniteResidueFieldPadicInt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:03.489307+00:00
-- url     : https://prove2.me/theorems/b0127c4d-051d-42a2-b49f-96ba5d3a3882
-- title:
--   Finite Residue Field Padic Int
-- statement:
--   Definitions and structural lemmas for Finite Residue Field Padic Int, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GaloisGeometry/FiniteResidueFieldPadicInt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LatHecke
open scoped TensorProduct
variable (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
def Lat (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (r : ℕ) : Type :=
  {L : Submodule O (Fin r → K) // L.IsLattice K}
def qRes [Finite (IsLocalRing.ResidueField O)] : ℕ := Nat.card (IsLocalRing.ResidueField O)
variable [IsFractionRing O K] (r : ℕ)
def std : Lat O K r :=
  ⟨Submodule.span O (Set.range (Pi.basisFun K (Fin r))),
    { fg := Submodule.fg_span (Set.finite_range _)
      span_eq_top := by
        rw [Submodule.span_span_of_tower]; exact (Pi.basisFun K (Fin r)).span_eq }⟩
instance instInhabitedLat : Inhabited (Lat O K r) := ⟨std O K r⟩
variable {O K r}
@[ext] theorem Lat.ext {L M : Lat O K r} (h : L.1 = M.1) : L = M := Subtype.ext h
def glMap (g : GL (Fin r) K) (L : Submodule O (Fin r → K)) : Submodule O (Fin r → K) :=
  L.map ((Matrix.toLin' (g : Matrix (Fin r) (Fin r) K)).restrictScalars O)
omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in

theorem glMap_one (L : Submodule O (Fin r → K)) : glMap 1 L = L := by
  ext x; simp [glMap]
omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in

theorem glMap_mul (g h : GL (Fin r) K) (L : Submodule O (Fin r → K)) :
    glMap (g * h) L = glMap g (glMap h L) := by
  simp only [glMap, ← Submodule.map_comp, Units.val_mul, Matrix.toLin'_mul]
  rfl
theorem glMap_isLattice (g : GL (Fin r) K) (L : Lat O K r) : (glMap g L.1).IsLattice K where
  fg := L.2.fg.map _
  span_eq_top := by
    have : (glMap g L.1 : Set (Fin r → K))
        = Matrix.toLin' (g : Matrix (Fin r) (Fin r) K) '' (L.1 : Set (Fin r → K)) := rfl
    rw [this, Submodule.span_image, L.2.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    intro y
    refine ⟨Matrix.toLin' ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) y, ?_⟩
    simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
def glLat (g : GL (Fin r) K) (L : Lat O K r) : Lat O K r := ⟨glMap g L.1, glMap_isLattice g L⟩
@[simp] theorem glLat_val (g : GL (Fin r) K) (L : Lat O K r) : (glLat g L).1 = glMap g L.1 := rfl
instance instMulActionLat : MulAction (GL (Fin r) K) (Lat O K r) where
  smul := glLat
  one_smul L := Lat.ext (glMap_one L.1)
  mul_smul g h L := Lat.ext (glMap_mul g h L.1)
def maxMul (L : Lat O K r) : Lat O K r :=
  ⟨IsLocalRing.maximalIdeal O • L.1,
    { fg := Submodule.FG.smul (IsNoetherian.noetherian _) L.2.fg
      span_eq_top := by
        obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
        have h0 : algebraMap O K ϖ ≠ 0 := by
          simpa using hϖ.ne_zero
        have hm : ϖ ∈ IsLocalRing.maximalIdeal O := hϖ.not_isUnit
        rw [eq_top_iff, ← L.2.span_eq_top, Submodule.span_le]
        intro x hx
        have : x = (algebraMap O K ϖ)⁻¹ • (ϖ • x) := by
          rw [← algebraMap_smul K ϖ x, smul_smul, inv_mul_cancel₀ h0, one_smul]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.smul_mem_smul hm hx)) }⟩
@[simp] theorem maxMul_val (L : Lat O K r) :
    (maxMul L).1 = IsLocalRing.maximalIdeal O • L.1 := rfl
theorem pow_smul_eq_bot {Q : Type} [AddCommGroup Q] [Module O Q] [Finite Q] (N : ℕ) :
    ∀ S : Submodule O Q, Nat.card S ≤ N + 1 → IsLocalRing.maximalIdeal O ^ N • S = ⊥ := by
  induction N with
  | zero =>
    intro S hS
    have : Subsingleton S := Finite.card_le_one_iff_subsingleton.1 (by simpa using hS)
    have hb : S = ⊥ := (Submodule.eq_bot_iff _).2 fun x hx =>
      congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : S) 0)
    simp [hb]
  | succ N ih =>
    intro S hS
    by_cases hb : S = ⊥
    · simp [hb]
    have hne : IsLocalRing.maximalIdeal O • S ≠ S := by
      intro h
      refine hb (Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O) S
        (IsNoetherian.noetherian S) h.ge ?_)
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    have hlt : ((IsLocalRing.maximalIdeal O • S : Submodule O Q) : Set Q) ⊂ (S : Set Q) :=
      ⟨Submodule.smul_le_right, fun h => hne (le_antisymm Submodule.smul_le_right h)⟩
    have hc := Set.Finite.card_lt_card (Set.toFinite _) hlt
    rw [pow_succ, Submodule.mul_smul]
    exact ih _ (by
      have : Nat.card (IsLocalRing.maximalIdeal O • S : Submodule O Q) < Nat.card S := hc
      omega)
variable [Finite (IsLocalRing.ResidueField O)]
theorem one_lt_qRes : 1 < qRes O := Finite.one_lt_card
theorem two_le_qRes : 2 ≤ qRes O := one_lt_qRes
def subIdx (n : ℕ) (L : Lat O K r) : Set (Lat O K r) :=
  {M | M.1 ≤ L.1 ∧ M.1.toAddSubgroup.relIndex L.1.toAddSubgroup = qRes O ^ n}
def subElem (k : ℕ) (L : Lat O K r) : Set (Lat O K r) :=
  {M | M ∈ subIdx k L ∧ IsLocalRing.maximalIdeal O • L.1 ≤ M.1}
theorem subIdx_finite (n : ℕ) (L : Lat O K r) :
    (subIdx n L).Finite := by
  haveI := L.2
  have hq : qRes O ^ n ≠ 0 := (pow_pos (lt_of_lt_of_le two_pos two_le_qRes) _).ne'
  set I := IsLocalRing.maximalIdeal O ^ (qRes O ^ n)
  haveI : Finite (O ⧸ IsLocalRing.maximalIdeal O) := ‹Finite (IsLocalRing.ResidueField O)›
  haveI : Finite (O ⧸ I) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) _
  set N : Submodule O L.1 := I • ⊤
  haveI hfin : Finite (L.1 ⧸ N) := Submodule.finite_quotient_smul I Module.Finite.fg_top
  haveI : Finite (Submodule O (L.1 ⧸ N)) :=
    Finite.of_injective (fun S : Submodule O (L.1 ⧸ N) => (S : Set (L.1 ⧸ N))) SetLike.coe_injective
  have key : ∀ M ∈ subIdx n L, N ≤ M.1.comap L.1.subtype := by
    rintro M ⟨-, h2⟩
    have h1 : Nat.card (L.1 ⧸ M.1.comap L.1.subtype) = qRes O ^ n := h2
    haveI : Finite (L.1 ⧸ M.1.comap L.1.subtype) := Nat.finite_of_card_ne_zero (h1 ▸ hq)
    have h3 := pow_smul_eq_bot (O := O) (qRes O ^ n) (⊤ : Submodule O (L.1 ⧸ M.1.comap L.1.subtype))
      (by rw [Nat.card_congr Submodule.topEquiv.toEquiv, h1]; omega)
    rw [← Submodule.ker_mkQ (M.1.comap L.1.subtype), ← Submodule.comap_bot,
      ← Submodule.map_le_iff_le_comap, Submodule.map_smul'', Submodule.map_top,
      Submodule.range_mkQ]
    exact h3.le
  refine Set.Finite.of_finite_image (f := fun M : Lat O K r => (M.1.comap L.1.subtype).map N.mkQ)
    (Set.toFinite _) ?_
  rintro M hM M' hM' h
  have e := congrArg (Submodule.comap N.mkQ) h
  simp only [Submodule.comap_map_mkQ] at e
  rw [sup_eq_right.2 (key M hM), sup_eq_right.2 (key M' hM')] at e
  have e2 := congrArg (Submodule.map L.1.subtype) e
  rw [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hM.1,
    inf_eq_right.2 hM'.1] at e2
  exact Subtype.ext e2
theorem subElem_finite (k : ℕ) (L : Lat O K r) : (subElem k L).Finite :=
  (subIdx_finite k L).subset fun _ h => h.1
theorem relIndex_maxMul (L : Lat O K r) :
    (maxMul L).1.toAddSubgroup.relIndex L.1.toAddSubgroup = qRes O ^ r := by
  haveI := L.2
  haveI : Module.Free O L.1 := Submodule.IsLattice.free K L.1
  have hc : (IsLocalRing.maximalIdeal O • L.1).comap L.1.subtype
      = IsLocalRing.maximalIdeal O • (⊤ : Submodule O L.1) := by
    apply Submodule.map_injective_of_injective L.1.injective_subtype
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype,
      Submodule.map_comap_subtype, inf_eq_right.2 Submodule.smul_le_right]
  have h1 : (maxMul L).1.toAddSubgroup.relIndex L.1.toAddSubgroup
      = Nat.card (L.1 ⧸ (IsLocalRing.maximalIdeal O • L.1).comap L.1.subtype) := rfl
  rw [h1, hc, ← Nat.card_congr
    (TensorProduct.quotTensorEquivQuotSMul L.1 (IsLocalRing.maximalIdeal O)).toEquiv]
  change Nat.card (IsLocalRing.ResidueField O ⊗[O] L.1) = _
  rw [Module.natCard_eq_pow_finrank (K := IsLocalRing.ResidueField O), Module.finrank_baseChange,
    Submodule.IsLattice.finrank_of_pi K L.1, Fintype.card_fin]
  rfl
theorem subElem_top (L : Lat O K r) :
    subElem r L = {maxMul L} := by
  ext M
  simp only [subElem, subIdx, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have h := AddSubgroup.relIndex_mul_relIndex (maxMul L).1.toAddSubgroup M.1.toAddSubgroup
      L.1.toAddSubgroup h3 h1
    rw [h2, relIndex_maxMul] at h
    have hq : 0 < qRes O ^ r := pow_pos (lt_of_lt_of_le two_pos two_le_qRes) _
    have h4 : (maxMul L).1.toAddSubgroup.relIndex M.1.toAddSubgroup = 1 :=
      Nat.eq_of_mul_eq_mul_right hq (by rw [h, one_mul])
    exact Subtype.ext (le_antisymm (AddSubgroup.relIndex_eq_one.1 h4) h3)
  · rintro rfl
    exact ⟨⟨Submodule.smul_le_right, relIndex_maxMul L⟩, le_rfl⟩
theorem maxMul_ne (hr : 0 < r) (L : Lat O K r) : maxMul L ≠ L := by
  intro h
  have h1 := relIndex_maxMul L
  rw [h, AddSubgroup.relIndex_self] at h1
  have := Nat.one_lt_pow hr.ne' (two_le_qRes (O := O))
  omega
variable {E : Type} [AddCommMonoid E]
def heckeAll (n : ℕ) (φ : Lat O K r → E) (L : Lat O K r) : E := ∑ᶠ M ∈ subIdx n L, φ M
def heckeElem (k : ℕ) (φ : Lat O K r → E) (L : Lat O K r) : E := ∑ᶠ M ∈ subElem k L, φ M
theorem heckeElem_top (φ : Lat O K r → E) (L : Lat O K r) : heckeElem r φ L = φ (maxMul L) := by
  simp [heckeElem, subElem_top]
theorem finite_residueField_padicInt (p : ℕ) [Fact p.Prime] :
    Finite (IsLocalRing.ResidueField ℤ_[p]) :=
  Finite.of_equiv _ (PadicInt.residueField (p := p)).toEquiv.symm
theorem qRes_padicInt (p : ℕ) [Fact p.Prime] [Finite (IsLocalRing.ResidueField ℤ_[p])] :
    qRes ℤ_[p] = p := by
  unfold qRes
  rw [Nat.card_congr (PadicInt.residueField (p := p)).toEquiv, Nat.card_zmod]
example : haveI := finite_residueField_padicInt 2
    (heckeElem 2 : (Lat ℤ_[2] ℚ_[2] 2 → ℕ) → Lat ℤ_[2] ℚ_[2] 2 → ℕ) ≠ id := by
  classical
  haveI := finite_residueField_padicInt 2
  intro h
  have h1 := congrFun (congrFun h fun M => if M = std ℤ_[2] ℚ_[2] 2 then 1 else 0) (std ℤ_[2] ℚ_[2] 2)
  rw [heckeElem_top] at h1
  simp [maxMul_ne] at h1
example : haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    (maxMul (std ℤ_[3] ℚ_[3] 2)).1.toAddSubgroup.relIndex (std ℤ_[3] ℚ_[3] 2).1.toAddSubgroup = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_residueField_padicInt 3
  rw [relIndex_maxMul, qRes_padicInt]; rfl
end GlobalTheory.LatHecke


