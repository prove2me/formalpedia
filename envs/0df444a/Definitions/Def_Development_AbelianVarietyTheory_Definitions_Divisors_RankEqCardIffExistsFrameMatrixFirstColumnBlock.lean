-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:57.15102+00:00
-- url     : https://prove2.me/theorems/faa73310-bfdb-4416-83a1-813b948a4455
-- title:
--   Rank Eq Card Iff Exists Frame Matrix First Column Block
-- statement:
--   Definitions and structural lemmas for Rank Eq Card Iff Exists Frame Matrix First Column Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_one
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
namespace GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def apow (x : kˣ) (z : ℂ) : ℂ := ((nabs k x : ℝ) : ℂ) ^ z
theorem apow_mul (x y : kˣ) (z : ℂ) : apow (x * y) z = apow x z * apow y z := by
  simp only [apow, nabs_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (nabs_pos x).le (nabs_pos y).le z
@[simp] theorem apow_one (z : ℂ) : apow (1 : kˣ) z = 1 := by simp [apow, nabs_one]
@[simp] theorem apow_zero (x : kˣ) : apow x 0 = 1 := by simp [apow]
def IsUnif (ϖ : kˣ) : Prop := valuation k (ϖ : k) = uniformizer k
def unitCong (c : kˣ) : Subgroup kˣ where
  carrier := {x | valuation k (x : k) = 1 ∧ valuation k ((x : k) - 1) ≤ valuation k (c : k)}
  one_mem' := by simp
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨by simp [hx, hy], ?_⟩
    rw [show ((x * y : kˣ) : k) - 1 = x * (y - 1) + (x - 1) by push_cast; ring]
    exact Valuation.map_add_le _ (by rwa [map_mul, hx, one_mul]) hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨by simp [hx], ?_⟩
    rw [show ((x⁻¹ : kˣ) : k) - 1 = -((x : k)⁻¹ * (x - 1)) by simp [mul_sub]]
    rwa [Valuation.map_neg, map_mul, map_inv₀, hx, inv_one, one_mul]
def CondLE (ϖ : kˣ) (e : ℕ) (χ : kˣ →* ℂˣ) : Prop := ∀ x ∈ unitCong (ϖ ^ e), χ x = 1
structure IsRightTranslationIsometric (ϖ : kˣ) (ψ : AddChar k Circle) (α β : kˣ →* ℂˣ) (e : ℕ) : Prop where
  unif : IsUnif ϖ
  cond : HasConductor ψ 1
  ram : ¬ IsUnram (α / β)
  unitary : ∀ x, ‖((α / β) x : ℂ)‖ = 1
  one_le : 1 ≤ e
  condα : CondLE ϖ e α
  condβ : CondLE ϖ e β
structure IsCoeffRing (ϖ : kˣ) (ψ : AddChar k Circle) (α β : kˣ →* ℂˣ) (e : ℕ) (R : Subring ℂ) : Prop where
  inv_card : ((resCard k : ℂ))⁻¹ ∈ R
  psi : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → (ψ x : ℂ) ∈ R
  units : ∀ x : kˣ, valuation k (x : k) = 1 → (α x : ℂ) ∈ R ∧ (β x : ℂ) ∈ R ∧ ((α / β) x : ℂ) ∈ R
  unif : ((α / β) ϖ : ℂ) ∈ R ∧ ((α / β) ϖ⁻¹ : ℂ) ∈ R
example (ϖ : kˣ) (ψ : AddChar k Circle) (α β : kˣ →* ℂˣ) (e : ℕ) : IsCoeffRing ϖ ψ α β e ⊤ :=
  ⟨trivial, fun _ _ => trivial, fun _ _ => ⟨trivial, trivial, trivial⟩, trivial, trivial⟩
theorem IsUnif.mem {ϖ : kˣ} (hϖ : IsUnif ϖ) : (ϖ : k) ∈ 𝒪[k] :=
  show valuation k (ϖ : k) ≤ 1 from hϖ ▸ uniformizer_lt_one.le
section Models
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

abbrev gdet (g : GL D k) : kˣ := Matrix.GeneralLinearGroup.det g
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def invT : GL D k →* GL D k where
  toFun h := ⟨(h⁻¹).valᵀ, h.valᵀ, by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp [Matrix.mul_inv_rev])
section
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
@[simp] theorem invT_invT (h : GL D k) : invT (invT h) = h := Units.ext rfl
end
def omA (ν β : kˣ →* ℂˣ) (g : GL A k) (h : GL D k) (Φ : Matrix A D k → ℂ) : Matrix A D k → ℂ := fun X =>
  (((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * β (gdet h) * apow (gdet g) (-(Fintype.card D : ℂ) / 2) *
    apow (gdet h) (-(Fintype.card A : ℂ) / 2) * Φ ((g⁻¹).val * X * (invT h).val)
def omB (ν α : kˣ →* ℂˣ) (g : GL A' k) (h : GL D k) (Ψ : Matrix A' D k → ℂ) : Matrix A' D k → ℂ := fun Y =>
  (ν (gdet g) : ℂ) * α (gdet h) * apow (gdet g) ((Fintype.card D : ℂ) / 2) *
    apow (gdet h) ((Fintype.card A' : ℂ) / 2) * Ψ (g.valᵀ * Y * h.val)
def repA (ν β : kˣ →* ℂˣ) : Representation ℂ (GL A k × GL D k) (Matrix A D k → ℂ) where
  toFun x :=
    { toFun := omA ν β x.1 x.2
      map_add' := fun Φ Φ' => by funext X; simp [omA, mul_add]
      map_smul' := fun c Φ => by funext X; simp only [omA, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_one' := by ext Φ X; simp [omA]
  map_mul' x y := by
    ext Φ X
    simp only [omA, Prod.fst_mul, Prod.snd_mul, map_mul, apow_mul, _root_.mul_inv_rev, Units.val_mul,
      Matrix.mul_assoc, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    ring
def repB (ν α : kˣ →* ℂˣ) : Representation ℂ (GL A' k × GL D k) (Matrix A' D k → ℂ) where
  toFun x :=
    { toFun := omB ν α x.1 x.2
      map_add' := fun Φ Φ' => by funext X; simp [omB, mul_add]
      map_smul' := fun c Φ => by funext X; simp only [omB, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  map_one' := by ext Φ X; simp [omB]
  map_mul' x y := by
    ext Φ X
    simp only [omB, Prod.fst_mul, Prod.snd_mul, map_mul, apow_mul, Units.val_mul, transpose_mul,
      Matrix.mul_assoc, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    ring
section
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (k) in

def X0 (σ : A ⊕ A' ≃ D) : Matrix A D k := Matrix.of fun i j => if σ (Sum.inl i) = j then 1 else 0
variable (k) in

def Y0 (σ : A ⊕ A' ≃ D) : Matrix A' D k := Matrix.of fun i j => if σ (Sum.inr i) = j then 1 else 0
def stdSplit {a a' d₁ d₂ : ℕ} (h : a + a' = d₁ + d₂) : Fin a ⊕ Fin a' ≃ Fin d₁ ⊕ Fin d₂ :=
  finSumFinEquiv.trans ((finCongr h).trans finSumFinEquiv.symm)
end
end Models
section Lattices
variable {A D : Type*}
variable (A) in

def matLat (Λ : Submodule 𝒪[k] (D → k)) : Submodule 𝒪[k] (Matrix A D k) where
  carrier := {X | ∀ i, X.row i ∈ Λ}
  add_mem' hX hY i := Λ.add_mem (hX i) (hY i)
  zero_mem' _ := Λ.zero_mem
  smul_mem' c _ hX i := Λ.smul_mem c (hX i)
def diagLat (c : D → kˣ) : Submodule 𝒪[k] (D → k) where
  carrier := {x | ∀ j, valuation k (x j) ≤ valuation k (c j : k)}
  add_mem' hx hy j := Valuation.map_add_le _ (hx j) (hy j)
  zero_mem' j := by simp
  smul_mem' r x hx j := by
    show valuation k ((r : k) * x j) ≤ _
    rw [map_mul]; exact (mul_le_of_le_one_left' r.2).trans (hx j)
variable (k D) in

def stdLat : Submodule 𝒪[k] (D → k) := diagLat 1
variable [Fintype D]
instance isLattice_diagLat (c : D → kˣ) : Submodule.IsLattice k (diagLat c) := by
  classical
  have hmem : ∀ j, (Pi.single j (c j : k) : D → k) ∈ diagLat c := fun j l => by
    by_cases h : l = j
    · subst h; simp
    · simp [h]
  have hx : ∀ x : D → k, x = ∑ j, (x j / c j) • (Pi.single j (c j : k) : D → k) := fun x => by
    funext l; simp [Finset.sum_apply, Pi.single_apply]
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_def.2 ⟨Set.range fun j => (Pi.single j (c j : k) : D → k), Set.finite_range _, le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hmem j)
    · intro x h
      rw [hx x]
      refine Submodule.sum_mem _ fun j _ => ?_
      have h0 : 0 < valuation k (c j : k) := zero_lt_iff.2 (by simp)
      have h1 : x j / c j ∈ 𝒪[k] := by
        rw [Valuation.mem_integer_iff, map_div₀]; exact (div_le_one₀ h0).2 (h j)
      exact Submodule.smul_mem _ (⟨_, h1⟩ : 𝒪[k]) (Submodule.subset_span ⟨j, rfl⟩)
  · rw [eq_top_iff]
    intro x _
    rw [hx x]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span (hmem j))
instance isLattice_stdLat : Submodule.IsLattice k (stdLat k D) := isLattice_diagLat 1
def dualLat (Λ : Submodule 𝒪[k] (D → k)) : Submodule 𝒪[k] (D → k) :=
  LinearMap.BilinForm.dualSubmodule (dotProductBilin k k) Λ
def IsPrimFrame [Fintype A] (Λ : Submodule 𝒪[k] (D → k)) (X : Matrix A D k) : Prop :=
  X.rank = Fintype.card A ∧ X ∈ matLat A Λ ∧
    Submodule.span 𝒪[k] (Set.range X.row) = (Submodule.span k (Set.range X.row)).restrictScalars 𝒪[k] ⊓ Λ
variable [DecidableEq D]
def glLat (Λ : Submodule 𝒪[k] (D → k)) : Subgroup (GL D k) where
  carrier := {h | ∀ x, x ᵥ* h.val ∈ Λ ↔ x ∈ Λ}
  one_mem' x := by simp
  mul_mem' {g h} hg hh x := by rw [Units.val_mul, ← vecMul_vecMul, hh, hg]
  inv_mem' {h} hh x := by rw [← hh, vecMul_vecMul, Units.inv_mul, vecMul_one]
def glLatCong (c : kˣ) (Λ : Submodule 𝒪[k] (D → k)) : Subgroup (GL D k) where
  carrier := {h | h ∈ glLat Λ ∧ ∀ x ∈ Λ, x ᵥ* (h.val - 1) ∈ c • Λ}
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨mul_mem hg hh, fun x hx => ?_⟩
    rw [show (g * h).val - 1 = g.val * (h.val - 1) + (g.val - 1) by simp [mul_sub], vecMul_add, ← vecMul_vecMul]
    exact add_mem (hh' _ ((hg x).2 hx)) (hg' x hx)
  inv_mem' := by
    rintro h ⟨hh, hh'⟩
    refine ⟨inv_mem hh, fun x hx => ?_⟩
    rw [show (h⁻¹).val - 1 = -((h⁻¹).val * (h.val - 1)) by rw [mul_sub, Units.inv_mul, mul_one, neg_sub],
      vecMul_neg, ← vecMul_vecMul]
    exact neg_mem (hh' _ (((glLat Λ).inv_mem hh x).2 hx))
omit [Fintype D] in

def blockUnits (ϖ : kˣ) (e : ℕ) (P : Finset D) : D → kˣ := fun j => if j ∈ P then (ϖ ^ e)⁻¹ else 1
omit [Fintype D] in

def blockLat (ϖ : kˣ) (e : ℕ) (P : Finset D) : Submodule 𝒪[k] (D → k) := diagLat (blockUnits ϖ e P)
def blockScale (ϖ : kˣ) (e : ℕ) (P : Finset D) : GL D k := diagGL (blockUnits ϖ e P)
instance isLattice_blockLat (ϖ : kˣ) (e : ℕ) (P : Finset D) : Submodule.IsLattice k (blockLat ϖ e P) :=
  isLattice_diagLat _
omit [DecidableEq D] in

def latA (ϖ : kˣ) (e : ℕ) (Λ' : Submodule 𝒪[k] (D → k)) : Submodule 𝒪[k] (D → k) := (ϖ ^ e)⁻¹ • dualLat Λ'
omit [Fintype D] [DecidableEq D]
def HasDepth (ϖ : kˣ) (e : ℕ) (Λ : Submodule 𝒪[k] (D → k)) (Φ : Matrix A D k → ℂ) : Prop :=
  (∀ X, X ∉ matLat A Λ → Φ X = 0) ∧ ∀ X, ∀ Z ∈ matLat A (ϖ ^ e • Λ), Φ (X + Z) = Φ X
variable (A) in

def depthSpace (ϖ : kˣ) (e : ℕ) (Λ : Submodule 𝒪[k] (D → k)) : Submodule ℂ (Matrix A D k → ℂ) where
  carrier := {Φ | HasDepth ϖ e Λ Φ}
  add_mem' h h' := ⟨fun X hX => by simp [h.1 X hX, h'.1 X hX], fun X Z hZ => by simp [h.2 X Z hZ, h'.2 X Z hZ]⟩
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  smul_mem' c _ h := ⟨fun X hX => by simp [h.1 X hX], fun X Z hZ => by simp [h.2 X Z hZ]⟩
def IsNatDatum (ϖ : kˣ) (e : ℕ) (Φ : Matrix A D k → ℂ) : Prop := HasDepth ϖ e (stdLat k D) Φ
end Lattices
section Fourier
variable {A D : Type*}
variable (k) in

abbrev Res (e : ℕ) : Type _ := 𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k] ^ e
instance finite_Res (e : ℕ) : Finite (Res k e) :=
  haveI : Finite (𝒪[k] ⧸ IsLocalRing.maximalIdeal 𝒪[k]) := inferInstanceAs (Finite 𝓀[k])
  Ideal.finite_quotient_pow (IsNoetherian.noetherian _) e
instance fintype_Res (e : ℕ) : Fintype (Res k e) := Fintype.ofFinite _
def liftRes {B : Type*} {e : ℕ} (T : A → B → Res k e) : Matrix A B k :=
  Matrix.of fun i j => ((Quotient.out (T i j) : 𝒪[k]) : k)
variable [DecidableEq D]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def setCols (P : Finset D) (Y : Matrix A D k) (T : Matrix A P k) : Matrix A D k :=
  Matrix.of fun i j => if h : j ∈ P then T i ⟨j, h⟩ else Y i j
variable [Fintype A]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq D] in

def pairCols (P : Finset D) (Y : Matrix A D k) (T : Matrix A P k) : k := ∑ i, ∑ j : P, T i j * Y i j
def fourierInt [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (m : Measure k) (P : Finset D)
    (Φ : Matrix A D k → ℂ) (Y : Matrix A D k) : ℂ :=
  ∫ T : Matrix A P k, Φ (setCols P Y T) * (ψ (pairCols P Y T) : ℂ) ∂(volM m A P)
variable [DecidableEq A]
open Classical in

def fourierSum (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) :
    (Matrix A D k → ℂ) →ₗ[ℂ] (Matrix A D k → ℂ) where
  toFun Φ Y := if ∀ i, ∀ j ∈ P, ((ϖ ^ e : kˣ) : k) * Y i j ∈ 𝒪[k] then
    ((resCard k : ℂ) ^ (e * Fintype.card A * P.card))⁻¹ *
      ∑ T : A → P → Res k e, Φ (setCols P Y (liftRes T)) * (ψ (pairCols P Y (liftRes T)) : ℂ) else 0
  map_add' Φ Φ' := by
    funext Y; simp only [Pi.add_apply]; split_ifs <;> simp [add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' c Φ := by
    funext Y; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · simp only [mul_assoc, ← Finset.mul_sum]; ring
    · simp
open Classical in

def invFourierSum (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (P : Finset D) :
    (Matrix A D k → ℂ) →ₗ[ℂ] (Matrix A D k → ℂ) where
  toFun Ψ T := if ∀ i, ∀ j ∈ P, T i j ∈ 𝒪[k] then
    ∑ S : A → P → Res k e, Ψ (setCols P T ((ϖ ^ e)⁻¹ • liftRes S)) *
      (ψ (-pairCols P T ((ϖ ^ e)⁻¹ • liftRes S)) : ℂ) else 0
  map_add' Φ Φ' := by
    funext Y; simp only [Pi.add_apply]; split_ifs <;> simp [add_mul, Finset.sum_add_distrib]
  map_smul' c Φ := by
    funext Y; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · simp only [mul_assoc, ← Finset.mul_sum]
    · simp
end Fourier
section Maps
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
def shellSet (ϖ : kˣ) (n : A → ℤ) : Set (GL A k) :=
  DoubleCoset.doubleCoset (diagGL fun i => ϖ ^ n i) (KO k A) (KO k A)
def boxSet (ϖ : kˣ) (e : ℕ) : Set (GL A k) :=
  {g | ∃ n : A → ℤ, (∀ i, 0 ≤ n i ∧ n i < e) ∧ g ∈ shellSet ϖ n}
variable [MeasurableSpace k] [BorelSpace k]
def shell (μ : Measure (GL A k)) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (z : ℂ) (φ : Matrix A A k → ℂ) (n : A → ℤ) : ℂ :=
  ∫ g in shellSet ϖ n, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂μ
def shellSum {a : ℕ} (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (z : ℂ)
    (φ : Matrix (Fin a) (Fin a) k → ℂ) : ℂ :=
  ∑ᶠ n : {n : Fin a → ℤ // Antitone n}, shell μ ϖ ν z φ n.1
def bigF {a : ℕ} (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (Φ : Matrix (Fin a) D k → ℂ)
    (X : Matrix (Fin a) D k) : ℂ :=
  shellSum μ ϖ ν ((Fintype.card D : ℂ) / 2) fun g => Φ (g * X)
def smallF (μ : Measure (GL A' k)) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (Y : Matrix A' D k) : ℂ :=
  ∫ g, Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card D : ℂ) / 2) ∂μ
def bigP {a : ℕ} (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (σ : Fin a ⊕ A' ≃ D) (ν β : kˣ →* ℂˣ)
    (Φ : Matrix (Fin a) D k → ℂ) (h : GL D k) : ℂ :=
  bigF μ ϖ ν (omA ν β 1 h Φ) (X0 k σ)
def smallP (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ D) (ν α : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (h : GL D k) : ℂ :=
  (α (gdet h) : ℂ) * apow (gdet h) ((Fintype.card A' : ℂ) / 2) * smallF μ ν Ψ (Y0 k σ * h.val)
open Classical in

def fFun (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (X : Matrix A D k) : ℂ :=
  if hX : ∃ h : GL D k, X = X0 k σ * (invT h).val then
    (ν (gdet hX.choose) : ℂ) * apow (gdet hX.choose) ((Fintype.card D : ℂ) / 2) *
      smallF μ ν Ψ (Y0 k σ * hX.choose.val) else 0
open Classical in

def phiA (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ D) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ) (Λ' : Submodule 𝒪[k] (D → k))
    (Ψ : Matrix A' D k → ℂ) (X : Matrix A D k) : ℂ :=
  if IsPrimFrame (latA ϖ e Λ') X then fFun μ σ ν Ψ X else 0
def squareFlip (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ D) (ψ : AddChar k Circle) (ν : kˣ →* ℂˣ) (ϖ : kˣ) (e : ℕ)
    (P : Finset D) (ΦB : Matrix A' D k → ℂ) : Matrix A D k → ℂ :=
  invFourierSum ψ⁻¹ ϖ e Pᶜ (phiA μ σ ν ϖ e (blockLat ϖ e P) (fourierSum ψ ϖ e P ΦB))
end Maps
inductive Assignment
  | one
  | two
  deriving DecidableEq
def Assignment.block (s : Assignment) (D₁ D₂ : Type*) [Fintype D₁] [Fintype D₂] : Finset (D₁ ⊕ D₂) :=
  match s with
  | .one => Finset.univ.filter fun j => j.isLeft
  | .two => Finset.univ.filter fun j => j.isRight
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def Assignment.read (s : Assignment) {n : Type*} [Fintype n] [DecidableEq n] : GL n k →* GL n k :=
  match s with
  | .one => invT
  | .two => MonoidHom.id _
section
variable {D₁ D₂ : Type*} [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
end
inductive Edge

  | theta (i j : ℕ)

  | ex (i j : ℕ)
  deriving DecidableEq
@[reducible] def Edge.src : Edge → ℕ × ℕ
  | .theta i j => (i, j + 1)
  | .ex i j => (i, j)
@[reducible] def Edge.tgt : Edge → ℕ × ℕ
  | .theta i j => (i, j)
  | .ex i j => (i + 1, j)
def Edge.InGrid (m : ℕ) : Edge → Prop
  | .theta i j => i ≤ m ∧ j < m
  | .ex i j => i < m ∧ j ≤ m
def IsPath (γ : List Edge) : Prop := γ.IsChain fun e e' => e.tgt = e'.src
def innerVertices (γ : List Edge) : List (ℕ × ℕ) := γ.tail.map Edge.src
def PassesThrough (i j : ℕ) (γ : List Edge) : Prop := [Edge.theta i j, Edge.ex i j] <:+: γ
def flipPath (i j : ℕ) (γ : List Edge) : List Edge :=
  γ.map fun e => if e = .theta i j then .ex i (j + 1) else if e = .ex i j then .theta (i + 1) j else e
inductive CanFlip : List Edge → List (ℕ × ℕ) → Prop
  | nil (γ : List Edge) : CanFlip γ []
  | cons {γ : List Edge} {x : ℕ × ℕ} {l : List (ℕ × ℕ)} :
      PassesThrough x.1 x.2 γ → CanFlip (flipPath x.1 x.2 γ) l → CanFlip γ (x :: l)
def givenPath (m : ℕ) : List Edge := (List.range m).reverse.map (Edge.theta 0) ++ (List.range m).map (Edge.ex · 0)
def oppositePath (m : ℕ) : List Edge :=
  (List.range m).map (Edge.ex · m) ++ (List.range m).reverse.map (Edge.theta m)
example : IsPath (givenPath 2) ∧ innerVertices (givenPath 2) = [(0, 1), (0, 0), (1, 0)] := by
  unfold IsPath; decide
example : CanFlip (givenPath 2) [(0, 0), (0, 1), (1, 0), (1, 1)] ∧
    [(0, 0), (0, 1), (1, 0), (1, 1)].foldl (fun γ x => flipPath x.1 x.2 γ) (givenPath 2) = oppositePath 2 := by
  refine ⟨.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil _)))), by decide⟩ <;> unfold PassesThrough <;> decide
variable (k) in

structure Grid where

  m : ℕ

  r : ℕ

  t : ℕ

  s : ℕ

  mu : ℕ → kˣ →* ℂˣ

  chi : ℕ → kˣ →* ℂˣ

  eta : kˣ →* ℂˣ
namespace Grid
variable (G : Grid k)
section
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def rank (X : ℕ × ℕ) : ℕ := G.r + X.2 * G.t + X.1 * G.s
theorem rank_square (i j : ℕ) : G.rank (i + 1, j + 1) + G.rank (i, j) = G.rank (i, j + 1) + G.rank (i + 1, j) := by
  simp only [rank]; ring
def blockChar : Edge → kˣ →* ℂˣ
  | .theta _ j => G.mu (j + 1)
  | .ex i _ => G.chi (G.m - i)
def kappa (e : Edge) (X : ℕ × ℕ) : kˣ →* ℂˣ := G.blockChar e / G.eta ^ ((G.rank X + 1) % 2)
def alpha (i j : ℕ) : kˣ →* ℂˣ := G.mu (j + 1) * G.eta ^ (G.rank (i, j) % 2)
def beta (i j : ℕ) : kˣ →* ℂˣ := G.chi (G.m - i) * G.eta ^ (G.rank (i, j) % 2)
def nu (i j : ℕ) : kˣ →* ℂˣ := G.mu (j + 1) / G.chi (G.m - i)
abbrev Args : Type _ := ∀ e : Edge, Matrix (Fin (G.rank e.tgt)) (Fin (G.rank e.src)) k
abbrev VertexGroup : Type _ := ∀ X : ℕ × ℕ, GL (Fin (G.rank X)) k
def moveArgs (s : Assignment) (g : G.VertexGroup) (x : G.Args) : G.Args := fun e =>
  ((s.read (g e.tgt))⁻¹).val * x e * (s.read (g e.src)).val
end
structure IsGood (ϖ : kˣ) (ψ : AddChar k Circle) (e : ℕ) : Prop where
  odd_splitThetaGridThetaRankIncrement : Odd G.t
  gridDataAtRealPlace_s_odd : Odd G.s
  eta : IsUnram G.eta
  square : ∀ i < G.m, ∀ j < G.m, IsRightTranslationIsometric ϖ ψ (G.alpha i j) (G.beta i j) e
def edgeFactor (s : Assignment) (g : G.VertexGroup) (e : Edge) : ℂ :=
  (G.kappa e e.src (gdet (g e.src)) : ℂ) * (((G.kappa e e.tgt (gdet (g e.tgt)))⁻¹ : ℂˣ) : ℂ) *
    apow (gdet (s.read (g e.src))) ((G.rank e.tgt : ℂ) / 2) * apow (gdet (s.read (g e.tgt))) (-(G.rank e.src : ℂ) / 2)
def pathAct (s : Assignment) (γ : List Edge) (g : G.VertexGroup) (T : G.Args → ℂ) : G.Args → ℂ := fun x =>
  (γ.map (G.edgeFactor s g)).prod * T (G.moveArgs s g x)
def IsTensor (ϖ : kˣ) (e : ℕ) (γ : List Edge) (T : G.Args → ℂ) : Prop :=
  DependsOn T {b | b ∈ γ} ∧ (∀ x : G.Args, ∀ b ∈ γ, x b ∉ matLat _ (stdLat k _) → T x = 0) ∧
    ∀ x z : G.Args, (∀ b, z b ∈ matLat _ (ϖ ^ e • stdLat k _)) → T (x + z) = T x
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

def lines₂ (γ : List Edge) (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ) :
    G.Args → ℂ := fun x => (γ.map fun b => φ b (x b)).prod
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

abbrev Level : Type _ := ∀ X : ℕ × ℕ, Subgroup (GL (Fin (G.rank X)) k)
def IsLevel (γ : List Edge) (J : G.Level) : Prop :=
  ∀ X ∈ innerVertices γ, IsOpen (J X : Set (GL (Fin (G.rank X)) k)) ∧ J X ≤ KO k _
def IsAdmissible (s : Assignment) (γ : List Edge) (J : G.Level) (T : G.Args → ℂ) : Prop :=
  ∀ X ∈ innerVertices γ, ∀ u ∈ J X, G.pathAct s γ (Pi.mulSingle X u) T = T
section
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
abbrev Cols (i j : ℕ) : Type := Fin (G.rank (i, j + 1)) ⊕ Fin (G.rank (i + 1, j))
def sliceB (i j : ℕ) (T : G.Args → ℂ) (x : G.Args) (Z : Matrix (Fin (G.rank (i, j))) (G.Cols i j) k) : ℂ :=
  T (Function.update (Function.update x (.theta i j) Z.toCols₁) (.ex i j) Z.toCols₂ᵀ)
def joinA (i j : ℕ) (x : G.Args) : Matrix (Fin (G.rank (i + 1, j + 1))) (G.Cols i j) k :=
  fromCols (x (.ex i (j + 1))) (x (.theta (i + 1) j))ᵀ
end
def flipLevel (i j : ℕ) (J : G.Level) : G.Level := Function.update J (i + 1, j + 1) (KO k _)
variable [MeasurableSpace k] [BorelSpace k]
def flipTensor (s : Assignment) (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (i j : ℕ) (J : G.Level)
    (T : G.Args → ℂ) : G.Args → ℂ := fun x =>
  squareFlip (haarVol ((J (i, j)).map invT)) (stdSplit (G.rank_square i j)) ψ (G.nu i j) ϖ e
    (s.block _ _) (G.sliceB i j T x) (G.joinA i j x)
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in

structure PiLocalization₂ where

  path : List Edge

  level : G.Level

  tensor : G.Args → ℂ
variable {G}
omit [MeasurableSpace k] [BorelSpace k] in

structure PiLocalization₂.IsAdmissible (S : G.PiLocalization₂) (s : Assignment) (ϖ : kˣ) (e : ℕ) : Prop where
  path : IsPath S.path
  level : G.IsLevel S.path S.level
  tensor : G.IsTensor ϖ e S.path S.tensor
  invariant : G.IsAdmissible s S.path S.level S.tensor
def PiLocalization₂.flip (s : Assignment) (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (S : G.PiLocalization₂) (x : ℕ × ℕ) : G.PiLocalization₂ :=
  ⟨flipPath x.1 x.2 S.path, G.flipLevel x.1 x.2 S.level, G.flipTensor s ψ ϖ e x.1 x.2 S.level S.tensor⟩
def PiLocalization₂.flips (s : Assignment) (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ) (S : G.PiLocalization₂) (l : List (ℕ × ℕ)) :
    G.PiLocalization₂ := l.foldl (PiLocalization₂.flip s ψ ϖ e) S
end Grid
def detCong (c : kˣ) (n : Type*) [Fintype n] [DecidableEq n] : Subgroup (GL n k) :=
  KO k n ⊓ (unitCong c).comap Matrix.GeneralLinearGroup.det
end GlobalTheory.SplitFlip


