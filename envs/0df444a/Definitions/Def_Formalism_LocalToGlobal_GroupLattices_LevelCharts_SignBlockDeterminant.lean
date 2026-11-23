-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_SignBlockDeterminant
-- name    : Formalism_LocalToGlobal_GroupLattices_LevelCharts_SignBlockDeterminant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:33:32.07785+00:00
-- url     : https://prove2.me/theorems/160334e4-e039-4fb2-bc77-d04a9f0c81f4
-- title:
--   Sign Block Determinant
-- statement:
--   Definitions and structural lemmas for Sign Block Determinant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelCharts/SignBlockDeterminant.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
namespace Formalism.L2.G
def lvlX (a t x : ℕ) : ℕ := if x < a then x else a + (x - a) / t
theorem lvlX_of_lt {a t x : ℕ} (h : x < a) : lvlX a t x = x := if_pos h
theorem lvlX_ge {a t x : ℕ} (h : ¬ x < a) : a ≤ lvlX a t x := by
  simp only [lvlX, h, if_false]; exact Nat.le_add_right _ _
theorem lvlX_eq_iff {a t x y : ℕ} (h : x < a) : lvlX a t y = x ↔ y = x := by
  by_cases hy : y < a
  · rw [lvlX_of_lt hy]
  · have := lvlX_ge (t := t) hy
    constructor <;> intro h' <;> omega
theorem lvlX_lt_iff {a t x y : ℕ} (h : x < a) : lvlX a t y < x ↔ y < x := by
  by_cases hy : y < a
  · rw [lvlX_of_lt hy]
  · have := lvlX_ge (t := t) hy
    constructor <;> intro h' <;> omega
theorem lt_lvlX_iff {a t x y : ℕ} (h : x < a) : x < lvlX a t y ↔ x < y := by
  by_cases hy : y < a
  · rw [lvlX_of_lt hy]
  · have := lvlX_ge (t := t) hy
    constructor <;> intro h' <;> omega
abbrev lvF (N a t : ℕ) : Fin N → ℕ := fun x => lvlX a t x.val
section Bar
variable {κ : Type} [CommRing κ] {N : ℕ} {a t : ℕ}
theorem mul_apply_block {α : Type} [LinearOrder α] {b : Fin N → α} {M M' : Matrix (Fin N) (Fin N) κ}
    (hM : M.BlockTriangular b) (hM' : M'.BlockTriangular b) {x y : Fin N} (hxy : b x = b y) :
    (M * M') x y = ∑ z, if b z = b x then M x z * M' z y else 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : b z = b x
  · rw [if_pos hz]
  · rw [if_neg hz]
    rcases lt_or_gt_of_ne hz with h | h
    · rw [hM h, zero_mul]
    · rw [hM' (hxy ▸ h), mul_zero]
theorem toSquareBlock_mul {α : Type} [LinearOrder α] {b : Fin N → α} {M M' : Matrix (Fin N) (Fin N) κ}
    (hM : M.BlockTriangular b) (hM' : M'.BlockTriangular b) (c : α) :
    (M * M').toSquareBlock b c = M.toSquareBlock b c * M'.toSquareBlock b c := by
  ext ⟨x, hx⟩ ⟨y, hy⟩
  rw [Matrix.mul_apply]
  show (M * M') x y = ∑ z : {z // b z = c}, M x z.1 * M' z.1 y
  rw [mul_apply_block hM hM' (hx.trans hy.symm), hx, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun z => by simp) _
theorem mul_diag {M M' : Matrix (Fin N) (Fin N) κ} (hM : M.BlockTriangular (lvF N a t))
    (hM' : M'.BlockTriangular (lvF N a t)) {x : Fin N} (hx : x.val < a) : (M * M') x x = M x x * M' x x := by
  rw [mul_apply_block hM hM' rfl, Finset.sum_eq_single x]
  · rw [if_pos rfl]
  · intro z _ hz
    rw [if_neg]
    intro h
    apply hz
    have h1 : lvlX a t z.val = x.val := by
      have : lvlX a t z.val = lvlX a t x.val := h
      rwa [lvlX_of_lt hx] at this
    exact Fin.ext ((lvlX_eq_iff hx).1 h1)
  · intro h; exact absurd (Finset.mem_univ x) h
def JBar (κ : Type) [CommRing κ] (N a t : ℕ) (fixLast : Bool) (fc : ℕ) : Subgroup (GL (Fin N) κ) where
  carrier := {g | (g : Matrix (Fin N) (Fin N) κ).BlockTriangular (lvF N a t) ∧
    (∀ x : Fin N, x.val < a → (g : Matrix (Fin N) (Fin N) κ) x x = 1) ∧
    (fixLast = true → ∀ l y : Fin N, l.val + 1 = N →
      (g : Matrix (Fin N) (Fin N) κ) l y = (1 : Matrix (Fin N) (Fin N) κ) l y ∧
      (g : Matrix (Fin N) (Fin N) κ) y l = (1 : Matrix (Fin N) (Fin N) κ) y l) ∧
    (∀ x y : Fin N, y.val = fc → (g : Matrix (Fin N) (Fin N) κ) x y = (1 : Matrix (Fin N) (Fin N) κ) x y)}
  one_mem' := ⟨Matrix.blockTriangular_one, fun x _ => Matrix.one_apply_eq x, fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl⟩
  mul_mem' := by
    rintro g h ⟨g1, g2, g3, g4⟩ ⟨h1, h2, h3, h4⟩
    refine ⟨g1.mul h1, fun x hx => ?_, fun hf l y hl => ⟨?_, ?_⟩, fun x y hy => ?_⟩
    · rw [Units.val_mul, mul_diag g1 h1 hx, g2 x hx, h2 x hx, one_mul]
    · rw [Units.val_mul, Matrix.mul_apply]
      simp only [(g3 hf l _ hl).1]
      rw [← Matrix.mul_apply, Matrix.one_mul]
      exact (h3 hf l y hl).1
    · rw [Units.val_mul, Matrix.mul_apply]
      simp only [(h3 hf l _ hl).2]
      rw [← Matrix.mul_apply, Matrix.mul_one]
      exact (g3 hf l y hl).2
    · have e : ∀ z, (h : Matrix (Fin N) (Fin N) κ) z y = (1 : Matrix (Fin N) (Fin N) κ) z y := fun z => h4 z y hy
      rw [Units.val_mul, Matrix.mul_apply]
      simp only [e]
      rw [← Matrix.mul_apply, Matrix.mul_one]
      exact g4 x y hy
  inv_mem' := by
    rintro g ⟨g1, g2, g3, g4⟩
    have hi : ((g⁻¹ : GL (Fin N) κ) : Matrix (Fin N) (Fin N) κ).BlockTriangular (lvF N a t) := by
      rw [Matrix.coe_units_inv]
      have : Invertible (g : Matrix (Fin N) (Fin N) κ) := g.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular g1
    refine ⟨hi, fun x hx => ?_, fun hf l y hl => ⟨?_, ?_⟩, fun x y hy => ?_⟩
    · have h := mul_diag g1 hi hx
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq, g2 x hx, one_mul] at h
      exact h.symm
    · have h : ((g * g⁻¹ : GL (Fin N) κ) : Matrix (Fin N) (Fin N) κ) l y = (1 : Matrix (Fin N) (Fin N) κ) l y := by
        rw [mul_inv_cancel, Units.val_one]
      rw [Units.val_mul, Matrix.mul_apply] at h
      simp only [(g3 hf l _ hl).1] at h
      rwa [← Matrix.mul_apply, Matrix.one_mul] at h
    · have h : ((g⁻¹ * g : GL (Fin N) κ) : Matrix (Fin N) (Fin N) κ) y l = (1 : Matrix (Fin N) (Fin N) κ) y l := by
        rw [inv_mul_cancel, Units.val_one]
      rw [Units.val_mul, Matrix.mul_apply] at h
      simp only [(g3 hf l _ hl).2] at h
      rwa [← Matrix.mul_apply, Matrix.mul_one] at h
    · have h : ((g⁻¹ * g : GL (Fin N) κ) : Matrix (Fin N) (Fin N) κ) x y = (1 : Matrix (Fin N) (Fin N) κ) x y := by
        rw [inv_mul_cancel, Units.val_one]
      have e : ∀ z, (g : Matrix (Fin N) (Fin N) κ) z y = (1 : Matrix (Fin N) (Fin N) κ) z y := fun z => g4 z y hy
      rw [Units.val_mul, Matrix.mul_apply] at h
      simp only [e] at h
      rwa [← Matrix.mul_apply, Matrix.mul_one] at h
def entN (M : Matrix (Fin N) (Fin N) κ) (x y : ℕ) : κ := if h : x < N ∧ y < N then M ⟨x, h.1⟩ ⟨y, h.2⟩ else 0
theorem entN_mul {M M' : Matrix (Fin N) (Fin N) κ} (hM : M.BlockTriangular (lvF N a t))
    (hM' : M'.BlockTriangular (lvF N a t)) (h1 : ∀ x : Fin N, x.val < a → M x x = 1)
    (h1' : ∀ x : Fin N, x.val < a → M' x x = 1) {x : ℕ} (hx : x + 1 < a) :
    entN (M * M') x (x + 1) = entN M x (x + 1) + entN M' x (x + 1) := by
  unfold entN
  by_cases h : x < N ∧ x + 1 < N
  · simp only [h, and_self, dif_pos]
    rw [Matrix.mul_apply]
    have hne : (⟨x, h.1⟩ : Fin N) ≠ ⟨x + 1, h.2⟩ := by
      intro e; have := congrArg Fin.val e; simp at this
    rw [← Finset.sum_subset (Finset.subset_univ ({⟨x, h.1⟩, ⟨x + 1, h.2⟩} : Finset (Fin N)))]
    · rw [Finset.sum_pair hne, h1 ⟨x, h.1⟩ (by show x < a; omega), h1' ⟨x + 1, h.2⟩ hx, one_mul, mul_one, add_comm]
    · intro z _ hz
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
      have hz1 : z.val ≠ x := fun e => hz.1 (Fin.ext e)
      have hz2 : z.val ≠ x + 1 := fun e => hz.2 (Fin.ext e)
      rcases Nat.lt_or_ge z.val x with hlt | hge
      · have : M ⟨x, h.1⟩ z = 0 := hM (by
          show lvlX a t z.val < lvlX a t x
          rw [lvlX_of_lt (show x < a by omega)]
          exact (lvlX_lt_iff (by omega)).2 hlt)
        rw [this, zero_mul]
      · have : M' z ⟨x + 1, h.2⟩ = 0 := hM' (by
          show lvlX a t (x + 1) < lvlX a t z.val
          rw [lvlX_of_lt hx]
          exact (lt_lvlX_iff hx).2 (by omega))
        rw [this, mul_zero]
  · simp only [h, dif_neg, not_false_eq_true, add_zero]
def supHom (κ : Type) [CommRing κ] (N a t : ℕ) (fixLast : Bool) (fc : ℕ) (Sd : Finset ℕ) :
    JBar κ N a t fixLast fc →* Multiplicative κ :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd
      (∑ x ∈ Sd.filter (fun x => x + 1 < a), entN ((g : GL (Fin N) κ) : Matrix (Fin N) (Fin N) κ) x (x + 1))) (by
    intro g h
    rw [← ofAdd_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Subgroup.coe_mul, Units.val_mul]
    exact entN_mul g.2.1 h.2.1 g.2.2.1 h.2.2.1 (Finset.mem_filter.1 hx).2)
def signBlockDeterminant (κ : Type) [CommRing κ] (N a t : ℕ) (fixLast : Bool) (fc : ℕ) (c : ℕ) : JBar κ N a t fixLast fc →* κ where
  toFun g := (((g : GL (Fin N) κ) : Matrix (Fin N) (Fin N) κ).toSquareBlock (lvF N a t) c).det
  map_one' := by
    rw [Subgroup.coe_one, Units.val_one]
    have : (1 : Matrix (Fin N) (Fin N) κ).toSquareBlock (lvF N a t) c = 1 := by
      ext x y
      simp [Matrix.toSquareBlock_def, Matrix.one_apply, Subtype.ext_iff]
    rw [this, Matrix.det_one]
  map_mul' g h := by
    rw [Subgroup.coe_mul, Units.val_mul, toSquareBlock_mul g.2.1 h.2.1, Matrix.det_mul]
def lamBar {Z : Type} [CommGroup Z] (κ : Type) [CommRing κ] (N a t : ℕ) (fixLast : Bool) (fc : ℕ) (ψ0 : AddChar κ Z)
    (χ : ℕ → κˣ →* Z) (Sd : Finset ℕ) (nb : ℕ) : JBar κ N a t fixLast fc →* Z :=
  ψ0.toMonoidHom.comp (supHom κ N a t fixLast fc Sd) *
    ∏ i ∈ Finset.range nb, (χ (i + 1)).comp (signBlockDeterminant κ N a t fixLast fc (a + i)).toHomUnits
end Bar
def aX (k m j : ℕ) : ℕ := if j = m then k + m - 1 else k + j
def fixX (m j : ℕ) : Bool := decide (j = m)
def fcX (k m j N : ℕ) : ℕ := if m ≤ j + 1 then k else N
def SdX (k m j : ℕ) : Finset ℕ :=
  if j = m then Finset.range (k + m - 2) else (Finset.range (k + j - 1)).filter fun x => x + 1 ≠ k ∨ j + 1 = m
abbrev JXbar (κ : Type) [CommRing κ] (N k m t j : ℕ) : Subgroup (GL (Fin N) κ) := JBar κ N (aX k m j) t (fixX m j) (fcX k m j N)
def lamXbar {Z : Type} [CommGroup Z] (κ : Type) [CommRing κ] (N k m t j : ℕ) (ψ0 : AddChar κ Z) (χ : ℕ → κˣ →* Z) :
    JXbar κ N k m t j →* Z :=
  lamBar κ N (aX k m j) t (fixX m j) (fcX k m j N) ψ0 χ (SdX k m j) j
section Cong
variable {A R : Type} [CommRing A] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
theorem bc_injective (ι : R →+* A) (h : Function.Injective ι) : Function.Injective (bc (n := n) ι) := by
  intro x y hxy
  apply Units.ext
  have h2 : (x : Matrix n n R).map ι = (y : Matrix n n R).map ι := congrArg Units.val hxy
  exact Matrix.map_injective h h2
def congChar {Z : Type} [Group Z] (ι : R →+* A) (hι : Function.Injective ι) (I : Ideal R) (H : Subgroup (GL n (R ⧸ I)))
    (lam : H →* Z) : congPre ι I H →* Z :=
  (lam.comp ((redGL I).subgroupComap H)).comp
    ((H.comap (redGL I)).equivMapOfInjective (bc ι) (bc_injective ι hι)).symm.toMonoidHom
end Cong
section Loc
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
abbrev resV : Type := (v.adicCompletionIntegers F) ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)
theorem algMapV_injective :
    Function.Injective (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) :=
  fun _ _ h => Subtype.ext h
def JLoc (N a t : ℕ) (fixLast : Bool) (fc : ℕ) : Subgroup (GL (Fin N) (v.adicCompletion F)) :=
  congPre (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) (JBar (resV F v) N a t fixLast fc)
def lamLoc {Z : Type} [CommGroup Z] (N a t : ℕ) (fixLast : Bool) (fc : ℕ) (ψ0 : AddChar (resV F v) Z) (χ : ℕ → (resV F v)ˣ →* Z)
    (Sd : Finset ℕ) (nb : ℕ) : JLoc F v N a t fixLast fc →* Z :=
  congChar _ (algMapV_injective F v) _ _ (lamBar (resV F v) N a t fixLast fc ψ0 χ Sd nb)
end Loc
section Uni
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (v : HeightOneSpectrum (𝓞 F))
  (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) (fr : GL (Fin N) (v.adicCompletion F))
def toFr : GL (Fin N) (E ⊗[F] v.adicCompletion F) →* GL (Fin N) (v.adicCompletion F) :=
  (MulAut.conj fr⁻¹).toMonoidHom.comp (bc ((RingHom.fst _ _).comp spl.toRingHom))
def JU (a t : ℕ) (fixLast : Bool) (fc : ℕ) : Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)) :=
  UPts σE J (v.adicCompletion F) ⊓ (JLoc F v N a t fixLast fc).comap (toFr v spl fr)
def lamU {Z : Type} [CommGroup Z] (a t : ℕ) (fixLast : Bool) (fc : ℕ) (ψ0 : AddChar (resV F v) Z) (χ : ℕ → (resV F v)ˣ →* Z)
    (Sd : Finset ℕ) (nb : ℕ) : JU σE J v spl fr a t fixLast fc →* Z :=
  (lamLoc F v N a t fixLast fc ψ0 χ Sd nb).comp
    (((toFr v spl fr).subgroupComap (JLoc F v N a t fixLast fc)).comp (Subgroup.inclusion inf_le_right))
abbrev JXU (k m t j : ℕ) : Subgroup (GL (Fin N) (E ⊗[F] v.adicCompletion F)) :=
  JU σE J v spl fr (aX k m j) t (fixX m j) (fcX k m j N)
def lamXU {Z : Type} [CommGroup Z] (k m t j : ℕ) (ψ0 : AddChar (resV F v) Z) (χ : ℕ → (resV F v)ˣ →* Z) :
    JXU σE J v spl fr k m t j →* Z :=
  lamU σE J v spl fr (aX k m j) t (fixX m j) (fcX k m j N) ψ0 χ (SdX k m j) j
end Uni
end Formalism.L2.G


