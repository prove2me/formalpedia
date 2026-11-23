-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:40.094302+00:00
-- url     : https://prove2.me/theorems/00098c75-f922-412c-8495-346961686b68
-- title:
--   Standard Five Nontrivial
-- statement:
--   Definitions and structural lemmas for Standard Five Nontrivial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
namespace GlobalTheory.BadShare
section Fn
variable {G : Type} [Group G] [Fintype G]
def conv (a b : G → ℂ) : G → ℂ := fun x => ∑ y, a y * b (y⁻¹ * x)
def op {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (e : G → ℂ) : Module.End ℂ M := ∑ γ, e γ • ρ γ
def rk {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (e : G → ℂ) : ℕ :=
  Module.finrank ℂ (LinearMap.range (op ρ e))
def IsProj (e : G → ℂ) : Prop := conv e e = e ∧ ∀ x, e x⁻¹ = (starRingEnd ℂ) (e x)
def zc (χ : G → ℂ) : G → ℂ := fun γ => χ 1 / (Fintype.card G : ℂ) * χ γ⁻¹
def eps (S : G → Prop) (χ : G → ℂ) : G → ℂ := fun γ => if S γ then (χ γ)⁻¹ / (Nat.card {u // S u} : ℂ) else 0
def dirac : G → ℂ := fun γ => if γ = 1 then 1 else 0
end Fn
def tens {ι G : Type} [Fintype ι] (e : ι → G → ℂ) : (ι → G) → ℂ := fun γ => ∏ v, e v (γ v)
def tens2 {G G' : Type} (a : G → ℂ) (b : G' → ℂ) : G × G' → ℂ := fun γ => a γ.1 * b γ.2
variable (g : ℕ) [Fact g.Prime] (N : ℕ)
abbrev GG : Type := GL (Fin N) (ZMod g)
def IsUp (u : GG g N) : Prop := (∀ a, u.val a a = 1) ∧ ∀ a b, b < a → u.val a b = 0
structure Lev where
  sharp : Bool
  s : ℕ
  k : ℕ
  hk : s + k < N
  ψ : AddChar (ZMod g) ℂ
  hψ : ψ ≠ 1
  co : Fin N → (ZMod g)ˣ
variable {g N}
def Lev.Mem (L : Lev g N) (u : GG g N) : Prop :=
  IsUp g N u ∧ (L.sharp = true → ∀ a b : Fin N, L.s ≤ a → (a : ℕ) < L.s + L.k → (b : ℕ) = L.s + L.k → u.val a b = 0)
def Lev.Edge (L : Lev g N) (a b : Fin N) : Prop :=
  if L.sharp = true then
    ((b : ℕ) = a + 1 ∧ (a : ℕ) + 1 ≠ L.s ∧ ¬ (0 < L.k ∧ (a : ℕ) + 1 = L.s + L.k)) ∨ ((a : ℕ) + 1 = L.s ∧ (b : ℕ) = L.s + L.k)
  else (b : ℕ) = a + 1
def Lev.chi (L : Lev g N) (u : GG g N) : ℂ :=
  L.ψ (∑ a, ∑ b, if L.Edge a b then (L.co a : ZMod g) * u.val a b else 0)
def Lev.e (L : Lev g N) : GG g N → ℂ := eps L.Mem L.chi
def IsGeneric {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GG g N) M) : Prop :=
  ∃ L : Lev g N, L.sharp = false ∧ ∃ x : M, x ≠ 0 ∧ ∀ u, IsUp g N u → ρ u x = L.chi u • x
def IsSeries (τ : (ZMod g)[X] → GG g N → ℂ) : Prop :=
  Set.InjOn τ (sqSet g N : Set (ZMod g)[X]) ∧ ∀ f ∈ sqSet g N, ∃ V : FDRep ℂ (GG g N), CategoryTheory.Simple V ∧
    V.character = τ f ∧ IsGeneric V.ρ ∧
    Module.finrank ℂ V * torusCard g f = ∏ i ∈ Finset.range N, (g ^ (i + 1) - 1)
def eGood {ι : Type} [Fintype ι] {m : ℕ} (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ) :
    (ι → GG g N) → ℂ :=
  ∑ F ∈ goodSet g N ch, tens fun v => zc (τ v (F v))
def AllUnip {ι : Type} (γ : ι → GG g N) : Prop := ∀ v, IsNilpotent ((γ v).val - 1)
def CountAt {g₁ g₂ N : ℕ} [Fact g₁.Prime] [Fact g₂.Prime] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M) (ep : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ e : (ι₁ → GG g₁ N) × (ι₂ → GG g₂ N) → ℂ, IsProj e →
    ((∀ γ, e γ ≠ 0 → AllUnip γ.1) ∨ ∀ γ, e γ ≠ 0 → AllUnip γ.2) →
    |(rk ρ e : ℝ) - c * (e 1).re| ≤ ep * (c * (e 1).re)
def PrimeOK (g q d : ℕ) : Prop :=
  q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1 ∧ 2 ^ 12 ≤ g
namespace Basic
theorem mem_one (L : Lev g N) : L.Mem 1 := by
  refine ⟨⟨fun a => by simp, fun a b h => by simp [Matrix.one_apply, h.ne']⟩, fun _ a b h1 h2 h3 => ?_⟩
  have : a ≠ b := by intro h; subst h; omega
  simp [Matrix.one_apply, this]
theorem mem_mul (L : Lev g N) {u w : GG g N} (hu : L.Mem u) (hw : L.Mem w) : L.Mem (u * w) := by
  have isUp_mul : ∀ {u w : GG g N}, IsUp g N u → IsUp g N w → IsUp g N (u * w) := by
    intro u w hu hw
    obtain ⟨hu1, hu0⟩ := hu
    obtain ⟨hw1, hw0⟩ := hw
    constructor
    · intro a
      rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single a]
      · rw [hu1, hw1, one_mul]
      · intro c _ hc
        rcases lt_or_gt_of_ne hc with h | h
        · rw [hu0 a c h, zero_mul]
        · rw [hw0 c a h, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ a) h
    · intro a b hab
      rw [Units.val_mul, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro c _
      rcases lt_or_ge c a with h | h
      · rw [hu0 a c h, zero_mul]
      · rw [hw0 c b (lt_of_lt_of_le hab h), mul_zero]
  obtain ⟨hu, hu'⟩ := hu
  obtain ⟨hw, hw'⟩ := hw
  refine ⟨isUp_mul hu hw, ?_⟩
  intro hs a b h1 h2 h3
  rw [Units.val_mul, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  rcases lt_or_ge c a with h | h
  · rw [hu.2 a c h, zero_mul]
  · rcases lt_trichotomy c b with h' | h' | h'
    · have hca : (a : ℕ) ≤ c := h
      have hcb : (c : ℕ) < b := h'
      rw [hw' hs c b (by omega) (by omega) h3, mul_zero]
    · subst h'
      rw [hu' hs a c h1 h2 h3, zero_mul]
    · rw [hw.2 c b h', mul_zero]
theorem entry_mul (L : Lev g N) {u w : GG g N} (hu : L.Mem u) (hw : L.Mem w) {a b : Fin N} (h : L.Edge a b) :
    (u * w).val a b = u.val a b + w.val a b := by
  obtain ⟨⟨u1, u2⟩, u3⟩ := hu
  obtain ⟨⟨w1, w2⟩, w3⟩ := hw
  have hab : (a : ℕ) < b := by
    unfold Lev.Edge at h
    split_ifs at h <;> omega
  have hne : b ≠ a := by intro h; subst h; omega
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem b a (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · rw [w1, u1, mul_one, one_mul]
  · intro c _ ⟨hcb, hca⟩
    rcases lt_or_gt_of_ne hca with h1 | h1
    · rw [u2 a c h1, zero_mul]
    · rcases lt_or_gt_of_ne hcb with h2 | h2
      · have h1' : (a : ℕ) < c := h1
        have h2' : (c : ℕ) < b := h2
        unfold Lev.Edge at h
        split_ifs at h with hs
        · rw [w3 hs c b (by omega) (by omega) (by omega), mul_zero]
        · omega
      · rw [w2 c b h2, mul_zero]
theorem chi_mul (L : Lev g N) {u w : GG g N} (hu : L.Mem u) (hw : L.Mem w) : L.chi (u * w) = L.chi u * L.chi w := by
  unfold Lev.chi
  rw [← AddChar.map_add_eq_mul, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · rw [entry_mul L hu hw h, mul_add]
  · simp
theorem mem_inv (L : Lev g N) {u : GG g N} (hu : L.Mem u) : L.Mem u⁻¹ := by
  have hp : ∀ n : ℕ, L.Mem (u ^ n) := by
    intro n
    induction n with
    | zero => simpa using mem_one L
    | succ n ih => rw [pow_succ]; exact mem_mul L ih hu
  have : u⁻¹ = u ^ (orderOf u - 1) := by
    have h0 : 0 < orderOf u := orderOf_pos u
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel h0, pow_orderOf_eq_one]
  rw [this]; exact hp _
theorem norm_chi (L : Lev g N) (u : GG g N) : ‖L.chi u‖ = 1 := AddChar.norm_apply _ _
theorem chi_ne (L : Lev g N) (u : GG g N) : L.chi u ≠ 0 := by
  intro h; have := norm_chi L u; rw [h] at this; simp at this
theorem chi_one (L : Lev g N) : L.chi 1 = 1 := by
  have := chi_mul L (mem_one L) (mem_one L)
  rw [mul_one] at this
  exact (mul_eq_left₀ (chi_ne L 1)).mp this.symm
def levOfChar (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (N : ℕ) (b : Bool) (s k : ℕ) (h : s + k < N) : Lev g N :=
  ⟨b, s, k, h, ψ, hψ, fun _ => 1⟩
def levStandard (g : ℕ) [Fact g.Prime] (N : ℕ) (b : Bool) (s k : ℕ) (h : s + k < N) : Lev g N :=
  levOfChar ZMod.stdAddChar (fun h1 => by
    have h2 : (ZMod.stdAddChar (N := g)) 1 = ZMod.stdAddChar (N := g) 0 := by rw [h1]; simp
    exact one_ne_zero (ZMod.injective_stdAddChar h2)) N b s k h
def transv (a b : Fin N) (h : a ≠ b) : GG g N :=
  ⟨Matrix.transvection a b 1, Matrix.transvection a b (-1),
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp,
    by rw [Matrix.transvection_mul_transvection_same _ _ h]; simp⟩
def levGrp (L : Lev g N) : Subgroup (GG g N) where
  carrier := {u | L.Mem u}
  one_mem' := mem_one L
  mul_mem' := mem_mul L
  inv_mem' := mem_inv L
def levChiHom (L : Lev g N) : levGrp L →* ℂ where
  toFun u := L.chi u
  map_one' := chi_one L
  map_mul' u w := chi_mul L u.2 w.2
section Alg
variable {G : Type} [Group G] [Fintype G]
def alg (e : G → ℂ) : MonoidAlgebra ℂ G := ∑ γ, MonoidAlgebra.single γ (e γ)
end Alg
section Proj
variable {G : Type} [Group G] [Fintype G]
def adj (e : G → ℂ) : G → ℂ := fun x => (starRingEnd ℂ) (e x⁻¹)
end Proj
section Reg
variable (G : Type) [Group G] [Fintype G]
def regFn : Representation ℂ G (G → ℂ) where
  toFun γ := LinearMap.funLeft ℂ ℂ (fun x => γ⁻¹ * x)
  map_one' := by ext f x; simp [LinearMap.funLeft_apply]
  map_mul' a b := by ext f x; simp [LinearMap.funLeft_apply, mul_assoc]
variable {G}
end Reg
def lineRep (χ : (ZMod g)ˣ →* ℂˣ) : Representation ℂ (GG g N) ℂ where
  toFun γ := ((χ (Matrix.GeneralLinearGroup.det γ) : ℂˣ) : ℂ) • LinearMap.id
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_comm]
end Basic
end GlobalTheory.BadShare


