-- Prove2me | solution 1 for AutomorphicForm.IsGL2RealKTypeModule.ne_bot_iff_parity_or_discreteSeries_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/73487217-dfb3-5895-b53e-2b3de8c62975

import Mathlib
import Definitions.Def_AutomorphicForm_GL2RealKTypeModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_IsGL2RealKTypeModule_ne_bot_iff_parity_or_discreteSeries_of_irreducible

set_option autoImplicit false

open AutomorphicForm

namespace GL2RealKTypeClassification

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}

section Basic

variable (hM : IsGL2RealKTypeModule wt E L ε)
include hM

theorem refl_raise (x : M) : ε (E x) = L (ε x) := by
  simpa using LinearMap.congr_fun hM.refl_comp_raise x

theorem refl_lower (x : M) : ε (L x) = E (ε x) := by
  simpa using LinearMap.congr_fun hM.refl_comp_lower x

theorem raise_refl (x : M) : E (ε x) = ε (L x) := (refl_lower hM x).symm

theorem lower_refl (x : M) : L (ε x) = ε (E x) := (refl_raise hM x).symm

private theorem _root_.GL2RealKTypeClassification.refl_refl (x : M) : ε (ε x) = x := hM.refl_refl x

p2m_export "GL2RealKTypeClassification" "refl_refl"
theorem refl_injective : Function.Injective ε := fun x y hxy => by
  have := congrArg ε hxy
  rwa [refl_refl hM, refl_refl hM] at this

theorem refl_ne_zero {x : M} (hx : x ≠ 0) : ε x ≠ 0 := fun h => by
  apply hx
  apply refl_injective hM
  rw [h, map_zero]

theorem refl_eq_zero_iff {x : M} : ε x = 0 ↔ x = 0 :=
  ⟨fun h => by_contra fun hx => refl_ne_zero hM hx h, fun h => by rw [h, map_zero]⟩

theorem lower_raise_of_mem {n : ℤ} {x : M} (hx : x ∈ wt n) :
    L (E x) = E (L x) - (n : ℂ) • x := by
  have h := hM.raise_lower_sub n x hx
  rw [← h]
  abel

theorem raise_lower_of_mem {n : ℤ} {x : M} (hx : x ∈ wt n) :
    E (L x) = L (E x) + (n : ℂ) • x := by
  have h := hM.raise_lower_sub n x hx
  rw [← h]
  abel

omit hM in
theorem mem_wt_of_eq {m m' : ℤ} {x : M} (h : m = m') (hx : x ∈ wt m) : x ∈ wt m' := h ▸ hx

theorem pow_raise_mem {n : ℤ} {x : M} (hx : x ∈ wt n) (a : ℕ) :
    (E ^ a) x ∈ wt (n + 2 * (a : ℤ)) := by
  induction a with
  | zero => simpa using hx
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply]
    have := hM.raise_mem ih
    refine mem_wt_of_eq ?_ this
    push_cast
    ring

theorem pow_lower_mem {n : ℤ} {x : M} (hx : x ∈ wt n) (b : ℕ) :
    (L ^ b) x ∈ wt (n - 2 * (b : ℤ)) := by
  induction b with
  | zero => simpa using hx
  | succ b ih =>
    rw [pow_succ', Module.End.mul_apply]
    have := hM.lower_mem ih
    refine mem_wt_of_eq ?_ this
    push_cast
    ring

theorem refl_pow_raise (x : M) (a : ℕ) : ε ((E ^ a) x) = (L ^ a) (ε x) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply, refl_raise hM, ih, pow_succ', Module.End.mul_apply]

theorem refl_pow_lower (x : M) (b : ℕ) : ε ((L ^ b) x) = (E ^ b) (ε x) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ', Module.End.mul_apply, refl_lower hM, ih, pow_succ', Module.End.mul_apply]

end Basic

section Chains

variable (hM : IsGL2RealKTypeModule wt E L ε)
include hM

variable {n₀ : ℤ} {v : M} {μ : ℂ}

theorem lower_pow_raise_succ (hv : v ∈ wt n₀) (hEL : E (L v) = μ • v) (a : ℕ) :
    ∃ c : ℂ, L ((E ^ (a + 1)) v) = c • (E ^ a) v := by
  induction a with
  | zero =>
    refine ⟨μ - (n₀ : ℂ), ?_⟩
    rw [zero_add, pow_one, pow_zero, Module.End.one_apply, lower_raise_of_mem hM hv, hEL, sub_smul]
  | succ a ih =>
    obtain ⟨c, hc⟩ := ih
    have hmem : (E ^ (a + 1)) v ∈ wt (n₀ + 2 * ((a + 1 : ℕ) : ℤ)) := pow_raise_mem hM hv (a + 1)
    refine ⟨c - ((n₀ + 2 * ((a + 1 : ℕ) : ℤ) : ℤ) : ℂ), ?_⟩
    rw [pow_succ' E (a + 1), Module.End.mul_apply, lower_raise_of_mem hM hmem, hc, map_smul,
      ← Module.End.mul_apply E (E ^ a) v, ← pow_succ' E a, sub_smul]

theorem raise_pow_lower_succ (hv : v ∈ wt n₀) (hEL : E (L v) = μ • v) (b : ℕ) :
    ∃ d : ℂ, E ((L ^ (b + 1)) v) = d • (L ^ b) v := by
  induction b with
  | zero =>
    refine ⟨μ, ?_⟩
    rw [zero_add, pow_one, pow_zero, Module.End.one_apply, hEL]
  | succ b ih =>
    obtain ⟨d, hd⟩ := ih
    have hmem : (L ^ (b + 1)) v ∈ wt (n₀ - 2 * ((b + 1 : ℕ) : ℤ)) := pow_lower_mem hM hv (b + 1)
    refine ⟨d + ((n₀ - 2 * ((b + 1 : ℕ) : ℤ) : ℤ) : ℂ), ?_⟩
    rw [pow_succ' L (b + 1), Module.End.mul_apply, raise_lower_of_mem hM hmem, hd, map_smul,
      ← Module.End.mul_apply L (L ^ b) v, ← pow_succ' L b, add_smul]

omit hM in

theorem pow_raise_eq_zero_of_le {a a' : ℕ} (h : (E ^ a) v = 0) (haa' : a ≤ a') :
    (E ^ a') v = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le haa'
  clear haa'
  induction d with
  | zero => simpa using h
  | succ d ih =>
    rw [← add_assoc, pow_succ', Module.End.mul_apply, ih, map_zero]

omit hM in

theorem pow_lower_eq_zero_of_le {b b' : ℕ} (h : (L ^ b) v = 0) (hbb' : b ≤ b') :
    (L ^ b') v = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hbb'
  clear hbb'
  induction d with
  | zero => simpa using h
  | succ d ih =>
    rw [← add_assoc, pow_succ', Module.End.mul_apply, ih, map_zero]

def chainSet (E L ε : M →ₗ[ℂ] M) (v : M) : Set M :=
  ((Set.range fun a : ℕ => (E ^ a) v) ∪ Set.range fun b : ℕ => (L ^ b) v) ∪
    ((Set.range fun a : ℕ => ε ((E ^ a) v)) ∪ Set.range fun b : ℕ => ε ((L ^ b) v))

omit hM in
theorem pow_raise_mem_chainSet (a : ℕ) : (E ^ a) v ∈ chainSet E L ε v :=
  Or.inl (Or.inl ⟨a, rfl⟩)

omit hM in
theorem pow_lower_mem_chainSet (b : ℕ) : (L ^ b) v ∈ chainSet E L ε v :=
  Or.inl (Or.inr ⟨b, rfl⟩)

omit hM in
theorem refl_pow_raise_mem_chainSet (a : ℕ) : ε ((E ^ a) v) ∈ chainSet E L ε v :=
  Or.inr (Or.inl ⟨a, rfl⟩)

omit hM in
theorem refl_pow_lower_mem_chainSet (b : ℕ) : ε ((L ^ b) v) ∈ chainSet E L ε v :=
  Or.inr (Or.inr ⟨b, rfl⟩)

omit hM in
theorem self_mem_chainSet : v ∈ chainSet E L ε v := by
  have := pow_raise_mem_chainSet (E := E) (L := L) (ε := ε) (v := v) 0
  simpa using this

theorem isGL2RealKTypeSubmodule_span_chainSet (hv : v ∈ wt n₀) (hEL : E (L v) = μ • v) :
    IsGL2RealKTypeSubmodule wt E L ε (Submodule.span ℂ (chainSet E L ε v)) := by
  set W := Submodule.span ℂ (chainSet E L ε v) with hW
  have hsub : chainSet E L ε v ⊆ W := Submodule.subset_span
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [Submodule.span_le]
    intro s hs
    have aux : ∀ (m : ℤ), s ∈ wt m → s ∈ ⨆ n : ℤ, W ⊓ wt n := fun m hm =>
      Submodule.mem_iSup_of_mem m ⟨hsub hs, hm⟩
    rcases hs with (⟨a, rfl⟩ | ⟨b, rfl⟩) | (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact aux _ (pow_raise_mem hM hv a)
    · exact aux _ (pow_lower_mem hM hv b)
    · exact aux _ (hM.refl_mem (pow_raise_mem hM hv a))
    · exact aux _ (hM.refl_mem (pow_lower_mem hM hv b))
  ·
    rw [Submodule.map_span_le]
    intro s hs
    rcases hs with (⟨a, rfl⟩ | ⟨b, rfl⟩) | (⟨a, rfl⟩ | ⟨b, rfl⟩) <;> dsimp only
    · rw [← Module.End.mul_apply E (E ^ a) v, ← pow_succ']
      exact hsub (pow_raise_mem_chainSet (a + 1))
    · cases b with
      | zero =>
        rw [pow_zero, Module.End.one_apply]
        have : E v = (E ^ 1) v := by rw [pow_one]
        rw [this]
        exact hsub (pow_raise_mem_chainSet 1)
      | succ b =>
        obtain ⟨d, hd⟩ := raise_pow_lower_succ hM hv hEL b
        rw [hd]
        exact W.smul_mem d (hsub (pow_lower_mem_chainSet b))
    · rw [raise_refl hM]
      cases a with
      | zero =>
        rw [pow_zero, Module.End.one_apply]
        have : L v = (L ^ 1) v := by rw [pow_one]
        rw [this]
        exact hsub (refl_pow_lower_mem_chainSet 1)
      | succ a =>
        obtain ⟨c, hc⟩ := lower_pow_raise_succ hM hv hEL a
        rw [hc, map_smul]
        exact W.smul_mem c (hsub (refl_pow_raise_mem_chainSet a))
    · rw [raise_refl hM, ← Module.End.mul_apply L (L ^ b) v, ← pow_succ']
      exact hsub (refl_pow_lower_mem_chainSet (b + 1))
  ·
    rw [Submodule.map_span_le]
    intro s hs
    rcases hs with (⟨a, rfl⟩ | ⟨b, rfl⟩) | (⟨a, rfl⟩ | ⟨b, rfl⟩) <;> dsimp only
    · cases a with
      | zero =>
        rw [pow_zero, Module.End.one_apply]
        have : L v = (L ^ 1) v := by rw [pow_one]
        rw [this]
        exact hsub (pow_lower_mem_chainSet 1)
      | succ a =>
        obtain ⟨c, hc⟩ := lower_pow_raise_succ hM hv hEL a
        rw [hc]
        exact W.smul_mem c (hsub (pow_raise_mem_chainSet a))
    · rw [← Module.End.mul_apply L (L ^ b) v, ← pow_succ']
      exact hsub (pow_lower_mem_chainSet (b + 1))
    · rw [lower_refl hM, ← Module.End.mul_apply E (E ^ a) v, ← pow_succ']
      exact hsub (refl_pow_raise_mem_chainSet (a + 1))
    · rw [lower_refl hM]
      cases b with
      | zero =>
        rw [pow_zero, Module.End.one_apply]
        have : E v = (E ^ 1) v := by rw [pow_one]
        rw [this]
        exact hsub (refl_pow_raise_mem_chainSet 1)
      | succ b =>
        obtain ⟨d, hd⟩ := raise_pow_lower_succ hM hv hEL b
        rw [hd, map_smul]
        exact W.smul_mem d (hsub (refl_pow_lower_mem_chainSet b))
  ·
    rw [Submodule.map_span_le]
    intro s hs
    rcases hs with (⟨a, rfl⟩ | ⟨b, rfl⟩) | (⟨a, rfl⟩ | ⟨b, rfl⟩) <;> dsimp only
    · exact hsub (refl_pow_raise_mem_chainSet a)
    · exact hsub (refl_pow_lower_mem_chainSet b)
    · rw [refl_refl hM]; exact hsub (pow_raise_mem_chainSet a)
    · rw [refl_refl hM]; exact hsub (pow_lower_mem_chainSet b)

theorem span_chainSet_eq_top (hirr : IsIrreducibleGL2RealKTypeModule wt E L ε)
    (hv : v ∈ wt n₀) (hv0 : v ≠ 0) (hEL : E (L v) = μ • v) :
    Submodule.span ℂ (chainSet E L ε v) = ⊤ := by
  rcases hirr.2 _ (isGL2RealKTypeSubmodule_span_chainSet hM hv hEL) with h | h
  · exfalso
    apply hv0
    have : v ∈ Submodule.span ℂ (chainSet E L ε v) := Submodule.subset_span self_mem_chainSet
    rw [h] at this
    exact (Submodule.mem_bot ℂ).mp this
  · exact h

end Chains

section Support

variable (hM : IsGL2RealKTypeModule wt E L ε)
include hM

theorem exists_proj (n : ℤ) :
    ∃ P : M →ₗ[ℂ] M, (∀ x ∈ wt n, P x = x) ∧ (∀ m : ℤ, m ≠ n → ∀ x ∈ wt m, P x = 0) := by
  letI := hM.isInternal.chooseDecomposition
  refine ⟨{ toFun := fun x => (DirectSum.decompose wt x n : M)
            map_add' := ?_
            map_smul' := ?_ }, ?_, ?_⟩
  · intro x y
    simp [DirectSum.decompose_add]
  · intro r x
    simp only [DirectSum.decompose_smul, RingHom.id_apply]
    rfl
  · intro x hx
    exact DirectSum.decompose_of_mem_same wt hx
  · intro m hmn x hx
    exact DirectSum.decompose_of_mem_ne wt hx hmn

variable {n₀ : ℤ} {v : M} {μ : ℂ}

theorem ne_bot_iff_exists_chain (hirr : IsIrreducibleGL2RealKTypeModule wt E L ε)
    (hv : v ∈ wt n₀) (hv0 : v ≠ 0) (hEL : E (L v) = μ • v) (n : ℤ) :
    wt n ≠ ⊥ ↔
      (∃ a : ℕ, (n₀ + 2 * (a : ℤ) = n ∨ n₀ + 2 * (a : ℤ) = -n) ∧ (E ^ a) v ≠ 0) ∨
      (∃ b : ℕ, (n₀ - 2 * (b : ℤ) = n ∨ n₀ - 2 * (b : ℤ) = -n) ∧ (L ^ b) v ≠ 0) := by
  constructor
  · intro hn
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hn
    by_contra hcon
    push Not at hcon
    obtain ⟨hE, hL⟩ := hcon
    obtain ⟨P, hPn, hPne⟩ := exists_proj hM n
    have hker : Submodule.span ℂ (chainSet E L ε v) ≤ LinearMap.ker P := by
      rw [Submodule.span_le]
      intro s hs
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      rcases hs with (⟨a, rfl⟩ | ⟨b, rfl⟩) | (⟨a, rfl⟩ | ⟨b, rfl⟩) <;> dsimp only
      · by_cases h : n₀ + 2 * (a : ℤ) = n
        · rw [hE a (Or.inl h), map_zero]
        · exact hPne _ h _ (pow_raise_mem hM hv a)
      · by_cases h : n₀ - 2 * (b : ℤ) = n
        · rw [hL b (Or.inl h), map_zero]
        · exact hPne _ h _ (pow_lower_mem hM hv b)
      · by_cases h : n₀ + 2 * (a : ℤ) = -n
        · rw [hE a (Or.inr h), map_zero, map_zero]
        · refine hPne _ ?_ _ (hM.refl_mem (pow_raise_mem hM hv a))
          intro h'; apply h; rw [← h', neg_neg]
      · by_cases h : n₀ - 2 * (b : ℤ) = -n
        · rw [hL b (Or.inr h), map_zero, map_zero]
        · refine hPne _ ?_ _ (hM.refl_mem (pow_lower_mem hM hv b))
          intro h'; apply h; rw [← h', neg_neg]
    have hu' : u ∈ Submodule.span ℂ (chainSet E L ε v) := by
      rw [span_chainSet_eq_top hM hirr hv hv0 hEL]; exact Submodule.mem_top
    have := hker hu'
    rw [LinearMap.mem_ker, hPn u hu] at this
    exact hu0 this
  · rintro (⟨a, ha | ha, hne⟩ | ⟨b, hb | hb, hne⟩)
    · exact (Submodule.ne_bot_iff _).mpr ⟨_, ha ▸ pow_raise_mem hM hv a, hne⟩
    · refine (Submodule.ne_bot_iff _).mpr ⟨ε ((E ^ a) v), ?_, refl_ne_zero hM hne⟩
      have := hM.refl_mem (pow_raise_mem hM hv a)
      rwa [ha, neg_neg] at this
    · exact (Submodule.ne_bot_iff _).mpr ⟨_, hb ▸ pow_lower_mem hM hv b, hne⟩
    · refine (Submodule.ne_bot_iff _).mpr ⟨ε ((L ^ b) v), ?_, refl_ne_zero hM hne⟩
      have := hM.refl_mem (pow_lower_mem hM hv b)
      rwa [hb, neg_neg] at this

omit hM in

theorem exists_bound_raise (hv0 : v ≠ 0) (h : ∃ a : ℕ, (E ^ a) v = 0) :
    ∃ A : ℕ, 0 < A ∧ ∀ a : ℕ, (E ^ a) v ≠ 0 ↔ a < A := by
  classical
  refine ⟨Nat.find h, ?_, fun a => ⟨fun ha => ?_, fun ha => Nat.find_min h ha⟩⟩
  · rw [Nat.pos_iff_ne_zero]
    intro h0
    have := Nat.find_spec h
    rw [h0, pow_zero, Module.End.one_apply] at this
    exact hv0 this
  · by_contra hle
    push Not at hle
    exact ha (pow_raise_eq_zero_of_le (Nat.find_spec h) hle)

omit hM in

theorem exists_bound_lower (hv0 : v ≠ 0) (h : ∃ b : ℕ, (L ^ b) v = 0) :
    ∃ B : ℕ, 0 < B ∧ ∀ b : ℕ, (L ^ b) v ≠ 0 ↔ b < B := by
  classical
  refine ⟨Nat.find h, ?_, fun b => ⟨fun hb => ?_, fun hb => Nat.find_min h hb⟩⟩
  · rw [Nat.pos_iff_ne_zero]
    intro h0
    have := Nat.find_spec h
    rw [h0, pow_zero, Module.End.one_apply] at this
    exact hv0 this
  · by_contra hle
    push Not at hle
    exact hb (pow_lower_eq_zero_of_le (Nat.find_spec h) hle)

theorem finite_of_bounds (hirr : IsIrreducibleGL2RealKTypeModule wt E L ε)
    (hv : v ∈ wt n₀) (hv0 : v ≠ 0) (hEL : E (L v) = μ • v) {A B : ℕ}
    (hA : ∀ a : ℕ, (E ^ a) v ≠ 0 → a < A) (hB : ∀ b : ℕ, (L ^ b) v ≠ 0 → b < B) :
    {n : ℤ | wt n ≠ ⊥}.Finite := by
  refine (Set.finite_Icc (-(|n₀| + 2 * ((A : ℤ) + B))) (|n₀| + 2 * ((A : ℤ) + B))).subset ?_
  intro n hn
  rw [Set.mem_setOf_eq, ne_bot_iff_exists_chain hM hirr hv hv0 hEL] at hn
  have h1 := le_abs_self n₀
  have h2 := neg_abs_le n₀
  rw [Set.mem_Icc]
  rcases hn with ⟨a, ha, hne⟩ | ⟨b, hb, hne⟩
  · have := hA a hne
    rcases ha with ha | ha <;> constructor <;> omega
  · have := hB b hne
    rcases hb with hb | hb <;> constructor <;> omega

theorem support_of_infinite_infinite (hirr : IsIrreducibleGL2RealKTypeModule wt E L ε)
    (hv : v ∈ wt n₀) (hv0 : v ≠ 0) (hEL : E (L v) = μ • v)
    (he : ∀ a : ℕ, (E ^ a) v ≠ 0) (hf : ∀ b : ℕ, (L ^ b) v ≠ 0) (n : ℤ) :
    wt n ≠ ⊥ ↔ Even (n - n₀) := by
  rw [ne_bot_iff_exists_chain hM hirr hv hv0 hEL, Int.even_iff]
  constructor
  · rintro (⟨a, ha, -⟩ | ⟨b, hb, -⟩) <;> omega
  · intro hpar
    by_cases hle : n₀ ≤ n
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ (n - n₀) / 2 by omega)
      exact Or.inl ⟨m, Or.inl (by omega), he m⟩
    · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ (n₀ - n) / 2 by omega)
      exact Or.inr ⟨m, Or.inl (by omega), hf m⟩

theorem support_of_infinite_finite (hirr : IsIrreducibleGL2RealKTypeModule wt E L ε)
    (hv : v ∈ wt n₀) (hv0 : v ≠ 0) (hEL : E (L v) = μ • v)
    (he : ∀ a : ℕ, (E ^ a) v ≠ 0) {B : ℕ} (hB : 0 < B) (hf : ∀ b : ℕ, (L ^ b) v ≠ 0 ↔ b < B)
    (n : ℤ) :
    wt n ≠ ⊥ ↔
      Even (n - (n₀ + 2 - 2 * (B : ℤ))) ∧
        (n₀ + 2 - 2 * (B : ℤ) ≤ n ∨ n ≤ -(n₀ + 2 - 2 * (B : ℤ))) := by
  rw [ne_bot_iff_exists_chain hM hirr hv hv0 hEL, Int.even_iff]
  constructor
  · rintro (⟨a, ha, -⟩ | ⟨b, hb, hne⟩)
    · have hB1 : (1 : ℤ) ≤ B := by exact_mod_cast hB
      rcases ha with ha | ha <;> constructor <;> omega
    · have hbB : b < B := (hf b).mp hne
      have hbB' : (b : ℤ) + 1 ≤ B := by exact_mod_cast hbB
      rcases hb with hb | hb <;> constructor <;> omega
  · rintro ⟨hpar, hj | hj⟩
    · by_cases hle : n₀ ≤ n
      · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ (n - n₀) / 2 by omega)
        exact Or.inl ⟨m, Or.inl (by omega), he m⟩
      · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ (n₀ - n) / 2 by omega)
        refine Or.inr ⟨m, Or.inl (by omega), (hf m).mpr ?_⟩
        have : (m : ℤ) < B := by omega
        exact_mod_cast this
    · by_cases hle : n₀ ≤ -n
      · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ (-n - n₀) / 2 by omega)
        exact Or.inl ⟨m, Or.inr (by omega), he m⟩
      · obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ (n₀ + n) / 2 by omega)
        refine Or.inr ⟨m, Or.inr (by omega), (hf m).mpr ?_⟩
        have : (m : ℤ) < B := by omega
        exact_mod_cast this

omit hM in

theorem shape_of_least_weight {S : ℤ → Prop} {j : ℤ}
    (hS : ∀ n : ℤ, S n ↔ Even (n - j) ∧ (j ≤ n ∨ n ≤ -j)) :
    (j ≤ 1 → ∀ n : ℤ, S n ↔ Even (n - j)) ∧
      (2 ≤ j → ∀ n : ℤ, S n ↔ (j ≤ |n| ∧ Even (n - j))) := by
  constructor
  · intro hj n
    rw [hS n, Int.even_iff]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, by omega⟩
  · intro hj n
    rw [hS n, Int.even_iff, le_abs']
    constructor
    · rintro ⟨h, h' | h'⟩
      · exact ⟨Or.inr h', h⟩
      · exact ⟨Or.inl (by omega), h⟩
    · rintro ⟨h' | h', h⟩
      · exact ⟨h, Or.inr (by omega)⟩
      · exact ⟨h, Or.inl h'⟩

theorem shape_of_raise_infinite (hirr : IsIrreducibleGL2RealKTypeModule wt E L ε)
    (hv : v ∈ wt n₀) (hv0 : v ≠ 0) (hEL : E (L v) = μ • v) (he : ∀ a : ℕ, (E ^ a) v ≠ 0) :
    (∃ e : ℤ, ∀ n : ℤ, wt n ≠ ⊥ ↔ Even (n - e)) ∨
      (∃ k : ℤ, 2 ≤ k ∧ ∀ n : ℤ, wt n ≠ ⊥ ↔ (k ≤ |n| ∧ Even (n - k))) := by
  by_cases hf : ∀ b : ℕ, (L ^ b) v ≠ 0
  · exact Or.inl ⟨n₀, support_of_infinite_infinite hM hirr hv hv0 hEL he hf⟩
  · push Not at hf
    obtain ⟨B, hB, hfB⟩ := exists_bound_lower hv0 hf
    have hsupp := support_of_infinite_finite hM hirr hv hv0 hEL he hB hfB
    have hshape := shape_of_least_weight hsupp
    by_cases hj : n₀ + 2 - 2 * (B : ℤ) ≤ 1
    · exact Or.inl ⟨_, hshape.1 hj⟩
    · exact Or.inr ⟨_, by omega, hshape.2 (by omega)⟩

theorem exists_eigenvector (hadm : ∀ n : ℤ, FiniteDimensional ℂ (wt n)) {n : ℤ}
    (hn : wt n ≠ ⊥) : ∃ v ∈ wt n, v ≠ 0 ∧ ∃ μ : ℂ, E (L v) = μ • v := by
  haveI := hadm n
  have hmap : ∀ x ∈ wt n, (E ∘ₗ L) x ∈ wt n := fun x hx => by
    have := hM.raise_mem (hM.lower_mem hx)
    rwa [sub_add_cancel] at this
  haveI : Nontrivial (wt n) := Submodule.nontrivial_iff_ne_bot.mpr hn
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ((E ∘ₗ L).restrict hmap)
  obtain ⟨x, hx⟩ := hμ.exists_hasEigenvector
  have hx0 : (x : M) ≠ 0 := fun h => hx.2 (Subtype.ext h)
  refine ⟨x, x.2, hx0, μ, ?_⟩
  have h1 := hx.apply_eq_smul
  have := congrArg Subtype.val h1
  simpa [LinearMap.restrict_apply] using this

end Support

theorem main (hM : IsGL2RealKTypeModule wt E L ε)
    (hadm : ∀ n : ℤ, FiniteDimensional ℂ (wt n))
    (hirr : IsIrreducibleGL2RealKTypeModule wt E L ε)
    (hinf : {n : ℤ | wt n ≠ ⊥}.Infinite) :
    ((∃ e : ℤ, ∀ n : ℤ, wt n ≠ ⊥ ↔ Even (n - e)) ∨
      (∃ k : ℤ, 2 ≤ k ∧ ∀ n : ℤ, wt n ≠ ⊥ ↔ (k ≤ |n| ∧ Even (n - k)))) ∧
    (∀ k : ℤ, 2 ≤ k →
      ((∃ v ∈ wt k, v ≠ 0 ∧ L v = 0) ↔ ∀ n : ℤ, wt n ≠ ⊥ ↔ (k ≤ |n| ∧ Even (n - k)))) := by
  refine ⟨?_, fun k hk => ⟨?_, fun h => ?_⟩⟩
  ·
    obtain ⟨n₀, hn₀⟩ := hinf.nonempty
    obtain ⟨v, hv, hv0, μ, hEL⟩ := exists_eigenvector hM hadm hn₀
    by_cases he : ∀ a : ℕ, (E ^ a) v ≠ 0
    · exact shape_of_raise_infinite hM hirr hv hv0 hEL he
    · push Not at he
      by_cases hf : ∀ b : ℕ, (L ^ b) v ≠ 0
      ·
        have hv' : ε v ∈ wt (-n₀) := hM.refl_mem hv
        have hv0' : ε v ≠ 0 := refl_ne_zero hM hv0
        have hEL' : E (L (ε v)) = (μ - (n₀ : ℂ)) • ε v := by
          rw [lower_refl hM, raise_refl hM, lower_raise_of_mem hM hv, hEL, ← sub_smul, map_smul]
        have he' : ∀ a : ℕ, (E ^ a) (ε v) ≠ 0 := fun a => by
          rw [← refl_pow_lower hM]
          exact refl_ne_zero hM (hf a)
        exact shape_of_raise_infinite hM hirr hv' hv0' hEL' he'
      · push Not at hf
        exfalso
        obtain ⟨A, -, hA⟩ := exists_bound_raise hv0 he
        obtain ⟨B, -, hB⟩ := exists_bound_lower hv0 hf
        exact hinf (finite_of_bounds hM hirr hv hv0 hEL (fun a h => (hA a).mp h)
          (fun b h => (hB b).mp h))
  ·
    rintro ⟨u, hu, hu0, hLu⟩
    have hEL : E (L u) = (0 : ℂ) • u := by rw [hLu, map_zero, zero_smul]
    have hfB : ∀ b : ℕ, (L ^ b) u ≠ 0 ↔ b < 1 := by
      intro b
      cases b with
      | zero => simpa using hu0
      | succ b =>
        simp only [Nat.succ_lt_succ_iff, Nat.not_lt_zero, iff_false, ne_eq, not_not]
        exact pow_lower_eq_zero_of_le (b := 1) (by rw [pow_one]; exact hLu) (by omega)
    have he : ∀ a : ℕ, (E ^ a) u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨A, -, hA⟩ := exists_bound_raise hu0 hcon
      exact hinf (finite_of_bounds hM hirr hu hu0 hEL (fun a h => (hA a).mp h)
        (fun b h => (hfB b).mp h))
    have hsupp := support_of_infinite_finite hM hirr hu hu0 hEL he one_pos hfB
    have hj : k + 2 - 2 * ((1 : ℕ) : ℤ) = k := by push_cast; ring
    rw [hj] at hsupp
    exact (shape_of_least_weight hsupp).2 hk
  ·
    have hk0 : wt k ≠ ⊥ := (h k).mpr ⟨by rw [abs_of_nonneg (by omega)], by simp⟩
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hk0
    refine ⟨u, hu, hu0, ?_⟩
    have hk2 : wt (k - 2) = ⊥ := by
      by_contra hne
      have := ((h (k - 2)).mp hne).1
      rw [abs_of_nonneg (by omega)] at this
      omega
    have : L u ∈ wt (k - 2) := hM.lower_mem hu
    rwa [hk2, Submodule.mem_bot] at this

end GL2RealKTypeClassification

theorem solution
    (M : Type*) [AddCommGroup M] [Module ℂ M]
    (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M)
    (hM : IsGL2RealKTypeModule wt E L ε)
    (hadm : ∀ n : ℤ, FiniteDimensional ℂ (wt n))
    (hirr : IsIrreducibleGL2RealKTypeModule wt E L ε)
    (hinf : {n : ℤ | wt n ≠ ⊥}.Infinite) :
    ((∃ e : ℤ, ∀ n : ℤ, wt n ≠ ⊥ ↔ Even (n - e)) ∨
      (∃ k : ℤ, 2 ≤ k ∧ ∀ n : ℤ, wt n ≠ ⊥ ↔ (k ≤ |n| ∧ Even (n - k)))) ∧
    (∀ k : ℤ, 2 ≤ k →
      ((∃ v ∈ wt k, v ≠ 0 ∧ L v = 0) ↔ ∀ n : ℤ, wt n ≠ ⊥ ↔ (k ≤ |n| ∧ Even (n - k)))) :=
  GL2RealKTypeClassification.main hM hadm hirr hinf

end S_AutomorphicForm_IsGL2RealKTypeModule_ne_bot_iff_parity_or_discreteSeries_of_irreducible
end P2MW
export P2MW.S_AutomorphicForm_IsGL2RealKTypeModule_ne_bot_iff_parity_or_discreteSeries_of_irreducible (solution)
