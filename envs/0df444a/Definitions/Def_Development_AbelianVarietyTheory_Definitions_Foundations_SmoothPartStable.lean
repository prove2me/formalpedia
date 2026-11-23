-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:44.286056+00:00
-- url     : https://prove2.me/theorems/21e0fd5b-873a-4f5c-8500-169e9976b331
-- title:
--   Smooth Part Stable
-- statement:
--   Definitions and structural lemmas for Smooth Part Stable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SmoothPartStable.lean

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
namespace GlobalTheory.PRep
variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
def eig (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) : Submodule k V where
  carrier := {v | ∀ h : H, ρ (h : G) v = (χ h : k) • v}
  add_mem' := by
    intro a b ha hb h
    rw [map_add, ha h, hb h, smul_add]
  zero_mem' := by intro h; simp
  smul_mem' := by
    intro c v hv h
    rw [map_smul, hv h, smul_comm]
def fixed (ρ : Representation k G V) (H : Subgroup G) : Submodule k V := eig ρ H 1
def twKer (ρ : Representation k G V) (N : Subgroup G) (ψ : N →* kˣ) : Submodule k V :=
  Submodule.span k {w | ∃ (n : N) (v : V), w = ρ (n : G) v - (ψ n : k) • v}
abbrev TwJacquet (ρ : Representation k G V) (N : Subgroup G) (ψ : N →* kˣ) : Type := V ⧸ twKer ρ N ψ
abbrev Jacquet (ρ : Representation k G V) (N : Subgroup G) : Type := TwJacquet ρ N 1
theorem twKer_le_comap (ρ : Representation k G V) (N : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (N : Set G)) :
    twKer ρ N 1 ≤ (twKer ρ N 1).comap (ρ g) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨n, v, rfl⟩
  have hn : g * (n : G) * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.1 hg n).1 n.2
  refine Submodule.subset_span ⟨⟨_, hn⟩, ρ g v, ?_⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group
def jacquet (ρ : Representation k G V) (N : Subgroup G) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) : Representation k M (Jacquet ρ N) where
  toFun m := (twKer ρ N 1).mapQ (twKer ρ N 1) (ρ (s m)) (twKer_le_comap ρ N _ (hs m))
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp
def onFixed (ρ : Representation k G V) (N : Subgroup G) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) : Representation k M (fixed ρ N) where
  toFun m := (ρ (s m)).restrict (p := fixed ρ N) (q := fixed ρ N) (by
    intro v hv n
    have hn : (s m)⁻¹ * (n : G) * (s m)⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.1 (inv_mem (hs m)) n).1 n.2
    have h := hv ⟨_, hn⟩
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h ⊢
    conv_rhs => rw [← h]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group)
  map_one' := by
    ext v
    simp
  map_mul' a b := by
    ext v
    simp only [map_mul]
    rfl
section Top
variable [TopologicalSpace G]
def IsSmooth (ρ : Representation k G V) : Prop := ∀ v : V, IsOpen {g : G | ρ g v = v}
def IsAdmissible (ρ : Representation k G V) : Prop :=
  IsSmooth ρ ∧ ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) → FiniteDimensional k (fixed ρ K)
end Top
variable {W : Type} [AddCommGroup W] [Module k W]
def rightReg (k G W : Type) [Field k] [Group G] [AddCommGroup W] [Module k W] :
    Representation k G (G → W) where
  toFun g := LinearMap.funLeft k W (fun x => x * g)
  map_one' := by ext f x; simp [LinearMap.funLeft]
  map_mul' a b := by ext f x; simp [LinearMap.funLeft, mul_assoc]
def indSpace (H : Subgroup G) (σ : Representation k H W) : Submodule k (G → W) where
  carrier := {f | ∀ (h : H) (g : G), f (h * g) = σ h (f g)}
  add_mem' := by
    intro a b ha hb h g
    simp [ha h g, hb h g]
  zero_mem' := by intro h g; simp
  smul_mem' := by
    intro c f hf h g
    simp [hf h g]
def sub (ρ : Representation k G V) (U : Submodule k V) (hU : ∀ g, ∀ v ∈ U, ρ g v ∈ U) :
    Representation k G U where
  toFun g := (ρ g).restrict (hU g)
  map_one' := by ext v; simp
  map_mul' a b := by ext v; simp
def ind (H : Subgroup G) (σ : Representation k H W) : Representation k G (indSpace H σ) :=
  sub (rightReg k G W) (indSpace H σ) (by
    intro g f hf h x
    have := hf h (x * g)
    simpa [rightReg, LinearMap.funLeft, mul_assoc] using this)
section Top2
variable [TopologicalSpace G] [IsTopologicalGroup G]
def smoothPart (ρ : Representation k G V) : Submodule k V where
  carrier := {v | IsOpen {g : G | ρ g v = v}}
  add_mem' := by
    intro a b ha hb
    let T : Subgroup G :=
      { carrier := {g | ρ g (a + b) = a + b}
        mul_mem' := by intro x y hx hy; simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *; rw [hy, hx]
        one_mem' := by simp
        inv_mem' := by
          intro x hx
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← hx]
          rw [← Module.End.mul_apply, ← map_mul]; simp }
    refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((ha.inter hb).mem_nhds (by simp)) ?_)
    rintro g ⟨h1, h2⟩
    show ρ g (a + b) = a + b
    rw [map_add, h1, h2]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    by_cases hc : c = 0
    · simp [hc]
    · have : {g : G | ρ g (c • v) = c • v} = {g : G | ρ g v = v} := by
        ext g; simp [smul_right_inj hc]
      show IsOpen {g : G | ρ g (c • v) = c • v}
      rw [this]; exact hv
theorem smoothPart_stable (ρ : Representation k G V) (g : G) (v : V) (hv : v ∈ smoothPart ρ) :
    ρ g v ∈ smoothPart ρ := by
  have : {x : G | ρ x (ρ g v) = ρ g v} = (fun x => g⁻¹ * x * g) ⁻¹' {x : G | ρ x v = v} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, Module.End.mul_apply]
    constructor
    · intro h; rw [h, ← Module.End.mul_apply, ← map_mul]; simp
    · intro h
      have := congrArg (ρ g) h
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
  show IsOpen {x : G | ρ x (ρ g v) = ρ g v}
  rw [this]
  exact IsOpen.preimage (by fun_prop) hv
def smoothRep (ρ : Representation k G V) : Representation k G (smoothPart ρ) :=
  sub ρ (smoothPart ρ) (smoothPart_stable ρ)
def smInd (H : Subgroup G) (σ : Representation k H W) :
    Representation k G (smoothPart (ind H σ)) := smoothRep (ind H σ)
def cIndSpace (H : Subgroup G) (σ : Representation k H W) : Submodule k (smoothPart (ind H σ)) where
  carrier := {f | ∃ C : Set G, IsCompact C ∧ ∀ g, f.1.1 g ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, g = h * c}
  add_mem' := by
    rintro a b ⟨C, hC, ha⟩ ⟨D, hD, hb⟩
    refine ⟨C ∪ D, hC.union hD, fun g hg => ?_⟩
    by_cases h : a.1.1 g = 0
    · obtain ⟨h, hh, c, hc, e⟩ := hb g (by intro h'; apply hg; simp [h, h'])
      exact ⟨h, hh, c, Or.inr hc, e⟩
    · obtain ⟨h, hh, c, hc, e⟩ := ha g h
      exact ⟨h, hh, c, Or.inl hc, e⟩
  zero_mem' := ⟨∅, isCompact_empty, by simp⟩
  smul_mem' := by
    rintro c f ⟨C, hC, hf⟩
    exact ⟨C, hC, fun g hg => hf g (by intro h; apply hg; simp [h])⟩
def cInd (H : Subgroup G) (σ : Representation k H W) : Representation k G (cIndSpace H σ) :=
  sub (smInd H σ) (cIndSpace H σ) (by
    rintro g f ⟨C, hC, hf⟩
    refine ⟨(fun c => c * g⁻¹) '' C, hC.image (by fun_prop), fun x hx => ?_⟩
    obtain ⟨h, hh, c, hc, e⟩ := hf (x * g) hx
    exact ⟨h, hh, c * g⁻¹, ⟨c, hc, rfl⟩, by rw [← mul_assoc, ← e]; group⟩)
def IsSupercuspidal (ρ : Representation k G V) : Prop :=
  IsSmooth ρ ∧ ∀ (v : V) (l : Module.Dual k V), l ∈ smoothPart ρ.dual →
    ∃ C : Set G, IsCompact C ∧ ∀ g, l (ρ g v) ≠ 0 → ∃ z ∈ Subgroup.center G, ∃ c ∈ C, g = z * c
end Top2
end GlobalTheory.PRep


