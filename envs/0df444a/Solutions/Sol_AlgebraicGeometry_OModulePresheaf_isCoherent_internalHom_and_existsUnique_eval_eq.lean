-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.isCoherent_internalHom_and_existsUnique_eval_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/bf906aad-d6a2-5914-91f3-9634ba909034

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace InternalHomCohSol

section Algebra

variable {B : Type*} [CommRing B] {P : Type*} [AddCommGroup P] [Module B P]

theorem span_range_pow_eq_top {ι : Type*} (h : ι → B) (hspan : Ideal.span (Set.range h) = ⊤)
    (N : ι → ℕ) : Ideal.span (Set.range fun i => h i ^ N i) = ⊤ := by
  rw [← Ideal.radical_eq_top, eq_top_iff, ← hspan, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨N i, Ideal.subset_span ⟨i, rfl⟩⟩

theorem eq_zero_of_forall_pow_smul_eq_zero {ι : Type*} (h : ι → B) (hspan : Ideal.span (Set.range h) = ⊤)
    (z : P) (hz : ∀ i, ∃ n : ℕ, h i ^ n • z = 0) : z = 0 := by
  choose N hN using hz
  have htop := span_range_pow_eq_top h hspan N
  have hle : Ideal.span (Set.range fun i => h i ^ N i) ≤ Ideal.torsionOf B P z := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact (Ideal.mem_torsionOf_iff z _).mpr (hN i)
  rw [htop, top_le_iff, Ideal.torsionOf_eq_top_iff] at hle
  exact hle

variable {ι : Type*} [Fintype ι] (h : ι → B)
variable {Pl : ι → Type*} [∀ i, AddCommGroup (Pl i)] [∀ i, Module B (Pl i)]
variable (ρ : ∀ i, P →ₗ[B] Pl i)

theorem exists_pow_smul_eq_of_isLocalizedModule [hρ : ∀ i, IsLocalizedModule (Submonoid.powers (h i)) (ρ i)]
    (y : ∀ i, Pl i) : ∃ (n : ℕ) (m : ι → P), ∀ i, h i ^ n • y i = ρ i (m i) := by
  have hi : ∀ i, ∃ (n : ℕ) (m : P), h i ^ n • y i = ρ i m := by
    intro i
    obtain ⟨⟨m, s, k, hk⟩, hs⟩ := (hρ i).surj (y i)
    refine ⟨k, m, ?_⟩
    rw [← hs, Submonoid.smul_def]
    exact congrArg (· • y i) hk
  choose n m hm using hi
  refine ⟨∑ i, n i, fun i => h i ^ (∑ j, n j - n i) • m i, fun i => ?_⟩
  have hle : n i ≤ ∑ j, n j := Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  rw [map_smul, ← hm i, smul_smul, ← pow_add, Nat.sub_add_cancel hle]

theorem exists_forall_eq_of_compatible (hspan : Ideal.span (Set.range h) = ⊤)
    [hρ : ∀ i, IsLocalizedModule (Submonoid.powers (h i)) (ρ i)]
    {Pll : ι → ι → Type*} [∀ i j, AddCommGroup (Pll i j)] [∀ i j, Module B (Pll i j)]
    (ρ2 : ∀ i j, P →ₗ[B] Pll i j)
    (hρ2 : ∀ (i j) (m : P), ρ2 i j m = 0 → ∃ n : ℕ, (h i * h j) ^ n • m = 0)
    (l : ∀ i j, Pl i →ₗ[B] Pll i j) (r : ∀ i j, Pl j →ₗ[B] Pll i j)
    (hl : ∀ i j, l i j ∘ₗ ρ i = ρ2 i j) (hr : ∀ i j, r i j ∘ₗ ρ j = ρ2 i j)
    (y : ∀ i, Pl i) (hy : ∀ i j, l i j (y i) = r i j (y j)) :
    ∃ z : P, ∀ i, ρ i z = y i := by
  classical

  obtain ⟨n, m, hm⟩ := exists_pow_smul_eq_of_isLocalizedModule h ρ y

  have hcomp : ∀ i j, ρ2 i j (h j ^ n • m i - h i ^ n • m j) = 0 := by
    intro i j
    have e1 : ρ2 i j (m i) = l i j (ρ i (m i)) := by rw [← hl i j]; rfl
    have e2 : ρ2 i j (m j) = r i j (ρ j (m j)) := by rw [← hr i j]; rfl
    rw [map_sub, map_smul, map_smul, e1, e2, ← hm i, ← hm j, map_smul, map_smul, hy i j, smul_smul,
      smul_smul, mul_comm, sub_self]

  choose K hK using fun p : ι × ι => hρ2 p.1 p.2 _ (hcomp p.1 p.2)
  set Kt : ℕ := ∑ p, K p with hKt
  have hKle : ∀ p : ι × ι, K p ≤ Kt := fun p =>
    Finset.single_le_sum (fun q _ => Nat.zero_le (K q)) (Finset.mem_univ p)
  have hkill : ∀ i j, (h i * h j) ^ Kt • (h j ^ n • m i - h i ^ n • m j) = 0 := by
    intro i j
    rw [← Nat.sub_add_cancel (hKle (i, j)), pow_add, mul_smul, hK (i, j), smul_zero]

  set m' : ι → P := fun i => h i ^ Kt • m i with hm'
  set N : ℕ := n + Kt with hN
  have hm'y : ∀ i, h i ^ N • y i = ρ i (m' i) := by
    intro i
    rw [hm', map_smul, ← hm i, smul_smul, ← pow_add, hN, add_comm]
  have hcross : ∀ i j, h j ^ N • m' i = h i ^ N • m' j := by
    intro i j
    have e := hkill i j
    rw [smul_sub, sub_eq_zero, smul_smul, smul_smul] at e
    rw [hm', smul_smul, smul_smul, hN]
    convert e using 2 <;> ring

  have h1 : (1 : B) ∈ Ideal.span (Set.range fun i => h i ^ N) := by
    rw [span_range_pow_eq_top h hspan fun _ => N]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp h1
  refine ⟨∑ i, a i • m' i, fun j => ?_⟩

  have key : h j ^ N • ρ j (∑ i, a i • m' i) = h j ^ N • y j := by
    rw [hm'y j, ← map_smul, Finset.smul_sum]
    congr 1
    calc ∑ i, h j ^ N • (a i • m' i) = ∑ i, a i • (h i ^ N • m' j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_comm, hcross i j]
      _ = (∑ i, a i • h i ^ N) • m' j := by rw [Finset.sum_smul]; simp only [smul_eq_mul, mul_smul]
      _ = m' j := by rw [ha, one_smul]
  have hu := (hρ j).map_units ⟨h j ^ N, N, rfl⟩
  rw [Module.End.isUnit_iff] at hu
  exact hu.1 key

end Algebra

section Datum

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

theorem bo_mul_le_left {U : V.Opens} (a b : Γ(V, U)) : V.basicOpen (a * b) ≤ V.basicOpen a :=
  (V.basicOpen_mul a b).le.trans inf_le_left

theorem bo_mul_le_right {U : V.Opens} (a b : Γ(V, U)) : V.basicOpen (a * b) ≤ V.basicOpen b :=
  (V.basicOpen_mul a b).le.trans inf_le_right

theorem basicOpen_res_of_le {U W : V.Opens} (hWU : W ≤ U) (g : Γ(V, U)) (hg : V.basicOpen g ≤ W) :
    V.basicOpen ((V.presheaf.map (homOfLE hWU).op).hom g) = V.basicOpen g := by
  rw [Scheme.basicOpen_res]
  exact inf_eq_right.mpr hg

theorem algebraMap_res_apply {U : V.Opens} {g g₂ : Γ(V, U)} (hle : V.basicOpen g₂ ≤ V.basicOpen g)
    (a : Γ(V, U)) :
    (V.presheaf.map (homOfLE hle).op).hom (algebraMap Γ(V, U) Γ(V, V.basicOpen g) a) =
      algebraMap Γ(V, U) Γ(V, V.basicOpen g₂) a := by
  show (V.presheaf.map (homOfLE hle).op).hom ((V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom a) =
    (V.presheaf.map (homOfLE (V.basicOpen_le g₂)).op).hom a
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]
  rfl

theorem algebraMap_basicOpen_apply {U : V.Opens} (g : Γ(V, U)) (a : Γ(V, U)) :
    algebraMap Γ(V, U) Γ(V, V.basicOpen g) a = (V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom a :=
  rfl

theorem isUnit_algebraMap_of_le (U : V.affineOpens) {g g₂ : Γ(V, U.1)}
    (hle : V.basicOpen g₂ ≤ V.basicOpen g) : IsUnit (algebraMap Γ(V, U.1) Γ(V, V.basicOpen g₂) g) := by
  haveI : IsLocalization.Away g Γ(V, V.basicOpen g) := U.2.isLocalization_basicOpen g
  have hu : IsUnit (algebraMap Γ(V, U.1) Γ(V, V.basicOpen g) g) := IsLocalization.Away.algebraMap_isUnit g
  have h := hu.map (V.presheaf.map (homOfLE hle).op).hom
  rwa [algebraMap_res_apply hle] at h

variable (F : OModulePresheaf π)

@[reducible] noncomputable def modBO (U : V.Opens) (f : Γ(V, U)) : Module Γ(V, U) (F.obj (V.basicOpen f)) :=
  Module.compHom (F.obj (V.basicOpen f)) (algebraMap Γ(V, U) Γ(V, V.basicOpen f))

theorem modBO_smul_def (U : V.Opens) (f : Γ(V, U)) (a : Γ(V, U)) (x : F.obj (V.basicOpen f)) :
    letI := modBO F U f
    a • x = algebraMap Γ(V, U) Γ(V, V.basicOpen f) a • x :=
  rfl

theorem isScalarTower_modBO (U : V.Opens) (f : Γ(V, U)) :
    letI := modBO F U f
    IsScalarTower Γ(V, U) Γ(V, V.basicOpen f) (F.obj (V.basicOpen f)) :=
  letI := modBO F U f
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

noncomputable def resBO (U : V.Opens) (f : Γ(V, U)) :
    letI := modBO F U f
    F.obj U →ₗ[Γ(V, U)] F.obj (V.basicOpen f) :=
  letI := modBO F U f
  { toFun := F.res (V.basicOpen_le f)
    map_add' := fun x y => map_add _ x y
    map_smul' := fun a x => F.res_smul (V.basicOpen_le f) a x }

theorem resBO_apply (U : V.Opens) (f : Γ(V, U)) (x : F.obj U) :
    letI := modBO F U f
    resBO F U f x = F.res (V.basicOpen_le f) x := rfl

theorem isLocalizedModule_resBO (hF : F.IsQuasicoherent) (U : V.affineOpens) (f : Γ(V, U.1)) :
    letI := modBO F U.1 f
    IsLocalizedModule (Submonoid.powers f) (resBO F U.1 f) := by
  letI := modBO F U.1 f
  haveI := isScalarTower_modBO F U.1 f
  haveI : IsLocalization.Away f Γ(V, V.basicOpen f) := U.2.isLocalization_basicOpen f
  obtain ⟨h1, h2⟩ := hF U f
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have hu : IsUnit (algebraMap Γ(V, U.1) Γ(V, V.basicOpen f) (f ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit f).pow n
    have := hu.smul_bijective (β := F.obj (V.basicOpen f))
    exact this
  · intro y
    obtain ⟨n, x, hx⟩ := h1 y
    exact ⟨⟨x, ⟨f ^ n, n, rfl⟩⟩, hx.symm⟩
  · intro x₁ x₂ h
    have h0 : F.res (V.basicOpen_le f) (x₁ - x₂) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr h
    obtain ⟨n, hn⟩ := h2 (x₁ - x₂) h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, ← sub_eq_zero, ← smul_sub]
    exact hn

theorem qcAt_of_isLocalizedModule (U : V.affineOpens) (f : Γ(V, U.1))
    (h : letI := modBO F U.1 f; IsLocalizedModule (Submonoid.powers f) (resBO F U.1 f)) :
    (∀ x : F.obj (V.basicOpen f), ∃ (n : ℕ) (y : F.obj U.1),
        F.res (V.basicOpen_le f) y = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) • x)
      ∧ (∀ y : F.obj U.1, F.res (V.basicOpen_le f) y = 0 → ∃ n : ℕ, (f ^ n : Γ(V, U.1)) • y = 0) := by
  letI := modBO F U.1 f
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨⟨y, ⟨s, n, rfl⟩⟩, hs⟩ := h.surj x
    exact ⟨n, y, hs.symm⟩
  · have h0 : resBO F U.1 f y = resBO F U.1 f 0 := by rw [map_zero]; exact hy
    obtain ⟨⟨s, n, rfl⟩, hs⟩ := h.exists_of_eq h0
    refine ⟨n, ?_⟩
    simpa [Submonoid.smul_def] using hs

noncomputable def resL (U : V.Opens) {g g₂ : Γ(V, U)} (hle : V.basicOpen g₂ ≤ V.basicOpen g) :
    letI := modBO F U g; letI := modBO F U g₂
    F.obj (V.basicOpen g) →ₗ[Γ(V, U)] F.obj (V.basicOpen g₂) :=
  letI := modBO F U g; letI := modBO F U g₂
  { toFun := F.res hle
    map_add' := fun x y => map_add _ x y
    map_smul' := fun a x => by
      show F.res hle (algebraMap Γ(V, U) Γ(V, V.basicOpen g) a • x) =
        algebraMap Γ(V, U) Γ(V, V.basicOpen g₂) a • F.res hle x
      rw [F.res_smul, algebraMap_res_apply hle] }

theorem resL_apply (U : V.Opens) {g g₂ : Γ(V, U)} (hle : V.basicOpen g₂ ≤ V.basicOpen g)
    (x : F.obj (V.basicOpen g)) :
    letI := modBO F U g; letI := modBO F U g₂
    resL F U hle x = F.res hle x := rfl

theorem map_units_of_le (U : V.affineOpens) {g g₂ : Γ(V, U.1)} (hle : V.basicOpen g₂ ≤ V.basicOpen g) :
    letI := modBO F U.1 g₂
    ∀ s : Submonoid.powers g,
      IsUnit (algebraMap Γ(V, U.1) (Module.End Γ(V, U.1) (F.obj (V.basicOpen g₂))) s) := by
  letI := modBO F U.1 g₂
  rintro ⟨s, n, rfl⟩
  rw [Module.End.isUnit_iff]
  have hu : IsUnit (algebraMap Γ(V, U.1) Γ(V, V.basicOpen g₂) (g ^ n)) := by
    rw [map_pow]; exact (isUnit_algebraMap_of_le U hle).pow n
  have := hu.smul_bijective (β := F.obj (V.basicOpen g₂))
  exact this

variable {F}

abbrev BelowIdx (U : V.affineOpens) (W : V.Opens) : Type u :=
  {g : (V.presheaf.obj (op U.1) : CommRingCat.{u}) // V.basicOpen g ≤ W}

theorem span_res_eq_top (U W : V.affineOpens) (hWU : W.1 ≤ U.1) :
    Ideal.span (Set.range fun g : BelowIdx U W.1 => (V.presheaf.map (homOfLE hWU).op).hom g.1) = ⊤ := by
  rw [← W.2.self_le_iSup_basicOpen_iff]
  intro x hx
  obtain ⟨g, hgW, hxg⟩ := U.2.exists_basicOpen_le ⟨x, hx⟩ (hWU hx)
  refine Opens.mem_iSup.mpr ⟨⟨_, ⟨⟨g, hgW⟩, rfl⟩⟩, ?_⟩
  show x ∈ V.basicOpen ((V.presheaf.map (homOfLE hWU).op).hom g)
  rw [basicOpen_res_of_le hWU g hgW]
  exact hxg

theorem eq_zero_of_forall_res_eq_zero (G : OModulePresheaf π) (hG : G.IsQuasicoherent) (W : V.affineOpens)
    {ι : Type*} (k : ι → Γ(V, W.1)) (hk : Ideal.span (Set.range k) = ⊤) (y : G.obj W.1)
    (hy : ∀ i, ∃ (O : V.Opens) (_ : V.basicOpen (k i) ≤ O) (h₂ : O ≤ W.1), G.res h₂ y = 0) : y = 0 := by
  refine eq_zero_of_forall_pow_smul_eq_zero k hk y fun i => ?_
  obtain ⟨O, h₁, h₂, h0⟩ := hy i
  have h0' : G.res (V.basicOpen_le (k i)) y = 0 := by
    have e : G.res (V.basicOpen_le (k i)) y = G.res h₁ (G.res h₂ y) := (G.res_res h₁ h₂ y).symm
    rw [e, h0, map_zero]
  exact (hG W (k i)).2 y h0'

end Datum

section Phi

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F G : OModulePresheaf π) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) (U : V.affineOpens)
  (f₀ : F.obj U.1 →ₗ[Γ(V, U.1)] G.obj U.1)

noncomputable def Phi (g : Γ(V, U.1)) :
    letI := modBO F U.1 g; letI := modBO G U.1 g
    F.obj (V.basicOpen g) →ₗ[Γ(V, U.1)] G.obj (V.basicOpen g) :=
  letI := modBO F U.1 g; letI := modBO G U.1 g
  haveI := isLocalizedModule_resBO F hF U g
  haveI := isLocalizedModule_resBO G hG U g
  IsLocalizedModule.map (Submonoid.powers g) (resBO F U.1 g) (resBO G U.1 g) f₀

include hF hG in
theorem Phi_res (g : Γ(V, U.1)) (x : F.obj U.1) :
    Phi F G hF hG U f₀ g (F.res (V.basicOpen_le g) x) = G.res (V.basicOpen_le g) (f₀ x) := by
  letI := modBO F U.1 g; letI := modBO G U.1 g
  haveI := isLocalizedModule_resBO F hF U g
  haveI := isLocalizedModule_resBO G hG U g
  exact IsLocalizedModule.map_apply (Submonoid.powers g) (resBO F U.1 g) (resBO G U.1 g) f₀ x

theorem Phi_smul (g : Γ(V, U.1)) (c : Γ(V, V.basicOpen g)) (x : F.obj (V.basicOpen g)) :
    Phi F G hF hG U f₀ g (c • x) = c • Phi F G hF hG U f₀ g x := by
  letI := modBO F U.1 g; letI := modBO G U.1 g
  haveI := isScalarTower_modBO F U.1 g; haveI := isScalarTower_modBO G U.1 g
  haveI : IsLocalization (Submonoid.powers g) Γ(V, V.basicOpen g) := U.2.isLocalization_basicOpen g
  exact (IsLocalization.linearMap_compatibleSMul (Submonoid.powers g) Γ(V, V.basicOpen g)
    (F.obj (V.basicOpen g)) (G.obj (V.basicOpen g))).map_smul (Phi F G hF hG U f₀ g) c x

theorem res_Phi {g g₂ : Γ(V, U.1)} (hle : V.basicOpen g₂ ≤ V.basicOpen g) (x : F.obj (V.basicOpen g)) :
    G.res hle (Phi F G hF hG U f₀ g x) = Phi F G hF hG U f₀ g₂ (F.res hle x) := by
  letI := modBO F U.1 g; letI := modBO G U.1 g; letI := modBO F U.1 g₂; letI := modBO G U.1 g₂
  haveI := isLocalizedModule_resBO F hF U g
  have key : (resL G U.1 hle) ∘ₗ (Phi F G hF hG U f₀ g) = (Phi F G hF hG U f₀ g₂) ∘ₗ (resL F U.1 hle) := by
    apply IsLocalizedModule.ext (Submonoid.powers g) (resBO F U.1 g) (map_units_of_le G U hle)
    refine LinearMap.ext fun y => ?_
    show G.res hle (Phi F G hF hG U f₀ g (F.res (V.basicOpen_le g) y)) =
      Phi F G hF hG U f₀ g₂ (F.res hle (F.res (V.basicOpen_le g) y))
    rw [Phi_res, G.res_res, F.res_res]
    exact (Phi_res F G hF hG U f₀ g₂ y).symm
  exact LinearMap.congr_fun key x

end Phi

section Inj

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}

open AlgebraicGeometry.OModulePresheaf

abbrev boBelow (U : V.affineOpens) (g : (V.presheaf.obj (op U.1) : CommRingCat.{u})) : AffBelow U.1 :=
  ⟨⟨V.basicOpen g, U.2.basicOpen g⟩, V.basicOpen_le g⟩

theorem apply_basicOpen_eq_zero (hF : F.IsQuasicoherent) (U : V.affineOpens)
    (φ : (internalHom F G).obj U.1) (h0 : ∀ x, φ.1 ⟨U, le_rfl⟩ x = 0)
    (g : (V.presheaf.obj (op U.1) : CommRingCat.{u})) (x : F.obj (V.basicOpen g)) :
    φ.1 (boBelow U g) x = 0 := by
  obtain ⟨n, y, hy⟩ := (hF U g).1 x
  have h1 : φ.1 (boBelow U g) (F.res (V.basicOpen_le g) y) = 0 := by
    rw [φ.2.2 (boBelow U g) ⟨U, le_rfl⟩ (V.basicOpen_le g) y, h0, map_zero]
  rw [hy, φ.2.1] at h1
  haveI : IsLocalization.Away g Γ(V, V.basicOpen g) := U.2.isLocalization_basicOpen g
  have hu : IsUnit ((V.presheaf.map (homOfLE (V.basicOpen_le g)).op).hom (g ^ n)) := by
    rw [← algebraMap_basicOpen_apply, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit g).pow n
  exact hu.smul_left_cancel.mp (h1.trans (smul_zero _).symm)

theorem eq_zero_of_eval_eq_zero (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) (U : V.affineOpens)
    (φ : (internalHom F G).obj U.1) (h0 : ∀ x, φ.1 ⟨U, le_rfl⟩ x = 0) : φ = 0 := by
  refine Subtype.ext (funext fun W => LinearMap.ext fun x => ?_)
  show φ.1 W x = 0
  refine eq_zero_of_forall_res_eq_zero G hG W.1
    (fun g : BelowIdx U W.1.1 => (V.presheaf.map (homOfLE W.2).op).hom g.1)
    (span_res_eq_top U W.1 W.2) _ fun g => ?_
  refine ⟨V.basicOpen g.1, le_of_eq (basicOpen_res_of_le W.2 g.1 g.2), g.2, ?_⟩
  rw [← φ.2.2 ⟨⟨V.basicOpen g.1, U.2.basicOpen g.1⟩, g.2.trans W.2⟩ W g.2 x]
  exact apply_basicOpen_eq_zero hF U φ h0 g.1 _

end Inj

section Exist

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}
variable (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) (U : V.affineOpens)
  (f₀ : F.obj U.1 →ₗ[Γ(V, U.1)] G.obj U.1)

open AlgebraicGeometry.OModulePresheaf

def IsGlued (W : AffBelow U.1) (x : F.obj W.1.1) (z : G.obj W.1.1) : Prop :=
  ∀ g : BelowIdx U W.1.1, G.res g.2 z = Phi F G hF hG U f₀ g.1 (F.res g.2 x)

include hG in
theorem isGlued_unique {W : AffBelow U.1} {x : F.obj W.1.1} {z z' : G.obj W.1.1}
    (hz : IsGlued hF hG U f₀ W x z) (hz' : IsGlued hF hG U f₀ W x z') : z = z' := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_res_eq_zero G hG W.1 _ (span_res_eq_top U W.1 W.2) _ fun g => ?_
  exact ⟨V.basicOpen g.1, le_of_eq (basicOpen_res_of_le W.2 g.1 g.2), g.2,
    by rw [map_sub, hz g, hz' g, sub_self]⟩

theorem isGlued_add {W : AffBelow U.1} {x x' : F.obj W.1.1} {z z' : G.obj W.1.1}
    (hz : IsGlued hF hG U f₀ W x z) (hz' : IsGlued hF hG U f₀ W x' z') :
    IsGlued hF hG U f₀ W (x + x') (z + z') :=
  fun g => by rw [map_add, map_add, map_add, hz g, hz' g]

theorem isGlued_smul {W : AffBelow U.1} {x : F.obj W.1.1} {z : G.obj W.1.1} (b : Γ(V, W.1.1))
    (hz : IsGlued hF hG U f₀ W x z) : IsGlued hF hG U f₀ W (b • x) (b • z) :=
  fun g => by rw [G.res_smul, F.res_smul, Phi_smul, hz g]

theorem isGlued_res {W₁ W₂ : AffBelow U.1} (h : W₂.1.1 ≤ W₁.1.1) {x : F.obj W₁.1.1} {z : G.obj W₁.1.1}
    (hz : IsGlued hF hG U f₀ W₁ x z) : IsGlued hF hG U f₀ W₂ (F.res h x) (G.res h z) :=
  fun g => by
    rw [G.res_res, F.res_res]
    exact hz ⟨g.1, g.2.trans h⟩

theorem isGlued_eval (x : F.obj U.1) : IsGlued hF hG U f₀ ⟨U, le_rfl⟩ x (f₀ x) :=
  fun g => (Phi_res F G hF hG U f₀ g.1 x).symm

theorem exists_isGlued (W : AffBelow U.1) (x : F.obj W.1.1) :
    ∃ z : G.obj W.1.1, IsGlued hF hG U f₀ W x z := by
  classical

  let k : BelowIdx U W.1.1 → Γ(V, W.1.1) := fun g => (V.presheaf.map (homOfLE W.2).op).hom g.1
  have hk : Ideal.span (Set.range k) = ⊤ := span_res_eq_top U W.1 W.2
  obtain ⟨T₀, hT₀, h1⟩ := Submodule.mem_span_finite_of_mem_span ((Ideal.eq_top_iff_one _).mp hk)
  have hsel' : ∀ b : ↥T₀, ∃ g : BelowIdx U W.1.1, k g = b := fun b => hT₀ b.2
  choose sel hsel using hsel'
  have hrange : Set.range (fun i : ↥T₀ => (i : Γ(V, W.1.1))) = ↑T₀ :=
    Set.ext fun b => ⟨fun ⟨i, hi⟩ => hi ▸ i.2, fun hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have hspanT : Ideal.span (Set.range fun i : ↥T₀ => (i : Γ(V, W.1.1))) = ⊤ := by
    rw [hrange, Ideal.eq_top_iff_one]; exact h1

  letI instPl : ∀ i : ↥T₀, Module Γ(V, W.1.1) (G.obj (V.basicOpen (i : Γ(V, W.1.1)))) :=
    fun i => modBO G W.1.1 (i : Γ(V, W.1.1))
  letI instPll : ∀ i j : ↥T₀, Module Γ(V, W.1.1) (G.obj (V.basicOpen ((i : Γ(V, W.1.1)) * (j : Γ(V, W.1.1))))) :=
    fun i j => modBO G W.1.1 ((i : Γ(V, W.1.1)) * (j : Γ(V, W.1.1)))
  haveI hρ : ∀ i : ↥T₀, IsLocalizedModule (Submonoid.powers (i : Γ(V, W.1.1)))
      (resBO G W.1.1 (i : Γ(V, W.1.1))) := fun i => isLocalizedModule_resBO G hG W.1 i

  have e : ∀ i : ↥T₀, V.basicOpen (i : Γ(V, W.1.1)) ≤ V.basicOpen (sel i).1 := fun i =>
    le_of_eq (by rw [← hsel i]; exact basicOpen_res_of_le W.2 (sel i).1 (sel i).2)
  have e' : ∀ i : ↥T₀, V.basicOpen (sel i).1 ≤ V.basicOpen (i : Γ(V, W.1.1)) := fun i =>
    le_of_eq (by rw [← hsel i]; exact (basicOpen_res_of_le W.2 (sel i).1 (sel i).2).symm)

  let y : ∀ i : ↥T₀, G.obj (V.basicOpen (i : Γ(V, W.1.1))) := fun i =>
    G.res (e i) (Phi F G hF hG U f₀ (sel i).1 (F.res (sel i).2 x))

  have hy : ∀ i j : ↥T₀, resL G W.1.1 (bo_mul_le_left (i : Γ(V, W.1.1)) j) (y i) =
      resL G W.1.1 (bo_mul_le_right (i : Γ(V, W.1.1)) j) (y j) := by
    intro i j
    have h3 : V.basicOpen ((i : Γ(V, W.1.1)) * (j : Γ(V, W.1.1))) ≤ V.basicOpen ((sel i).1 * (sel j).1) := by
      rw [Scheme.basicOpen_mul, Scheme.basicOpen_mul]; exact inf_le_inf (e i) (e j)
    have lhs : resL G W.1.1 (bo_mul_le_left (i : Γ(V, W.1.1)) j) (y i) =
        G.res h3 (Phi F G hF hG U f₀ ((sel i).1 * (sel j).1)
          (F.res ((bo_mul_le_left _ _).trans (sel i).2) x)) := by
      show G.res _ (G.res (e i) (Phi F G hF hG U f₀ (sel i).1 (F.res (sel i).2 x))) = _
      rw [G.res_res, ← G.res_res h3 (bo_mul_le_left (sel i).1 (sel j).1),
        res_Phi F G hF hG U f₀ (bo_mul_le_left (sel i).1 (sel j).1), F.res_res]
    have rhs : resL G W.1.1 (bo_mul_le_right (i : Γ(V, W.1.1)) j) (y j) =
        G.res h3 (Phi F G hF hG U f₀ ((sel i).1 * (sel j).1)
          (F.res ((bo_mul_le_right _ _).trans (sel j).2) x)) := by
      show G.res _ (G.res (e j) (Phi F G hF hG U f₀ (sel j).1 (F.res (sel j).2 x))) = _
      rw [G.res_res, ← G.res_res h3 (bo_mul_le_right (sel i).1 (sel j).1),
        res_Phi F G hF hG U f₀ (bo_mul_le_right (sel i).1 (sel j).1), F.res_res]
    rw [lhs, rhs]

  obtain ⟨z, hz⟩ := exists_forall_eq_of_compatible (P := G.obj W.1.1)
    (fun i : ↥T₀ => (i : Γ(V, W.1.1))) (fun i => resBO G W.1.1 (i : Γ(V, W.1.1))) hspanT
    (Pll := fun i j => G.obj (V.basicOpen ((i : Γ(V, W.1.1)) * (j : Γ(V, W.1.1)))))
    (fun i j => resBO G W.1.1 ((i : Γ(V, W.1.1)) * (j : Γ(V, W.1.1))))
    (fun i j m hm => (hG W.1 ((i : Γ(V, W.1.1)) * (j : Γ(V, W.1.1)))).2 m hm)
    (fun i j => resL G W.1.1 (bo_mul_le_left (i : Γ(V, W.1.1)) j))
    (fun i j => resL G W.1.1 (bo_mul_le_right (i : Γ(V, W.1.1)) j))
    (fun i j => LinearMap.ext fun m => G.res_res _ _ m)
    (fun i j => LinearMap.ext fun m => G.res_res _ _ m)
    y hy
  refine ⟨z, fun g => ?_⟩

  have hspan' : Ideal.span (Set.range fun i : ↥T₀ =>
      (V.presheaf.map (homOfLE g.2).op).hom (i : Γ(V, W.1.1))) = ⊤ := by
    have h := congrArg (Ideal.map (V.presheaf.map (homOfLE g.2).op).hom) hspanT
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    exact h
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_res_eq_zero G hG ⟨V.basicOpen g.1, U.2.basicOpen g.1⟩ _ hspan' _ fun i => ?_
  have h5 : V.basicOpen ((V.presheaf.map (homOfLE g.2).op).hom (i : Γ(V, W.1.1))) ≤
      V.basicOpen (g.1 * (sel i).1) := by
    rw [Scheme.basicOpen_res, Scheme.basicOpen_mul]
    exact inf_le_inf le_rfl (e i)
  have h6 : V.basicOpen (g.1 * (sel i).1) ≤ V.basicOpen (i : Γ(V, W.1.1)) :=
    (bo_mul_le_right g.1 (sel i).1).trans (e' i)
  refine ⟨V.basicOpen (g.1 * (sel i).1), h5, bo_mul_le_left g.1 (sel i).1, ?_⟩
  rw [map_sub, sub_eq_zero, G.res_res, res_Phi F G hF hG U f₀ (bo_mul_le_left g.1 (sel i).1), F.res_res,
    ← G.res_res h6 (V.basicOpen_le (i : Γ(V, W.1.1)))]
  have hzi : G.res (V.basicOpen_le (i : Γ(V, W.1.1))) z = y i := hz i
  rw [hzi]
  show G.res h6 (G.res (e i) (Phi F G hF hG U f₀ (sel i).1 (F.res (sel i).2 x))) = _
  rw [G.res_res, res_Phi F G hF hG U f₀ (h6.trans (e i)), F.res_res]

noncomputable def glueFun (W : AffBelow U.1) (x : F.obj W.1.1) : G.obj W.1.1 :=
  Classical.choose (exists_isGlued hF hG U f₀ W x)

theorem isGlued_glueFun (W : AffBelow U.1) (x : F.obj W.1.1) :
    IsGlued hF hG U f₀ W x (glueFun hF hG U f₀ W x) :=
  Classical.choose_spec (exists_isGlued hF hG U f₀ W x)

theorem glueFun_eq {W : AffBelow U.1} {x : F.obj W.1.1} {z : G.obj W.1.1} (hz : IsGlued hF hG U f₀ W x z) :
    glueFun hF hG U f₀ W x = z :=
  isGlued_unique hF hG U f₀ (isGlued_glueFun hF hG U f₀ W x) hz

noncomputable def glueLin (W : AffBelow U.1) : F.obj W.1.1 →ₗ[R] G.obj W.1.1 where
  toFun := glueFun hF hG U f₀ W
  map_add' x x' :=
    glueFun_eq hF hG U f₀ (isGlued_add hF hG U f₀ (isGlued_glueFun hF hG U f₀ W x)
      (isGlued_glueFun hF hG U f₀ W x'))
  map_smul' r x := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π W.1.1
    have hx : r • x = algebraMap R Γ(V, W.1.1) r • x := (algebraMap_smul Γ(V, W.1.1) r x).symm
    have hz : r • glueFun hF hG U f₀ W x = algebraMap R Γ(V, W.1.1) r • glueFun hF hG U f₀ W x :=
      (algebraMap_smul Γ(V, W.1.1) r _).symm
    rw [RingHom.id_apply, hx, hz]
    exact glueFun_eq hF hG U f₀ (isGlued_smul hF hG U f₀ _ (isGlued_glueFun hF hG U f₀ W x))

theorem glueLin_apply (W : AffBelow U.1) (x : F.obj W.1.1) :
    glueLin hF hG U f₀ W x = glueFun hF hG U f₀ W x := rfl

noncomputable def glueFamily : (internalHom F G).obj U.1 :=
  ⟨fun W => glueLin hF hG U f₀ W,
    ⟨fun W a x => glueFun_eq hF hG U f₀ (isGlued_smul hF hG U f₀ a (isGlued_glueFun hF hG U f₀ W x)),
      fun _ W' h x => glueFun_eq hF hG U f₀ (isGlued_res hF hG U f₀ h (isGlued_glueFun hF hG U f₀ W' x))⟩⟩

theorem glueFamily_apply (W : AffBelow U.1) (x : F.obj W.1.1) :
    (glueFamily hF hG U f₀).1 W x = glueFun hF hG U f₀ W x := rfl

include hF hG in

theorem existsUnique_eval_eq :
    ∃! φ : (internalHom F G).obj U.1, ∀ x : F.obj U.1, φ.1 ⟨U, le_rfl⟩ x = f₀ x := by
  refine ⟨glueFamily hF hG U f₀, fun x => glueFun_eq hF hG U f₀ (isGlued_eval hF hG U f₀ x), fun φ hφ => ?_⟩
  rw [← sub_eq_zero]
  refine eq_zero_of_eval_eq_zero hF hG U _ fun x => ?_
  show φ.1 ⟨U, le_rfl⟩ x - glueFun hF hG U f₀ ⟨U, le_rfl⟩ x = 0
  rw [hφ x, glueFun_eq hF hG U f₀ (isGlued_eval hF hG U f₀ x), sub_self]

end Exist

section CohQcoh

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F G : OModulePresheaf π}

open AlgebraicGeometry.OModulePresheaf

theorem sections_map_refl_apply (W : V.Opens) (a : Γ(V, W)) :
    (V.presheaf.map (homOfLE (le_refl W)).op).hom a = a := by
  rw [Subsingleton.elim (homOfLE (le_refl W)).op (𝟙 (op W)), V.presheaf.map_id]
  rfl

theorem isNoetherian_linearMap (A : Type u) [CommRing A] [IsNoetherianRing A] (M N : Type u)
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module.Finite A M] [Module.Finite A N] :
    IsNoetherian A (M →ₗ[A] N) := by
  obtain ⟨r, p, hp⟩ := Module.Finite.exists_fin' A M
  let E : (M →ₗ[A] N) →ₗ[A] (Fin r → N) :=
    { toFun := fun g i => g (p (Pi.single i 1))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hexp : ∀ (g : M →ₗ[A] N) (x : Fin r → A), g (p x) = ∑ i, x i • g (p (Pi.single i 1)) := by
    intro g x
    conv_lhs => rw [← Finset.univ_sum_single x]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show (Pi.single i (x i) : Fin r → A) = x i • Pi.single i 1 by
      rw [← Pi.single_smul', smul_eq_mul, mul_one], map_smul, map_smul]
  refine isNoetherian_of_injective E fun g₁ g₂ h => LinearMap.ext fun m => ?_
  obtain ⟨x, rfl⟩ := hp m
  rw [hexp g₁, hexp g₂]
  exact Finset.sum_congr rfl fun i _ => by
    rw [show g₁ (p (Pi.single i 1)) = E g₁ i from rfl, h]; rfl

noncomputable def evalU (U : V.affineOpens) :
    (internalHom F G).obj U.1 →ₗ[Γ(V, U.1)] (F.obj U.1 →ₗ[Γ(V, U.1)] G.obj U.1) where
  toFun φ :=
    { toFun := φ.1 ⟨U, le_rfl⟩
      map_add' := map_add _
      map_smul' := fun a x => φ.2.1 ⟨U, le_rfl⟩ a x }
  map_add' _ _ := LinearMap.ext fun _ => rfl
  map_smul' a φ := by
    refine LinearMap.ext fun x => ?_
    show (V.presheaf.map (homOfLE (le_refl U.1)).op).hom a • φ.1 ⟨U, le_rfl⟩ x = a • φ.1 ⟨U, le_rfl⟩ x
    rw [sections_map_refl_apply]

theorem evalU_apply (U : V.affineOpens) (φ : (internalHom F G).obj U.1) (x : F.obj U.1) :
    evalU U φ x = φ.1 ⟨U, le_rfl⟩ x := rfl

theorem evalU_injective (hFq : F.IsQuasicoherent) (hGq : G.IsQuasicoherent) (U : V.affineOpens) :
    Function.Injective (evalU (F := F) (G := G) U) := by
  intro φ ψ h
  rw [← sub_eq_zero]
  refine eq_zero_of_eval_eq_zero hFq hGq U _ fun x => ?_
  show φ.1 ⟨U, le_rfl⟩ x - ψ.1 ⟨U, le_rfl⟩ x = 0
  rw [sub_eq_zero]
  exact LinearMap.congr_fun h x

theorem evalU_bijective (hFq : F.IsQuasicoherent) (hGq : G.IsQuasicoherent) (U : V.affineOpens) :
    Function.Bijective (evalU (F := F) (G := G) U) := by
  refine ⟨evalU_injective hFq hGq U, fun f₀ => ?_⟩
  obtain ⟨φ, hφ, -⟩ := existsUnique_eval_eq hFq hGq U f₀
  exact ⟨φ, LinearMap.ext hφ⟩

theorem isCoherent_internalHom [IsLocallyNoetherian V] (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent)
    (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent) : (internalHom F G).IsCoherent := by
  intro U
  haveI : IsNoetherianRing Γ(V, U.1) := IsLocallyNoetherian.component_noetherian U
  haveI := hFc U; haveI := hGc U
  haveI := isNoetherian_linearMap Γ(V, U.1) (F.obj U.1) (G.obj U.1)
  exact Module.Finite.of_injective (evalU U) (evalU_injective hFq hGq U)

section QC

variable (hFq : F.IsQuasicoherent) (hGq : G.IsQuasicoherent) (U : V.affineOpens) (f : Γ(V, U.1))

abbrev Daff : V.affineOpens := ⟨V.basicOpen f, U.2.basicOpen f⟩

noncomputable def evalD :
    letI := modBO F U.1 f; letI := modBO G U.1 f; letI := modBO (internalHom F G) U.1 f
    (internalHom F G).obj (V.basicOpen f) →ₗ[Γ(V, U.1)] (F.obj (V.basicOpen f) →ₗ[Γ(V, U.1)] G.obj (V.basicOpen f)) :=
  letI := modBO F U.1 f; letI := modBO G U.1 f; letI := modBO (internalHom F G) U.1 f
  { toFun := fun φ =>
      { toFun := φ.1 ⟨Daff U f, le_rfl⟩
        map_add' := map_add _
        map_smul' := fun a x => φ.2.1 ⟨Daff U f, le_rfl⟩ (algebraMap Γ(V, U.1) Γ(V, V.basicOpen f) a) x }
    map_add' := fun _ _ => LinearMap.ext fun _ => rfl
    map_smul' := fun a φ => by
      refine LinearMap.ext fun x => ?_
      show (V.presheaf.map (homOfLE (le_refl (V.basicOpen f))).op).hom (algebraMap Γ(V, U.1) Γ(V, V.basicOpen f) a) •
          φ.1 ⟨Daff U f, le_rfl⟩ x =
        algebraMap Γ(V, U.1) Γ(V, V.basicOpen f) a • φ.1 ⟨Daff U f, le_rfl⟩ x
      rw [sections_map_refl_apply] }

theorem evalD_apply (φ : (internalHom F G).obj (V.basicOpen f)) (x : F.obj (V.basicOpen f)) :
    letI := modBO F U.1 f; letI := modBO G U.1 f; letI := modBO (internalHom F G) U.1 f
    evalD U f φ x = φ.1 ⟨Daff U f, le_rfl⟩ x := rfl

include hFq hGq in
theorem evalD_bijective :
    letI := modBO F U.1 f; letI := modBO G U.1 f; letI := modBO (internalHom F G) U.1 f
    Function.Bijective (evalD (F := F) (G := G) U f) := by
  letI := modBO F U.1 f; letI := modBO G U.1 f; letI := modBO (internalHom F G) U.1 f
  haveI := isScalarTower_modBO F U.1 f; haveI := isScalarTower_modBO G U.1 f
  haveI : IsLocalization (Submonoid.powers f) Γ(V, V.basicOpen f) := U.2.isLocalization_basicOpen f
  refine ⟨fun φ ψ h => ?_, fun h => ?_⟩
  · rw [← sub_eq_zero]
    refine eq_zero_of_eval_eq_zero hFq hGq (Daff U f) _ fun x => ?_
    show φ.1 ⟨Daff U f, le_rfl⟩ x - ψ.1 ⟨Daff U f, le_rfl⟩ x = 0
    rw [sub_eq_zero]
    exact LinearMap.congr_fun h x
  · obtain ⟨φ, hφ, -⟩ := existsUnique_eval_eq hFq hGq (Daff U f)
      (h.extendScalarsOfIsLocalization (Submonoid.powers f) Γ(V, V.basicOpen f))
    exact ⟨φ, LinearMap.ext hφ⟩

include hFq hGq in

theorem evalD_res (φ : (internalHom F G).obj U.1) :
    letI := modBO F U.1 f; letI := modBO G U.1 f; letI := modBO (internalHom F G) U.1 f
    haveI := isLocalizedModule_resBO F hFq U f; haveI := isLocalizedModule_resBO G hGq U f
    evalD U f ((internalHom F G).res (V.basicOpen_le f) φ) =
      IsLocalizedModule.map (Submonoid.powers f) (resBO F U.1 f) (resBO G U.1 f) (evalU U φ) := by
  letI := modBO F U.1 f; letI := modBO G U.1 f; letI := modBO (internalHom F G) U.1 f
  haveI := isLocalizedModule_resBO F hFq U f; haveI := isLocalizedModule_resBO G hGq U f
  apply IsLocalizedModule.ext (Submonoid.powers f) (resBO F U.1 f)
    (IsLocalizedModule.map_units (S := Submonoid.powers f) (resBO G U.1 f))
  rw [IsLocalizedModule.map_comp]
  refine LinearMap.ext fun x => ?_
  show φ.1 ⟨Daff U f, V.basicOpen_le f⟩ (F.res (V.basicOpen_le f) x) = G.res (V.basicOpen_le f) (φ.1 ⟨U, le_rfl⟩ x)
  exact φ.2.2 ⟨Daff U f, V.basicOpen_le f⟩ ⟨U, le_rfl⟩ (V.basicOpen_le f) x

include hFq hGq in

theorem isLocalizedModule_res_internalHom [IsLocallyNoetherian V] (hFc : F.IsCoherent) :
    letI := modBO (internalHom F G) U.1 f
    IsLocalizedModule (Submonoid.powers f) (resBO (internalHom F G) U.1 f) := by
  letI := modBO F U.1 f; letI := modBO G U.1 f; letI := modBO (internalHom F G) U.1 f
  haveI := isLocalizedModule_resBO F hFq U f; haveI := isLocalizedModule_resBO G hGq U f
  haveI : IsNoetherianRing Γ(V, U.1) := IsLocallyNoetherian.component_noetherian U
  haveI := hFc U
  haveI : Module.FinitePresentation Γ(V, U.1) (F.obj U.1) := Module.finitePresentation_of_finite _ _
  let e₁ : (internalHom F G).obj U.1 ≃ₗ[Γ(V, U.1)] (F.obj U.1 →ₗ[Γ(V, U.1)] G.obj U.1) :=
    LinearEquiv.ofBijective (evalU U) (evalU_bijective hFq hGq U)
  let e₂ : (internalHom F G).obj (V.basicOpen f) ≃ₗ[Γ(V, U.1)]
      (F.obj (V.basicOpen f) →ₗ[Γ(V, U.1)] G.obj (V.basicOpen f)) :=
    LinearEquiv.ofBijective (evalD U f) (evalD_bijective hFq hGq U f)
  let mapL := IsLocalizedModule.map (Submonoid.powers f) (resBO F U.1 f) (resBO G U.1 f)
  have h1 : IsLocalizedModule (Submonoid.powers f) (mapL ∘ₗ e₁.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f) mapL e₁
  have h2 : IsLocalizedModule (Submonoid.powers f) (e₂.symm.toLinearMap ∘ₗ (mapL ∘ₗ e₁.toLinearMap)) :=
    IsLocalizedModule.of_linearEquiv (Submonoid.powers f) (mapL ∘ₗ e₁.toLinearMap) e₂.symm
  have hEq : resBO (internalHom F G) U.1 f = e₂.symm.toLinearMap ∘ₗ (mapL ∘ₗ e₁.toLinearMap) := by
    refine LinearMap.ext fun φ => ?_
    show (internalHom F G).res (V.basicOpen_le f) φ = e₂.symm (mapL (e₁ φ))
    rw [eq_comm, LinearEquiv.symm_apply_eq]
    exact (evalD_res hFq hGq U f φ).symm
  rw [hEq]
  exact h2

end QC

theorem isQuasicoherent_internalHom [IsLocallyNoetherian V] (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent)
    (hGq : G.IsQuasicoherent) : (internalHom F G).IsQuasicoherent := fun U f =>
  qcAt_of_isLocalizedModule (internalHom F G) U f (isLocalizedModule_res_internalHom hFq hGq U f hFc)

end CohQcoh

theorem main {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R))
    [IsLocallyNoetherian V] (F G : OModulePresheaf π)
    (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent) :
    (OModulePresheaf.internalHom F G).IsCoherent ∧ (OModulePresheaf.internalHom F G).IsQuasicoherent ∧
      ∀ (U : V.affineOpens) (f : F.obj U.1 →ₗ[Γ(V, U.1)] G.obj U.1),
        ∃! φ : (OModulePresheaf.internalHom F G).obj U.1, ∀ x : F.obj U.1, φ.1 ⟨U, le_rfl⟩ x = f x :=
  ⟨isCoherent_internalHom hFc hFq hGc hGq, isQuasicoherent_internalHom hFc hFq hGq,
    fun U f => existsUnique_eval_eq hFq hGq U f⟩

end InternalHomCohSol

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) [IsLocallyNoetherian V]
    (F G : OModulePresheaf π)
    (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent) :
    (AlgebraicGeometry.OModulePresheaf.internalHom F G).IsCoherent ∧
      (AlgebraicGeometry.OModulePresheaf.internalHom F G).IsQuasicoherent ∧
      ∀ (U : V.affineOpens) (f : F.obj U.1 →ₗ[Γ(V, U.1)] G.obj U.1),
        ∃! φ : (AlgebraicGeometry.OModulePresheaf.internalHom F G).obj U.1,
          ∀ x : F.obj U.1, φ.1 ⟨U, le_rfl⟩ x = f x :=
  InternalHomCohSol.main π F G hFc hFq hGc hGq

end S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_isCoherent_internalHom_and_existsUnique_eval_eq (solution)
