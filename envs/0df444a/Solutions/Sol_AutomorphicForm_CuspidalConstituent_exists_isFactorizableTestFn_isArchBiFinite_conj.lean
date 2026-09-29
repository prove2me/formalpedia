-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/677291cc-05dc-5258-9568-6de121046230

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
p2m_open "AutomorphicForm.CuspidalConstituent P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.AutomorphicForm.CuspidalConstituent"

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsRightEquivariant typeSubmodule mem_typeSubmodule_of_isRightEquivariant comp_mul_mem_typeSubmodule comp_mul_mem_typeSubmodule_of_commute ArchRepAt rowIsometryInclAt₀ commute_adelicArchGLInclAt_of_ne archTypeSubmoduleAt archDualTypeSubmoduleAt ArchTypeFamily archCutSubmodule archDualCutSubmodule mem_archCutSubmodule_iff mem_archDualCutSubmodule_iff IsArchBiFinite glFin_rowIsometryInclAt₀ AdelicGL2 finiteAdelicGL2Subgroup rowIsometrySubgroup₀ archEntries archEntries_apply IsArchTestFactor IsFinTestFactor IsFactorizableTestFn"
namespace CuspidalConstituent
namespace Conj
p2m_open "AutomorphicForm.CuspidalConstituent AutomorphicForm"

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.AutomorphicForm"

section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def rT (a : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun u x := u (x * a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def lT (a : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun u x := u (a * x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem rT_apply (a : G) (u : G → ℂ) (x : G) : rT a u x = u (x * a) := rfl
@[scoped simp] theorem lT_apply (a : G) (u : G → ℂ) (x : G) : lT a u x = u (a * x) := rfl

theorem rT_mul (a b : G) (u : G → ℂ) : rT (a * b) u = rT a (rT b u) := by
  funext x; simp [mul_assoc]

theorem lT_mem_typeSubmodule {ι : H →* G} {ρ : Representation ℂ H W} {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) (a : G) : lT a f ∈ typeSubmodule ι ρ := by
  refine Submodule.span_induction (p := fun f _ => lT a f ∈ typeSubmodule ι ρ) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    have hS : IsRightEquivariant ι ρ ((lT a) ∘ₗ T) := by
      intro k' v' x
      show T (ρ k' v') (a * x) = T v' (a * (x * ι k'))
      rw [hT k' v' (a * x), mul_assoc]
    exact mem_typeSubmodule_of_isRightEquivariant hS v
  · show lT a 0 ∈ typeSubmodule ι ρ
    rw [map_zero]; exact (typeSubmodule ι ρ).zero_mem
  · intro u₁ u₂ _ _ hu hw
    show lT a (u₁ + u₂) ∈ typeSubmodule ι ρ
    rw [map_add]; exact (typeSubmodule ι ρ).add_mem hu hw
  · intro c u₁ _ hu
    show lT a (c • u₁) ∈ typeSubmodule ι ρ
    rw [map_smul]; exact (typeSubmodule ι ρ).smul_mem c hu

theorem rT_mem_typeSubmodule_of_commute {ι : H →* G} {ρ : Representation ℂ H W} {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) (g : G) (hg : ∀ k : H, Commute g (ι k)) : rT g f ∈ typeSubmodule ι ρ :=
  comp_mul_mem_typeSubmodule_of_commute hf g hg

theorem rT_mem_typeSubmodule_self {ι : H →* G} {ρ : Representation ℂ H W} {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) (k : H) : rT (ι k) f ∈ typeSubmodule ι ρ :=
  comp_mul_mem_typeSubmodule hf k

end TypePiece

section Adelic

open NumberField IsDedekindDomain NumberField.AdelicLevel

variable (F : Type) [Field F] [NumberField F]

theorem map_mem_iSup_of_forall {M : Type*} [AddCommGroup M] [Module ℂ M] {ι₀ : Type*}
    (Λ : M →ₗ[ℂ] M) (S : ι₀ → Submodule ℂ M) (h : ∀ i, ∀ u ∈ S i, Λ u ∈ S i) {u : M}
    (hu : u ∈ ⨆ i, S i) : Λ u ∈ ⨆ i, S i := by
  have hle : (⨆ i, S i) ≤ (⨆ i, S i).comap Λ :=
    iSup_le fun i => fun v hv => Submodule.mem_comap.mpr (le_iSup S i (h i v hv))
  exact hle hu

theorem commute_of_glArch_eq_one_of_glFin_eq_one {a b : AdelicGL2 (𝓞 F) F}
    (ha : glArch (𝓞 F) F a = 1) (hb : glFin (𝓞 F) F b = 1) : Commute a b := by
  have h1 : glArch (𝓞 F) F (a * b) = glArch (𝓞 F) F (b * a) := by rw [map_mul, map_mul, ha, one_mul, mul_one]
  have h2 : glFin (𝓞 F) F (a * b) = glFin (𝓞 F) F (b * a) := by rw [map_mul, map_mul, hb, one_mul, mul_one]
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · show (((a * b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 =
      (((b * a : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1
    rw [← glArch_apply, ← glArch_apply, h1]
  · show (((a * b : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 =
      (((b * a : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2
    rw [← glFin_apply, ← glFin_apply, h2]

def StabilisesPieces (c : AdelicGL2 (𝓞 F) F) : Prop :=
  ∀ (w : InfinitePlace F) (τ : ArchRepAt F w),
    (∀ u ∈ archTypeSubmoduleAt F w τ, rT c u ∈ archTypeSubmoduleAt F w τ) ∧
    (∀ u ∈ archDualTypeSubmoduleAt F w τ, rT c u ∈ archDualTypeSubmoduleAt F w τ)

theorem rT_one_eq (u : AdelicGL2 (𝓞 F) F → ℂ) : rT (1 : AdelicGL2 (𝓞 F) F) u = u :=
  funext fun x => by rw [rT_apply, mul_one]

theorem stabilisesPieces_one : StabilisesPieces F 1 := fun w τ =>
  ⟨fun u hu => by rw [rT_one_eq]; exact hu, fun u hu => by rw [rT_one_eq]; exact hu⟩

theorem StabilisesPieces.mul {a b : AdelicGL2 (𝓞 F) F} (ha : StabilisesPieces F a) (hb : StabilisesPieces F b) :
    StabilisesPieces F (a * b) := fun w τ =>
  ⟨fun u hu => by rw [rT_mul]; exact (ha w τ).1 _ ((hb w τ).1 u hu),
   fun u hu => by rw [rT_mul]; exact (ha w τ).2 _ ((hb w τ).2 u hu)⟩

theorem stabilisesPieces_of_mem_finiteAdelic {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F) :
    StabilisesPieces F g := by
  have hc : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), Commute g (rowIsometryInclAt₀ F w k) :=
    fun w k => commute_of_glArch_eq_one_of_glFin_eq_one F hg (glFin_rowIsometryInclAt₀ F w k)
  intro w τ
  exact ⟨fun u hu => rT_mem_typeSubmodule_of_commute hu g (hc w),
    fun u hu => rT_mem_typeSubmodule_of_commute hu g (hc w)⟩

theorem stabilisesPieces_rowIsometryInclAt₀ (w' : InfinitePlace F) (k : rowIsometrySubgroup₀ w'.Completion) :
    StabilisesPieces F (rowIsometryInclAt₀ F w' k) := by
  intro w τ
  by_cases hw : w = w'
  · subst hw
    exact ⟨fun u hu => rT_mem_typeSubmodule_self hu k, fun u hu => rT_mem_typeSubmodule_self hu k⟩
  · have hc : ∀ k'' : rowIsometrySubgroup₀ w.Completion, Commute (rowIsometryInclAt₀ F w' k) (rowIsometryInclAt₀ F w k'') :=
      fun k'' => commute_adelicArchGLInclAt_of_ne F (fun h => hw h.symm) _ _
    exact ⟨fun u hu => rT_mem_typeSubmodule_of_commute hu _ hc, fun u hu => rT_mem_typeSubmodule_of_commute hu _ hc⟩

theorem stabilisesPieces_of_mem_iSup {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    StabilisesPieces F k ∧ glFin (𝓞 F) F k = 1 := by
  refine Subgroup.iSup_induction (fun w : InfinitePlace F => (rowIsometryInclAt₀ F w).range)
    (C := fun k => StabilisesPieces F k ∧ glFin (𝓞 F) F k = 1) hk ?_ ?_ ?_
  · rintro w _ ⟨k', rfl⟩
    exact ⟨stabilisesPieces_rowIsometryInclAt₀ F w k', glFin_rowIsometryInclAt₀ F w k'⟩
  · exact ⟨stabilisesPieces_one F, map_one _⟩
  · rintro a b ⟨ha, ha1⟩ ⟨hb, hb1⟩
    exact ⟨ha.mul F hb, by rw [map_mul, ha1, hb1, one_mul]⟩

theorem StabilisesPieces.rT_mem_archCutSubmodule {c : AdelicGL2 (𝓞 F) F} (hc : StabilisesPieces F c)
    (tys : ArchTypeFamily F) {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : u ∈ archCutSubmodule F tys) :
    rT c u ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hu ⊢
  exact fun w => map_mem_iSup_of_forall (rT c) _ (fun i v hv => (hc w (tys.rep w i)).1 v hv) (hu w)

theorem StabilisesPieces.rT_mem_archDualCutSubmodule {c : AdelicGL2 (𝓞 F) F} (hc : StabilisesPieces F c)
    (tys : ArchTypeFamily F) {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : u ∈ archDualCutSubmodule F tys) :
    rT c u ∈ archDualCutSubmodule F tys := by
  rw [mem_archDualCutSubmodule_iff] at hu ⊢
  exact fun w => map_mem_iSup_of_forall (rT c) _ (fun i v hv => (hc w (tys.rep w i)).2 v hv) (hu w)

theorem lT_mem_archCutSubmodule (a : AdelicGL2 (𝓞 F) F) (tys : ArchTypeFamily F)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : u ∈ archCutSubmodule F tys) : lT a u ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hu ⊢
  exact fun w => map_mem_iSup_of_forall (lT a) _ (fun i v hv => lT_mem_typeSubmodule hv a) (hu w)

theorem lT_mem_archDualCutSubmodule (a : AdelicGL2 (𝓞 F) F) (tys : ArchTypeFamily F)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : u ∈ archDualCutSubmodule F tys) : lT a u ∈ archDualCutSubmodule F tys := by
  rw [mem_archDualCutSubmodule_iff] at hu ⊢
  exact fun w => map_mem_iSup_of_forall (lT a) _ (fun i v hv => lT_mem_typeSubmodule hv a) (hu w)

omit [NumberField F] in
open scoped Classical in

theorem archEntries_conj (c a : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (c * a * c⁻¹) = fun i j => ∑ l, (∑ m, archEntries F c i m * archEntries F a m l) *
      archEntries F (c⁻¹) l j := by
  funext i j
  simp only [archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

open scoped Classical in

theorem isArchTestFactor_conj {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : IsArchTestFactor F fa)
    (c : GL (Fin 2) (InfiniteAdeleRing F)) : IsArchTestFactor F (fun a => fa (c * a * c⁻¹)) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa
  refine ⟨⟨fun E => Φ (fun i j => ∑ l, (∑ m, archEntries F c i m * E m l) * archEntries F (c⁻¹) l j), ?_, ?_⟩, ?_⟩
  · refine hΦ.comp ?_
    refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
    refine ContDiff.sum fun l _ => ContDiff.mul (ContDiff.sum fun m _ => ?_) contDiff_const
    exact contDiff_const.mul (contDiff_apply_apply ℝ (mixedEmbedding.mixedSpace F) m l)
  · intro a
    show fa (c * a * c⁻¹) = Φ _
    rw [hfaΦ, archEntries_conj]
  ·
    have heq : (fun a => fa (c * a * c⁻¹)) = fa ∘ ((Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹)) := by
      funext a; rfl
    rw [heq]
    exact hsupp.comp_homeomorph _

theorem isFinTestFactor_conj {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ} (hff : IsFinTestFactor F ff)
    (c : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : IsFinTestFactor F (fun b => ff (c * b * c⁻¹)) := by
  obtain ⟨hlc, hsupp⟩ := hff
  have heq : (fun b => ff (c * b * c⁻¹)) = ff ∘ ((Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹)) := by
    funext b; rfl
  rw [heq]
  exact ⟨hlc.comp_continuous (Homeomorph.continuous _), hsupp.comp_homeomorph _⟩

end Adelic

end AutomorphicForm.CuspidalConstituent.Conj
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.AutomorphicForm.CuspidalConstituent P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.AutomorphicForm.CuspidalConstituent.Conj"
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.AutomorphicForm.CuspidalConstituent"
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.AutomorphicForm.CuspidalConstituent P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj.AutomorphicForm.CuspidalConstituent.Conj"

open AutomorphicForm.CuspidalConstituent.Conj in

theorem solution
    (F : Type) [Field F] [NumberField F]
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F)
    (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F)
    (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f) :
    ∃ tys' : ArchTypeFamily F,
      IsFactorizableTestFn F (fun y => f ((g * k) * y * (g * k)⁻¹)) ∧
      IsArchBiFinite F tys' (fun y => f ((g * k) * y * (g * k)⁻¹)) := by
  classical
  generalize hc : g * k = c
  have hstab : StabilisesPieces F c⁻¹ := by
    rw [← hc, mul_inv_rev]
    exact (stabilisesPieces_of_mem_iSup F ((⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range).inv_mem hk)).1.mul F
      (stabilisesPieces_of_mem_finiteAdelic F ((finiteAdelicGL2Subgroup F).inv_mem hg))
  refine ⟨tys, ?_, ?_⟩
  ·
    obtain ⟨fa, ff, hfa, hff, hfact⟩ := hf
    refine ⟨fun a => fa (glArch (𝓞 F) F c * a * (glArch (𝓞 F) F c)⁻¹),
      fun b => ff (glFin (𝓞 F) F c * b * (glFin (𝓞 F) F c)⁻¹),
      isArchTestFactor_conj F hfa _, isFinTestFactor_conj F hff _, fun y => ?_⟩
    simp only [hfact, map_mul, map_inv]
  ·
    obtain ⟨hL, hR⟩ := hbf
    constructor
    · have heq : (fun x => (fun y => f (c * y * c⁻¹)) x⁻¹) = lT c (rT c⁻¹ (fun x => f x⁻¹)) := by
        funext x
        show f (c * x⁻¹ * c⁻¹) = f (c * x * c⁻¹)⁻¹
        congr 1; group
      show (fun x => (fun y => f (c * y * c⁻¹)) x⁻¹) ∈ archCutSubmodule F tys
      rw [heq]
      exact lT_mem_archCutSubmodule F c tys (hstab.rT_mem_archCutSubmodule F tys hL)
    · have heq : (fun y => f (c * y * c⁻¹)) = lT c (rT c⁻¹ f) := funext fun y => rfl
      rw [heq]
      exact lT_mem_archDualCutSubmodule F c tys (hstab.rT_mem_archDualCutSubmodule F tys hR)

end S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_conj (solution)
