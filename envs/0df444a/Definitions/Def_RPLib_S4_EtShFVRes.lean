-- Prove2me | Definitions.Def_RPLib_S4_EtShFVRes
-- name    : RPLib_S4_EtShFVRes
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T07:38:59.874189+00:00
-- url     : https://prove2.me/theorems/2b7dc295-455d-491f-8acb-577f1e19f313
-- title:
--   $F_V$ becomes constant on the Galois cover, so it is lisse
-- statement:
--   In the setting of the sheaf $F_V$ of a representation $\rho$ of the group $G$ of a Galois cover $\pi : Y \to X$: for $T$ etale over $Y$, restriction along the section $t \mapsto (t, t)$ is an isomorphism $F_V(T) \cong V_X(T)$ (a section of $F_V$ is determined by $s(1)$, and $\tau \mapsto \rho(\tau^{-1}) v$ glues to a section of $F_V$), naturally in $T$. Hence $\pi^* F_V \cong \pi^* V_X \cong V_Y$, and $F_V$ is lisse for finite $V$ since $\pi$ is surjective.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale sheaves of $\Lambda$-modules on Mathlib's small etale site, geometric points, stalks and the Galois action on generic stalks). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. Grothendieck, Revetements etales et groupe fondamental (SGA 1), Lecture Notes in Math. 224, Springer (1971), Expose V; J. S. Milne, Etale Cohomology, Princeton University Press (1980)

import Mathlib
import Definitions.Def_RPLib_S4_EtShFV

/-!
# S4-EtSheaves, part O10d-2(iii): `F_V` becomes constant on the Galois cover, so it is lisse

For `T` etale over `Y`, restriction along the section `ι 1` is an isomorphism `F_V(T) ≅ V_X(T)` (`eT`: a section of
`F_V` is determined by `s(1)`, and `τ ↦ ρ(τ⁻¹) v` glues to a section of `F_V`, `glueV`). These are natural in `T`, so
`π^* F_V ≅ π^* V_X ≅ V_Y` (`resIso`, `pullIso`), and `F_V` is lisse for finite `V` since `π` is surjective
(`isLisse_FV`).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtSheaves.TorSec

attribute [local instance] GalCover.ring GalCover.dom GalCover.alg GalCover.inj GalCover.fin
  GalCover.grp GalCover.fG GalCover.act GalCover.gal

variable {A : Type} [CommRing A] [IsDomain A] {C : GalCover A} (Λ : Type) [CommRing Λ] {V : Type}
  [AddCommGroup V] [Module Λ V] (ρ : Representation Λ C.G V)

/-- The family `τ ↦ ρ(τ⁻¹) v` glued over `T ×_X Y`. -/
def glueV (T : (SY C).Etale) (v : (VX A Λ V).obj.obj (op (tx T))) : (VX A Λ V).obj.obj (op (tp T)) :=
  (secEquiv Λ (VX A Λ V) T).symm (fun τ => ((th C Λ ρ τ).hom.app (op (tx T))).hom v)

theorem sec_glueV (T : (SY C).Etale) (v : (VX A Λ V).obj.obj (op (tx T))) (τ : C.G) :
    ((VX A Λ V).obj.map (sec T τ).op).hom (glueV Λ ρ T v) = ((th C Λ ρ τ).hom.app (op (tx T))).hom v :=
  congrFun ((secEquiv Λ (VX A Λ V) T).apply_symm_apply
    (fun τ => ((th C Λ ρ τ).hom.app (op (tx T))).hom v)) τ

theorem glueV_mem (T : (SY C).Etale) (v : (VX A Λ V).obj.obj (op (tx T))) :
    glueV Λ ρ T v ∈ eqSecSub (SV C Λ V) (aS C Λ V) (bS C Λ ρ) (tx T) :=
  (mem_FV_iff Λ ρ T _).2 fun σ τ => by
    rw [sec_glueV, sec_glueV, th_app_comp]

/-- **`F_V(T) ≅ V_X(T)`** for `T` etale over `Y`: restriction along `ι 1`. -/
def eT (T : (SY C).Etale) : (FV C Λ ρ).obj.obj (op (tx T)) ≃ₗ[Λ] (VX A Λ V).obj.obj (op (tx T)) where
  toFun s := ((VX A Λ V).obj.map (sec T 1).op).hom s.1
  map_add' s t := map_add _ s.1 t.1
  map_smul' c s := map_smul _ c s.1
  invFun v := ⟨glueV Λ ρ T v, glueV_mem Λ ρ T v⟩
  left_inv s := Subtype.ext ((secMap_bijective Λ (VX A Λ V) T).1 (funext fun τ => by
    change ((VX A Λ V).obj.map (sec T τ).op).hom (glueV Λ ρ T _) =
      ((VX A Λ V).obj.map (sec T τ).op).hom s.1
    rw [sec_glueV]
    have h := (mem_FV_iff Λ ρ T s.1).1 s.2 τ 1
    rw [one_mul] at h
    exact h.symm))
  right_inv v := by
    change ((VX A Λ V).obj.map (sec T 1).op).hom (glueV Λ ρ T v) = v
    rw [sec_glueV, th_app_one]

theorem eT_apply (T : (SY C).Etale) (s : (FV C Λ ρ).obj.obj (op (tx T))) :
    eT Λ ρ T s = ((VX A Λ V).obj.map (sec T 1).op).hom s.1 := rfl

theorem eT_naturality {T' T : (SY C).Etale} (h : T' ⟶ T) (s : (FV C Λ ρ).obj.obj (op (tx T))) :
    eT Λ ρ T' (((FV C Λ ρ).obj.map ((etComp (pr C)).map h).op).hom s) =
      ((VX A Λ V).obj.map ((etComp (pr C)).map h).op).hom (eT Λ ρ T s) := by
  let s1 : (VX A Λ V).obj.obj (op (tp T)) := s.1
  change ((VX A Λ V).obj.map (sec T' 1).op).hom (((VX A Λ V).obj.map
      ((etComp (pr C)).map ((etPull (pr C)).map ((etComp (pr C)).map h))).op).hom s1) =
    ((VX A Λ V).obj.map ((etComp (pr C)).map h).op).hom (((VX A Λ V).obj.map (sec T 1).op).hom s1)
  exact (map_map_apply (VX A Λ V) _ (sec T' 1) s1).trans
    ((congrArg (fun g => ((VX A Λ V).obj.map g.op).hom s1) (sec_naturality h 1)).trans
      (map_map_apply (VX A Λ V) (sec T 1) ((etComp (pr C)).map h) s1).symm)

/-- **`F_V|_Y ≅ V_X|_Y`.** -/
def resIso : (res (pr C) Λ).obj (FV C Λ ρ) ≅ (res (pr C) Λ).obj (VX A Λ V) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
    (fun T => (eT Λ ρ T.unop).toModuleIso) (by
      intro T T' h
      ext s
      exact eT_naturality Λ ρ h.unop s))

/-- **`π^* F_V ≅ V_Y`.** -/
def pullIso : (pull (pr C) Λ).obj (FV C Λ ρ) ≅ constSh Λ (SY C) (ModuleCat.of Λ V) :=
  (pullIsoRes (pr C) Λ).app _ ≪≫ resIso Λ ρ ≪≫ ((pullIsoRes (pr C) Λ).app _).symm ≪≫
    pullConst Λ (pr C) (ModuleCat.of Λ V)

/-- **`F_V` is lisse** for a finite `Λ`-module `V`. -/
theorem isLisse_FV [Module.Finite Λ V] : IsLisse Λ (FV C Λ ρ) := fun x => by
  obtain ⟨y, hy⟩ := pr_surjective C x
  exact ⟨MorphismProperty.Over.mk ⊤ (pr C) inferInstance, y, hy, ModuleCat.of Λ V, inferInstance,
    ⟨pullIso Λ ρ⟩⟩

end RamanujanPetersson.EtSheaves.TorSec


