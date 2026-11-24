-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwistedModelAdmissibleCocycles
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwistedModelAdmissibleCocycles
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T19:16:45.885135+00:00
-- url     : https://prove2.me/theorems/d6785465-1f85-47df-bfe9-70b9eb7b9434
-- title:
--   Twisted Model Admissible Cocycles
-- statement:
--   Definitions and structural lemmas for Twisted Model Admissible Cocycles, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Models
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1)
structure Ob (k G : Type) [Field k] [Group G] where

  m : ℕ

  ρ : Representation k G (Fin m → k)
abbrev Vc (k : Type) [Field k] (m : ℕ) : Type := Fin m → k⸨X⸩
abbrev Lats (k : Type) [Field k] (n m : ℕ) : Type := ZMod n → Submodule k⟦X⟧ (Vc k m)
variable {k G : Type} [Field k] [Group G]
def IsHom (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) : Prop := ∀ g x, f (A.ρ g x) = B.ρ g (f x)
@[reducible] def chr (χ : G →* kˣ) : Ob k G where
  m := 1
  ρ :=
    { toFun := fun g => (χ g : k) • LinearMap.id
      map_one' := by ext; simp
      map_mul' := fun g h => by ext; simp [mul_smul, Module.End.mul_eq_comp, mul_assoc, mul_comm, mul_left_comm] }
structure DFun {l : ℕ} (R : RingPG k l) (n : ℕ) (G : Type) [Group G] where

  Obj : Ob k G → Prop

  obj_sub : ∀ A B f, IsHom A B f → Function.Injective f → Obj B → Obj A

  obj_quot : ∀ A B f, IsHom A B f → Function.Surjective f → Obj A → Obj B

  obj_sum : ∀ A B C i j, IsHom A C i → IsHom B C j → Function.Surjective (i.coprod j) → Obj A → Obj B → Obj C

  obj_one : Obj (chr 1)

  D : ∀ A : Ob k G, ModPG R n (Vc k A.m)

  map : ∀ A B : Ob k G, ((Fin A.m → k) →ₗ[k] (Fin B.m → k)) → ZMod n → (Vc k A.m →ₗ[k⸨X⸩] Vc k B.m)

  map_φ : ∀ A B f, Obj A → Obj B → IsHom A B f → ∀ i x, map A B f i ((D A).φ i x) = (D B).φ i (map A B f (i - 1) x)

  map_γ : ∀ A B f, Obj A → Obj B → IsHom A B f → ∀ i x, map A B f i ((D A).γ i x) = (D B).γ i (map A B f i x)

  map_id : ∀ A, Obj A → ∀ i, map A A LinearMap.id i = LinearMap.id

  map_comp : ∀ A B C f g, Obj A → Obj B → Obj C → IsHom A B f → IsHom B C g →
    ∀ i, map A C (g ∘ₗ f) i = map B C g i ∘ₗ map A B f i

  map_add : ∀ A B f g, Obj A → Obj B → IsHom A B f → IsHom A B g →
    ∀ i x, map A B (f + g) i x = map A B f i x + map A B g i x

  map_smul : ∀ A B f (c : k), Obj A → Obj B → IsHom A B f → ∀ i x, map A B (c • f) i x = c • map A B f i x

  map_inj : ∀ A B f, Obj A → Obj B → IsHom A B f → Function.Injective f → ∀ i, Function.Injective (map A B f i)

  map_surj : ∀ A B f, Obj A → Obj B → IsHom A B f → Function.Surjective f → ∀ i, Function.Surjective (map A B f i)

  unit : ZMod n → Vc k 1

  unit_ne : ∀ i, unit i ≠ 0

  unit_φ : ∀ i, (D (chr 1)).φ i (unit (i - 1)) = unit i

  unit_γ : ∀ i, (D (chr 1)).γ i (unit i) = unit i

  fix : ∀ A, Obj A → ∀ x : ZMod n → Vc k A.m, (∀ i, (D A).φ i (x (i - 1)) = x i) → (∀ i, (D A).γ i (x i) = x i) →
    ∃ f, IsHom (chr 1) A f ∧ ∀ i, map (chr 1) A f i (unit i) = x i
variable {l n : ℕ} {R : RingPG k l}
def DFun.push (F : DFun R n G) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n A.m) :
    Lats k n B.m := fun i => (N i).map ((F.map A B f i).restrictScalars k⟦X⟧)
def DFun.pre (F : DFun R n G) (A B : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n B.m) :
    Lats k n A.m := fun i => (N i).comap ((F.map A B f i).restrictScalars k⟦X⟧)
def IsModel (F : DFun R n G) (Base : ∀ A : Ob k G, Lats k n A.m → Prop) (A : Ob k G) (N : Lats k n A.m) : Prop :=
  ∃ (B : Ob k G) (Nb : Lats k n B.m) (A₁ : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k))
    (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)), Base B Nb ∧ IsHom A₁ B j ∧ Function.Injective j ∧
      IsHom A₁ A p ∧ Function.Surjective p ∧ N = F.push A₁ A p (F.pre A₁ B j Nb)
def ABC {m : ℕ} (D : ModPG R n (Vc k m)) (w w' : ZMod n → ℤ) (N : Lats k n m) : Prop :=
  (∀ i, IsLat (N i)) ∧ CondAB D.φ w w' N ∧ ∀ i, CondC (D.γ i) (N i)
def EPoly {m : ℕ} (g : Vc k m →ₗ[k] Vc k m) (N : Submodule k⟦X⟧ (Vc k m)) (s : ℤ) : Prop :=
  ∃ f : Polynomial k, f.eval 0 ≠ 0 ∧ ∀ x ∈ N, nab g (Polynomial.aeval (nab g) f x) ∈ sh s N
def resCount (U : Multiset ℤ) (w : ℤ) (x : k) : ℕ :=
  open Classical in Multiset.card (U.filter fun u => ((u - w : ℤ) : k) = x)
def refSum (T : Ob k G) (ω : G →* kˣ) (t : ℕ) :
    Representation k G ((Fin T.m → k) × (Fin t → (Fin 1 → k))) :=
  T.ρ.prod (piRep fun e : Fin t => (chr (ω ^ (-(e.val : ℤ)))).ρ)
structure ModTh (F : DFun R n G) {r : ℕ} (Dt : TopData n r) where

  T : Ob k G

  T_m : T.m = r

  ω : G →* kˣ

  ω_ne : ∀ e : ℕ, 0 < e → e + 1 < l → ω ^ e ≠ 1

  Base : ∀ A : Ob k G, Lats k n A.m → Prop

  base_obj : ∀ A N, Base A N → F.Obj A

  base_abc : ∀ A N, Base A N → ABC (F.D A) Dt.w Dt.wst N

  base_sen : ∀ A N, Base A N → ∃ μ : ℕ, SameSS A.ρ (piRep fun _ : Fin μ => refSum T ω Dt.t) ∧
    ∀ i x, sen ((F.D A).γ i) (N i) x = μ * resCount (Dt.Ut i) (Dt.w i) x

  base_sum : ∀ A N B N', Base A N → Base B N' → ∃ C i j, IsHom A C i ∧ IsHom B C j ∧
    Function.Bijective (i.coprod j) ∧ Base C (fun a => F.push A C i N a ⊔ F.push B C j N' a)

  base_e : Dt.T1 l → Dt.T3 l → ∀ A N, Base A N → ∀ i, Dt.ty i = LType.Bd →
    EPoly ((F.D A).γ i) (N i) (Dt.wst i + 1)

  Nstd : Lats k n T.m

  std_model : IsModel F Base T Nstd

  std_sen : ∀ i x, sen ((F.D T).γ i) (Nstd i) x = resCount (Dt.U i) (Dt.w i) x

  Nχ : ℤ → Lats k n 1

  χ_obj : ∀ e : ℤ, -1 ≤ e → e < Dt.t → F.Obj (chr (ω ^ (-e)))

  χ_lat : ∀ e : ℤ, -1 ≤ e → e < Dt.t → ∀ i, IsLat (Nχ e i) ∧ CondC ((F.D (chr (ω ^ (-e)))).γ i) (Nχ e i) ∧
    pull ((F.D (chr (ω ^ (-e)))).φ i) (Nχ e (i - 1)) = sh e (Nχ e i) ∧
    ∀ x, sen ((F.D (chr (ω ^ (-e)))).γ i) (Nχ e i) x = resCount {e} 0 x

  χ_model : ∀ e : ℤ, 0 ≤ e → e < Dt.t → IsModel F Base (chr (ω ^ (-e))) (Nχ e)

  χ_zero : ∀ i, Nχ 0 i = Submodule.span k⟦X⟧ {F.unit i}
abbrev ModTh.Model {F : DFun R n G} {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m) :
    Prop := IsModel F M.Base A N
def IsExt (A E : Ob k G) (z : G → Fin A.m → k) : Prop :=
  E.m = A.m + 1 ∧ ∃ (a : (Fin A.m → k) →ₗ[k] (Fin E.m → k)) (e : Fin E.m → k), IsHom A E a ∧ Function.Injective a ∧
    e ∉ LinearMap.range a ∧ ∀ g, E.ρ g e = e + a (z g)
def ModTh.twistedModelAdmissibleCocycles {F : DFun R n G} {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) :
    Set (G → Fin A.m → k) := {z | ∃ E N, IsExt A E z ∧ M.Model E N}
def cob (A : Ob k G) : Submodule k (G → Fin A.m → k) :=
  LinearMap.range (LinearMap.pi fun g : G => A.ρ g - LinearMap.id)
def InZZ {m r : ℕ} (D : ModPG R n (Vc k m)) (Dt : TopData n r) (N : Lats k n m) (b g : ZMod n → Vc k m) : Prop :=
  ∀ i, D.γ i (b i) - b i = D.φ i (g (i - 1)) - g i ∧ g i ∈ sh 1 (N i) ∧
    (Dt.ty i = LType.G → b i ∈ sh (-Dt.w i) (N i)) ∧
    (Dt.ty i = LType.Bd → b i ∈ sh (-Dt.wst i) (pull (D.φ i) (N (i - 1))) ∧
      ∃ x ∈ N i, g i - (D.γ i x - x) ∈ sh (Dt.wst i + 2) (N i))
def herrB {m : ℕ} (D : ModPG R n (Vc k m)) : Submodule k ((ZMod n → Vc k m) × (ZMod n → Vc k m)) :=
  LinearMap.range
    (LinearMap.prod
      (LinearMap.pi fun i => D.φ i ∘ₗ (LinearMap.proj (i - 1) : (ZMod n → Vc k m) →ₗ[k] Vc k m) - LinearMap.proj i)
      (LinearMap.pi fun i => D.γ i ∘ₗ (LinearMap.proj i : (ZMod n → Vc k m) →ₗ[k] Vc k m) - LinearMap.proj i))
theorem const_smul_mem_lat {m : ℕ} (N : Submodule k⟦X⟧ (Vc k m)) (c : k) {x : Vc k m} (hx : x ∈ N) : c • x ∈ N :=
  N.smul_of_tower_mem c hx
def pairSpace {m r : ℕ} (D : ModPG R n (Vc k m)) (Dt : TopData n r) (N : Lats k n m) :
    Submodule k ((ZMod n → Vc k m) × (ZMod n → Vc k m)) where
  carrier := {p | InZZ D Dt N p.1 p.2}
  zero_mem' := fun i => ⟨by simp, Submodule.zero_mem _, fun _ => Submodule.zero_mem _,
    fun _ => ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩⟩
  add_mem' := fun {p q} hp hq i => by
    obtain ⟨a0, a1, a2, a3⟩ := hp i
    obtain ⟨b0, b1, b2, b3⟩ := hq i
    refine ⟨?_, Submodule.add_mem _ a1 b1, fun h => Submodule.add_mem _ (a2 h) (b2 h), fun h => ?_⟩
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]
      rw [add_sub_add_comm, add_sub_add_comm, a0, b0]
    · obtain ⟨c1, x, hx, c2⟩ := a3 h
      obtain ⟨d1, y, hy, d2⟩ := b3 h
      refine ⟨Submodule.add_mem _ c1 d1, x + y, Submodule.add_mem _ hx hy, ?_⟩
      have := Submodule.add_mem _ c2 d2
      simp only [Prod.snd_add, Pi.add_apply, map_add]
      rwa [add_sub_add_comm (D.γ i x), add_sub_add_comm]
  smul_mem' := fun c p hp i => by
    obtain ⟨a0, a1, a2, a3⟩ := hp i
    refine ⟨?_, const_smul_mem_lat _ c a1, fun h => const_smul_mem_lat _ c (a2 h), fun h => ?_⟩
    · simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul]
      rw [← smul_sub, ← smul_sub, a0]
    · obtain ⟨c1, x, hx, c2⟩ := a3 h
      refine ⟨const_smul_mem_lat _ c c1, c • x, const_smul_mem_lat _ c hx, ?_⟩
      have := const_smul_mem_lat _ c c2
      simp only [Prod.smul_snd, Pi.smul_apply, map_smul]
      rwa [← smul_sub, ← smul_sub]
def herrD {m : ℕ} (D : ModPG R n (Vc k m)) :
    (ZMod n → Vc k m) →ₗ[k] ((ZMod n → Vc k m) × (ZMod n → Vc k m)) :=
  LinearMap.prod
    (LinearMap.pi fun i => D.φ i ∘ₗ (LinearMap.proj (i - 1) : (ZMod n → Vc k m) →ₗ[k] Vc k m) - LinearMap.proj i)
    (LinearMap.pi fun i => D.γ i ∘ₗ (LinearMap.proj i : (ZMod n → Vc k m) →ₗ[k] Vc k m) - LinearMap.proj i)
theorem herrD_apply {m : ℕ} (D : ModPG R n (Vc k m)) (x : ZMod n → Vc k m) :
    herrD D x = (fun i => D.φ i (x (i - 1)) - x i, fun i => D.γ i (x i) - x i) := rfl
def latB {m : ℕ} (D : ModPG R n (Vc k m)) (N : Lats k n m) :
    Submodule k ((ZMod n → Vc k m) × (ZMod n → Vc k m)) :=
  (Submodule.pi Set.univ fun i => (N i).restrictScalars k).map (herrD D)
abbrev PairQuot {m r : ℕ} (D : ModPG R n (Vc k m)) (Dt : TopData n r) (N : Lats k n m) : Type :=
  ↥(pairSpace D Dt N) ⧸ (latB D N).submoduleOf (pairSpace D Dt N)
def maxModel (F : DFun R n G) (Base : ∀ A : Ob k G, Lats k n A.m → Prop) (A : Ob k G) : Lats k n A.m :=
  fun i => ⨆ N : {N : Lats k n A.m // IsModel F Base A N}, N.1 i
structure ModData (k G : Type) [Field k] [Group G] (n : ℕ) where

  T : Ob k G

  ω : G →* kˣ

  Base : ∀ A : Ob k G, Lats k n A.m → Prop

  Nstd : Lats k n T.m

  Nχ : ℤ → Lats k n 1
namespace Law
variable (F : DFun R n G) {r : ℕ} (Dt : TopData n r) (Y : ModData k G n)
def OmegaNe (l : ℕ) (ω : G →* kˣ) : Prop := ∀ e : ℕ, 0 < e → e + 1 < l → ω ^ e ≠ 1
def BaseObj : Prop := ∀ A N, Y.Base A N → F.Obj A
def BaseABC : Prop := ∀ A N, Y.Base A N → ABC (F.D A) Dt.w Dt.wst N
def BaseSen : Prop := ∀ A N, Y.Base A N → ∃ μ : ℕ, SameSS A.ρ (piRep fun _ : Fin μ => refSum Y.T Y.ω Dt.t) ∧
  ∀ i x, sen ((F.D A).γ i) (N i) x = μ * resCount (Dt.Ut i) (Dt.w i) x
def BaseSum : Prop := ∀ A N B N', Y.Base A N → Y.Base B N' → ∃ C i j, IsHom A C i ∧ IsHom B C j ∧
  Function.Bijective (i.coprod j) ∧ Y.Base C (fun a => F.push A C i N a ⊔ F.push B C j N' a)
def BaseE : Prop := Dt.T1 l → Dt.T3 l → ∀ A N, Y.Base A N → ∀ i, Dt.ty i = LType.Bd →
  EPoly ((F.D A).γ i) (N i) (Dt.wst i + 1)
def Std : Prop := Y.T.m = r ∧ IsModel F Y.Base Y.T Y.Nstd ∧
  ∀ i x, sen ((F.D Y.T).γ i) (Y.Nstd i) x = resCount (Dt.U i) (Dt.w i) x
def CharLat : Prop := ∀ e : ℤ, -1 ≤ e → e < Dt.t → F.Obj (chr (Y.ω ^ (-e))) ∧
  ∀ i, IsLat (Y.Nχ e i) ∧ CondC ((F.D (chr (Y.ω ^ (-e)))).γ i) (Y.Nχ e i) ∧
    pull ((F.D (chr (Y.ω ^ (-e)))).φ i) (Y.Nχ e (i - 1)) = sh e (Y.Nχ e i) ∧
    ∀ x, sen ((F.D (chr (Y.ω ^ (-e)))).γ i) (Y.Nχ e i) x = resCount {e} 0 x
def CharModel : Prop := (∀ e : ℤ, 0 ≤ e → e < Dt.t → IsModel F Y.Base (chr (Y.ω ^ (-e))) (Y.Nχ e)) ∧
  ∀ i, Y.Nχ 0 i = Submodule.span k⟦X⟧ {F.unit i}
def All : Prop := OmegaNe l Y.ω ∧ BaseObj F Y ∧ BaseABC F Dt Y ∧ BaseSen F Dt Y ∧ BaseSum F Y ∧ BaseE F Dt Y ∧
  Std F Dt Y ∧ CharLat F Dt Y ∧ CharModel F Dt Y
end Law
@[reducible] def ModTh.data {F : DFun R n G} {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) : ModData k G n :=
  ⟨M.T, M.ω, M.Base, M.Nstd, M.Nχ⟩
@[reducible] def ModTh.ofLaws {F : DFun R n G} {r : ℕ} {Dt : TopData n r} (Y : ModData k G n)
    (h : Law.All F Dt Y) : ModTh F Dt where
  T := Y.T
  T_m := h.2.2.2.2.2.2.1.1
  ω := Y.ω
  ω_ne := h.1
  Base := Y.Base
  base_obj := h.2.1
  base_abc := h.2.2.1
  base_sen := h.2.2.2.1
  base_sum := h.2.2.2.2.1
  base_e := h.2.2.2.2.2.1
  Nstd := Y.Nstd
  std_model := h.2.2.2.2.2.2.1.2.1
  std_sen := h.2.2.2.2.2.2.1.2.2
  Nχ := Y.Nχ
  χ_obj e h1 h2 := (h.2.2.2.2.2.2.2.1 e h1 h2).1
  χ_lat e h1 h2 := (h.2.2.2.2.2.2.2.1 e h1 h2).2
  χ_model := h.2.2.2.2.2.2.2.2.1
  χ_zero := h.2.2.2.2.2.2.2.2.2
example : resCount ({3, 5, 5} : Multiset ℤ) 1 (4 : ℚ) = 2 := by
  rw [resCount, show ({3, 5, 5} : Multiset ℤ) = {3} + ({5} + {5}) from rfl]
  simp only [Multiset.filter_add, Multiset.filter_singleton, Multiset.card_add]
  norm_num
example : cob (chr (1 : G →* kˣ)) = ⊥ := by
  rw [cob, LinearMap.range_eq_bot]
  ext x g j
  simp
example (hγ : Function.Bijective R.γ) : herrD (Inh.powMod R hγ n 1) (fun _ _ => 1) = 0 := by
  rw [herrD_apply]
  refine Prod.ext (funext fun i => funext fun j => ?_) (funext fun i => funext fun j => ?_)
  · exact sub_eq_zero.2 (map_one R.φ)
  · exact sub_eq_zero.2 (map_one R.γ)
end GlobalTheory.Models


