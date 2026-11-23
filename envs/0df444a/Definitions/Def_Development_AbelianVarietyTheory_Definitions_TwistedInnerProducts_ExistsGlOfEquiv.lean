-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
-- name    : Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:20.415739+00:00
-- url     : https://prove2.me/theorems/8b7c1a52-c68f-4010-8235-5dfe1741e3ec
-- title:
--   Exists Gl Of Equiv
-- statement:
--   Definitions and structural lemmas for Exists Gl Of Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
namespace GlobalTheory.LatPair
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
abbrev Unif : Type _ := {q : 𝒪[k] // Irreducible q}
instance : Nonempty (Unif k) :=
  let ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  ⟨⟨q, hq⟩⟩
variable {k}
namespace Unif
variable (q : Unif k)
theorem ne_zero : ((q.1 : 𝒪[k]) : k) ≠ 0 := fun h => q.2.ne_zero (Subtype.ext h)
def unit : kˣ := Units.mk0 _ q.ne_zero
def inv : k := ((q.1 : 𝒪[k]) : k)⁻¹
theorem mem_max_iff {a : 𝒪[k]} : a ∈ maximalIdeal 𝒪[k] ↔ q.1 ∣ a := by
  rw [q.2.maximalIdeal_eq, Ideal.mem_span_singleton]
theorem mem_max : q.1 ∈ maximalIdeal 𝒪[k] := q.mem_max_iff.2 dvd_rfl
@[simp] theorem smul_inv_smul {n : Type*} (x : n → k) : q.1 • q.inv • x = x := by
  change ((q.1 : 𝒪[k]) : k) • q.inv • x = x
  rw [smul_smul, inv, mul_inv_cancel₀ q.ne_zero, one_smul]
@[simp] theorem inv_smul_smul {n : Type*} (x : n → k) : q.inv • q.1 • x = x := by
  rw [smul_comm, smul_inv_smul]
end Unif
variable (k) in

structure Pair (n : Type*) where

  lat : Submodule 𝒪[k] (n → k)
  isLat : lat.IsLattice k

  fn : lat →ₗ[𝒪[k]] 𝓀[k]
  fn_ne : fn ≠ 0
variable {n n' : Type*}
namespace Pair
def HasVal (P : Pair k n) (x : n → k) (a : 𝓀[k]) : Prop := ∃ h : x ∈ P.lat, P.fn ⟨x, h⟩ = a
variable {P Q : Pair k n} {x y e : n → k} {a b : 𝓀[k]}
theorem HasVal.mem (h : P.HasVal x a) : x ∈ P.lat := h.1
theorem HasVal.unique (h : P.HasVal x a) (h' : P.HasVal x b) : a = b := h.2.symm.trans h'.2
theorem hasVal_fn (P : Pair k n) (x : P.lat) : P.HasVal x (P.fn x) := ⟨x.2, rfl⟩
theorem mem_lat_iff : x ∈ P.lat ↔ ∃ a, P.HasVal x a := ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h⟩ => h.1⟩
theorem HasVal.add (h : P.HasVal x a) (h' : P.HasVal y b) : P.HasVal (x + y) (a + b) :=
  ⟨add_mem h.1 h'.1, by rw [← h.2, ← h'.2, ← map_add]; rfl⟩
theorem HasVal.sub (h : P.HasVal x a) (h' : P.HasVal y b) : P.HasVal (x - y) (a - b) :=
  ⟨sub_mem h.1 h'.1, by rw [← h.2, ← h'.2, ← map_sub]; rfl⟩
theorem HasVal.smul (h : P.HasVal x a) (s : 𝒪[k]) : P.HasVal (s • x) (residue 𝒪[k] s * a) :=
  ⟨P.lat.smul_mem s h.1, by
    rw [← h.2, ← ResidueField.algebraMap_eq, ← Algebra.smul_def, ← map_smul]; rfl⟩
theorem ext (h : ∀ x a, P.HasVal x a ↔ Q.HasVal x a) : P = Q := by
  obtain ⟨L, hL, f, hf⟩ := P
  obtain ⟨L', hL', f', hf'⟩ := Q
  have : L = L' := by
    ext x
    exact (mem_lat_iff (P := ⟨L, hL, f, hf⟩)).trans
      ((exists_congr (h x)).trans (mem_lat_iff (P := ⟨L', hL', f', hf'⟩)).symm)
  subst this
  have : f = f' := by
    ext x
    exact ((h x _).1 ⟨x.2, rfl⟩).2.symm
  subst this
  rfl
theorem exists_hasVal_one (P : Pair k n) : ∃ e, P.HasVal e 1 := by
  obtain ⟨x, hx⟩ : ∃ x, P.fn x ≠ 0 := by
    by_contra h
    push Not at h
    exact P.fn_ne (LinearMap.ext h)
  obtain ⟨s, hs⟩ := residue_surjective (R := 𝒪[k]) (P.fn x)⁻¹
  exact ⟨s • (x : n → k), by simpa [hs, inv_mul_cancel₀ hx] using (P.hasVal_fn x).smul s⟩
def ker (P : Pair k n) : Submodule 𝒪[k] (n → k) := (LinearMap.ker P.fn).map P.lat.subtype
theorem mem_ker : x ∈ P.ker ↔ P.HasVal x 0 :=
  ⟨fun ⟨y, hy, h⟩ => h ▸ ⟨y.2, hy⟩, fun ⟨h, h'⟩ => ⟨⟨x, h⟩, h', rfl⟩⟩
theorem smul_mem_ker {s : 𝒪[k]} (hs : s ∈ maximalIdeal 𝒪[k]) (hx : x ∈ P.lat) : s • x ∈ P.ker := by
  have := (P.hasVal_fn ⟨x, hx⟩).smul s
  rw [(residue_eq_zero_iff s).2 hs, zero_mul] at this
  exact mem_ker.2 this
theorem ker_isLat (P : Pair k n) : P.ker.IsLattice k := by
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  haveI := P.isLat
  refine ⟨?_, ?_⟩
  · haveI : IsNoetherian 𝒪[k] P.lat := inferInstance
    exact (IsNoetherian.noetherian _).map _
  · rw [eq_top_iff, ← P.isLat.span_eq_top, Submodule.span_le]
    intro x hx
    rw [← q.inv_smul_smul x]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (smul_mem_ker q.mem_max hx))
def vec (P : Pair k n) : n → k := P.exists_hasVal_one.choose
theorem hasVal_vec (P : Pair k n) : P.HasVal P.vec 1 := P.exists_hasVal_one.choose_spec
theorem hasVal_iff (he : P.HasVal e 1) :
    P.HasVal x a ↔ ∃ s : 𝒪[k], residue 𝒪[k] s = a ∧ x - s • e ∈ P.ker := by
  constructor
  · intro h
    obtain ⟨s, rfl⟩ := residue_surjective (R := 𝒪[k]) a
    exact ⟨s, rfl, mem_ker.2 (by simpa using h.sub (he.smul s))⟩
  · rintro ⟨s, rfl, h⟩
    simpa using (mem_ker.1 h).add (he.smul s)
theorem hasVal_one_iff (he : P.HasVal e 1) : P.HasVal x 1 ↔ x - e ∈ P.ker :=
  ⟨fun h => mem_ker.2 (by simpa using h.sub he), fun h => by simpa using (mem_ker.1 h).add he⟩
theorem sub_vec_mem (he : P.HasVal e 1) : e - P.vec ∈ P.ker := (hasVal_one_iff P.hasVal_vec).1 he
theorem ext_ker (hk : P.ker = Q.ker) (he : P.HasVal e 1) (he' : Q.HasVal e 1) : P = Q :=
  ext fun _ _ => by rw [hasVal_iff he, hasVal_iff he', hk]
end Pair
structure IsGlue (L : Submodule 𝒪[k] (n → k)) (e : n → k) : Prop where
  isLat : L.IsLattice k
  not_mem : e ∉ L
  smul_mem : ∀ s ∈ maximalIdeal 𝒪[k], s • e ∈ L
theorem isGlue_iff (q : Unif k) {L : Submodule 𝒪[k] (n → k)} {e : n → k} :
    IsGlue L e ↔ L.IsLattice k ∧ e ∉ L ∧ q.1 • e ∈ L := by
  refine ⟨fun h => ⟨h.1, h.2, h.3 _ q.mem_max⟩, fun h => ⟨h.1, h.2.1, fun s hs => ?_⟩⟩
  obtain ⟨t, rfl⟩ := q.mem_max_iff.1 hs
  rw [mul_comm, mul_smul]
  exact L.smul_mem _ h.2.2
theorem Pair.isGlue {P : Pair k n} {e : n → k} (he : P.HasVal e 1) : IsGlue P.ker e :=
  ⟨P.ker_isLat, fun h => one_ne_zero (he.unique (Pair.mem_ker.1 h)), fun _ hs => Pair.smul_mem_ker hs he.mem⟩
theorem IsGlue.smul_mem_iff {L : Submodule 𝒪[k] (n → k)} {e : n → k} (h : IsGlue L e) {s : 𝒪[k]} :
    s • e ∈ L ↔ s ∈ maximalIdeal 𝒪[k] := by
  refine ⟨fun hs => ?_, h.smul_mem s⟩
  by_contra hn
  obtain ⟨u, rfl⟩ := notMem_maximalIdeal.1 hn
  apply h.not_mem
  simpa [smul_smul] using L.smul_mem ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) hs
theorem IsGlue.exists_pair {L : Submodule 𝒪[k] (n → k)} {e : n → k} (h : IsGlue L e) :
    ∃ P : Pair k n, P.ker = L ∧ P.HasVal e 1 := by
  let j : 𝒪[k] →ₗ[𝒪[k]] (n → k) ⧸ L := L.mkQ ∘ₗ LinearMap.toSpanSingleton 𝒪[k] _ e
  have hj : ∀ s, j s = 0 ↔ s ∈ maximalIdeal 𝒪[k] := fun s => by
    rw [← h.smul_mem_iff]
    exact Submodule.Quotient.mk_eq_zero L
  let ι : 𝓀[k] →ₗ[𝒪[k]] (n → k) ⧸ L := (maximalIdeal 𝒪[k]).liftQ j fun s hs => (hj s).2 hs
  have hι : ∀ s, ι (residue 𝒪[k] s) = L.mkQ (s • e) := fun s => rfl
  have hinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨s, rfl⟩ := residue_surjective (R := 𝒪[k]) a
    exact (residue_eq_zero_iff s).2 ((hj s).1 ha)
  let M := L ⊔ Submodule.span 𝒪[k] {e}
  have hM : ∀ x : M, (L.mkQ ∘ₗ M.subtype) x ∈ LinearMap.range ι := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hz
    refine ⟨residue _ s, ?_⟩
    simp [hι, (Submodule.Quotient.mk_eq_zero L).2 hy]
  let f : M →ₗ[𝒪[k]] 𝓀[k] :=
    (LinearEquiv.ofInjective ι hinj).symm.toLinearMap ∘ₗ LinearMap.codRestrict _ _ hM
  have hf : ∀ x : M, ι (f x) = L.mkQ x := fun x => by
    have := (LinearEquiv.ofInjective ι hinj).apply_symm_apply (LinearMap.codRestrict _ _ hM x)
    exact congrArg Subtype.val this
  have he : e ∈ M := Submodule.mem_sup_right (Submodule.mem_span_singleton_self e)
  have hfe : f ⟨e, he⟩ = 1 := hinj (by rw [hf, ← map_one (residue 𝒪[k]), hι, one_smul])
  haveI := h.isLat
  have hlat : M.IsLattice k := Submodule.IsLattice.of_le_of_isLattice_of_fg k (M := L) le_sup_left
    (h.isLat.fg.sup (Submodule.fg_span_singleton e))
  refine ⟨⟨M, hlat, f, fun h0 => by simp [h0] at hfe⟩, ?_, he, hfe⟩
  ext x
  rw [Pair.mem_ker]
  constructor
  · rintro ⟨hx, h0⟩
    have := hf ⟨x, hx⟩
    rw [show f ⟨x, hx⟩ = 0 from h0, map_zero] at this
    exact (Submodule.Quotient.mk_eq_zero L).1 this.symm
  · intro hx
    refine ⟨Submodule.mem_sup_left hx, hinj ?_⟩
    rw [map_zero]
    exact (hf _).trans ((Submodule.Quotient.mk_eq_zero L).2 hx)
def glue {L : Submodule 𝒪[k] (n → k)} {e : n → k} (h : IsGlue L e) : Pair k n := h.exists_pair.choose
section
variable {L L' : Submodule 𝒪[k] (n → k)} {e e' : n → k}
@[simp] theorem glue_ker (h : IsGlue L e) : (glue h).ker = L := h.exists_pair.choose_spec.1
theorem glue_hasVal (h : IsGlue L e) : (glue h).HasVal e 1 := h.exists_pair.choose_spec.2
end
variable (k) in

structure GluePair (n : Type*) where

  ker : Submodule 𝒪[k] (n → k)
  isLat : ker.IsLattice k

  cls : (n → k) ⧸ ker
  cls_ne : cls ≠ 0
  smul_cls : ∀ s ∈ maximalIdeal 𝒪[k], s • cls = 0
def Pair.toGlue (P : Pair k n) : GluePair k n where
  ker := P.ker
  isLat := P.ker_isLat
  cls := P.ker.mkQ P.vec
  cls_ne h := (Pair.isGlue P.hasVal_vec).not_mem ((Submodule.Quotient.mk_eq_zero _).1 h)
  smul_cls s hs := (Submodule.Quotient.mk_eq_zero _).2 (Pair.smul_mem_ker hs P.hasVal_vec.mem)
theorem Pair.toGlue_bijective : Function.Bijective (Pair.toGlue : Pair k n → GluePair k n) := by
  constructor
  · intro P Q h
    have hk : P.ker = Q.ker := congrArg GluePair.ker h
    have key : ∀ (G G' : GluePair k n) (x y : n → k), G = G' → G.cls = G.ker.mkQ x → G'.cls = G'.ker.mkQ y →
        x - y ∈ G'.ker := by
      rintro G _ x y rfl h1 h2
      exact (Submodule.Quotient.eq _).1 (h1.symm.trans h2)
    exact Pair.ext_ker hk P.hasVal_vec ((Pair.hasVal_one_iff Q.hasVal_vec).2 (key _ _ _ _ h rfl rfl))
  · rintro ⟨L, hL, c, hc, hs⟩
    obtain ⟨e, rfl⟩ := L.mkQ_surjective c
    have h : IsGlue L e := ⟨hL, fun h => hc ((Submodule.Quotient.mk_eq_zero _).2 h),
      fun s hs' => (Submodule.Quotient.mk_eq_zero _).1 (hs s hs')⟩
    obtain ⟨P, rfl, hP⟩ := h.exists_pair
    refine ⟨P, ?_⟩
    have : P.ker.mkQ P.vec = P.ker.mkQ e := ((Submodule.Quotient.eq _).2 (Pair.sub_vec_mem hP)).symm
    simp only [Pair.toGlue, this]
def Pair.glueEquiv : Pair k n ≃ GluePair k n := Equiv.ofBijective _ Pair.toGlue_bijective
namespace Pair
instance (P : Pair k n) : P.lat.IsLattice k := P.isLat
instance (P : Pair k n) : P.ker.IsLattice k := P.ker_isLat
instance : SMul 𝓀[k]ˣ (Pair k n) where
  smul c P := ⟨P.lat, P.isLat, (c : 𝓀[k]) • P.fn, smul_ne_zero c.ne_zero P.fn_ne⟩
@[simp] theorem dia_lat (c : 𝓀[k]ˣ) (P : Pair k n) : (c • P).lat = P.lat := rfl
theorem dia_hasVal {c : 𝓀[k]ˣ} {P : Pair k n} {x : n → k} {a : 𝓀[k]} :
    (c • P).HasVal x a ↔ P.HasVal x ((c⁻¹ : 𝓀[k]ˣ) * a) :=
  exists_congr fun _ => by
    change (c : 𝓀[k]) * _ = a ↔ _
    rw [Units.eq_inv_mul_iff_mul_eq]
instance : MulAction 𝓀[k]ˣ (Pair k n) where
  one_smul P := ext fun x a => by simp [dia_hasVal]
  mul_smul c d P := ext fun x a => by simp only [dia_hasVal, _root_.mul_inv_rev, Units.val_mul, mul_assoc]
@[simp] theorem dia_ker (c : 𝓀[k]ˣ) (P : Pair k n) : (c • P).ker = P.ker := by
  ext x
  simp [mem_ker, dia_hasVal]
open Classical in

def ev (P : Pair k n) (x : n → k) : 𝓀[k] := if h : x ∈ P.lat then P.fn ⟨x, h⟩ else 0
end Pair
def Red (L : Submodule 𝒪[k] (n → k)) : Type _ := L ⧸ (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L)
namespace Red
variable (L : Submodule 𝒪[k] (n → k))
instance : AddCommGroup (Red L) :=
  inferInstanceAs (AddCommGroup (L ⧸ (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L)))
instance : Module 𝒪[k] (Red L) :=
  inferInstanceAs (Module 𝒪[k] (L ⧸ (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L)))
instance : Module 𝓀[k] (Red L) :=
  inferInstanceAs (Module (𝒪[k] ⧸ maximalIdeal 𝒪[k]) (L ⧸ (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L)))
instance : IsScalarTower 𝒪[k] 𝓀[k] (Red L) :=
  inferInstanceAs
    (IsScalarTower 𝒪[k] (𝒪[k] ⧸ maximalIdeal 𝒪[k]) (L ⧸ (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L)))
def mk : L →ₗ[𝒪[k]] Red L := (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] L).mkQ
theorem mk_surjective : Function.Surjective (mk L) := Submodule.mkQ_surjective _
variable {L}
theorem mk_eq_zero (q : Unif k) {x : L} : mk L x = 0 ↔ q.inv • (x : n → k) ∈ L := by
  refine (Submodule.Quotient.mk_eq_zero _).trans ?_
  rw [q.2.maximalIdeal_eq, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩
    simp
  · intro h
    exact ⟨⟨_, h⟩, trivial, Subtype.ext (q.smul_inv_smul _)⟩
def out (x : Red L) : L := (mk_surjective L x).choose
@[simp] theorem mk_out (x : Red L) : mk L x.out = x := (mk_surjective L x).choose_spec
instance [L.IsLattice k] : Module.Finite 𝓀[k] (Red L) :=
  haveI : Module.Finite 𝒪[k] (Red L) := Module.Finite.of_surjective _ (mk_surjective L)
  Module.Finite.of_restrictScalars_finite 𝒪[k] _ _
instance [L.IsLattice k] : Finite (Red L) := Module.finite_of_finite 𝓀[k]
instance [L.IsLattice k] : Finite (Module.Dual 𝓀[k] (Red L)) := Module.finite_of_finite 𝓀[k]
theorem finrank_eq [Fintype n] [L.IsLattice k] : Module.finrank 𝓀[k] (Red L) = Fintype.card n := by
  let e : TensorProduct 𝒪[k] 𝓀[k] L ≃ₗ[𝒪[k]] Red L := TensorProduct.quotTensorEquivQuotSMul L (maximalIdeal 𝒪[k])
  let e' : TensorProduct 𝒪[k] 𝓀[k] L ≃ₗ[𝓀[k]] Red L := e.extendScalarsOfSurjective residue_surjective
  rw [← e'.finrank_eq, Module.finrank_baseChange, Submodule.IsLattice.finrank_of_pi k L]
end Red
def Pair.red (P : Pair k n) : Module.Dual 𝓀[k] (Red P.lat) :=
  let f : Red P.lat →ₗ[𝒪[k]] 𝓀[k] :=
    (maximalIdeal 𝒪[k] • ⊤ : Submodule 𝒪[k] P.lat).liftQ P.fn (Submodule.smul_le.2 fun _ hs x _ =>
      (Pair.mem_ker.1 (Pair.smul_mem_ker hs x.2)).2)
  f.extendScalarsOfSurjective residue_surjective
@[simp] theorem Pair.red_mk (P : Pair k n) (x : P.lat) : P.red (Red.mk _ x) = P.fn x := rfl
theorem Pair.red_ne (P : Pair k n) : P.red ≠ 0 := fun h =>
  P.fn_ne (LinearMap.ext fun x => by rw [← P.red_mk, h]; rfl)
section
variable (L : Submodule 𝒪[k] (n → k)) [hL : L.IsLattice k]
def ofDual (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) : Pair k n where
  lat := L
  isLat := hL
  fn := f.1.restrictScalars 𝒪[k] ∘ₗ Red.mk L
  fn_ne h := f.2 (LinearMap.ext fun x => by
    obtain ⟨y, rfl⟩ := Red.mk_surjective L x
    exact LinearMap.congr_fun h y)
@[simp] theorem ofDual_lat (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) : (ofDual L f).lat = L := rfl
theorem ofDual_hasVal (f : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0}) (x : L) :
    (ofDual L f).HasVal x (f.1 (Red.mk L x)) := ⟨x.2, rfl⟩
def latEquiv : {f : Module.Dual 𝓀[k] (Red L) // f ≠ 0} ≃ {P : Pair k n // P.lat = L} :=
  Equiv.ofBijective (fun f => ⟨ofDual L f, rfl⟩) <| by
    constructor
    · intro f g h
      refine Subtype.ext (LinearMap.ext fun x => ?_)
      obtain ⟨y, rfl⟩ := Red.mk_surjective L x
      have h' : ofDual L f = ofDual L g := congrArg Subtype.val h
      exact (ofDual_hasVal L f y).unique (h' ▸ ofDual_hasVal L g y)
    · rintro ⟨P, rfl⟩
      exact ⟨⟨P.red, P.red_ne⟩, rfl⟩
variable (q : Unif k)
theorem isGlue_inv_smul {x : L} (hx : Red.mk L x ≠ 0) : IsGlue L (q.inv • (x : n → k)) :=
  (isGlue_iff q).2 ⟨hL, fun h => hx ((Red.mk_eq_zero q).2 h), by simp⟩
def up (x : {x : Red L // x ≠ 0}) : Pair k n :=
  glue (isGlue_inv_smul L q (x := x.1.out) (by simpa using x.2))
@[simp] theorem up_ker (x : {x : Red L // x ≠ 0}) : (up L q x).ker = L := glue_ker _
theorem up_hasVal_iff (x : {x : Red L // x ≠ 0}) (y : L) :
    (up L q x).HasVal (q.inv • (y : n → k)) 1 ↔ Red.mk L y = x.1 := by
  rw [up, Pair.hasVal_one_iff (glue_hasVal _), glue_ker, ← smul_sub, ← Submodule.coe_sub, ← Red.mk_eq_zero q,
    map_sub, Red.mk_out, sub_eq_zero]
def kerEquiv : {x : Red L // x ≠ 0} ≃ {P : Pair k n // P.ker = L} :=
  Equiv.ofBijective (fun x => ⟨up L q x, up_ker L q x⟩) <| by
    constructor
    · intro x y h
      have h' : up L q x = up L q y := congrArg Subtype.val h
      have := (up_hasVal_iff L q x x.1.out).2 (Red.mk_out _)
      rw [h', up_hasVal_iff, Red.mk_out] at this
      exact Subtype.ext this
    · rintro ⟨P, rfl⟩
      let y : P.ker := ⟨q.1 • P.vec, Pair.smul_mem_ker q.mem_max P.hasVal_vec.mem⟩
      have hy : Red.mk _ y ≠ 0 := fun h =>
        (Pair.isGlue P.hasVal_vec).not_mem (by simpa [y] using (Red.mk_eq_zero q).1 h)
      refine ⟨⟨_, hy⟩, Subtype.ext (Pair.ext_ker (e := P.vec) (up_ker _ _ _) ?_ P.hasVal_vec)⟩
      simpa [y] using (up_hasVal_iff P.ker q ⟨_, hy⟩ y).2 rfl
end
theorem finite_lat (L : Submodule 𝒪[k] (n → k)) : {P : Pair k n | P.lat = L}.Finite := by
  rcases Set.eq_empty_or_nonempty {P : Pair k n | P.lat = L} with h | ⟨P, rfl⟩
  · simp [h]
  · exact Finite.of_equiv _ (latEquiv P.lat)
theorem finite_ker (L : Submodule 𝒪[k] (n → k)) : {P : Pair k n | P.ker = L}.Finite := by
  obtain ⟨q⟩ : Nonempty (Unif k) := inferInstance
  rcases Set.eq_empty_or_nonempty {P : Pair k n | P.ker = L} with h | ⟨P, rfl⟩
  · simp [h]
  · exact Finite.of_equiv _ (kerEquiv P.ker q)
def withLat (L : Submodule 𝒪[k] (n → k)) : Finset (Pair k n) := (finite_lat L).toFinset
def withKer (L : Submodule 𝒪[k] (n → k)) : Finset (Pair k n) := (finite_ker L).toFinset
@[simp] theorem mem_withLat {L : Submodule 𝒪[k] (n → k)} {P : Pair k n} : P ∈ withLat L ↔ P.lat = L :=
  (finite_lat L).mem_toFinset
@[simp] theorem mem_withKer {L : Submodule 𝒪[k] (n → k)} {P : Pair k n} : P ∈ withKer L ↔ P.ker = L :=
  (finite_ker L).mem_toFinset
def cross (q : Unif k) (P₁ P : Pair k n) : 𝓀[k] := P.ev (q.1 • P₁.vec)
section Action
variable [Fintype n] [DecidableEq n]
theorem mem_smul_iff {g : GL n k} {L : Submodule 𝒪[k] (n → k)} {x : n → k} : x ∈ g • L ↔ g⁻¹ • x ∈ L := by
  refine (Submodule.mem_smul_pointwise_iff_exists x g L).trans ?_
  exact ⟨fun ⟨y, hy, h⟩ => by simpa [← h] using hy, fun h => ⟨_, h, smul_inv_smul _ _⟩⟩
instance isLattice_smul (g : GL n k) (L : Submodule 𝒪[k] (n → k)) [hL : L.IsLattice k] : (g • L).IsLattice k := by
  refine ⟨hL.fg.map _, ?_⟩
  rw [eq_top_iff]
  intro x _
  have hx : g⁻¹ • x ∈ Submodule.span k (L : Set (n → k)) := hL.span_eq_top ▸ trivial
  have h : Submodule.span k (L : Set (n → k)) ≤
      (Submodule.span k ((g • L : Submodule 𝒪[k] (n → k)) : Set (n → k))).comap
        (DistribMulAction.toLinearMap k _ g) :=
    Submodule.span_le.2 fun y hy => Submodule.subset_span (Submodule.smul_mem_pointwise_smul y g L hy)
  have h2 : g • g⁻¹ • x ∈ Submodule.span k ((g • L : Submodule 𝒪[k] (n → k)) : Set (n → k)) := h hx
  rwa [smul_inv_smul] at h2
abbrev latStab (L : Submodule 𝒪[k] (n → k)) : Subgroup (GL n k) := MulAction.stabilizer (GL n k) L
namespace Pair
instance : SMul (GL n k) (Pair k n) where
  smul g P :=
    { lat := g • P.lat
      isLat := inferInstance
      fn := P.fn ∘ₗ (DistribMulAction.toLinearMap 𝒪[k] _ g⁻¹).restrict fun _ hx => mem_smul_iff.1 hx
      fn_ne := fun h => by
        have h1 := LinearMap.congr_fun h ⟨g • P.vec, Submodule.smul_mem_pointwise_smul _ g _ P.hasVal_vec.mem⟩
        have h2 : P.HasVal (g⁻¹ • g • P.vec) 0 := ⟨_, h1⟩
        rw [inv_smul_smul] at h2
        exact one_ne_zero (P.hasVal_vec.unique h2) }
@[simp] theorem smul_lat (g : GL n k) (P : Pair k n) : (g • P).lat = g • P.lat := rfl
theorem smul_hasVal {g : GL n k} {P : Pair k n} {x : n → k} {a : 𝓀[k]} :
    (g • P).HasVal x a ↔ P.HasVal (g⁻¹ • x) a :=
  ⟨fun ⟨h, h'⟩ => ⟨mem_smul_iff.1 h, h'⟩, fun ⟨h, h'⟩ => ⟨mem_smul_iff.2 h, h'⟩⟩
instance : MulAction (GL n k) (Pair k n) where
  one_smul P := ext fun x a => by simp [smul_hasVal]
  mul_smul g h P := ext fun x a => by simp only [smul_hasVal, _root_.mul_inv_rev, mul_smul]
instance : SMulCommClass (GL n k) 𝓀[k]ˣ (Pair k n) where
  smul_comm g c P := ext fun x a => by simp only [smul_hasVal, dia_hasVal]
@[simp] theorem smul_ker (g : GL n k) (P : Pair k n) : (g • P).ker = g • P.ker := by
  ext x
  rw [mem_ker, smul_hasVal, mem_smul_iff, mem_ker]
end Pair
theorem exists_gl_of_equiv {L L' : Submodule 𝒪[k] (n → k)} [L.IsLattice k] [L'.IsLattice k] (e : L ≃ₗ[𝒪[k]] L') :
    ∃ g : GL n k, ∀ x : L, g • (x : n → k) = e x := by
  let b := Module.Free.chooseBasis 𝒪[k] L
  let E : (n → k) ≃ₗ[k] (n → k) := (b.extendOfIsLattice k).equiv ((b.map e).extendOfIsLattice k) (Equiv.refl _)
  refine ⟨Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv E), ?_⟩
  have : (E.toLinearMap.restrictScalars 𝒪[k]) ∘ₗ L.subtype = L'.subtype ∘ₗ e.toLinearMap := by
    refine b.ext fun i => ?_
    have := (b.extendOfIsLattice k).equiv_apply i ((b.map e).extendOfIsLattice k) (Equiv.refl _)
    simpa [E] using this
  intro x
  refine Eq.trans ?_ (LinearMap.congr_fun this x)
  change LinearMap.toMatrix' E.toLinearMap *ᵥ (x : n → k) = E x
  rw [LinearMap.toMatrix'_mulVec]
  rfl
omit [Fintype n] [DecidableEq n] in

theorem Pair.exists_split (P : Pair k n) :
    ∃ (K : Submodule 𝒪[k] P.lat) (e : (K × 𝒪[k]) ≃ₗ[𝒪[k]] P.lat), ∀ z, P.fn (e z) = residue 𝒪[k] z.2 := by
  obtain ⟨F, hF⟩ := Module.projective_lifting_property (Algebra.linearMap 𝒪[k] 𝓀[k]) P.fn residue_surjective
  have hF' : ∀ x, residue 𝒪[k] (F x) = P.fn x := fun x => LinearMap.congr_fun hF x
  have hu : IsUnit (F ⟨P.vec, P.hasVal_vec.mem⟩) := by
    rw [← notMem_maximalIdeal, ← residue_eq_zero_iff, hF', P.hasVal_vec.2]
    exact one_ne_zero
  obtain ⟨u, hu⟩ := hu
  obtain ⟨v, hv⟩ : ∃ v, F v = 1 :=
    ⟨(u⁻¹ : 𝒪[k]ˣ).val • ⟨P.vec, P.hasVal_vec.mem⟩, by rw [map_smul, ← hu, smul_eq_mul, Units.inv_mul]⟩
  let j := (LinearMap.ker F).subtype.coprod (LinearMap.toSpanSingleton 𝒪[k] _ v)
  have hj : ∀ z, F (j z) = z.2 := fun z => by
    have := z.1.2
    rw [LinearMap.mem_ker] at this
    simp [j, hv, this]
  refine ⟨LinearMap.ker F, LinearEquiv.ofBijective j ⟨?_, fun x => ?_⟩, fun z => by rw [← hF', ← hj]; rfl⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨y, s⟩ h
    have hs : s = 0 := by simpa [h] using (hj (y, s)).symm
    subst hs
    simpa [j] using h
  · exact ⟨(⟨x - F x • v, by simp [hv]⟩, F x), by simp [j]⟩
instance : MulAction.IsPretransitive (GL n k) (Pair k n) where
  exists_smul_eq P Q := by
    obtain ⟨K, e, he⟩ := P.exists_split
    obtain ⟨K', e', he'⟩ := Q.exists_split
    have h1 := e.finrank_eq
    have h2 := e'.finrank_eq
    rw [Module.finrank_prod, Submodule.IsLattice.finrank_of_pi k] at h1 h2
    let d : K ≃ₗ[𝒪[k]] K' := LinearEquiv.ofFinrankEq _ _ (by omega)
    let t : P.lat ≃ₗ[𝒪[k]] Q.lat := e.symm ≪≫ₗ d.prodCongr (LinearEquiv.refl _ _) ≪≫ₗ e'
    have ht : ∀ x, Q.fn (t x) = P.fn x := fun x => by
      obtain ⟨z, rfl⟩ := e.surjective x
      simp [t, he, he']
    obtain ⟨g, hg⟩ := exists_gl_of_equiv t
    refine ⟨g, Pair.ext fun x a => ?_⟩
    rw [Pair.smul_hasVal]
    constructor
    · rintro ⟨h, rfl⟩
      have := Q.hasVal_fn (t ⟨_, h⟩)
      rwa [← hg, ht, smul_inv_smul] at this
    · rintro ⟨h, rfl⟩
      obtain ⟨y, hy⟩ := t.surjective ⟨x, h⟩
      have hx : x = g • (y : n → k) := by rw [hg, hy]
      rw [← hy, ht, hx, inv_smul_smul]
      exact P.hasVal_fn y
end Action
section Std
variable [Fintype n]
variable (k n) in

def stdLat : Submodule 𝒪[k] (n → k) := LinearMap.range ((Algebra.linearMap 𝒪[k] k).compLeft n)
omit [Fintype n] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem mem_stdLat {x : n → k} : x ∈ stdLat k n ↔ ∀ i, x i ∈ 𝒪[k] :=
  ⟨fun ⟨y, hy⟩ i => hy ▸ (y i).2, fun h => ⟨fun i => ⟨x i, h i⟩, rfl⟩⟩
instance : (stdLat k n).IsLattice k := by
  classical
  refine ⟨by rw [stdLat, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _, ?_⟩
  rw [eq_top_iff, ← (Pi.basisFun k n).span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  refine mem_stdLat.2 fun j => ?_
  rw [Pi.basisFun_apply, Pi.single_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]
variable (k) in

def stdPair (i : n) : Pair k n where
  lat := stdLat k n
  isLat := inferInstance
  fn :=
    { toFun := fun x => residue 𝒪[k] ⟨x.1 i, mem_stdLat.1 x.2 i⟩
      map_add' := fun x y => by rw [← map_add]; rfl
      map_smul' := fun s x => by
        rw [RingHom.id_apply, Algebra.smul_def, ResidueField.algebraMap_eq, ← map_mul]; rfl }
  fn_ne h := by
    have := LinearMap.congr_fun h ⟨fun _ => 1, mem_stdLat.2 fun _ => one_mem _⟩
    exact one_ne_zero ((map_one (residue 𝒪[k])).symm.trans this)
instance [Nonempty n] : Nonempty (Pair k n) := ⟨stdPair k (Classical.arbitrary n)⟩
end Std
end GlobalTheory.LatPair


