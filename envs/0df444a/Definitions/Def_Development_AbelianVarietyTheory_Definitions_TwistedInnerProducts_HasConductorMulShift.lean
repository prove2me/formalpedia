-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
-- name    : Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:26:11.724175+00:00
-- url     : https://prove2.me/theorems/335aec94-d2be-4c8f-99ad-eb4715041681
-- title:
--   Has Conductor Mul Shift
-- statement:
--   Definitions and structural lemmas for Has Conductor Mul Shift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/HasConductorMulShift.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Theorems.Thm_GlobalTheory_LatPair_stdPair_hasVal

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
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
section Forms
variable (k n) in

abbrev Form (M : Type*) : Type _ := Pair k n → M
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
def sumOp (S : Pair k n → Finset (Pair k n)) (w : Pair k n → Pair k n → ℂ) : Module.End ℂ (Form k n M) where
  toFun φ P := ∑ Q ∈ S P, w P Q • φ Q
  map_add' φ φ' := by
    ext P
    simp [Finset.sum_add_distrib]
  map_smul' c φ := by
    ext P
    simp [Finset.smul_sum, smul_comm c]
def dia : 𝓀[k]ˣ →* Module.End ℂ (Form k n M) where
  toFun c := LinearMap.funLeft ℂ M fun P => c • P
  map_one' := by
    ext φ P
    simp
  map_mul' c d := by
    ext φ P
    simp [mul_comm c d, mul_smul]
@[simp] theorem dia_apply (c : 𝓀[k]ˣ) (φ : Form k n M) (P : Pair k n) : dia c φ P = φ (c • P) := rfl
def Nm : Module.End ℂ (Form k n M) :=
  letI := Fintype.ofFinite 𝓀[k]ˣ
  ∑ c : 𝓀[k]ˣ, dia c
variable (k n M) in

def Mram : Submodule ℂ (Form k n M) := LinearMap.ker Nm
def trLat (L : Submodule 𝒪[k] (n → k)) : Form k n M →ₗ[ℂ] M := ∑ P ∈ withLat L, LinearMap.proj P
def trKer (L : Submodule 𝒪[k] (n → k)) : Form k n M →ₗ[ℂ] M := ∑ P ∈ withKer L, LinearMap.proj P
def tr : Module.End ℂ (Form k n M) := LinearMap.pi fun P => trLat P.lat
def tr' : Module.End ℂ (Form k n M) := LinearMap.pi fun P => trKer P.ker
open Classical in

def Da (q : Unif k) (a : 𝓀[k]) : Module.End ℂ (Form k n M) :=
  sumOp (fun P₁ => (withLat P₁.ker).filter fun P => cross q P₁ P = a) fun _ _ => 1
def D (q : Unif k) : Module.End ℂ (Form k n M) := Da q 1
open Classical in

def U (q : Unif k) : Module.End ℂ (Form k n M) :=
  sumOp (fun P => (withKer P.lat).filter fun P₁ => cross q P₁ P = 1) fun _ _ => 1
def Gs (χ : AddChar 𝓀[k] ℂ) : Module.End ℂ (Form k n M) :=
  letI := Fintype.ofFinite 𝓀[k]ˣ
  ∑ c : 𝓀[k]ˣ, χ c • dia c
def GsStar (χ : AddChar 𝓀[k] ℂ) : Module.End ℂ (Form k n M) :=
  letI := Fintype.ofFinite 𝓀[k]ˣ
  ∑ c : 𝓀[k]ˣ, χ (-(c : 𝓀[k])) • dia c⁻¹
def FF (q : Unif k) (χ : AddChar 𝓀[k] ℂ) : Module.End ℂ (Form k n M) :=
  sumOp (fun P₁ => withLat P₁.ker) fun P₁ P => χ (cross q P₁ P)
def FFStar (q : Unif k) (χ : AddChar 𝓀[k] ℂ) : Module.End ℂ (Form k n M) :=
  sumOp (fun P => withKer P.lat) fun P P₁ => χ (-cross q P₁ P)
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n M)
section Formulas
variable (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k]
end Formulas
def cntIp (φ φ' : Form k n ℂ) : ℂ := ∑ᶠ P, φ P * (starRingEnd ℂ) (φ' P)
def IsAdj (A B : Module.End ℂ (Form k n ℂ)) : Prop :=
  ∀ φ φ' : Form k n ℂ, (Function.support φ).Finite → (Function.support φ').Finite → cntIp (A φ) φ' = cntIp φ (B φ')
section Equivariance
variable [Fintype n] [DecidableEq n]
def transl : Representation ℂ (GL n k) (Form k n M) where
  toFun g := LinearMap.funLeft ℂ M fun P => g⁻¹ • P
  map_one' := by
    ext φ P
    simp
  map_mul' g h := by
    ext φ P
    simp [mul_smul]
@[simp] theorem transl_apply (g : GL n k) (P : Pair k n) : transl g φ P = φ (g⁻¹ • P) := rfl
variable (π : Representation ℂ (GL n k) M)
def EqForm : Submodule ℂ (Form k n M) where
  carrier := {φ | ∀ (g : GL n k) P, φ (g • P) = π g (φ P)}
  add_mem' h h' g P := by simp [h g P, h' g P]
  zero_mem' g P := by simp
  smul_mem' c φ h g P := by simp [h g P]
def levelVec (P₀ : Pair k n) : Submodule ℂ M where
  carrier := {v | ∀ g : GL n k, g • P₀ = P₀ → π g v = v}
  add_mem' h h' g hg := by simp [h g hg, h' g hg]
  zero_mem' g _ := by simp
  smul_mem' c v h g hg := by simp [h g hg]
def formOf (P₀ : Pair k n) (v : levelVec π P₀) : Form k n M := fun P =>
  π (MulAction.exists_smul_eq (GL n k) P₀ P).choose v
theorem formOf_smul (P₀ : Pair k n) (v : levelVec π P₀) (g : GL n k) : formOf π P₀ v (g • P₀) = π g v := by
  have h := (MulAction.exists_smul_eq (GL n k) P₀ (g • P₀)).choose_spec
  rw [formOf]
  generalize (MulAction.exists_smul_eq (GL n k) P₀ (g • P₀)).choose = g' at h
  have := v.2 (g⁻¹ * g') (by rw [mul_smul, h, inv_smul_smul])
  rw [← mul_inv_cancel_left g g', map_mul, Module.End.mul_apply, this]
theorem formOf_mem (P₀ : Pair k n) (v : levelVec π P₀) : formOf π P₀ v ∈ EqForm π := fun g P => by
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P₀ P
  rw [smul_smul, formOf_smul, formOf_smul, map_mul, Module.End.mul_apply]
def evalEquiv (P₀ : Pair k n) : EqForm π ≃ₗ[ℂ] levelVec π P₀ where
  toFun φ := ⟨φ.1 P₀, fun g hg => by rw [← φ.2 g P₀, hg]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨formOf π P₀ v, formOf_mem π P₀ v⟩
  left_inv φ := Subtype.ext (funext fun P => by
    obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P₀ P
    exact (formOf_smul π P₀ _ h).trans (φ.2 h P₀).symm)
  right_inv v := Subtype.ext (by simpa using formOf_smul π P₀ v 1)
variable (g : GL n k) (P : Pair k n)
variable {π φ}
end Equivariance
end Forms
section Character
open SplitWeil
theorem apply_int_eq_one {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (x : 𝒪[k]) : ψ x = 1 :=
  (hψ x).2 (by simpa using (Valuation.mem_integer_iff _ _).1 x.2) x le_rfl
theorem apply_inv_mul_congr {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) (q : Unif k) {s t : 𝒪[k]}
    (h : residue 𝒪[k] s = residue 𝒪[k] t) : ψ (q.inv * s) = ψ (q.inv * t) := by
  obtain ⟨u, hu⟩ := q.mem_max_iff.1 ((residue_eq_zero_iff (s - t)).1 (by rw [map_sub, h, sub_self]))
  have : q.inv * s = q.inv * t + u := by
    have hu' : (s : k) = t + q.1 * u := by exact_mod_cast congrArg Subtype.val (sub_eq_iff_eq_add'.1 hu)
    rw [hu', mul_add, Unif.inv, inv_mul_cancel_left₀ q.ne_zero]
  rw [this, AddChar.map_add_eq_mul, apply_int_eq_one hψ, mul_one]
def resChar (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (q : Unif k) : AddChar 𝓀[k] ℂ where
  toFun a := ψ (q.inv * ((residue_surjective (R := 𝒪[k]) a).choose : 𝒪[k]))
  map_zero_eq_one' := by
    rw [apply_inv_mul_congr hψ q (t := 0) (by rw [(residue_surjective (R := 𝒪[k]) 0).choose_spec, map_zero])]
    simp
  map_add_eq_mul' a b := by
    rw [apply_inv_mul_congr hψ q
      (t := (residue_surjective (R := 𝒪[k]) a).choose + (residue_surjective (R := 𝒪[k]) b).choose)
      (by rw [map_add, (residue_surjective (R := 𝒪[k]) _).choose_spec, (residue_surjective (R := 𝒪[k]) _).choose_spec,
        (residue_surjective (R := 𝒪[k]) _).choose_spec])]
    simp [mul_add, AddChar.map_add_eq_mul]
end Character
section Kernel
variable [Fintype n']
open Classical in

def latInd (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) (x : Matrix n n' k) : ℂ :=
  if ∀ y ∈ S, x *ᵥ y ∈ L then 1 else 0
def Maps (P : Pair k n') (Q : Pair k n) (x : Matrix n n' k) : Prop :=
  ∃ h : ∀ y ∈ P.lat, x *ᵥ y ∈ Q.lat, ∀ y : P.lat, Q.fn ⟨x *ᵥ y, h y y.2⟩ = P.fn y
open Classical in

def phiOne (P : Pair k n') (Q : Pair k n) (x : Matrix n n' k) : ℂ := if Maps P Q x then 1 else 0
variable {P : Pair k n'} {Q : Pair k n} {x : Matrix n n' k}
theorem maps_iff_hasVal : Maps P Q x ↔ ∀ y a, P.HasVal y a → Q.HasVal (x *ᵥ y) a :=
  ⟨fun ⟨h, h'⟩ y _ ⟨hy, ha⟩ => ⟨h y hy, ha ▸ h' ⟨y, hy⟩⟩,
    fun h => ⟨fun y hy => (h y _ (P.hasVal_fn ⟨y, hy⟩)).mem, fun y => (h y _ (P.hasVal_fn y)).2⟩⟩
variable [DecidableEq n'] [Fintype n] [DecidableEq n]
end Kernel
section Glued
variable {c : ℕ}
variable (k n) in

def inX (c : ℕ) : (n → k) →ₗ[𝒪[k]] (n ⊕ Fin c → k) where
  toFun x := Sum.elim x 0
  map_add' x y := by ext (i | i) <;> simp
  map_smul' s x := by ext (i | i) <;> simp
variable (k n) in

def avec (c p : ℕ) : n ⊕ Fin c → k := Sum.elim 0 fun i => if i.val + 1 = p then 1 else 0
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem sum_smul_avec (z : Fin c → k) : ∑ i : Fin c, z i • avec k n c (i.val + 1) = Sum.elim (0 : n → k) z := by
  ext (j | j) <;> simp [avec, Fin.val_inj]
def gluedLat (q : Unif k) (c p : ℕ) (L : Submodule 𝒪[k] (n → k)) (f : n → k) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L.map (inX k n c) ⊔ Submodule.span 𝒪[k] {q.inv • avec k n c p + inX k n c f} ⊔
    Submodule.span 𝒪[k] {y | ∃ i, 1 ≤ i ∧ i < p ∧ i ≤ c ∧ y = avec k n c i} ⊔
    Submodule.span 𝒪[k] {y | ∃ i, p < i ∧ i ≤ c ∧ y = q.inv • avec k n c i}
def gluedS (q : Unif k) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) (f : n → k) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  L.map (inX k n c) ⊔ Submodule.span 𝒪[k] {q.inv • avec k n c 1 + inX k n c f} ⊔
    Submodule.span 𝒪[k] {y | ∃ i, 2 ≤ i ∧ i ≤ c ∧ y = q.inv • avec k n c i}
theorem gluedLat_one (q : Unif k) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    gluedLat q c 1 L f = gluedS q c L f := by
  have : {y | ∃ i, 1 ≤ i ∧ i < 1 ∧ i ≤ c ∧ y = avec k n c i} = ∅ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨i, h1, h2, -⟩
    omega
  rw [gluedLat, this, Submodule.span_empty, sup_bot_eq]
  rfl
theorem mem_gluedLat {q : Unif k} {p : ℕ} {L : Submodule 𝒪[k] (n → k)} {f : n → k} {y : n ⊕ Fin c → k} :
    y ∈ gluedLat q c p L f ↔ ∃ s : 𝒪[k], y ∘ Sum.inl - s • f ∈ L ∧ ∀ i : Fin c,
      (i.val + 1 < p → y (Sum.inr i) ∈ 𝒪[k]) ∧ (i.val + 1 = p → y (Sum.inr i) = q.inv * s) ∧
        (p < i.val + 1 → (q.1 : k) * y (Sum.inr i) ∈ 𝒪[k]) := by
  let T : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
    { carrier := {y | ∃ s : 𝒪[k], y ∘ Sum.inl - s • f ∈ L ∧ ∀ i : Fin c,
        (i.val + 1 < p → y (Sum.inr i) ∈ 𝒪[k]) ∧ (i.val + 1 = p → y (Sum.inr i) = q.inv * s) ∧
          (p < i.val + 1 → (q.1 : k) * y (Sum.inr i) ∈ 𝒪[k])}
      zero_mem' := ⟨0, by simp, fun i => by simp⟩
      add_mem' := by
        rintro y z ⟨s, hs, h⟩ ⟨t, ht, h'⟩
        refine ⟨s + t, ?_, fun i => ⟨fun hi => add_mem ((h i).1 hi) ((h' i).1 hi), fun hi => ?_, fun hi => ?_⟩⟩
        · convert add_mem hs ht using 1
          rw [Pi.add_comp, add_smul]
          abel
        · simp [(h i).2.1 hi, (h' i).2.1 hi, mul_add]
        · simpa [mul_add] using add_mem ((h i).2.2 hi) ((h' i).2.2 hi)
      smul_mem' := by
        rintro t y ⟨s, hs, h⟩
        refine ⟨t * s, ?_, fun i => ⟨fun hi => mul_mem t.2 ((h i).1 hi), fun hi => ?_, fun hi => ?_⟩⟩
        · convert L.smul_mem t hs using 1
          rw [smul_sub, mul_smul]
          rfl
        · change (t : k) * y _ = _
          simp [(h i).2.1 hi, mul_left_comm]
        · change (q.1 : k) * ((t : k) * y _) ∈ _
          rw [mul_left_comm]
          exact mul_mem t.2 ((h i).2.2 hi) }
  have hq : (q.1 : k) * q.inv = 1 := mul_inv_cancel₀ q.ne_zero
  constructor
  · refine fun hy => (?_ : gluedLat q c p L f ≤ T) hy
    refine sup_le (sup_le (sup_le ?_ (Submodule.span_le.2 ?_)) (Submodule.span_le.2 ?_)) (Submodule.span_le.2 ?_)
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨0, by simpa [inX] using hx, fun i => by simp [inX]⟩
    · rintro _ rfl
      refine ⟨1, ?_, fun i => ⟨fun hi => ?_, fun hi => ?_, fun hi => ?_⟩⟩
      · convert L.zero_mem
        ext j
        simp [inX, avec]
      · simp [inX, avec, hi.ne]
      · simp [inX, avec, hi]
      · simp [inX, avec, hi.ne']
    · rintro _ ⟨j, -, hj, -, rfl⟩
      refine ⟨0, by simp [avec], fun i => ⟨fun hi => ?_, fun hi => ?_, fun hi => ?_⟩⟩
      · simp only [avec, Sum.elim_inr]
        split_ifs
        exacts [one_mem _, zero_mem _]
      · simp [avec, show i.val + 1 ≠ j by omega]
      · simp [avec, show i.val + 1 ≠ j by omega]
    · rintro _ ⟨j, hj, -, rfl⟩
      refine ⟨0, ?_, fun i => ⟨fun hi => ?_, fun hi => ?_, fun hi => ?_⟩⟩
      · convert L.zero_mem
        ext j
        simp [avec]
      · simp [avec, show i.val + 1 ≠ j by omega]
      · simp [avec, show i.val + 1 ≠ j by omega]
      · by_cases h : i.val + 1 = j <;> simp [avec, h, hq]
  · rintro ⟨s, hs, h⟩
    have hy : y = inX k n c (y ∘ Sum.inl - s • f) + s • (q.inv • avec k n c p + inX k n c f) +
        ∑ i : Fin c, (if i.val + 1 = p then 0 else y (Sum.inr i)) • avec k n c (i.val + 1) := by
      rw [sum_smul_avec]
      ext (j | j)
      · simp [inX, avec]
      · have hs' : ∀ z : k, s • z = (s : k) * z := fun _ => rfl
        by_cases hj : j.val + 1 = p
        · simp [inX, avec, Fin.val_inj, hj, (h j).2.1 hj, hs', mul_comm]
        · simp [inX, avec, Fin.val_inj, hj]
    rw [hy]
    refine add_mem (add_mem ?_ ?_) (sum_mem fun i _ => ?_)
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left ⟨_, hs, rfl⟩))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))))
    · rcases lt_trichotomy (i.val + 1) p with hi | hi | hi
      · rw [if_neg hi.ne]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.smul_mem _ (⟨_, (h i).1 hi⟩ : 𝒪[k])
          (Submodule.subset_span ⟨_, by omega, hi, i.2, rfl⟩)))
      · simp [hi]
      · rw [if_neg hi.ne']
        have := Submodule.smul_mem _ (⟨_, (h i).2.2 hi⟩ : 𝒪[k]) (Submodule.subset_span (R := 𝒪[k])
          (s := {y | ∃ i, p < i ∧ i ≤ c ∧ y = q.inv • avec k n c i}) ⟨_, hi, i.2, rfl⟩)
        refine Submodule.mem_sup_right ?_
        convert this using 1
        change _ = ((q.1 : k) * y (Sum.inr i)) • q.inv • avec k n c (i.val + 1)
        rw [smul_smul, mul_right_comm, hq, one_mul]
instance gluedLat_isLattice (q : Unif k) (c p : ℕ) (L : Submodule 𝒪[k] (n → k)) [hL : L.IsLattice k] (f : n → k) :
    (gluedLat q c p L f).IsLattice k := by
  refine ⟨(((hL.fg.map _).sup (Submodule.fg_span_singleton _)).sup (Submodule.fg_span ?_)).sup
    (Submodule.fg_span ?_), ?_⟩
  · exact ((Set.finite_le_nat c).image (avec k n c)).subset fun _ ⟨i, _, _, h, e⟩ => ⟨i, h, e.symm⟩
  · exact ((Set.finite_le_nat c).image (q.inv • avec k n c ·)).subset fun _ ⟨i, _, h, e⟩ => ⟨i, h, e.symm⟩
  · set W := Submodule.span k (gluedLat q c p L f : Set (n ⊕ Fin c → k))
    have hX : ∀ x, inX k n c x ∈ W := fun x => by
      have hx : x ∈ Submodule.span k (L : Set (n → k)) := hL.span_eq_top ▸ trivial
      induction hx using Submodule.span_induction with
      | mem x hx =>
        exact Submodule.subset_span (mem_gluedLat.2 ⟨0, by simpa [inX] using hx, fun i => by simp [inX]⟩)
      | zero => simp
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | smul a x _ hx =>
        convert W.smul_mem a hx using 1
        ext (i | i) <;> simp [inX]
    have hA : ∀ i : Fin c, avec k n c (i.val + 1) ∈ W := fun i => by
      by_cases hi : i.val + 1 = p
      · have h1 : q.inv • avec k n c p + inX k n c f ∈ W := Submodule.subset_span (Submodule.mem_sup_left
          (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))
        have h2 := W.smul_mem (q.1 : k) ((W.add_mem_iff_left (hX f)).1 h1)
        rwa [smul_smul, Unif.inv, mul_inv_cancel₀ q.ne_zero, one_smul, ← hi] at h2
      · refine Submodule.subset_span (mem_gluedLat.2 ⟨0, by simp [avec], fun j => ⟨fun _ => ?_, fun hj => ?_, fun _ => ?_⟩⟩)
        · by_cases h : j = i <;> simp [avec, Fin.val_inj, h]
        · simp [avec, show j.val ≠ i.val by omega]
        · by_cases h : j = i <;> simp [avec, Fin.val_inj, h]
    refine eq_top_iff.2 fun y _ => ?_
    have hy : y = inX k n c (y ∘ Sum.inl) + ∑ i : Fin c, y (Sum.inr i) • avec k n c (i.val + 1) := by
      ext (j | j) <;> simp [inX, avec, Fin.val_inj]
    rw [hy]
    exact add_mem (hX _) (sum_mem fun i _ => W.smul_mem _ (hA i))
instance gluedS_isLattice (q : Unif k) (c : ℕ) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (f : n → k) :
    (gluedS q c L f).IsLattice k := gluedLat_one q c L f ▸ inferInstance
def Pair.glued (P : Pair k n) (q : Unif k) (c p : ℕ) : Submodule 𝒪[k] (n ⊕ Fin c → k) := gluedLat q c p P.ker P.vec
instance (P : Pair k n) (q : Unif k) (c p : ℕ) : (P.glued q c p).IsLattice k := gluedLat_isLattice _ _ _ _ _
variable [Fintype n] [DecidableEq n]
end Glued
section Spherical
variable [Fintype n] [DecidableEq n]
theorem exists_smul_lat (L L' : Submodule 𝒪[k] (n → k)) [L.IsLattice k] [L'.IsLattice k] :
    ∃ g : GL n k, g • L = L' := by
  let e : L ≃ₗ[𝒪[k]] L' := LinearEquiv.ofFinrankEq _ _ (by
    rw [Submodule.IsLattice.finrank_of_pi k, Submodule.IsLattice.finrank_of_pi k])
  obtain ⟨g, hg⟩ := exists_gl_of_equiv e
  refine ⟨g, Submodule.ext fun x => mem_smul_iff.trans ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [← smul_inv_smul g x, hg ⟨_, h⟩]
    exact (e _).2
  · obtain ⟨y, hy⟩ := e.surjective ⟨x, h⟩
    have hx : x = g • (y : n → k) := by rw [hg, hy]
    rw [hx, inv_smul_smul]
    exact y.2
variable {A : Type*} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL n k) A)
def sphVecs (L₀ : Submodule 𝒪[k] (n → k)) : Submodule ℂ A where
  carrier := {v | ∀ g ∈ latStab L₀, σ g v = v}
  add_mem' h h' g hg := by simp [h g hg, h' g hg]
  zero_mem' g _ := by simp
  smul_mem' c v h g hg := by simp [h g hg]
def vecAt {L₀ : Submodule 𝒪[k] (n → k)} [L₀.IsLattice k] (v : sphVecs σ L₀) (L : Submodule 𝒪[k] (n → k))
    [L.IsLattice k] : A := σ (exists_smul_lat L₀ L).choose v
variable {L₀ : Submodule 𝒪[k] (n → k)} [L₀.IsLattice k] (v : sphVecs σ L₀)
end Spherical
section Examples
example [Fintype n] [DecidableEq n] (P : Pair k n) : phiOne P P 1 = 1 :=
  if_pos (maps_iff_hasVal.2 fun y a h => by simpa using h)
example [Fintype n'] (P : Pair k n') (Q : Pair k n) : phiOne P Q 0 = 0 :=
  if_neg fun h => by
    have h1 := maps_iff_hasVal.1 h _ _ P.hasVal_vec
    rw [zero_mulVec] at h1
    exact one_ne_zero (h1.unique (Pair.mem_ker.1 (zero_mem _)))
example [Fintype n] (i : n) (x : n → k) :
    x ∈ (stdPair k i).ker ↔ ∃ h : ∀ j, x j ∈ 𝒪[k], (⟨x i, h i⟩ : 𝒪[k]) ∈ maximalIdeal 𝒪[k] := by
  simp only [Pair.mem_ker, stdPair_hasVal, residue_eq_zero_iff]
example (P : Pair k n) (q : Unif k) (x : n → k) : inX k n 0 x ∈ P.glued q 0 1 ↔ x ∈ P.lat := by
  rw [Pair.glued, mem_gluedLat, Pair.mem_lat_iff]
  simp [inX, Pair.hasVal_iff P.hasVal_vec]
example (r : ℕ) : Nonempty (GluePair k (Fin (r + 1))) := ⟨(stdPair k 0).toGlue⟩
end Examples
end GlobalTheory.LatPair


