-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InvertibleSpanSingleton
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_InvertibleSpanSingleton
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:14.781518+00:00
-- url     : https://prove2.me/theorems/7a7bfeb8-a19b-4b42-acaa-a250e86e14ae
-- title:
--   Invertible Span Singleton
-- statement:
--   Definitions and structural lemmas for Invertible Span Singleton, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/InvertibleSpanSingleton.lean

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
namespace GlobalTheory.Prism
def SemiBC {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module B N] {f : A →+* B} (u : M →ₛₗ[f] N) : Prop :=
  ∀ (Q : Type) [AddCommGroup Q] [Module B Q] (v : M →ₛₗ[f] Q), ∃! w : N →ₗ[B] Q, ∀ x, w (u x) = v x
structure Delta (l : ℕ) (A : Type) [CommRing A] where
  δ : A → A
  δ_one : δ 1 = 0
  δ_mul : ∀ a b, δ (a * b) = a ^ l * δ b + b ^ l * δ a + (l : A) * δ a * δ b
  δ_add : ∀ a b, δ (a + b) = δ a + δ b -
    ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * a ^ k * b ^ (l - k)
  φ : A →+* A
  φ_eq : ∀ a, φ a = a ^ l + (l : A) * δ a
structure Obj (l : ℕ) (R : Type) [CommRing R] where
  A : Type
  [ring : CommRing A]
  D : Delta l A
  I : Ideal A
  inv : Module.Invertible A ↥I
  complete : IsAdicComplete (Ideal.span {(l : A)} ⊔ I) A
  l_mem : (l : A) ∈ I ⊔ I.map D.φ
  bdd : ∃ n : ℕ, ∀ x : A ⧸ I, (∃ m : ℕ, (l : A ⧸ I) ^ m * x = 0) → (l : A ⧸ I) ^ n * x = 0
  str : R →+* A ⧸ I
attribute [instance] Obj.ring
variable {l : ℕ} {R : Type} [CommRing R]
structure Hom (P P' : Obj l R) where
  f : P.A →+* P'.A
  f_δ : ∀ a, f (P.D.δ a) = P'.D.δ (f a)
  f_I : ∀ a ∈ P.I, f a ∈ P'.I
  f_str : ∀ (r : R) (a : P.A), Ideal.Quotient.mk P.I a = P.str r →
    Ideal.Quotient.mk P'.I (f a) = P'.str r
def Hom.id (P : Obj l R) : Hom P P where
  f := RingHom.id _
  f_δ := fun _ => rfl
  f_I := fun _ h => h
  f_str := fun _ _ h => h
def Hom.comp {P P' P'' : Obj l R} (g : Hom P' P'') (f : Hom P P') : Hom P P'' where
  f := g.f.comp f.f
  f_δ := fun a => by simp [f.f_δ, g.f_δ]
  f_I := fun a h => g.f_I _ (f.f_I a h)
  f_str := fun r a h => g.f_str r _ (f.f_str r a h)
def IsFrac {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (d : A)
    (y : LocalizedModule (Submonoid.powers d) M) (m : M) (k : ℕ) : Prop :=
  y = LocalizedModule.mk m (⟨d ^ k, (Submonoid.mem_powers_iff _ _).2 ⟨k, rfl⟩⟩ : ↥(Submonoid.powers d))
structure FCrys (l : ℕ) (R : Type) [CommRing R] where
  M : Obj l R → Type
  [acg : ∀ P, AddCommGroup (M P)]
  [mod : ∀ P, Module P.A (M P)]
  fin : ∀ P, Module.Finite P.A (M P)
  proj : ∀ P, Module.Projective P.A (M P)
  tr : ∀ {P P' : Obj l R} (f : Hom P P'), M P →ₛₗ[f.f] M P'
  tr_bc : ∀ {P P' : Obj l R} (f : Hom P P'), SemiBC (tr f)
  tr_id : ∀ (P : Obj l R) x, tr (Hom.id P) x = x
  tr_comp : ∀ {P P' P'' : Obj l R} (g : Hom P' P'') (f : Hom P P') x,
    tr (g.comp f) x = tr g (tr f x)

  Φ : ∀ (P : Obj l R) (d : ↥P.I), M P →ₛₗ[(algebraMap P.A (Localization.Away (d : P.A))).comp P.D.φ]
    LocalizedModule (Submonoid.powers (d : P.A)) (M P)
  Φ_bc : ∀ (P : Obj l R) (d : ↥P.I), SemiBC (Φ P d)

  Φ_nat : ∀ {P P' : Obj l R} (f : Hom P P') (d : ↥P.I) (d' : ↥P'.I) (x m : M P) (k : ℕ) (n : M P') (j : ℕ),
    IsFrac (d : P.A) (Φ P d x) m k → IsFrac (d' : P'.A) (Φ P' d' (tr f x)) n j →
      ∃ r : ℕ, (f.f d * d') ^ r • ((d' : P'.A) ^ j • tr f m - f.f d ^ k • n) = 0
attribute [instance] FCrys.acg FCrys.mod
structure FHom (E E' : FCrys l R) where
  u : ∀ P : Obj l R, E.M P →ₗ[P.A] E'.M P
  u_tr : ∀ {P P' : Obj l R} (f : Hom P P') x, u P' (E.tr f x) = E'.tr f (u P x)
  u_Φ : ∀ (P : Obj l R) (d : ↥P.I) (x m : E.M P) (k : ℕ),
    IsFrac (d : P.A) (E.Φ P d x) m k → IsFrac (d : P.A) (E'.Φ P d (u P x)) (u P m) k
structure VBun (l : ℕ) (R : Type) [CommRing R] where
  M : Obj l R → Type
  [acg : ∀ P, AddCommGroup (M P)]
  [mod : ∀ P, Module P.A (M P)]
  fin : ∀ P, Module.Finite P.A (M P)
  proj : ∀ P, Module.Projective P.A (M P)
  tr : ∀ {P P' : Obj l R} (f : Hom P P'), M P →ₛₗ[f.f] M P'
  tr_bc : ∀ {P P' : Obj l R} (f : Hom P P'), SemiBC (tr f)
  tr_id : ∀ (P : Obj l R) x, tr (Hom.id P) x = x
  tr_comp : ∀ {P P' P'' : Obj l R} (g : Hom P' P'') (f : Hom P P') x,
    tr (g.comp f) x = tr g (tr f x)
attribute [instance] VBun.acg VBun.mod
def FCrys.toVBun (E : FCrys l R) : VBun l R where
  M := E.M
  fin := E.fin
  proj := E.proj
  tr := E.tr
  tr_bc := E.tr_bc
  tr_id := E.tr_id
  tr_comp := E.tr_comp
def FCrys.Effective (E : FCrys l R) : Prop :=
  ∀ (P : Obj l R) (x : E.M P), ∃ m : E.M P, ∀ d : ↥P.I, IsFrac (d : P.A) (E.Φ P d x) m 0
def Delta.ofLift (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (φ : A →+* A)
    (htf : ∀ x : A, (l : A) * x = 0 → x = 0) (h : ∀ a, ∃ b, φ a = a ^ l + (l : A) * b) : Delta l A where
  δ a := (h a).choose
  δ_one := by
    apply htf
    have := (h 1).choose_spec
    simp only [map_one, one_pow] at this ⊢
    linear_combination -this
  δ_mul a b := by
    rw [← sub_eq_zero]; apply htf
    have h1 := (h a).choose_spec
    have h2 := (h b).choose_spec
    have h3 := (h (a * b)).choose_spec
    have h4 := map_mul φ a b
    generalize (h a).choose = x at *
    generalize (h b).choose = y at *
    generalize (h (a*b)).choose = z at *
    rw [h1, h2, h3, mul_pow] at h4
    linear_combination h4
  δ_add a b := by
    rw [← sub_eq_zero]; apply htf
    have h1 := (h a).choose_spec
    have h2 := (h b).choose_spec
    have h3 := (h (a + b)).choose_spec
    have h4 := map_add φ a b
    generalize (h a).choose = x at *
    generalize (h b).choose = y at *
    generalize (h (a+b)).choose = z at *
    have h5 : (a + b) ^ l = a ^ l + b ^ l + (l : A) *
        ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * a ^ k * b ^ (l - k) := by
      rw [add_pow_prime_eq' hl.out]
      congr 2
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [h1, h2, h3, h5] at h4
    linear_combination h4
  φ := φ
  φ_eq a := (h a).choose_spec
@[simp] theorem Delta.ofLift_φ (l : ℕ) [Fact l.Prime] {A : Type} [CommRing A] (φ : A →+* A)
    (htf : ∀ x : A, (l : A) * x = 0 → x = 0) (h : ∀ a, ∃ b, φ a = a ^ l + (l : A) * b) :
    (Delta.ofLift l φ htf h).φ = φ := rfl
theorem Delta.map_φ_of_map_δ {A B : Type} [CommRing A] [CommRing B] (D : Delta l A) (D' : Delta l B)
    (f : A →+* B) (h : ∀ a, f (D.δ a) = D'.δ (f a)) (a : A) : f (D.φ a) = D'.φ (f a) := by
  simp [D.φ_eq, D'.φ_eq, h]
theorem Hom.f_φ {P P' : Obj l R} (f : Hom P P') (a : P.A) : f.f (P.D.φ a) = P'.D.φ (f.f a) :=
  P.D.map_φ_of_map_δ P'.D f.f f.f_δ a
theorem Delta.l_mem_of_isUnit (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {q : A}
    (hq : IsUnit (D.δ q)) : (l : A) ∈ Ideal.span {q} ⊔ (Ideal.span {q}).map D.φ := by
  obtain ⟨v, hv⟩ := hq.exists_right_inv
  have e : (l : A) = v * (D.φ q - q ^ l) := by
    rw [D.φ_eq]; linear_combination (-(l : A)) * hv
  rw [e]
  refine Ideal.mul_mem_left _ _ (Ideal.sub_mem _ ?_ ?_)
  · exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self q))
  · exact Ideal.mem_sup_left (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self q) _ hl)
theorem invertible_span_singleton {A : Type} [CommRing A] {q : A} (hq : q ∈ nonZeroDivisors A) :
    Module.Invertible A ↥(Ideal.span {q}) :=
  Module.Invertible.congr (M := A)
    ((LinearEquiv.ofInjective (LinearMap.toSpanSingleton A A q) (by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      exact fun a h => (mem_nonZeroDivisors_iff.1 hq).2 a h)).trans
      (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range A A q).symm))
def Obj.ofDistinguished (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) (q : A)
    (hq : q ∈ nonZeroDivisors A) (hδ : IsUnit (D.δ q))
    (hc : IsAdicComplete (Ideal.span {(l : A)} ⊔ Ideal.span {q}) A)
    (hb : ∃ n : ℕ, ∀ x : A ⧸ Ideal.span {q}, (∃ m : ℕ, (l : A ⧸ Ideal.span {q}) ^ m * x = 0) →
      (l : A ⧸ Ideal.span {q}) ^ n * x = 0)
    (str : R →+* A ⧸ Ideal.span {q}) : Obj l R where
  A := A
  D := D
  I := Ideal.span {q}
  inv := invertible_span_singleton hq
  complete := hc
  l_mem := D.l_mem_of_isUnit hl hδ
  bdd := hb
  str := str
def Obj.restrict {R' : Type} [CommRing R'] (g : R →+* R') (P : Obj l R') : Obj l R where
  A := P.A
  D := P.D
  I := P.I
  inv := P.inv
  complete := P.complete
  l_mem := P.l_mem
  bdd := P.bdd
  str := P.str.comp g
def Hom.restrict {R' : Type} [CommRing R'] (g : R →+* R') {P P' : Obj l R'} (f : Hom P P') :
    Hom (P.restrict g) (P'.restrict g) where
  f := f.f
  f_δ := f.f_δ
  f_I := f.f_I
  f_str r a h := f.f_str (g r) a h
def FCrys.pullback {R' : Type} [CommRing R'] (g : R →+* R') (E : FCrys l R) : FCrys l R' where
  M P := E.M (P.restrict g)
  acg P := E.acg (P.restrict g)
  mod P := E.mod (P.restrict g)
  fin P := E.fin (P.restrict g)
  proj P := E.proj (P.restrict g)
  tr f := E.tr (f.restrict g)
  tr_bc f := E.tr_bc (f.restrict g)
  tr_id P := E.tr_id (P.restrict g)
  tr_comp f' f := E.tr_comp (f'.restrict g) (f.restrict g)
  Φ P := E.Φ (P.restrict g)
  Φ_bc P := E.Φ_bc (P.restrict g)
  Φ_nat f := E.Φ_nat (f.restrict g)
def Obj.crys (l : ℕ) [hl : Fact l.Prime] : Obj l ℤ_[l] where
  A := ℤ_[l]
  D := Delta.ofLift l (RingHom.id _)
    (fun x hx => (mul_eq_zero.1 hx).resolve_left (by exact_mod_cast hl.out.ne_zero))
    (fun a => by
      have : a - a ^ l ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
        simp [RingHom.mem_ker]
      rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
      obtain ⟨b, hb⟩ := this
      exact ⟨b, by simp only [RingHom.id_apply]; linear_combination hb⟩)
  I := Ideal.span {(l : ℤ_[l])}
  inv := invertible_span_singleton (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hl.out.ne_zero))
  complete := by
    rw [sup_idem, ← PadicInt.maximalIdeal_eq_span_p]; infer_instance
  l_mem := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  bdd := ⟨1, fun x _ => by
    have : ((l : ℕ) : ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l])}) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    simp [this]⟩
  str := Ideal.Quotient.mk _
theorem semiBC_self {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : SemiBC f.toSemilinearMap := by
  intro Q _ _ v
  refine ⟨LinearMap.toSpanSingleton B Q (v 1), fun x => ?_, fun w hw => ?_⟩
  · have := v.map_smulₛₗ x 1
    simp at this
    simp [this]
  · ext
    have := hw 1
    simpa using this
def FCrys.unit (l : ℕ) (R : Type) [CommRing R] : FCrys l R where
  M P := P.A
  fin _ := inferInstance
  proj _ := inferInstance
  tr f := f.f.toSemilinearMap
  tr_bc f := semiBC_self f.f
  tr_id _ _ := rfl
  tr_comp _ _ _ := rfl
  Φ P d := ((algebraMap P.A (Localization.Away (d : P.A))).comp P.D.φ).toSemilinearMap
  Φ_bc P d := semiBC_self _
  Φ_nat := by
    intro P P' f d d' x m k n j h1 h2
    have key : ∀ {A : Type} [CommRing A] (e y m : A) (k : ℕ),
        IsFrac e (algebraMap A (Localization.Away e) y) m k → ∃ a : ℕ, e ^ a * (e ^ k * y) = e ^ a * m := by
      intro A _ e y m k h
      have h' : LocalizedModule.mk y (1 : Submonoid.powers e) = _ := h
      rw [LocalizedModule.mk_eq] at h'
      obtain ⟨⟨_, a, rfl⟩, ha⟩ := h'
      exact ⟨a, by simpa [Submonoid.smul_def] using ha⟩
    obtain ⟨a, ha⟩ := key _ _ _ _ h1
    obtain ⟨b, hb⟩ := key _ _ _ _ h2
    have ha' := congrArg f.f ha
    simp only [map_mul, map_pow, f.f_φ] at ha'
    refine ⟨a + b, ?_⟩
    change (f.f d * d') ^ (a + b) * ((d' : P'.A) ^ j * f.f m - f.f d ^ k * n) = 0
    change (d' : P'.A) ^ b * ((d' : P'.A) ^ j * P'.D.φ (f.f x)) = _ at hb
    linear_combination (-(f.f d) ^ b * (d' : P'.A) ^ (a + b + j)) * ha' +
      (f.f d ^ (a + b + k) * (d' : P'.A) ^ a) * hb
def VBun.unit (l : ℕ) (R : Type) [CommRing R] : VBun l R := (FCrys.unit l R).toVBun
def FHom.id (E : FCrys l R) : FHom E E where
  u _ := LinearMap.id
  u_tr _ _ := rfl
  u_Φ _ _ _ _ _ h := h
def FHom.comp {E E' E'' : FCrys l R} (v : FHom E' E'') (u : FHom E E') : FHom E E'' where
  u P := (v.u P).comp (u.u P)
  u_tr f x := by simp [u.u_tr, v.u_tr]
  u_Φ P d x m k h := v.u_Φ P d _ _ k (u.u_Φ P d x m k h)
instance FCrys.unit_crys_nontrivial (l : ℕ) [Fact l.Prime] :
    Nontrivial ((FCrys.unit l ℤ_[l]).M (Obj.crys l)) :=
  inferInstanceAs (Nontrivial ℤ_[l])
instance VBun.unit_crys_nontrivial (l : ℕ) [Fact l.Prime] :
    Nontrivial ((VBun.unit l ℤ_[l]).M (Obj.crys l)) :=
  inferInstanceAs (Nontrivial ℤ_[l])
example (l : ℕ) [hl : Fact l.Prime] :
    (Obj.crys l).D.δ (l : ℤ_[l]) = (1 : ℤ_[l]) - (l : ℤ_[l]) ^ (l - 1) := by
  have h : (l : ℤ_[l]) = (l : ℤ_[l]) ^ l + (l : ℤ_[l]) * (show ℤ_[l] from (Obj.crys l).D.δ (l : ℤ_[l])) :=
    (Obj.crys l).D.φ_eq (l : ℤ_[l])
  have h0 : (l : ℤ_[l]) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have h1 : (l : ℤ_[l]) ^ l = (l : ℤ_[l]) * (l : ℤ_[l]) ^ (l - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hl.out.one_le]
  refine mul_left_cancel₀ h0 (b := (show ℤ_[l] from (Obj.crys l).D.δ (l : ℤ_[l]))) ?_
  linear_combination -h - h1
example {A : Type} [CommRing A] (D : Delta 2 A) : D.δ 2 = -1 := by
  have hI : Finset.Ioo 0 2 = {1} := by decide
  have h1 := D.δ_add 1 1
  rw [hI, D.δ_one, one_add_one_eq_two] at h1
  simpa using h1
end GlobalTheory.Prism


