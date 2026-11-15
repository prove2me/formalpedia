-- Prove2me | Definitions.Def_RPLib_S3_X1CountB
-- name    : RPLib_S3_X1CountB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:23:37.906616+00:00
-- url     : https://prove2.me/theorems/35496ec3-10e6-4eee-a881-d437879d4393
-- title:
--   Weight-two Ramanujan-Petersson library: one plane-curve component versus the places of its function field
-- statement:
--   One plane-curve component versus the places of its function field.
--
--   For `g ∈ k[X][Y]` monic in `Y`, irreducible, with `∂g/∂Y ≠ 0` (a `Comp k`), the function field
--   `FF g = k(X)[Y]/(g)` is a separable function field over `k(X)`, and the number of `L`-points of the affine
--   curve `g = 0` differs from `numPoints k (FF g) [L : k]` by a constant independent of the finite field `L`.
--   Route: `#{g = 0}(L) = #Hom_k(k[X][Y]/(g), L)`; a conductor `c` with `c · Rfin ⊆ k[X][y]` makes restriction a
--   bijection away from `c = 0`; the bad homs factor through finite quotients (`card_algHom_le_finrank`);
--   every hom out of `Rinf` kills `1/x`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_PlacesC

/-!
# S3-X1Count, part B: one plane-curve component versus the places of its function field

For `g ∈ k[X][Y]` monic in `Y`, irreducible, with `∂g/∂Y ≠ 0` (a `Comp k`), the function field
`FF g = k(X)[Y]/(g)` is a separable function field over `k(X)`, and the number of `L`-points of the affine
curve `g = 0` differs from `numPoints k (FF g) [L : k]` by a constant independent of the finite field `L`.
Route: `#{g = 0}(L) = #Hom_k(k[X][Y]/(g), L)`; a conductor `c` with `c · Rfin ⊆ k[X][y]` makes restriction a
bijection away from `c = 0`; the bad homs factor through finite quotients (`card_algHom_le_finrank`);
every hom out of `Rinf` kills `1/x`.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.X1Count

open RamanujanPetersson.Places

/-! ### Evaluation of bivariate polynomials -/

section Ev

variable {k : Type*} [Field k] {L : Type*} [Field L] [Algebra k L]

/-- Evaluation of `g(X, Y) ∈ k[X][Y]` (outer variable `Y`) at `v = (x, y)`. -/
noncomputable def ev (v : L × L) : k[X][X] →ₐ[k] L := aevalTower (aeval v.1) v.2

@[simp] lemma ev_C (v : L × L) (a : k[X]) : ev v (C a) = aeval v.1 a := aevalTower_C _ _ _

@[simp] lemma ev_X (v : L × L) : ev v (X : k[X][X]) = v.2 := aevalTower_X _ _

lemma ev_apply (v : L × L) (g : k[X][X]) :
    ev v g = g.eval₂ ((aeval v.1 : k[X] →ₐ[k] L) : k[X] →+* L) v.2 := rfl

end Ev

/-! ### Extension of homomorphisms across a conductor -/

section Ext

variable {k A R L : Type*} [Field k] [CommRing A] [CommRing R] [Algebra k A] [Algebra k R]
  [Field L] [Algebra k L]

/-- Extension of `φ : A → L` with `φ c ≠ 0` to `R ⊇ A` when `c R ⊆ A`. -/
noncomputable def extHom {ι : A →ₐ[k] R} (hι : Function.Injective ι) {c : A}
    (hc : ∀ b : R, ∃ a : A, ι a = ι c * b) (φ : A →ₐ[k] L) (hφ : ¬ φ c = 0) : R →ₐ[k] L where
  toFun b := φ (hc b).choose / φ c
  map_one' := by
    have h : ι (hc 1).choose = ι c := by rw [(hc 1).choose_spec, mul_one]
    show φ (hc 1).choose / φ c = 1
    rw [hι h, div_self hφ]
  map_mul' b₁ b₂ := by
    have h := (hc (b₁ * b₂)).choose_spec
    have h1 := (hc b₁).choose_spec
    have h2 := (hc b₂).choose_spec
    have e0 : c * (hc (b₁ * b₂)).choose = (hc b₁).choose * (hc b₂).choose :=
      hι (by rw [map_mul, map_mul, h, h1, h2]; ring)
    have e : φ c * φ (hc (b₁ * b₂)).choose = φ (hc b₁).choose * φ (hc b₂).choose := by
      rw [← map_mul, ← map_mul, e0]
    show φ (hc (b₁ * b₂)).choose / φ c = φ (hc b₁).choose / φ c * (φ (hc b₂).choose / φ c)
    rw [div_mul_div_comm, div_eq_div_iff hφ (mul_ne_zero hφ hφ)]
    linear_combination (φ c) * e
  map_zero' := by
    have h : ι (hc 0).choose = ι 0 := by rw [(hc 0).choose_spec, mul_zero, map_zero]
    show φ (hc 0).choose / φ c = 0
    rw [hι h, map_zero, zero_div]
  map_add' b₁ b₂ := by
    have h := (hc (b₁ + b₂)).choose_spec
    have h1 := (hc b₁).choose_spec
    have h2 := (hc b₂).choose_spec
    have e0 : (hc (b₁ + b₂)).choose = (hc b₁).choose + (hc b₂).choose :=
      hι (by rw [map_add, h, h1, h2]; ring)
    show φ (hc (b₁ + b₂)).choose / φ c = φ (hc b₁).choose / φ c + φ (hc b₂).choose / φ c
    rw [e0, map_add, add_div]
  commutes' r := by
    have h := (hc (algebraMap k R r)).choose_spec
    have e0 : (hc (algebraMap k R r)).choose = r • c :=
      hι (by rw [h, map_smul, Algebra.smul_def, mul_comm])
    show φ (hc (algebraMap k R r)).choose / φ c = algebraMap k L r
    rw [e0, map_smul, Algebra.smul_def, mul_div_assoc, div_self hφ, mul_one]

lemma extHom_comp {ι : A →ₐ[k] R} (hι : Function.Injective ι) {c : A}
    (hc : ∀ b : R, ∃ a : A, ι a = ι c * b) (φ : A →ₐ[k] L) (hφ : ¬ φ c = 0) :
    (extHom hι hc φ hφ).comp ι = φ := by
  ext a
  show φ (hc (ι a)).choose / φ c = φ a
  have h := (hc (ι a)).choose_spec
  have e0 : (hc (ι a)).choose = c * a := hι (by rw [h, map_mul])
  rw [e0, map_mul, mul_div_cancel_left₀ _ hφ]

/-- Homs killing `d` factor through `B ⧸ (d)`. -/
noncomputable def killMap {B : Type*} [CommRing B] [Algebra k B] (d : B) :
    {φ : B →ₐ[k] L // φ d = 0} → (B ⧸ Ideal.span {d} →ₐ[k] L) := fun φ =>
  Ideal.Quotient.liftₐ (Ideal.span {d}) φ.1 (fun a ha => by
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, φ.2, mul_zero])

lemma killMap_injective {B : Type*} [CommRing B] [Algebra k B] (d : B) :
    Function.Injective (killMap (L := L) (k := k) d) := by
  intro φ₁ φ₂ h
  apply Subtype.ext
  ext a
  have := congrArg (fun ψ : (B ⧸ Ideal.span {d}) →ₐ[k] L => ψ (Ideal.Quotient.mk _ a)) h
  exact this

lemma card_kill_le {B : Type*} [CommRing B] [Algebra k B] (d : B) [Finite (B ⧸ Ideal.span {d})] :
    Nat.card {φ : B →ₐ[k] L // φ d = 0} ≤ Module.finrank k (B ⧸ Ideal.span {d}) := by
  have : Module.Finite k (B ⧸ Ideal.span {d}) := Module.Finite.of_finite
  exact (Nat.card_le_card_of_injective _ (killMap_injective d)).trans (card_algHom_le_finrank k _ L)

lemma restrict_injective {ι : A →ₐ[k] R} {c : A} (hc : ∀ b : R, ∃ a : A, ι a = ι c * b) :
    Function.Injective (fun ψ : {ψ : R →ₐ[k] L // ¬ ψ (ι c) = 0} => ψ.1.comp ι) := by
  intro ψ₁ ψ₂ h
  apply Subtype.ext
  ext b
  obtain ⟨a, ha⟩ := hc b
  have ea := congrArg (fun φ : A →ₐ[k] L => φ a) h
  have ec := congrArg (fun φ : A →ₐ[k] L => φ c) h
  simp only [AlgHom.comp_apply] at ea ec
  rw [ha, map_mul, map_mul, ec] at ea
  exact mul_left_cancel₀ (ec ▸ ψ₁.2) ea

lemma ext_injective {ι : A →ₐ[k] R} (hι : Function.Injective ι) {c : A}
    (hc : ∀ b : R, ∃ a : A, ι a = ι c * b) :
    Function.Injective (fun φ : {φ : A →ₐ[k] L // ¬ φ c = 0} => extHom hι hc φ.1 φ.2) := by
  intro φ₁ φ₂ h
  apply Subtype.ext
  rw [← extHom_comp hι hc φ₁.1 φ₁.2, ← extHom_comp hι hc φ₂.1 φ₂.2]
  exact congrArg (fun ψ : R →ₐ[k] L => ψ.comp ι) h

/-- **Conductor count**: `#Hom(A, L)` and `#Hom(R, L)` differ by at most the dimensions of `A/(c)`, `R/(c)`. -/
theorem card_algHom_le_of_conductor {ι : A →ₐ[k] R} (hι : Function.Injective ι) {c : A}
    (hc : ∀ b : R, ∃ a : A, ι a = ι c * b) [Finite (A ⧸ Ideal.span {c})]
    [Finite (R ⧸ Ideal.span {ι c})] [Finite (A →ₐ[k] L)] :
    Nat.card (A →ₐ[k] L) ≤ Nat.card (R →ₐ[k] L) + Module.finrank k (A ⧸ Ideal.span {c}) ∧
    Nat.card (R →ₐ[k] L) ≤ Nat.card (A →ₐ[k] L) + Module.finrank k (R ⧸ Ideal.span {ι c}) := by
  classical
  have : Module.Finite k (R ⧸ Ideal.span {ι c}) := Module.Finite.of_finite
  have : Finite {ψ : R →ₐ[k] L // ψ (ι c) = 0} := Finite.of_injective _ (killMap_injective (ι c))
  have : Finite {ψ : R →ₐ[k] L // ¬ ψ (ι c) = 0} := Finite.of_injective _ (restrict_injective hc)
  have : Finite (R →ₐ[k] L) := Finite.of_equiv _ (Equiv.sumCompl (fun ψ : R →ₐ[k] L => ψ (ι c) = 0))
  have eA : Nat.card (A →ₐ[k] L) =
      Nat.card {φ : A →ₐ[k] L // φ c = 0} + Nat.card {φ : A →ₐ[k] L // ¬ φ c = 0} := by
    rw [← Nat.card_sum]; exact Nat.card_congr (Equiv.sumCompl _).symm
  have eR : Nat.card (R →ₐ[k] L) =
      Nat.card {ψ : R →ₐ[k] L // ψ (ι c) = 0} + Nat.card {ψ : R →ₐ[k] L // ¬ ψ (ι c) = 0} := by
    rw [← Nat.card_sum]; exact Nat.card_congr (Equiv.sumCompl _).symm
  have a1 := card_kill_le (k := k) (L := L) c
  have a2 := card_kill_le (k := k) (L := L) (ι c)
  have a3 : Nat.card {φ : A →ₐ[k] L // ¬ φ c = 0} ≤ Nat.card (R →ₐ[k] L) :=
    Nat.card_le_card_of_injective _ (ext_injective hι hc)
  have a4 : Nat.card {ψ : R →ₐ[k] L // ¬ ψ (ι c) = 0} ≤ Nat.card (A →ₐ[k] L) :=
    Nat.card_le_card_of_injective _ (restrict_injective hc)
  constructor <;> omega

end Ext

/-! ### Points of `g = 0` are the homs out of `k[X][Y]/(g)` -/

section Points

variable {k : Type*} [Field k] (g : k[X][X]) (L : Type*) [Field L] [Algebra k L]

lemma aeval_eq_comp (φ : AdjoinRoot g →ₐ[k] L) :
    ((aeval (φ (AdjoinRoot.of g X)) : k[X] →ₐ[k] L) : k[X] →+* L) =
      (φ : AdjoinRoot g →+* L).comp (AdjoinRoot.of g) := by
  have : (aeval (φ (AdjoinRoot.of g X)) : k[X] →ₐ[k] L) = φ.comp (AdjoinRoot.ofAlgHom k g) :=
    Polynomial.algHom_ext (by simp)
  rw [this]
  rfl

lemma liftAlgHom_ofX (x y : L) (h : g.eval₂ ((aeval x : k[X] →ₐ[k] L) : k[X] →+* L) y = 0) :
    AdjoinRoot.liftAlgHom g (aeval x) y h ((AdjoinRoot.ofAlgHom k g) X) = x :=
  (AdjoinRoot.liftAlgHom_of g (aeval x) y h X).trans (aeval_X x)

/-- `Hom_k(k[X][Y]/(g), L) ≃ {v ∈ L² | g(v) = 0}`. -/
noncomputable def ptEquiv : (AdjoinRoot g →ₐ[k] L) ≃ {v : L × L // ev v g = 0} where
  toFun φ := ⟨(φ (AdjoinRoot.of g X), φ (AdjoinRoot.root g)), by
    have := congrArg φ (AdjoinRoot.eval₂_root g)
    rw [map_zero, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂] at this
    rw [ev_apply, aeval_eq_comp]
    exact this⟩
  invFun v := AdjoinRoot.liftAlgHom g (aeval v.1.1) v.1.2 v.2
  left_inv φ := by
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      rw [AlgHom.comp_apply, AlgHom.comp_apply]
      exact liftAlgHom_ofX g L _ _ _
    · exact AdjoinRoot.liftAlgHom_root _ _ _ _
  right_inv v := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · exact (AdjoinRoot.liftAlgHom_of g _ _ _ X).trans (aeval_X _)
    · exact AdjoinRoot.liftAlgHom_root g _ _ _

lemma card_points_eq : Nat.card {v : L × L // ev v g = 0} = Nat.card (AdjoinRoot g →ₐ[k] L) :=
  (Nat.card_congr (ptEquiv g L)).symm

instance finite_algHom_adjoinRoot [Finite L] : Finite (AdjoinRoot g →ₐ[k] L) :=
  Finite.of_equiv _ (ptEquiv g L).symm

end Points

/-! ### Components and their function fields -/

section FF

variable (k : Type) [Field k] [Fintype k] [DecidableEq (RatFunc k)]

/-- A component: `g ∈ k[X][Y]` monic in `Y`, irreducible, with `∂g/∂Y ≠ 0`. -/
def Comp : Type := {g : k[X][X] // g.Monic ∧ Irreducible g ∧ derivative g ≠ 0}

variable {k}

/-- `g` over `k(X)`. -/
noncomputable def Comp.gK (g : Comp k) : (RatFunc k)[X] := g.1.map (algebraMap k[X] (RatFunc k))

lemma Comp.gK_monic (g : Comp k) : g.gK.Monic := g.2.1.map _

lemma Comp.gK_irreducible (g : Comp k) : Irreducible g.gK :=
  (g.2.1.irreducible_iff_irreducible_map_fraction_map (K := RatFunc k)).1 g.2.2.1

instance (g : Comp k) : Fact (Irreducible g.gK) := ⟨g.gK_irreducible⟩

/-- The function field `k(X)[Y]/(g)` of the component. -/
abbrev Comp.FF (g : Comp k) : Type := AdjoinRoot g.gK

instance (g : Comp k) : FunctionField k g.FF := (AdjoinRoot.powerBasis g.gK_monic.ne_zero).finite

lemma Comp.gK_separable (g : Comp k) : g.gK.Separable := by
  rw [Polynomial.separable_iff_derivative_ne_zero g.gK_irreducible, Comp.gK, Polynomial.derivative_map]
  exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective k[X] (RatFunc k))).mpr g.2.2.2

instance (g : Comp k) : Algebra.IsSeparable (RatFunc k) g.FF := by
  have hroot : IsSeparable (RatFunc k) (AdjoinRoot.root g.gK) := by
    rw [IsSeparable, AdjoinRoot.minpoly_root g.gK_monic.ne_zero, g.gK_monic.leadingCoeff, inv_one, C_1,
      mul_one]
    exact g.gK_separable
  have h1 := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (RatFunc k) g.FF).2 hroot
  have htop : IntermediateField.adjoin (RatFunc k) {AdjoinRoot.root g.gK} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ (by rw [AdjoinRoot.adjoinRoot_eq_top]; trivial)
  rw [htop] at h1
  exact Algebra.IsSeparable.of_algHom _ _ (IntermediateField.topEquiv (F := RatFunc k) (E := g.FF)).symm.toAlgHom

example (g : Comp k) : IsScalarTower k[X] (RatFunc k) g.FF := inferInstance
example (g : Comp k) : IsScalarTower k k[X] g.FF := inferInstance

variable (g : Comp k)

/-- The affine coordinate ring `k[X][Y]/(g)`. -/
abbrev Comp.A : Type := AdjoinRoot g.1

lemma Comp.aeval_root : aeval (AdjoinRoot.root g.gK) g.1 = 0 := by
  rw [← Polynomial.aeval_map_algebraMap (RatFunc k), AdjoinRoot.aeval_eq]
  exact AdjoinRoot.mk_self

/-- `k[X][Y]/(g) → FF g`. -/
noncomputable def Comp.ιF : g.A →ₐ[k[X]] g.FF :=
  AdjoinRoot.liftAlgHom g.1 (Algebra.ofId k[X] g.FF) (AdjoinRoot.root g.gK) g.aeval_root

lemma Comp.ιF_mk (q : k[X][X]) :
    g.ιF (AdjoinRoot.mk g.1 q) = AdjoinRoot.mk g.gK (q.map (algebraMap k[X] (RatFunc k))) := by
  refine (AdjoinRoot.liftAlgHom_mk g.1 (Algebra.ofId k[X] g.FF) (AdjoinRoot.root g.gK) g.aeval_root q).trans ?_
  change aeval (AdjoinRoot.root g.gK) q = _
  rw [← Polynomial.aeval_map_algebraMap (RatFunc k), AdjoinRoot.aeval_eq]

lemma Comp.ιF_injective : Function.Injective g.ιF := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
  rw [Comp.ιF_mk, AdjoinRoot.mk_eq_zero] at ha
  rw [AdjoinRoot.mk_eq_zero]
  exact (Polynomial.map_dvd_map _ (IsFractionRing.injective k[X] (RatFunc k)) g.2.1).mp ha

lemma Comp.exists_smul_mem (b : g.FF) : ∃ d : k[X], d ≠ 0 ∧ ∃ a : g.A, g.ιF a = d • b := by
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective b
  obtain ⟨⟨d, hd⟩, hq⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors k[X]) q
  refine ⟨d, nonZeroDivisors.ne_zero hd,
    AdjoinRoot.mk g.1 (IsLocalization.integerNormalization (nonZeroDivisors k[X]) q), ?_⟩
  rw [g.ιF_mk, hq, Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1

instance : Algebra.IsIntegral k[X] g.A := by
  have := (AdjoinRoot.powerBasis' g.2.1).finite
  infer_instance

/-- `k[X][Y]/(g) → Rfin`. -/
noncomputable def Comp.ιR : g.A →ₐ[k[X]] Rfin k g.FF :=
  g.ιF.codRestrict (FunctionField.ringOfIntegers k g.FF) (fun a => by
    show g.ιF a ∈ integralClosure k[X] g.FF
    exact (Algebra.IsIntegral.isIntegral a).map g.ιF)

lemma Comp.coe_ιR (a : g.A) : (g.ιR a : g.FF) = g.ιF a := rfl

lemma Comp.ιR_injective : Function.Injective g.ιR := fun a b h =>
  g.ιF_injective (by rw [← g.coe_ιR, ← g.coe_ιR, h])

lemma Comp.exists_conductor :
    ∃ c : k[X], c ≠ 0 ∧ ∀ b : Rfin k g.FF, ∃ a : g.A, g.ιR a = c • b := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := k[X]) (M := Rfin k g.FF)
  choose! d hd a ha using fun b : Rfin k g.FF => g.exists_smul_mem (b : g.FF)
  refine ⟨∏ b ∈ s, d b, Finset.prod_ne_zero_iff.mpr fun b _ => hd b, ?_⟩
  let N : Submodule k[X] (Rfin k g.FF) :=
    (LinearMap.range g.ιR.toLinearMap).comap ((∏ b ∈ s, d b) • LinearMap.id)
  have hsN : (s : Set (Rfin k g.FF)) ⊆ N := by
    intro b hb
    have e1 : d b • b = g.ιR (a b) := Subtype.ext (by rw [g.coe_ιR, ha b]; rfl)
    have e2 : (∏ b ∈ s, d b) • b = (∏ b' ∈ s.erase b, d b') • g.ιR (a b) := by
      rw [← e1, smul_smul, Finset.prod_erase_mul s d hb]
    show ((∏ b ∈ s, d b) • LinearMap.id : Rfin k g.FF →ₗ[k[X]] Rfin k g.FF) b ∈ LinearMap.range g.ιR.toLinearMap
    rw [LinearMap.smul_apply, LinearMap.id_apply, e2]
    exact Submodule.smul_mem _ _ ⟨a b, rfl⟩
  intro b
  have hb : b ∈ N := by
    have := Submodule.span_le.mpr hsN
    rw [hs] at this
    exact this Submodule.mem_top
  obtain ⟨a', ha'⟩ := hb
  exact ⟨a', ha'⟩

/-- `k[X][Y]/(g) → Rfin` over `k`. -/
noncomputable def Comp.ιk : g.A →ₐ[k] Rfin k g.FF := g.ιR.restrictScalars k

instance : Module.Free k[X] g.A := Module.Free.of_basis (AdjoinRoot.powerBasis' g.2.1).basis
instance : Module.Finite k[X] g.A := (AdjoinRoot.powerBasis' g.2.1).finite
instance : IsDomain g.A := AdjoinRoot.isDomain_of_prime g.2.2.1.prime

lemma Comp.ιF_algebraMap_ne_zero {c : k[X]} (hc : c ≠ 0) : g.ιF (algebraMap k[X] g.A c) ≠ 0 := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k[X] (RatFunc k) g.FF, Ne,
    map_eq_zero_iff _ (algebraMap (RatFunc k) g.FF).injective,
    map_eq_zero_iff _ (IsFractionRing.injective k[X] (RatFunc k))]
  exact hc

lemma Comp.finite_quot {c : k[X]} (hc : c ≠ 0) :
    Finite (g.A ⧸ Ideal.span {algebraMap k[X] g.A c}) := by
  have hne : algebraMap k[X] g.A c ≠ 0 := fun h => g.ιF_algebraMap_ne_zero hc (by rw [h, map_zero])
  apply Nat.finite_of_card_ne_zero
  rw [card_quot_eq_card_quot_norm (A := k[X]) _ hne, Algebra.norm_algebraMap,
    card_polyQuot (pow_ne_zero _ hc)]
  exact pow_ne_zero _ Fintype.card_ne_zero

/-! ### Homs out of `Rinf` kill `1/x` -/

lemma isUnit_piInf_pow_sub_one {n : ℕ} (hn : n ≠ 0) : IsUnit (piInf k ^ n - 1) := by
  by_contra h
  have hmax : (Ideal.span {piInf k}) = IsLocalRing.maximalIdeal (Oinf k) :=
    IsLocalRing.eq_maximalIdeal (span_piInf_isMaximal k)
  have hmem : piInf k ^ n - 1 ∈ Ideal.span {piInf k} := by
    rw [hmax]; exact h
  have hpow : piInf k ^ n ∈ Ideal.span {piInf k} :=
    Ideal.mem_span_singleton.mpr (dvd_pow_self _ hn)
  have h1 : (1 : Oinf k) ∈ Ideal.span {piInf k} := by
    have := Ideal.sub_mem _ hpow hmem
    rwa [sub_sub_cancel] at this
  exact (span_piInf_isMaximal k).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

lemma card_algHom_Rinf_le (L : Type) [Field L] [Finite L] [Algebra k L] :
    Nat.card (Rinf k g.FF →ₐ[k] L) ≤
      Module.finrank k (Rinf k g.FF ⧸ Ideal.span {algebraMap (Oinf k) (Rinf k g.FF) (piInf k)}) := by
  set π' := algebraMap (Oinf k) (Rinf k g.FF) (piInf k)
  have hπ : π' ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (Oinf k) (Rinf k g.FF)), (algebraMap_Oinf_Rinf_injective k g.FF).eq_iff]
    exact piInf_ne_zero k
  have : Finite (Rinf k g.FF ⧸ Ideal.span {π'}) := FiniteQuot.finite _ hπ
  have hkill : ∀ ψ : Rinf k g.FF →ₐ[k] L, ψ π' = 0 := by
    intro ψ
    have : Fintype L := Fintype.ofFinite L
    set Q := Fintype.card L with hQ
    have hQ1 : 1 ≤ Q := Fintype.card_pos
    have hu : IsUnit (ψ (π' ^ (Q - 1) - 1)) := by
      have := (isUnit_piInf_pow_sub_one (k := k) (n := Q - 1) (by
        have : 2 ≤ Q := by
          have := Fintype.one_lt_card (α := L)
          omega
        omega)).map (algebraMap (Oinf k) (Rinf k g.FF))
      rw [map_sub, map_pow, map_one] at this
      exact this.map ψ
    have hF : ψ π' ^ Q = ψ π' := FiniteField.pow_card _
    have h0 : ψ π' * ψ (π' ^ (Q - 1) - 1) = 0 := by
      rw [map_sub, map_pow, map_one, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hQ1, hF, sub_self]
    exact (mul_eq_zero.mp h0).resolve_right hu.ne_zero
  have : Module.Finite k (Rinf k g.FF ⧸ Ideal.span {π'}) := Module.Finite.of_finite
  calc Nat.card (Rinf k g.FF →ₐ[k] L) = Nat.card {ψ : Rinf k g.FF →ₐ[k] L // ψ π' = 0} :=
        (Nat.card_congr (Equiv.subtypeUnivEquiv hkill)).symm
    _ ≤ _ := card_kill_le π'

/-! ### The per-component count -/

/-- **Component count**: `|#{g = 0}(L) - N_{[L:k]}(FF g)| ≤ C` for every finite field `L ⊇ k`. -/
theorem Comp.card_points_sub_numPoints_le :
    ∃ C : ℕ, ∀ (L : Type) [Field L] [Finite L] [Algebra k L],
      |(Nat.card {v : L × L // ev v g.1 = 0} : ℤ) - numPoints k g.FF (Module.finrank k L)| ≤ C := by
  obtain ⟨c, hc0, hc⟩ := g.exists_conductor
  set c' := algebraMap k[X] g.A c
  have hι : Function.Injective g.ιk := g.ιR_injective
  have hc' : ∀ b : Rfin k g.FF, ∃ a : g.A, g.ιk a = g.ιk c' * b := by
    intro b
    obtain ⟨a, ha⟩ := hc b
    refine ⟨a, ?_⟩
    show g.ιR a = g.ιR c' * b
    rw [ha, AlgHom.commutes, Algebra.smul_def]
  have : Finite (g.A ⧸ Ideal.span {c'}) := g.finite_quot hc0
  have hne : g.ιk c' ≠ 0 := fun h => g.ιF_algebraMap_ne_zero hc0 (by
    rw [← g.coe_ιR]; exact congrArg Subtype.val h)
  have : Finite (Rfin k g.FF ⧸ Ideal.span {g.ιk c'}) := FiniteQuot.finite _ hne
  refine ⟨Module.finrank k (g.A ⧸ Ideal.span {c'}) + Module.finrank k (Rfin k g.FF ⧸ Ideal.span {g.ιk c'}) +
    Module.finrank k (Rinf k g.FF ⧸ Ideal.span {algebraMap (Oinf k) (Rinf k g.FF) (piInf k)}), ?_⟩
  intro L _ _ _
  obtain ⟨h1, h2⟩ := card_algHom_le_of_conductor (L := L) hι hc'
  have h3 := card_algHom_Rinf_le g L
  have e : Nat.card {v : L × L // ev v g.1 = 0} = Nat.card (g.A →ₐ[k] L) := card_points_eq g.1 L
  rw [numPoints_eq_card_algHom k g.FF L, e]
  rw [abs_le]
  constructor <;> push_cast <;> omega

end FF

end RamanujanPetersson.X1Count


