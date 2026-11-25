-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:44:44.278372+00:00
-- url     : https://prove2.me/theorems/6bbb61d7-17aa-5102-87b1-a9d54fbdb096
-- title:
--   Map CSmul Mul Vec
-- statement:
--   Definitions and structural lemmas for Map CSmul Mul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MapCSmulMulVec.lean

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
open PowerSeries
namespace GlobalTheory.NB
structure Fr (l : ℕ) (O : Type) [CommRing O] where
  prime : l.Prime
  odd : l ≠ 2
  l_nonunit : ¬ IsUnit (l : O)

  root : ∃ x : O, Associated (x ^ (l - 1)) (l : O)
  e : ℕ
  s : ℕ
  es : e * s = l - 1
  ϖ : Fin e → O
  ϖ_val : ∀ τ, Associated (ϖ τ ^ e) (l : O)
  ϖ_sub : ∀ τ τ', τ ≠ τ' → Associated (ϖ τ - ϖ τ') (ϖ τ)
  E : O⟦X⟧
  E_def : E = ∏ τ, (X - C (ϖ τ))
  φ : O⟦X⟧ →ₐ[O] O⟦X⟧
  γ : O⟦X⟧ →ₐ[O] O⟦X⟧
  comm : ∀ a, φ (γ a) = γ (φ a)
  u : (O⟦X⟧)ˣ
  φ_X : φ X = (u : O⟦X⟧) * X * E ^ s
  κ : (O⟦X⟧)ˣ
  γ_X : γ X = X * (1 + (κ : O⟦X⟧) * E)
  χ : Oˣ
  χ_gen : Associated ((χ : O) - 1) (l : O)
  χ_zero : constantCoeff (1 + (κ : O⟦X⟧) * E) = (χ : O) ^ s

  lev : Fin e → (O⟦X⟧ ≃ₐ[O] O⟦X⟧)
  lev_X : ∀ τ, lev τ X = X + C (ϖ τ)

  χ_lev : ∀ τ, ∃ w : O⟦X⟧, γ (X - C (ϖ τ)) = (X - C (ϖ τ)) * w ∧ constantCoeff (lev τ w) = (χ : O)

  lvl_red : ∀ (k : ℕ) (a : O⟦X⟧), (φ ^ k) E ∣ a ^ 2 → (φ ^ k) E ∣ a

  lvl_triv : ∀ (k : ℕ) (a : O⟦X⟧), (φ ^ k) E ∣ (γ ^ (l ^ k)) a - a

  lvl_inv : e = 1 → ∀ (k : ℕ) (a : O⟦X⟧), (φ ^ k) E ∣ γ a - a → ∃ c : O, (φ ^ k) E ∣ a - C c

  EE : Type
  [eeRing : CommRing EE]
  [eeAlgA : Algebra O⟦X⟧ EE]
  [eeAlgO : Algebra O EE]
  [eeTow : IsScalarTower O O⟦X⟧ EE]
  EE_inj : Function.Injective (algebraMap O⟦X⟧ EE)
  EE_X : IsUnit (algebraMap O⟦X⟧ EE X)
  EE_complete : IsAdicComplete (Ideal.span {(l : EE)}) EE
  EE_dense : ∀ (x : EE) (k : ℕ), ∃ (a : O⟦X⟧) (m : ℕ),
    (l : EE) ^ k ∣ x * algebraMap O⟦X⟧ EE (X ^ m) - algebraMap O⟦X⟧ EE a
  EE_sat : ∀ (a : O⟦X⟧) (k : ℕ), (l : EE) ^ k ∣ algebraMap O⟦X⟧ EE a → (l : O⟦X⟧) ^ k ∣ a
  φE : EE →ₐ[O] EE
  φE_ext : ∀ a, φE (algebraMap O⟦X⟧ EE a) = algebraMap O⟦X⟧ EE (φ a)
  γE : EE →ₐ[O] EE
  γE_ext : ∀ a, γE (algebraMap O⟦X⟧ EE a) = algebraMap O⟦X⟧ EE (γ a)

  coeffRing : ∃ (_ : IsDomain O) (_ : IsDiscreteValuationRing O),
      IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧ CharZero O := by
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
attribute [instance] Fr.eeRing Fr.eeAlgA Fr.eeAlgO Fr.eeTow
def val (l : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (c : O) : ℝ :=
  ((IsDiscreteValuationRing.addVal O c).toNat : ℝ) / ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℝ)
open Classical in

def valTop (l : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (c : O) :
    WithTop ℝ :=
  if c = 0 then ⊤ else (val l c : ℝ)
def LenLe (l : ℕ) (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] (b : ℝ) : Prop :=
  ∃ m k : ℕ, Module.length O M = m ∧ Module.length O (O ⧸ Ideal.span {(l : O)}) = k ∧ (m : ℝ) ≤ b * k
def eF (l r : ℕ) : ℕ := r + padicValNat l r.factorial
inductive Size (l : ℕ) (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] :
    Submodule O M → Submodule O M → ℕ → ℝ → Prop
  | refl (A : Submodule O M) (μ : ℕ) (x : ℝ) (hx : 0 ≤ x) : Size l O M A A μ x
  | gen (A B C : Submodule O M) (μ ν : ℕ) (x : ℝ) (h : Size l O M A B μ x) (t : Finset M)
      (ht : t.card ≤ ν) (hC : C = B ⊔ Submodule.span O (t : Set M)) : Size l O M A C (μ + ν) x
  | len (A B C : Submodule O M) (μ : ℕ) (x y : ℝ) (h : Size l O M A B μ x) (hBC : B ≤ C)
      (hC : LenLe l O (↥C ⧸ B.comap C.subtype) y) : Size l O M A C μ (x + y)
def InId {O : Type} [CommRing O] (c : O) (g f : O⟦X⟧) : Prop := f ∈ Ideal.span {C c, g}
def killer (l : ℕ) {O : Type} [CommRing O] (χ : Oˣ) (m : ℕ) (J : Finset ℤ) : Polynomial O :=
  (∏ i ∈ J.erase 0, (Polynomial.X ^ (l ^ m) - Polynomial.C ((χ ^ (i * (l : ℤ) ^ m) : Oˣ) : O))) *
    ∑ k ∈ Finset.range (l ^ m), Polynomial.X ^ k
namespace Fr
variable {l : ℕ} {O : Type} [CommRing O] (R : Fr l O)
def IsA : Prop := R.e = 1 ∧ ∀ τ, R.ϖ τ = -(l : O)
def IsCyc : Prop :=
  ∃ j γ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧, Function.Injective j ∧ Associated (j X) (X ^ R.s) ∧
    (∀ a, j (R.φ a) = (j a).subst ((1 + X : O⟦X⟧) ^ l - 1)) ∧ (∀ a, j (R.γ a) = γ₀ (j a)) ∧
    (∀ b : O⟦X⟧, γ₀ (b.subst ((1 + X : O⟦X⟧) ^ l - 1)) = (γ₀ b).subst ((1 + X : O⟦X⟧) ^ l - 1)) ∧
    constantCoeff (γ₀ X) = 0 ∧ coeff 1 (γ₀ X) = (R.χ : O)
theorem isUnit_γX_div_X : IsUnit (1 + (R.κ : O⟦X⟧) * R.E) := by
  rw [isUnit_iff_constantCoeff, R.χ_zero]
  exact R.χ.isUnit.pow _
def p (k : ℕ) : O⟦X⟧ := (R.φ ^ k) R.E
def IsLam (f : O⟦X⟧) : Prop := ∃ m : Multiset ℕ, f = (m.map R.p).prod
def pp (j : ℕ) (a : ℕ → ℕ) : O⟦X⟧ := ∏ k ∈ Finset.range j, R.p k ^ a k
abbrev ι : O⟦X⟧ →+* R.EE := algebraMap O⟦X⟧ R.EE
def N0 (r : ℕ) : Submodule O⟦X⟧ (Fin r → R.EE) :=
  Submodule.pi Set.univ fun _ => LinearMap.range (Algebra.linearMap O⟦X⟧ R.EE)
variable [IsDomain O]
def toL (_R : Fr l O) : O⟦X⟧ →+* (FractionRing O)⟦X⟧ := PowerSeries.map (algebraMap O (FractionRing O))
def γL (f : (FractionRing O)⟦X⟧) : (FractionRing O)⟦X⟧ := f.subst (R.toL (R.γ X))
def φL (f : (FractionRing O)⟦X⟧) : (FractionRing O)⟦X⟧ := f.subst (R.toL (R.φ X))
def levL (τ : Fin R.e) : O⟦X⟧ →+* (FractionRing O)⟦X⟧ := R.toL.comp (R.lev τ).toRingEquiv.toRingHom
def φτ (τ : Fin R.e) (f : (FractionRing O)⟦X⟧) : (FractionRing O)⟦X⟧ := f.subst (R.levL τ (R.φ X))
def cc (x : ℤ) : FractionRing O :=
  (algebraMap O (FractionRing O) ((R.χ ^ (-x) : Oˣ) : O) - 1) / (-(l : FractionRing O))
end Fr
structure Sys {l : ℕ} {O : Type} [CommRing O] (R : Fr l O) (n r : ℕ) where
  M : ℕ
  Φ : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧
  G : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧
  G_one : ∀ i, ∃ B : Matrix (Fin r) (Fin r) O⟦X⟧, G i = 1 + (X : O⟦X⟧) • B
  Φ_inv : ∀ i, ∃ (k : ℕ) (Ψ : Matrix (Fin r) (Fin r) O⟦X⟧), Φ i * Ψ = R.E ^ k • (1 : Matrix _ _ _)
  comm : ∀ i, R.E ^ M • (G i * (Φ i).map R.γ) = R.γ R.E ^ M • (Φ i * (G (i - 1)).map R.φ)
abbrev DD {l : ℕ} {O : Type} [CommRing O] (R : Fr l O) (n r : ℕ) : Type := ZMod n → Fin r → R.EE
namespace Sys
variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r : ℕ} (S : Sys R n r)
def one (R : Fr l O) (n g : ℕ) : Sys R n g where
  M := 0
  Φ := fun _ => 1
  G := fun _ => 1
  G_one := fun _ => ⟨0, by simp⟩
  Φ_inv := fun _ => ⟨0, 1, by simp⟩
  comm := fun _ => by simp
def twistNeg (R : Fr l O) (n : ℕ) : Sys R n 1 where
  M := R.s
  Φ := fun _ => ((R.u⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) • 1
  G := fun _ => (C ((R.χ : O) ^ R.s) * ((R.isUnit_γX_div_X.unit⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧)) • 1
  G_one := fun _ => by
    have hw := R.isUnit_γX_div_X.unit_spec
    set w := R.isUnit_γX_div_X.unit
    have h0 : constantCoeff ((w⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) * (R.χ : O) ^ R.s = 1 := by
      rw [← R.χ_zero, ← hw, ← map_mul]; simp
    have : (X : O⟦X⟧) ∣ C ((R.χ : O) ^ R.s) * ((w⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) - 1 := by
      rw [X_dvd_iff]; simp only [map_sub, map_mul, constantCoeff_C, map_one]; rw [mul_comm, h0]; simp
    obtain ⟨b, hb⟩ := this
    refine ⟨b • 1, ?_⟩
    rw [smul_smul, ← hb, sub_smul]; simp
  Φ_inv := fun _ => ⟨0, (R.u : O⟦X⟧) • 1, by simp [smul_smul]⟩
  comm := fun _ => by
    have hw := R.isUnit_γX_div_X.unit_spec
    set w := R.isUnit_γX_div_X.unit
    have hc := R.comm X
    rw [R.γ_X, R.φ_X, ← hw, map_mul, R.φ_X, map_mul, map_mul, map_pow, R.γ_X, ← hw] at hc
    have h1 : (R.u : O⟦X⟧) * R.E ^ R.s * R.φ w = R.γ R.u * w * R.γ R.E ^ R.s := by
      apply X_mul_cancel; linear_combination hc
    have a1 : R.γ ((R.u⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) * R.γ R.u = 1 := by rw [← map_mul]; simp
    have a2 : R.φ ((w⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) * R.φ w = 1 := by rw [← map_mul]; simp
    have a3 : ((w⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) * w = 1 := by simp
    have a4 : ((R.u⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧) * R.u = 1 := by simp
    have hC : R.φ (C ((R.χ : O) ^ R.s)) = C ((R.χ : O) ^ R.s) := R.φ.commutes _
    ext1 i j
    have hij : i = j := Subsingleton.elim _ _
    subst hij
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, Finset.univ_unique,
      Finset.sum_singleton, Subsingleton.elim i default, Matrix.one_apply_eq, smul_eq_mul, map_mul,
      map_one, mul_one, hC]
    set c := C ((R.χ : O) ^ R.s)
    set wi := ((w⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧)
    set ui := ((R.u⁻¹ : (O⟦X⟧)ˣ) : O⟦X⟧)
    linear_combination (c * wi * R.γ ui * ui * R.φ wi) * h1
      - (R.E ^ R.s * c * wi * R.γ ui) * (a4 * (R.φ wi * R.φ w)) - (R.E ^ R.s * c * wi * R.γ ui) * a2
      + (R.γ R.E ^ R.s * c * ui * R.φ wi * (wi * w)) * a1 + (R.γ R.E ^ R.s * c * ui * R.φ wi) * a3
def φl (i : ZMod n) : (Fin r → R.EE) →ₗ[O] (Fin r → R.EE) :=
  ((Ring.inverse (R.ι R.E) ^ S.M • (S.Φ i).map R.ι).mulVecLin.restrictScalars O).comp
    (R.φE.toLinearMap.compLeft (Fin r))
def γl (i : ZMod n) : (Fin r → R.EE) →ₗ[O] (Fin r → R.EE) :=
  (((S.G i).map R.ι).mulVecLin.restrictScalars O).comp (R.γE.toLinearMap.compLeft (Fin r))
def φit (c : ZMod n) (j : ℕ) : (Fin r → R.EE) →ₗ[O] (Fin r → R.EE) :=
  Nat.rec LinearMap.id (fun j f => (S.φl (c + (j : ZMod n) + 1)).comp f) j
def P (c : ZMod n) (j : ℕ) : Submodule O⟦X⟧ (Fin r → R.EE) :=
  Submodule.span O⟦X⟧ (S.φit c j '' (R.N0 r : Set (Fin r → R.EE)))
def InMul (f : O⟦X⟧) (N' : Submodule O⟦X⟧ (Fin r → R.EE)) (x : Fin r → R.EE) : Prop :=
  ∃ y ∈ N', x = f • y
def I (c : ZMod n) : Set (Fin r → R.EE) := {w | InMul X (R.N0 r) (S.γl c w - w)}
def Poles (w : Fin r → R.EE) : Prop := ∃ f, R.IsLam f ∧ f • w ∈ R.N0 r
def φD : DD R n r →ₗ[O] DD R n r := LinearMap.pi fun i => (S.φl i).comp (LinearMap.proj (i - 1))
def γD : DD R n r →ₗ[O] DD R n r := LinearMap.pi fun i => (S.γl i).comp (LinearMap.proj i)
def Z1 : Submodule O (DD R n r × DD R n r) :=
  LinearMap.ker ((S.γD - LinearMap.id).coprod (-(S.φD - LinearMap.id)))
def B1 : Submodule O (DD R n r × DD R n r) :=
  LinearMap.range ((S.φD - LinearMap.id).prod (S.γD - LinearMap.id))
def IntRep (pr : DD R n r × DD R n r) : Prop :=
  ∀ i, Poles (pr.1 i) ∧ InMul X (R.N0 r) (pr.2 i)
def Zf : Submodule O (DD R n r × DD R n r) :=
  Submodule.span O {pr | pr ∈ S.Z1 ∧ ∃ a : ℕ, ∃ b ∈ S.B1, IntRep ((l ^ a : ℕ) • pr + b)} ⊔ S.B1
def FIN (g : ℕ) : Prop :=
  ∃ t : Finset (DD R n r × DD R n r), t.card ≤ g ∧ Submodule.span O (t : Set _) ⊔ S.B1 = S.Zf
def IsCls (m : ℕ) (y z : DD R n r) : Prop := (y, z) ∈ S.Z1 ∧ ∀ i, InMul (X ^ m) (R.N0 r) (z i)
def IsRel (c : ZMod n) (j : ℕ) (f : O⟦X⟧) (g : ℕ) (w z : Fin r → R.EE) : Prop :=
  ∃ (ρ k : ℕ) (W t : Fin r → R.EE), f ∣ ((R.φ ^ j) X) ^ ρ ∧ InMul X (R.N0 r) W ∧
    InMul (X ^ ρ) (R.N0 r) ((S.γl c W - W) - (l ^ k : ℕ) • (S.γl c w - w)) ∧ t ∈ S.P c j ∧
    InMul f (S.P c j) ((l ^ k : ℕ) • t - (l ^ g : ℕ) • S.φit c j W) ∧
    z = (l ^ g : ℕ) • S.φit c j w - t
def IsRho (c : ZMod n) (j : ℕ) (f : O⟦X⟧) (g m : ℕ) (w : Fin r → R.EE)
    (pr : DD R n r × DD R n r) : Prop :=
  ∃ (z : Fin r → R.EE) (z' : DD R n r), S.IsRel c j f g w z ∧
    S.IsCls m (Pi.single (c + (j : ZMod n)) z) z' ∧ pr - (Pi.single (c + (j : ZMod n)) z, z') ∈ S.B1
def Up (i : ZMod n) (f : O⟦X⟧) : Prop := ∀ x ∈ S.P (i - 1) 1, f • x ∈ R.N0 r
def Down (i : ZMod n) (f : O⟦X⟧) : Prop := ∀ x ∈ R.N0 r, f • x ∈ S.P (i - 1) 1
def d (i : ZMod n) : (Fin r → R.EE) →ₗ[O] (Fin r → R.EE) :=
  (Ring.inverse (R.ι X)) • (S.γl i - LinearMap.id)
variable [IsDomain O]
def γF (i : ZMod n) (h : Fin r → (FractionRing O)⟦X⟧) : Fin r → (FractionRing O)⟦X⟧ :=
  ((S.G i).map R.toL).mulVec (fun k => R.γL (h k))
def Horiz (i : ZMod n) (h : Fin r → (FractionRing O)⟦X⟧) : Prop := S.γF i h = h
def φ0 (i : ZMod n) : Matrix (Fin r) (Fin r) (FractionRing O) :=
  ((constantCoeff (R.toL R.E)) ^ S.M)⁻¹ • (S.Φ i).map (fun a => constantCoeff (R.toL a))
def φ0it (c : ZMod n) (j : ℕ) : Matrix (Fin r) (Fin r) (FractionRing O) :=
  Nat.rec 1 (fun j f => S.φ0 (c + (j : ZMod n) + 1) * f) j
def Fil (i : ZMod n) (τ : Fin R.e) (a : ℤ) : Submodule (FractionRing O) (Fin r → FractionRing O) :=
  Submodule.span _ {δ | ∃ h, S.Horiz (i - 1) h ∧ δ = (S.φ0 i).mulVec (fun k => constantCoeff (h k)) ∧
    ∀ k, X ^ ((S.M : ℤ) + a).toNat ∣ ((S.Φ i).map (R.levL τ)).mulVec (fun k' => R.φτ τ (h k')) k}
def IsJump (i : ZMod n) (τ : Fin R.e) (a : ℤ) : Prop := S.Fil i τ (a + 1) ≠ S.Fil i τ a
def JumpsIn (i : ZMod n) (τ : Fin R.e) (J : Set ℤ) : Prop := ∀ a, S.IsJump i τ a → a ∈ J
def count (i : ZMod n) (τ : Fin R.e) (a b : ℤ) : ℕ :=
  Module.finrank (FractionRing O) (S.Fil i τ a) - Module.finrank (FractionRing O) (S.Fil i τ (b + 1))
end Sys
def D0 (O : Type) [CommRing O] [IsDomain O] (r : ℕ) : Submodule O (Fin r → FractionRing O) :=
  Submodule.pi Set.univ fun _ => LinearMap.range (Algebra.linearMap O (FractionRing O))
structure Hom {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r r' : ℕ} (S : Sys R n r)
    (S' : Sys R n r') where
  F : ZMod n → Matrix (Fin r') (Fin r) O⟦X⟧
  φ_comm : ∀ i x, ((F i).map R.ι).mulVec (S.φl i x) = S'.φl i (((F (i - 1)).map R.ι).mulVec x)
  γ_comm : ∀ i x, ((F i).map R.ι).mulVec (S.γl i x) = S'.γl i (((F i).map R.ι).mulVec x)
namespace Hom
variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r r' r'' : ℕ} {S : Sys R n r} {S' : Sys R n r'}
  {S'' : Sys R n r''} (F : Hom S S')
def id (S : Sys R n r) : Hom S S where
  F := fun _ => 1
  φ_comm := fun i x => by simp [Matrix.map_one R.ι (map_zero _) (map_one _)]
  γ_comm := fun i x => by simp [Matrix.map_one R.ι (map_zero _) (map_one _)]
def comp (F' : Hom S' S'') (F : Hom S S') : Hom S S'' where
  F := fun i => F'.F i * F.F i
  φ_comm := fun i x => by
    rw [Matrix.map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F.φ_comm,
      F'.φ_comm]
  γ_comm := fun i x => by
    rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F.γ_comm, F'.γ_comm]
theorem map_C_smul_mulVec (c : O) (B : Matrix (Fin r') (Fin r) O⟦X⟧) (x : Fin r → R.EE) :
    (((C c : O⟦X⟧) • B).map R.ι).mulVec x = c • (B.map R.ι).mulVec x := by
  have hc : R.ι (C c) = algebraMap O R.EE c := (IsScalarTower.algebraMap_apply O O⟦X⟧ R.EE c).symm
  funext k
  simp [Matrix.mulVec, dotProduct, hc, Algebra.smul_def, Finset.mul_sum, mul_assoc]
def smul (c : O) (F : Hom S S') : Hom S S' where
  F := fun i => (C c : O⟦X⟧) • F.F i
  φ_comm := fun i x => by rw [map_C_smul_mulVec, map_C_smul_mulVec, map_smul, F.φ_comm]
  γ_comm := fun i x => by rw [map_C_smul_mulVec, map_C_smul_mulVec, map_smul, F.γ_comm]
def fl (i : ZMod n) : (Fin r → R.EE) →ₗ[R.EE] (Fin r' → R.EE) := ((F.F i).map R.ι).mulVecLin
def fD : DD R n r →ₗ[O] DD R n r' :=
  LinearMap.pi fun i => ((F.fl i).restrictScalars O).comp (LinearMap.proj i)
def Onto : Prop := ∀ i, Function.Surjective (F.fl i)
def ImF : Submodule O (DD R n r' × DD R n r') := S.Zf.map (F.fD.prodMap F.fD) ⊔ S'.B1
def Lifts (c : O) : Prop := ∀ pr ∈ S'.Zf, c • pr ∈ F.ImF
def LiftF (e : ℕ) : Prop := F.Lifts ((l : O) ^ e)
def ColLe (b : ℝ) : Prop := LenLe l O (↥S'.Zf ⧸ F.ImF.comap S'.Zf.subtype) b
def Kills (i : ZMod n) (f : O⟦X⟧) : Prop :=
  ∀ y ∈ R.N0 r', ∃ x ∈ R.N0 r, F.fl i x = f • y
def IsSES (F : Hom S S') (F' : Hom S' S'') : Prop :=
  F'.Onto ∧ ∀ i, Function.Injective (F.fl i) ∧ (∀ x, F'.fl i x = 0 ↔ ∃ y, F.fl i y = x) ∧
    ∀ y, F.fl i y ∈ R.N0 r' → y ∈ R.N0 r
def IsClassOf {g : ℕ} (F : Hom S S') (F' : Hom S' (Sys.one R n g)) (a : Fin g → O)
    (pr : DD R n r × DD R n r) : Prop :=
  ∃ x : DD R n r', (∀ i k, F'.fD x i k = algebraMap O R.EE (a k)) ∧
    F.fD pr.1 = S'.φD x - x ∧ F.fD pr.2 = S'.γD x - x
end Hom
def ExtProp {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r : ℕ} (S : Sys R n r) : Prop :=
  ∀ (g : ℕ) (pr : Fin g → DD R n r × DD R n r), (∀ k, pr k ∈ S.Zf) →
    ∃ (Y : Sys R n (r + g)) (F : Hom S Y) (F' : Hom Y (Sys.one R n g)), F.IsSES F' ∧
      ∀ k, F.IsClassOf F' (Pi.single k 1) (pr k)
end GlobalTheory.NB


