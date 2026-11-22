-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs
-- name    : Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:09:27.306553+00:00
-- url     : https://prove2.me/theorems/cd394f97-3f51-4625-a025-a5984feed9f1
-- title:
--   Exp Defs
-- statement:
--   Definitions and structural lemmas for Exp Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/ExpDefs.lean

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace Formalism.L2.NX
section Unip
variable {ι : Type} [Fintype ι] (p : ι → ℕ) (r : ℕ)
abbrev GProd : Type := ∀ x : ι, GL (Fin r) (ZMod (p x))
def IsUniTri {R : Type} [CommRing R] (M : Matrix (Fin r) (Fin r) R) : Prop :=
  M.BlockTriangular id ∧ ∀ a, M a a = 1
variable {r}
theorem mul_diag_of_tri {R : Type} [CommRing R] {M N : Matrix (Fin r) (Fin r) R} (hM : M.BlockTriangular id)
    (hN : N.BlockTriangular id) (a : Fin r) : (M * N) a a = M a a * N a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hM h, zero_mul]
    · rw [hN h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h
theorem IsUniTri.mul {R : Type} [CommRing R] {M N : Matrix (Fin r) (Fin r) R} (hM : IsUniTri r M)
    (hN : IsUniTri r N) : IsUniTri r (M * N) :=
  ⟨hM.1.mul hN.1, fun a => by rw [mul_diag_of_tri hM.1 hN.1, hM.2, hN.2, one_mul]⟩
theorem IsUniTri.inv {R : Type} [CommRing R] {M : Matrix (Fin r) (Fin r) R} [Invertible M] (hM : IsUniTri r M) :
    IsUniTri r M⁻¹ := by
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hM.1
  refine ⟨hi, fun a => ?_⟩
  have h := mul_diag_of_tri hM.1 hi a
  rw [Matrix.mul_inv_of_invertible, hM.2, one_mul, Matrix.one_apply_eq] at h
  exact h.symm
variable (r)
def Uup : Subgroup (GProd p r) where
  carrier := {g | ∀ x, IsUniTri r ((g x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x)))}
  one_mem' := fun x => ⟨Matrix.blockTriangular_one, fun a => by simp⟩
  mul_mem' := by
    intro g h hg hh x
    simpa using (hg x).mul (hh x)
  inv_mem' := by
    intro g hg x
    have e : (((g⁻¹ : GProd p r) x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))) =
        ((g x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x)))⁻¹ := by
      simp [Matrix.coe_units_inv]
    rw [e]
    exact (hg x).inv
variable {p r}
variable (r)
def supSum {R : Type} [CommRing R] (M : Matrix (Fin r) (Fin r) R) : R :=
  ∑ a : Fin r, ∑ b : Fin r, if (b : ℕ) = a + 1 then M a b else 0
variable {r}
theorem mul_sup {R : Type} [CommRing R] {M N : Matrix (Fin r) (Fin r) R} (hM : IsUniTri r M) (hN : IsUniTri r N)
    {a b : Fin r} (h : (b : ℕ) = a + 1) : (M * N) a b = M a b + N a b := by
  have hab : a ≠ b := by
    intro e
    rw [e] at h
    omega
  rw [Matrix.mul_apply, Finset.sum_eq_add a b hab]
  · rw [hM.2, hN.2, one_mul, mul_one, add_comm]
  · intro c _ hc
    rcases lt_or_gt_of_ne hc.1 with h1 | h1
    · rw [hM.1 h1, zero_mul]
    · have h2 : b < c := by
        have := hc.2
        rw [Fin.lt_def] at h1 ⊢
        rw [Ne, Fin.ext_iff] at this
        omega
      rw [hN.1 h2, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h
  · intro h
    exact absurd (Finset.mem_univ b) h
theorem supSum_mul {R : Type} [CommRing R] {M N : Matrix (Fin r) (Fin r) R} (hM : IsUniTri r M) (hN : IsUniTri r N) :
    supSum r (M * N) = supSum r M + supSum r N := by
  simp only [supSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · exact mul_sup hM hN h
  · simp
theorem supSum_one {R : Type} [CommRing R] : supSum r (1 : Matrix (Fin r) (Fin r) R) = 0 := by
  simp only [supSum]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    intro e
    rw [e] at h
    omega
  · rfl
variable (p r)
def stdVal {K : Type} [Field K] (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) (g : GProd p r) : Kˣ :=
  ∏ x, θ x (Multiplicative.ofAdd (supSum r ((g x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x)))))
def psiStd {K : Type} [Field K] (θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ) : Uup p r →* Kˣ where
  toFun u := stdVal p r θ u
  map_one' := by simp [stdVal, supSum_one]
  map_mul' u v := by
    simp only [stdVal]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [← map_mul, ← ofAdd_add]
    congr 2
    simpa using supSum_mul (u.2 x) (v.2 x)
def IsStdGeneric {K : Type} [Field K] {S : Subgroup (GProd p r)} (ψ : S →* Kˣ) : Prop :=
  ∃ θ : ∀ x, Multiplicative (ZMod (p x)) →* Kˣ, (2 ≤ r → ∀ x, θ x ≠ 1) ∧ ∀ u : S, ψ u = stdVal p r θ u
end Unip
section Test
variable {ι : Type} [Fintype ι] {p : ι → ℕ} {r : ℕ}
def tv {R : Type} [CommRing R] (hr : 2 ≤ r) (c : R) : Matrix (Fin r) (Fin r) R :=
  Matrix.transvection (⟨0, by omega⟩ : Fin r) ⟨1, by omega⟩ c
def tvAt [DecidableEq ι] (hr : 2 ≤ r) (x : ι) : GProd p r :=
  Pi.mulSingle x (Matrix.SpecialLinearGroup.toGL
    ⟨tv hr (1 : ZMod (p x)), Matrix.det_transvection_of_ne _ _ (by simp [Fin.ext_iff]) 1⟩)
def charOf {K : Type} [Field K] {q : ℕ} (ζ : Kˣ) (hζ : ζ ^ q = 1) : Multiplicative (ZMod q) →* Kˣ :=
  AddMonoidHom.toMultiplicativeLeft (ZMod.lift q ⟨MonoidHom.toAdditiveRight (zpowersHom Kˣ ζ), by
    change Additive.ofMul (ζ ^ ((q : ℕ) : ℤ)) = 0
    rw [zpow_natCast, hζ]; rfl⟩)
end Test
section Forms
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
local notation3 "L⁺" => NumberField.maximalRealSubfield L
def TypeSpF (K : Type) [Field K] {W : Type} [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W)
    (J : Subgroup (GAf L n)) (χ : J →* Kˣ) : Submodule K (GAf L n → W) where
  carrier := {f | (∀ (γ : GQ L n) (g : GAf L n), f ((γ : GAf L n) * g) = ρ γ (f g)) ∧
    ∀ (κ : J) (g : GAf L n), f (g * (κ : GAf L n)) = ((χ κ : Kˣ) : K) • f g}
  zero_mem' := ⟨fun γ g => by simp, fun κ g => by simp⟩
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h1', h2'⟩
    exact ⟨fun γ g => by simp [h1 γ g, h1' γ g], fun κ g => by simp [h2 κ g, h2' κ g, smul_add]⟩
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    exact ⟨fun γ g => by simp [h1 γ g], fun κ g => by simp [h2 κ g, smul_comm c]⟩
variable {L n}
def HypOutsideF {K : Type} [Field K] (J : Subgroup (GAf L n)) (χ : J →* Kˣ) (B : Set (HeightOneSpectrum (𝓞 L⁺))) :
    Prop :=
  ∀ κ : GAf L n, TrivOutside Bᶜ κ → (κ ∈ J ↔ κ ∈ Umax L n) ∧ ∀ h : κ ∈ J, χ ⟨κ, h⟩ = 1
end Forms
section Local
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
local notation3 "L⁺" => NumberField.maximalRealSubfield L
def InParah (v : HeightOneSpectrum (𝓞 L⁺)) (r : ℕ) (x : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) : Prop :=
  (∀ a b, x a b ∈ v.adicCompletionIntegers L⁺) ∧ ∀ a b : Fin n, r ≤ (a : ℕ) → (b : ℕ) < r → Valued.v (x a b) < 1
def InLevG (v : HeightOneSpectrum (𝓞 L⁺)) (r : ℕ) (x : Matrix (Fin n) (Fin n) (v.adicCompletion L⁺)) : Prop :=
  InParah v r x ∧ ∀ a b : Fin n, (a : ℕ) < r → (b : ℕ) < r →
    (b < a → Valued.v (x a b) < 1) ∧ (a = b → Valued.v (x a b - 1) < 1)
def detT (r : ℕ) {R : Type} [CommRing R] (x : Matrix (Fin n) (Fin n) R) : R :=
  (x.submatrix (fun a : {i : Fin n // r ≤ (i : ℕ)} => a.1) (fun a => a.1)).det
def topR {r : ℕ} (h : r ≤ n) {R : Type} (x : Matrix (Fin n) (Fin n) R) : Matrix (Fin r) (Fin r) R :=
  x.submatrix (Fin.castLE h) (Fin.castLE h)
open Classical in

def intLift (v : HeightOneSpectrum (𝓞 L⁺)) (y : v.adicCompletion L⁺) : v.adicCompletionIntegers L⁺ :=
  if h : y ∈ v.adicCompletionIntegers L⁺ then ⟨y, h⟩ else 0
def redMat (v : HeightOneSpectrum (𝓞 L⁺)) {ι R : Type} [CommRing R] (red : v.adicCompletionIntegers L⁺ →+* R)
    (x : Matrix ι ι (v.adicCompletion L⁺)) : Matrix ι ι R :=
  fun a b => red (intLift v (x a b))
open Classical in

def glOf {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (M : Matrix ι ι R) : GL ι R :=
  if h : IsUnit M.det then M.nonsingInvUnit h else 1
variable (L n) in

def IsAlgWeightF (K : Type) [Field K] {W : Type} [AddCommGroup W] [Module K W] (ρ : Representation K (GQ L n) W) : Prop :=
  FiniteDimensional K W ∧
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b : Module.Basis ι K W) (κ : Type) (_ : Fintype κ)
    (e : Module.Basis κ ℚ L) (P : ι → ι → MvPolynomial (κ × Fin n × Fin n) K),
    ∀ (γ : GQ L n) (γ₀ : GL (Fin n) L),
      (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map (Algebra.TensorProduct.includeLeftRingHom) →
      LinearMap.toMatrix b b (ρ γ) = fun i j =>
        MvPolynomial.eval (fun p => ((e.repr ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2) p.1 : ℚ) : K)) (P i j)
end Local
end Formalism.L2.NX


