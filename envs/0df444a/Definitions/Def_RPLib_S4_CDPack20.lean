-- Prove2me | Definitions.Def_RPLib_S4_CDPack20
-- name    : RPLib_S4_CDPack20
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T06:16:19.250231+00:00
-- url     : https://prove2.me/theorems/c2a33ceb-5131-4f20-bb62-51b8a56370cf
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 20 of 71
-- statement:
--   Part 20 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_CupDuality_LamSep`: S4-CurveDuality O5d (1): `ℤ/N`-characters, parabolic homomorphisms and perfect matrix pairings
--   * `Def_RP_IsogDegA_Fib1`: S4-IsogDegA, file Fib1: generic fibre count, part 1 (finite dimensionality, fibres, upper bound)
--   * `Def_RP_IsogDegA_Fib2`: S4-IsogDegA, file Fib2: generic fibre count, part 2 (lower bound via going-up, exact count)
--   * `Def_RP_IsogDegA_Fib3`: S4-IsogDegA, file Fib3: generic fibre count, part 3 (choice of a generic primitive element)
--   * `Def_RP_IsogDegA_Fib4`: S4-IsogDegA, file Fib4: the generic fibre has `finSepDegree` points (O1 headline)
--   * `Def_RP_JacSymA_A`: S4-JacSymA, file A: the coordinate ring of `X^g`, the `S_g`-action and the chart `Sym^g`
--   * `Def_RP_JacSymA_B`: S4-JacSymA, file B: the `k`-points of the chart `Sym^g X` (lemma L8 of S4_COREB_ROUTE.md)
--   * `Def_RP_JacSymA_C`: S4-JacSymA, file C: points of the chart are effective divisors (L8, divisor form)
--   * `Def_RP_JacSymA_D`: S4-JacSymA, file D: `X^g` is integral
--   * `Def_RP_JacSymA_E`: S4-JacSymA, file E: the function field of `Sym^g X` (L9)
--   * `Def_RP_JacSymA`: S4-JacSymA: affine charts of `Sym^g` of a smooth curve (umbrella)
--   * `Def_RP_JacSymB_Poly`: S4-JacSymB, file A (L10): `Sym^g A^1 = A^g`
--   * `Def_RP_JacSymB_Map`: S4-JacSymB, file B: functoriality of `X^g` and `Sym^g`; surjections stay surjective on invariants
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_TameInertiaCoef

/-!
# Curve-duality library package, part 20 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_CupDuality_LamSep`: S4-CurveDuality O5d (1): `ℤ/N`-characters, parabolic homomorphisms and perfect matrix pairings
* `Def_RP_IsogDegA_Fib1`: S4-IsogDegA, file Fib1: generic fibre count, part 1 (finite dimensionality, fibres, upper bound)
* `Def_RP_IsogDegA_Fib2`: S4-IsogDegA, file Fib2: generic fibre count, part 2 (lower bound via going-up, exact count)
* `Def_RP_IsogDegA_Fib3`: S4-IsogDegA, file Fib3: generic fibre count, part 3 (choice of a generic primitive element)
* `Def_RP_IsogDegA_Fib4`: S4-IsogDegA, file Fib4: the generic fibre has `finSepDegree` points (O1 headline)
* `Def_RP_JacSymA_A`: S4-JacSymA, file A: the coordinate ring of `X^g`, the `S_g`-action and the chart `Sym^g`
* `Def_RP_JacSymA_B`: S4-JacSymA, file B: the `k`-points of the chart `Sym^g X` (lemma L8 of S4_COREB_ROUTE.md)
* `Def_RP_JacSymA_C`: S4-JacSymA, file C: points of the chart are effective divisors (L8, divisor form)
* `Def_RP_JacSymA_D`: S4-JacSymA, file D: `X^g` is integral
* `Def_RP_JacSymA_E`: S4-JacSymA, file E: the function field of `Sym^g X` (L9)
* `Def_RP_JacSymA`: S4-JacSymA: affine charts of `Sym^g` of a smooth curve (umbrella)
* `Def_RP_JacSymB_Poly`: S4-JacSymB, file A (L10): `Sym^g A^1 = A^g`
* `Def_RP_JacSymB_Map`: S4-JacSymB, file B: functoriality of `X^g` and `Sym^g`; surjections stay surjective on invariants
-/

set_option autoImplicit false

-- ===== S4.Def_RP_CupDuality_LamSep =====
section

/-!
# S4-CurveDuality O5d (1): `ℤ/N`-characters, parabolic homomorphisms and perfect matrix pairings

* `exists_zmod_hom_ne_zero`: an `N`-torsion abelian group is separated by homomorphisms to `ℤ/N`;
* `span_of_zmod`: if the `ℤ/N`-valued parabolic homomorphisms have a dual basis `χ_i`, `e_i`, then every
  `k`-valued one (`k` a `ℤ/N`-algebra) is `x g = Σ_i χ_i(g) x(e_i)`;
* `isPerfPair_toLinearMap₂'`: the pairing `(v, w) ↦ v ⬝ (A w)` on `R^n` is perfect for invertible `A`;
  `exists_inv_of_isPerfPair`: a perfect matrix pairing has an invertible matrix; `map_mul_eq_one`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open TameInertia

section Sep

variable {N : ℕ} [NeZero N] {A : Type*} [AddCommGroup A]

/-- `ℤ/N`-valued characters separate the points of an `N`-torsion group. -/
theorem exists_zmod_hom_ne_zero (hN : ∀ a : A, N • a = 0) {a : A} (ha : a ≠ 0) :
    ∃ ψ : A →+ ZMod N, ψ a ≠ 0 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  have hex : ∀ b : A, ∃ z : ZMod N, toQCircle N z = c b := fun b =>
    exists_toQCircle_eq N (by rw [← map_nsmul, hN b, map_zero])
  choose ψ hψ using hex
  have hadd : ∀ b b', ψ (b + b') = ψ b + ψ b' := fun b b' =>
    toQCircle_injective N (by rw [map_add, hψ, hψ, hψ, map_add])
  refine ⟨AddMonoidHom.mk' ψ hadd, fun h0 => hc ?_⟩
  have h1 : toQCircle N (ψ a) = c a := hψ a
  rw [← h1, show ψ a = 0 from h0, map_zero]

theorem eq_of_zmod_hom (hN : ∀ a : A, N • a = 0) {a b : A} (h : ∀ ψ : A →+ ZMod N, ψ a = ψ b) : a = b := by
  by_contra hab
  obtain ⟨ψ, hψ⟩ := exists_zmod_hom_ne_zero hN (sub_ne_zero.2 hab)
  exact hψ (by rw [map_sub, h ψ, sub_self])

end Sep

section Span

variable {N : ℕ} [NeZero N] {k : Type*} [CommRing k] (ι : ZMod N →+* k)

theorem nsmul_eq_zero_of_hom (ι : ZMod N →+* k) (a : k) : N • a = 0 := by
  rw [nsmul_eq_mul, ← map_natCast ι N, ZMod.natCast_self, map_zero, zero_mul]

theorem zmod_hom_map_mul (ψ : k →+ ZMod N) (c : ZMod N) (y : k) : ψ (ι c * y) = c * ψ y := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c, map_natCast, ← nsmul_eq_mul, map_nsmul]
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- Locally constant homomorphisms `Γ → A` vanishing on the elements satisfying `P` (parabolic homs). -/
def IsParHom {A : Type*} [AddCommGroup A] (P : Γ → Prop) (x : Γ → A) : Prop :=
  IsLocallyConstant x ∧ (∀ g h, x (g * h) = x g + x h) ∧ ∀ g, P g → x g = 0

theorem IsParHom.comp {A B : Type*} [AddCommGroup A] [AddCommGroup B] {P : Γ → Prop} {x : Γ → A}
    (hx : IsParHom P x) (ψ : A →+ B) : IsParHom P (fun g => ψ (x g)) :=
  ⟨hx.1.comp ψ, fun g h => by show ψ (x (g * h)) = ψ (x g) + ψ (x h); rw [hx.2.1, map_add],
    fun g hg => by show ψ (x g) = 0; rw [hx.2.2 g hg, map_zero]⟩

/-- **Coordinates of `k`-valued parabolic homomorphisms** from a `ℤ/N` dual basis. -/
theorem span_of_zmod {P : Γ → Prop} {r : ℕ} (χ : Fin r → Γ → ZMod N) (e : Fin r → Γ)
    (hspan : ∀ y : Γ → ZMod N, IsParHom P y → ∀ g, y g = ∑ i, y (e i) * χ i g)
    {x : Γ → k} (hx : IsParHom P x) (g : Γ) : x g = ∑ i, ι (χ i g) * x (e i) := by
  refine eq_of_zmod_hom (nsmul_eq_zero_of_hom ι) fun ψ => ?_
  rw [hspan _ (hx.comp ψ) g, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [zmod_hom_map_mul, mul_comm]

end Span

section Mat

open Matrix

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem toLinearMap₂'_eq_dot (A : Matrix n n R) (v w : n → R) :
    Matrix.toLinearMap₂' R A v w = (v ᵥ* A) ⬝ᵥ w := by
  rw [Matrix.toLinearMap₂'_apply', dotProduct_mulVec]

theorem toLinearMap₂'_single (A : Matrix n n R) (v : n → R) (j : n) :
    Matrix.toLinearMap₂' R A v (Pi.single j (1 : R)) = (v ᵥ* A) j := by
  rw [toLinearMap₂'_eq_dot, dotProduct_single, mul_one]

theorem bijective_toLinearMap₂' {A B : Matrix n n R} (hBA : B * A = 1) (hAB : A * B = 1) :
    Function.Bijective (Matrix.toLinearMap₂' R A : (n → R) →ₗ[R] (n → R) →ₗ[R] R) := by
  refine ⟨fun v v' h => ?_, fun φ => ?_⟩
  · have h2 : v ᵥ* A = v' ᵥ* A := funext fun j => by
      rw [← toLinearMap₂'_single, ← toLinearMap₂'_single, h]
    calc v = v ᵥ* A ᵥ* B := by rw [vecMul_vecMul, hAB, vecMul_one]
      _ = v' ᵥ* A ᵥ* B := by rw [h2]
      _ = v' := by rw [vecMul_vecMul, hAB, vecMul_one]
  · refine ⟨(fun j => φ (fun i => if j = i then 1 else 0)) ᵥ* B, LinearMap.ext fun w => ?_⟩
    rw [toLinearMap₂'_eq_dot, vecMul_vecMul, hBA, vecMul_one, LinearMap.pi_apply_eq_sum_univ φ w,
      dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_eq_mul, mul_comm]

/-- The matrix pairing of an invertible matrix is perfect. -/
theorem isPerfPair_toLinearMap₂' {A B : Matrix n n R} (hBA : B * A = 1) (hAB : A * B = 1) :
    (Matrix.toLinearMap₂' R A).IsPerfPair :=
  LinearMap.IsPerfPair.of_bijective _ (bijective_toLinearMap₂' hBA hAB)

/-- A perfect matrix pairing has an invertible matrix. -/
theorem exists_inv_of_isPerfPair {A : Matrix n n R} (h : (Matrix.toLinearMap₂' R A).IsPerfPair) :
    ∃ B : Matrix n n R, B * A = 1 ∧ A * B = 1 := by
  have hs := (LinearMap.IsPerfPair.bijective_left (Matrix.toLinearMap₂' R A)).2
  choose v hv using fun j : n => hs (LinearMap.proj j)
  have hBA : Matrix.of (fun j i => v j i) * A = 1 := by
    ext j l
    have h1 := LinearMap.congr_fun (hv j) (Pi.single l (1 : R))
    rw [toLinearMap₂'_single, LinearMap.proj_apply, Pi.single_apply] at h1
    rw [Matrix.mul_apply, Matrix.one_apply, ← h1]
    simp only [Matrix.of_apply, Matrix.vecMul, dotProduct]
  exact ⟨_, hBA, mul_eq_one_comm.1 hBA⟩

theorem map_mul_eq_one {S : Type*} [CommRing S] (ι : R →+* S) {A B : Matrix n n R} (h : B * A = 1) :
    B.map ι * A.map ι = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one ι (map_zero ι) (map_one ι)]

/-- Perfectness of a matrix pairing is preserved by a ring homomorphism. -/
theorem isPerfPair_map {S : Type*} [CommRing S] (ι : R →+* S) {A : Matrix n n R}
    (h : (Matrix.toLinearMap₂' R A).IsPerfPair) : (Matrix.toLinearMap₂' S (A.map ι)).IsPerfPair := by
  obtain ⟨B, hBA, hAB⟩ := exists_inv_of_isPerfPair h
  exact isPerfPair_toLinearMap₂' (map_mul_eq_one ι hBA) (map_mul_eq_one ι hAB)

end Mat

end CupDuality
end RamanujanPetersson

end

-- ===== S4.Def_RP_IsogDegA_Fib1 =====
section

/-!
# S4-IsogDegA, file Fib1: generic fibre count, part 1 (finite dimensionality, fibres, upper bound)
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.IsogDegA

section FinDim

variable {R B K L : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
  [Algebra R B] [Module.Finite R B]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]

omit [IsDomain R] [IsDomain B] [IsFractionRing R K] in
include R B in
/-- If `B` is a finite `R`-algebra (domains), then `Frac B` is finite dimensional over `Frac R`. -/
theorem finiteDimensional_of_finite : FiniteDimensional K L := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := B)
  set S : Set L := (algebraMap B L) '' (s : Set B) with hSdef
  have hint : ∀ x ∈ S, IsIntegral K x := by
    rintro _ ⟨b, -, rfl⟩
    have hb : IsIntegral R b := Algebra.IsIntegral.isIntegral b
    exact (hb.map (IsScalarTower.toAlgHom R B L)).tower_top
  have hfin : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin hint
  have hB : ∀ c : B, algebraMap B L c ∈ IntermediateField.adjoin K S := by
    intro c
    have hc : c ∈ Submodule.span R (s : Set B) := hs ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin K S ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply R K L]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) hy
  have htop : IntermediateField.adjoin K S = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    exact div_mem (hB a) (hB b)
  rw [htop] at hfin
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end FinDim

section Fibre

variable (k : Type*) [Field k]
variable {R : Type*} (B : Type*) [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]

/-- The `k`-points of `Spec B` lying over the `k`-point `χ` of `Spec R`. -/
abbrev fiber (χ : R →ₐ[k] k) : Type _ :=
  {ψ : B →ₐ[k] k // ψ.comp (IsScalarTower.toAlgHom k R B) = χ}

variable {k B}

theorem fiber_apply_algebraMap {χ : R →ₐ[k] k} (ψ : fiber k B χ) (r : R) :
    ψ.1 (algebraMap R B r) = χ r := by
  have h := congrArg (fun φ : R →ₐ[k] k => φ r) ψ.2
  simpa using h

theorem fiber_aeval {χ : R →ₐ[k] k} (ψ : fiber k B χ) (β : B) (g : R[X]) :
    ψ.1 (aeval β g) = eval₂ (χ : R →+* k) (ψ.1 β) g := by
  rw [aeval_def]
  refine (Polynomial.hom_eval₂ g (algebraMap R B) (ψ.1 : B →+* k) β).trans ?_
  congr 1
  ext r
  exact fiber_apply_algebraMap ψ r

/-- Two points of the fibre agreeing at `β` agree, provided every generator of `B` over `R` has a
`q`-power that is (up to a unit at `χ`) a polynomial in `β`. -/
theorem fiber_ext {χ : R →ₐ[k] k} (s : Set B) (hs : Submodule.span R s = ⊤) (β : B)
    (q : ℕ) [ExpChar k q]
    (hgen : ∀ b ∈ s, ∃ n : ℕ, ∃ c : R, ∃ h : R[X],
      χ c ≠ 0 ∧ algebraMap R B c * b ^ q ^ n = aeval β h)
    (ψ₁ ψ₂ : fiber k B χ) (hβ : ψ₁.1 β = ψ₂.1 β) : ψ₁ = ψ₂ := by
  have hgen' : ∀ b ∈ s, ψ₁.1 b = ψ₂.1 b := by
    intro b hb
    obtain ⟨n, c, h, hc, hbh⟩ := hgen b hb
    have e1 := congrArg ψ₁.1 hbh
    have e2 := congrArg ψ₂.1 hbh
    rw [map_mul, map_pow, fiber_apply_algebraMap, fiber_aeval] at e1 e2
    rw [hβ] at e1
    have h3 : ψ₁.1 b ^ q ^ n = ψ₂.1 b ^ q ^ n := mul_left_cancel₀ hc (e1.trans e2.symm)
    apply iterateFrobenius_inj k q n
    simpa [iterateFrobenius_def] using h3
  apply Subtype.ext
  apply AlgHom.ext
  intro x
  have hx : x ∈ Submodule.span R s := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen' y hy
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul r y _ hy =>
    rw [Algebra.smul_def, map_mul, map_mul, fiber_apply_algebraMap, fiber_apply_algebraMap, hy]

/-- Upper bound: the fibre injects into the roots of `f0` mod `χ`. -/
theorem card_fiber_le {χ : R →ₐ[k] k} (s : Set B) (hs : Submodule.span R s = ⊤) (β : B)
    (q : ℕ) [ExpChar k q]
    (hgen : ∀ b ∈ s, ∃ n : ℕ, ∃ c : R, ∃ h : R[X],
      χ c ≠ 0 ∧ algebraMap R B c * b ^ q ^ n = aeval β h)
    (f0 : R[X]) (hf0 : f0.Monic) (hβ0 : aeval β f0 = 0) :
    Finite (fiber k B χ) ∧ Nat.card (fiber k B χ) ≤ f0.natDegree := by
  classical
  set p : k[X] := f0.map (χ : R →+* k) with hpdef
  have hp : p ≠ 0 := (hf0.map _).ne_zero
  let F : fiber k B χ → p.roots.toFinset := fun ψ => ⟨ψ.1 β, by
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot, hpdef, eval_map, ← fiber_aeval, hβ0,
      map_zero]⟩
  have hF : Function.Injective F := fun ψ₁ ψ₂ h =>
    fiber_ext s hs β q hgen ψ₁ ψ₂ (congrArg Subtype.val h)
  refine ⟨Finite.of_injective F hF, ?_⟩
  calc Nat.card (fiber k B χ) ≤ Nat.card p.roots.toFinset := Nat.card_le_card_of_injective F hF
    _ = p.roots.toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p
    _ = f0.natDegree := hf0.natDegree_map _

end Fibre

end RamanujanPetersson.IsogDegA

end

-- ===== S4.Def_RP_IsogDegA_Fib2 =====
section

/-!
# S4-IsogDegA, file Fib2: generic fibre count, part 2 (lower bound via going-up, exact count)
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.IsogDegA

section Lower

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {R B : Type*} [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B] [Algebra.IsIntegral R B]

/-- Lower bound, pointwise: every root `α` of `f0 mod χ` is the value at `β` of a point of the
fibre over `χ`, provided `f0` divides every polynomial relation of `β`. -/
theorem exists_fiber_of_root (χ : R →ₐ[k] k) (β : B) (f0 : R[X])
    (hdvd : ∀ g : R[X], aeval β g = 0 → f0 ∣ g) (α : k)
    (hα : eval₂ (χ : R →+* k) α f0 = 0) : ∃ ψ : fiber k B χ, ψ.1 β = α := by
  classical
  set ev : R[X] →+* k := eval₂RingHom (χ : R →+* k) α with hev
  have hevC : ∀ c : k, ev (C (algebraMap k R c)) = c := fun c => by
    simp [hev]
  have hsurj : Function.Surjective ev := fun c => ⟨_, hevC c⟩
  have hPmax : (RingHom.ker ev).IsMaximal := RingHom.ker_isMaximal_of_surjective ev hsurj
  let _ : Algebra R[X] B := (aeval β).toRingHom.toAlgebra
  have halg : ∀ g : R[X], algebraMap R[X] B g = aeval β g := fun _ => rfl
  have hcomp : (algebraMap R[X] B).comp (C : R →+* R[X]) = algebraMap R B := by
    ext r; simp [halg]
  have hint : Algebra.IsIntegral R[X] B := by
    refine ⟨fun x => ?_⟩
    have h0 : ((algebraMap R[X] B).comp (C : R →+* R[X])).IsIntegral := by
      rw [hcomp]; exact fun y => Algebra.IsIntegral.isIntegral (R := R) y
    exact RingHom.IsIntegral.tower_top (f := (C : R →+* R[X])) (g := algebraMap R[X] B) h0 x
  have hker : RingHom.ker (algebraMap R[X] B) ≤ RingHom.ker ev := by
    intro g hg
    rw [RingHom.mem_ker, halg] at hg
    obtain ⟨h, rfl⟩ := hdvd g hg
    rw [RingHom.mem_ker, map_mul]
    simp [hev, hα]
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (RingHom.ker ev) hker
  -- key: modulo `Q`, `aeval β g` is the constant `ev g`
  have hkey : ∀ g : R[X], Ideal.Quotient.mk Q (aeval β g) =
      algebraMap k (B ⧸ Q) (ev g) := by
    intro g
    have hmem : g - C (algebraMap k R (ev g)) ∈ RingHom.ker ev := by
      rw [RingHom.mem_ker, map_sub, hevC, sub_self]
    rw [← hQ, Ideal.mem_comap, halg, map_sub] at hmem
    rw [Ideal.Quotient.eq.mpr hmem, aeval_C, ← IsScalarTower.algebraMap_apply]
    rfl
  have hR : ∀ r : R, Ideal.Quotient.mk Q (algebraMap R B r) = algebraMap k (B ⧸ Q) (χ r) := by
    intro r
    have := hkey (C r)
    rwa [aeval_C, show ev (C r) = χ r by simp [hev]] at this
  -- `B ⧸ Q` is integral, hence equal to `k`
  have hintk : Algebra.IsIntegral k (B ⧸ Q) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := R) b
    refine ⟨p.map (χ : R →+* k), hpm.map _, ?_⟩
    rw [eval₂_map]
    have hc : (algebraMap k (B ⧸ Q)).comp (χ : R →+* k) =
        (Ideal.Quotient.mk Q).comp (algebraMap R B) := by
      ext r; exact (hR r).symm
    rw [hc, ← hom_eval₂, hp, map_zero]
  have hbij : Function.Bijective (algebraMap k (B ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : k ≃ₐ[k] B ⧸ Q := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ Q)) hbij
  let ψ : B →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k Q)
  have hψ : ∀ b : B, e (ψ b) = Ideal.Quotient.mk Q b := fun b => by
    simp [ψ]
  have hψg : ∀ g : R[X], ψ (aeval β g) = ev g := by
    intro g
    apply e.injective
    rw [hψ, hkey]
    rfl
  refine ⟨⟨ψ, ?_⟩, ?_⟩
  · ext r
    simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    have := hψg (C r)
    rwa [aeval_C, show ev (C r) = χ r by simp [hev]] at this
  · have := hψg X
    rwa [aeval_X, show ev X = α by simp [hev]] at this

/-- Exact count: if moreover `f0 mod χ` is separable, the fibre has exactly `deg f0` points. -/
theorem card_fiber_eq (χ : R →ₐ[k] k) (s : Set B) (hs : Submodule.span R s = ⊤) (β : B)
    (q : ℕ) [ExpChar k q]
    (hgen : ∀ b ∈ s, ∃ n : ℕ, ∃ c : R, ∃ h : R[X],
      χ c ≠ 0 ∧ algebraMap R B c * b ^ q ^ n = aeval β h)
    (f0 : R[X]) (hf0 : f0.Monic) (hβ0 : aeval β f0 = 0)
    (hdvd : ∀ g : R[X], aeval β g = 0 → f0 ∣ g) (hsep : (f0.map (χ : R →+* k)).Separable) :
    Finite (fiber k B χ) ∧ Nat.card (fiber k B χ) = f0.natDegree := by
  classical
  obtain ⟨hfin, hle⟩ := card_fiber_le s hs β q hgen f0 hf0 hβ0
  refine ⟨hfin, le_antisymm hle ?_⟩
  set p : k[X] := f0.map (χ : R →+* k) with hpdef
  have hp : p ≠ 0 := (hf0.map _).ne_zero
  have hroot : ∀ α ∈ p.roots.toFinset, ∃ ψ : fiber k B χ, ψ.1 β = α := by
    intro α hα
    rw [Multiset.mem_toFinset, mem_roots hp, IsRoot, hpdef, eval_map] at hα
    exact exists_fiber_of_root χ β f0 hdvd α hα
  choose G hG using hroot
  let G' : p.roots.toFinset → fiber k B χ := fun α => G α.1 α.2
  have hG' : Function.Injective G' := by
    intro a b hab
    apply Subtype.ext
    rw [← hG a.1 a.2, ← hG b.1 b.2]
    exact congrArg (fun ψ : fiber k B χ => ψ.1 β) hab
  calc f0.natDegree = p.natDegree := (hf0.natDegree_map _).symm
    _ = Multiset.card p.roots := IsAlgClosed.card_roots_eq_natDegree.symm
    _ = p.roots.toFinset.card := (Multiset.toFinset_card_of_nodup (nodup_roots hsep)).symm
    _ = Nat.card p.roots.toFinset := (Nat.card_eq_finsetCard _).symm
    _ ≤ Nat.card (fiber k B χ) := Nat.card_le_card_of_injective G' hG'

end Lower

end RamanujanPetersson.IsogDegA

end

-- ===== S4.Def_RP_IsogDegA_Fib3 =====
section

/-!
# S4-IsogDegA, file Fib3: generic fibre count, part 3 (choice of a generic primitive element)
-/

set_option autoImplicit false

open Polynomial IntermediateField

namespace RamanujanPetersson.IsogDegA

section Adjoin

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem adjoin_simple_mul_eq {e : K} (he : e ≠ 0) (θ : L) :
    K⟮algebraMap K L e * θ⟯ = K⟮θ⟯ := by
  apply le_antisymm
  · rw [adjoin_simple_le_iff]
    exact mul_mem (IntermediateField.algebraMap_mem _ e) (mem_adjoin_simple_self K θ)
  · rw [adjoin_simple_le_iff]
    have h : algebraMap K L e⁻¹ * (algebraMap K L e * θ) ∈ K⟮algebraMap K L e * θ⟯ :=
      mul_mem (IntermediateField.algebraMap_mem _ _) (mem_adjoin_simple_self K _)
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ he, map_one, one_mul] at h

theorem minpoly_mul_eq {e : K} (he : e ≠ 0) {θ : L} (hθ : IsIntegral K θ) :
    minpoly K (algebraMap K L e * θ) = (minpoly K θ).scaleRoots e := by
  have hθ' : IsIntegral K (algebraMap K L e * θ) := isIntegral_algebraMap.mul hθ
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hθ')
    ((monic_scaleRoots_iff e).2 (minpoly.monic hθ)) ?_ ?_).symm
  · exact minpoly.dvd K _ (scaleRoots_aeval_eq_zero (minpoly.aeval K θ))
  · refine le_of_eq ?_
    rw [natDegree_scaleRoots, ← adjoin.finrank hθ, ← adjoin.finrank hθ', adjoin_simple_mul_eq he]

theorem exists_adjoin_eq_separableClosure [FiniteDimensional K L] :
    ∃ θ : L, K⟮θ⟯ = separableClosure K L := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element K (separableClosure K L)
  exact ⟨α.1, by rw [← lift_adjoin_simple, hα, lift_top]⟩

end Adjoin

section Lift

variable {R K L : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]

theorem exists_monic_lift_minpoly {θ : L} (hθ : IsIntegral K θ) :
    ∃ d : R, d ≠ 0 ∧ ∃ f0 : R[X], f0.Monic ∧
      f0.map (algebraMap R K) = minpoly K (algebraMap R L d * θ) := by
  classical
  have hp : (minpoly K θ).Monic := minpoly.monic hθ
  obtain ⟨f0, hf1, -, hf2⟩ := lifts_and_natDegree_eq_and_monic
    (IsLocalization.scaleRoots_commonDenom_mem_lifts (nonZeroDivisors R) (minpoly K θ)
      (by rw [hp.leadingCoeff]; exact one_mem _)) ((monic_scaleRoots_iff _).2 hp)
  set D := IsLocalization.commonDenom (nonZeroDivisors R) (minpoly K θ).support (minpoly K θ).coeff
  have hD : algebraMap R K D ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors D.2
  refine ⟨D, nonZeroDivisors.ne_zero D.2, f0, hf2, ?_⟩
  rw [hf1, IsScalarTower.algebraMap_apply R K L, minpoly_mul_eq hD hθ]

omit [IsDomain R] in
/-- A monic lift of a minimal polynomial divides every polynomial relation. -/
theorem dvd_of_aeval_eq_zero {B : Type*} [CommRing B] [Algebra R B] [Algebra B L]
    [IsScalarTower R B L] (β : B) (f0 : R[X]) (hf0 : f0.Monic)
    (hmap : f0.map (algebraMap R K) = minpoly K (algebraMap B L β)) (g : R[X])
    (hg : aeval β g = 0) : f0 ∣ g := by
  have h1 : minpoly K (algebraMap B L β) ∣ g.map (algebraMap R K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, aeval_algebraMap_apply, hg, map_zero]
  have h2 : (g %ₘ f0).map (algebraMap R K) = 0 := by
    rw [map_modByMonic _ hf0, (modByMonic_eq_zero_iff_dvd (hf0.map _)).2 (hmap ▸ h1)]
  have h3 : g %ₘ f0 = 0 :=
    map_injective _ (IsFractionRing.injective R K) (by rw [h2, Polynomial.map_zero])
  exact (modByMonic_eq_zero_iff_dvd hf0).1 h3

/-- Separability of `f0` over `Frac R` spreads out: it holds modulo every `χ` with `χ a ≠ 0`. -/
theorem exists_sep_witness (k : Type*) [Field k] (f0 : R[X])
    (hsep : (f0.map (algebraMap R K)).Separable) :
    ∃ a : R, a ≠ 0 ∧ ∀ χ : R →+* k, χ a ≠ 0 → (f0.map χ).Separable := by
  classical
  obtain ⟨u, v, huv⟩ := hsep
  obtain ⟨bu, hbu, hu⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) u
  obtain ⟨bv, hbv, hv⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) v
  set U := IsLocalization.integerNormalization (nonZeroDivisors R) u
  set V := IsLocalization.integerNormalization (nonZeroDivisors R) v
  have hu' : U.map (algebraMap R K) = C (algebraMap R K bu) * u := by
    rw [hu, ← smul_eq_C_mul, algebraMap_smul]
  have hv' : V.map (algebraMap R K) = C (algebraMap R K bv) * v := by
    rw [hv, ← smul_eq_C_mul, algebraMap_smul]
  have key : (C (bu * bv) : R[X]) = C bv * U * f0 + C bu * V * derivative f0 := by
    apply map_injective (algebraMap R K) (IsFractionRing.injective R K)
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hu', hv',
      ← derivative_map, map_mul]
    linear_combination (-(C (algebraMap R K bu) * C (algebraMap R K bv))) * huv
  refine ⟨bu * bv, mul_ne_zero (nonZeroDivisors.ne_zero hbu) (nonZeroDivisors.ne_zero hbv), ?_⟩
  intro χ hχ
  have hk := congrArg (Polynomial.map χ) key
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at hk
  have hinv : C (χ (bu * bv))⁻¹ * C (χ (bu * bv)) = 1 := by
    rw [← C_mul, inv_mul_cancel₀ hχ, C_1]
  rw [Separable, derivative_map]
  refine ⟨C (χ (bu * bv))⁻¹ * (C (χ bv) * U.map χ), C (χ (bu * bv))⁻¹ * (C (χ bu) * V.map χ), ?_⟩
  linear_combination (-C (χ (bu * bv))⁻¹) * hk + hinv

end Lift

section Generic

variable {R B K L : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
  [Algebra R B] [Module.Finite R B]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]

variable (R B K L) in
/-- A generic element: `β ∈ B` generating the separable closure, with a monic lift over `R` of its
minimal polynomial. -/
theorem exists_generic_element :
    ∃ β : B, ∃ f0 : R[X], f0.Monic ∧ f0.map (algebraMap R K) = minpoly K (algebraMap B L β) ∧
      K⟮algebraMap B L β⟯ = separableClosure K L := by
  have : FiniteDimensional K L := finiteDimensional_of_finite (R := R) (B := B)
  obtain ⟨θ0, hθ0⟩ := exists_adjoin_eq_separableClosure (K := K) (L := L)
  obtain ⟨b, c, hc, hbc⟩ := IsFractionRing.div_surjective (A := B) θ0
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hne := Ideal.comap_ne_bot_of_integral_mem hc0 (Ideal.mem_span_singleton_self c)
    (Algebra.IsIntegral.isIntegral (R := R) c)
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hr
  obtain ⟨c', hc'⟩ := hr
  have hcL : algebraMap B L c ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc
  have hrK : algebraMap R K r ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hr0)
  have hθ : algebraMap B L (b * c') = algebraMap K L (algebraMap R K r) * θ0 := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R B L, ← hc', ← hbc,
      map_mul, map_mul]
    first | (field_simp; ring) | field_simp
  have hθint : IsIntegral K (algebraMap B L (b * c')) :=
    ((Algebra.IsIntegral.isIntegral (R := R) (b * c')).map
      (IsScalarTower.toAlgHom R B L)).tower_top
  obtain ⟨d, hd, f0, hf0, hmap⟩ := exists_monic_lift_minpoly (R := R) hθint
  have hdK : algebraMap R K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero hd)
  refine ⟨algebraMap R B d * (b * c'), f0, hf0, ?_, ?_⟩
  · rw [map_mul, ← IsScalarTower.algebraMap_apply]; exact hmap
  · rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R K L,
      adjoin_simple_mul_eq hdK, hθ, adjoin_simple_mul_eq hrK, hθ0]

end Generic

end RamanujanPetersson.IsogDegA

end

-- ===== S4.Def_RP_IsogDegA_Fib4 =====
section

/-!
# S4-IsogDegA, file Fib4: the generic fibre has `finSepDegree` points (O1 headline)

`B` finite over `R` (domains, `k`-algebras, `k` algebraically closed), `K = Frac R`, `L = Frac B`.
Over a dense open set of `k`-points `χ` of `Spec R` (those with `χ a ≠ 0`), the fibre of
`Spec B → Spec R` has exactly `[L : K]_s` points.
-/

set_option autoImplicit false

open Polynomial IntermediateField

namespace RamanujanPetersson.IsogDegA

section Headline

variable {R B K L : Type*} [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
  [Algebra R B] [Module.Finite R B]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]

/-- Every element of `B` has a `q`-power which, up to a nonzero constant, is a polynomial in a
generic element. -/
theorem exists_pow_eq_aeval (q : ℕ) [ExpChar K q] (β : B)
    (hβ : K⟮algebraMap B L β⟯ = separableClosure K L) (b : B) :
    ∃ n : ℕ, ∃ c : R, ∃ h : R[X], c ≠ 0 ∧ algebraMap R B c * b ^ q ^ n = aeval β h := by
  have : FiniteDimensional K L := finiteDimensional_of_finite (R := R) (B := B)
  have : ExpChar (separableClosure K L) q :=
    expChar_of_injective_algebraMap (algebraMap K _).injective q
  obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem (separableClosure K L) q (algebraMap B L b)
  obtain ⟨y, hy⟩ := RingHom.mem_range.1 hn
  have hθint : IsIntegral K (algebraMap B L β) :=
    ((Algebra.IsIntegral.isIntegral (R := R) β).map (IsScalarTower.toAlgHom R B L)).tower_top
  have hmem : algebraMap B L b ^ q ^ n ∈ Algebra.adjoin K {algebraMap B L β} := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hθint.isAlgebraic, hβ, ← hy]
    exact y.2
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨hK, hhK⟩ := (AlgHom.mem_range _).1 hmem
  obtain ⟨c, hc, hH⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) hK
  refine ⟨n, c, IsLocalization.integerNormalization (nonZeroDivisors R) hK,
    nonZeroDivisors.ne_zero hc, ?_⟩
  apply IsFractionRing.injective B L
  calc algebraMap B L (algebraMap R B c * b ^ q ^ n)
      = algebraMap R L c * algebraMap B L b ^ q ^ n := by
        rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply]
    _ = aeval (algebraMap B L β)
          ((IsLocalization.integerNormalization (nonZeroDivisors R) hK).map (algebraMap R K)) := by
        rw [hH, ← algebraMap_smul K c hK, smul_eq_C_mul, aeval_mul, aeval_C, hhK,
          ← IsScalarTower.algebraMap_apply]
    _ = _ := by rw [aeval_map_algebraMap, aeval_algebraMap_apply]

variable (k : Type*) [Field k] [IsAlgClosed k] [Algebra k R] [Algebra k B] [IsScalarTower k R B]

variable (K L) in
/-- **O1 headline.** There is `a ≠ 0` in `R` such that over every `k`-point `χ` with `χ a ≠ 0` the
fibre has exactly `Field.finSepDegree K L` points. -/
theorem exists_card_fiber_eq_finSepDegree :
    ∃ a : R, a ≠ 0 ∧ ∀ χ : R →ₐ[k] k, χ a ≠ 0 →
      Finite (fiber k B χ) ∧ Nat.card (fiber k B χ) = Field.finSepDegree K L := by
  classical
  have : FiniteDimensional K L := finiteDimensional_of_finite (R := R) (B := B)
  obtain ⟨q, hq⟩ := ExpChar.exists k
  have : ExpChar K q := expChar_of_injective_ringHom
    (f := (algebraMap R K).comp (algebraMap k R)) (RingHom.injective _) q
  obtain ⟨β, f0, hf0, hmap, hadj⟩ := exists_generic_element R B K L
  have hθint : IsIntegral K (algebraMap B L β) :=
    ((Algebra.IsIntegral.isIntegral (R := R) β).map (IsScalarTower.toAlgHom R B L)).tower_top
  have hsep : (f0.map (algebraMap R K)).Separable := by
    rw [hmap]
    have h : algebraMap B L β ∈ separableClosure K L := hadj ▸ mem_adjoin_simple_self K _
    exact h
  obtain ⟨a1, ha1, hsepχ⟩ := exists_sep_witness (K := K) k f0 hsep
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := B)
  have hg := fun b : B => exists_pow_eq_aeval (R := R) (K := K) (L := L) q β hadj b
  choose n c h hc hch using hg
  refine ⟨a1 * ∏ b ∈ s, c b, mul_ne_zero ha1 (Finset.prod_ne_zero_iff.2 fun b _ => hc b), ?_⟩
  intro χ hχ
  rw [map_mul, map_prod] at hχ
  have hχ1 : χ a1 ≠ 0 := left_ne_zero_of_mul hχ
  have hχ2 := Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hχ)
  have hβ0 : aeval β f0 = 0 := by
    have h0 : aeval (algebraMap B L β) (f0.map (algebraMap R K)) = 0 := by
      rw [hmap]; exact minpoly.aeval K _
    rw [aeval_map_algebraMap, aeval_algebraMap_apply] at h0
    exact IsFractionRing.injective B L (h0.trans (map_zero _).symm)
  have hdeg : f0.natDegree = Field.finSepDegree K L := by
    rw [← hf0.natDegree_map (algebraMap R K), hmap, ← adjoin.finrank hθint, hadj,
      Field.finSepDegree_eq K L]
    rfl
  rw [← hdeg]
  exact card_fiber_eq χ (s : Set B) hs β q (fun b hb => ⟨n b, c b, h b, hχ2 b hb, hch b⟩) f0 hf0
    hβ0 (dvd_of_aeval_eq_zero (K := K) (L := L) β f0 hf0 hmap) (hsepχ χ hχ1)

end Headline

end RamanujanPetersson.IsogDegA

end

-- ===== S4.Def_RP_JacSymA_A =====
section

/-!
# S4-JacSymA, file A: the coordinate ring of `X^g`, the `S_g`-action and the chart `Sym^g`

For a commutative `k`-algebra `B` (the coordinate ring of an affine chart `X = Spec B` of a curve), the coordinate
ring of `X^g` is the tensor power `XPow k B g = ⨂[k] _ : Fin g, B`. The symmetric group `S_g = Perm (Fin g)` acts by
permuting the tensor factors, and the affine chart of `Sym^g X` is `Spec (SymRing k B g)` with
`SymRing k B g = (⨂ B)^(S_g)`. A `g`-tuple of `k`-points of `B` is the same as a `k`-point of `XPow k B g`.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace RamanujanPetersson.JacSym

variable (k : Type*) [CommRing k] (B : Type*) [CommRing B] [Algebra k B] (g : ℕ)

/-- The coordinate ring of `X^g`: the `g`-fold tensor power of `B` over `k`. -/
abbrev XPow : Type _ := PiTensorProduct k (fun _ : Fin g => B)

variable {k B g}

/-- The algebra map of `X^g` that permutes the factors: `b_1 ⊗ ... ⊗ b_g ↦ b_(σ⁻¹ 1) ⊗ ... ⊗ b_(σ⁻¹ g)`. -/
noncomputable def permHom (σ : Equiv.Perm (Fin g)) : XPow k B g →ₐ[k] XPow k B g :=
  PiTensorProduct.liftAlgHom ((PiTensorProduct.tprod k).domDomCongr σ.symm)
    (by simp [MultilinearMap.domDomCongr_apply, PiTensorProduct.one_def]; rfl)
    (fun x y => by
      simp only [MultilinearMap.domDomCongr_apply, PiTensorProduct.tprod_mul_tprod]; rfl)

@[simp] theorem permHom_tprod (σ : Equiv.Perm (Fin g)) (b : Fin g → B) :
    permHom σ (PiTensorProduct.tprod k b) = PiTensorProduct.tprod k (fun i => b (σ.symm i)) := by
  simp [permHom, MultilinearMap.domDomCongr_apply]

theorem algHom_ext_tprod {f h : XPow k B g →ₐ[k] XPow k B g}
    (H : ∀ b : Fin g → B, f (PiTensorProduct.tprod k b) = h (PiTensorProduct.tprod k b)) : f = h :=
  AlgHom.toLinearMap_injective (PiTensorProduct.ext (MultilinearMap.ext H))

theorem permHom_one : permHom (1 : Equiv.Perm (Fin g)) = AlgHom.id k (XPow k B g) :=
  algHom_ext_tprod (fun b => by rw [permHom_tprod]; rfl)

theorem permHom_mul (σ τ : Equiv.Perm (Fin g)) :
    permHom (σ * τ) = (permHom σ).comp (permHom τ : XPow k B g →ₐ[k] XPow k B g) :=
  algHom_ext_tprod (fun b => by simp [Equiv.Perm.mul_def])

/-- `S_g` acts on `X^g` by ring automorphisms. -/
noncomputable instance : MulSemiringAction (Equiv.Perm (Fin g)) (XPow k B g) where
  smul σ x := permHom σ x
  one_smul x := by
    change permHom 1 x = x
    rw [permHom_one]; rfl
  mul_smul σ τ x := by
    change permHom (σ * τ) x = permHom σ (permHom τ x)
    rw [permHom_mul]; rfl
  smul_zero σ := map_zero (permHom σ)
  smul_add σ := map_add (permHom σ)
  smul_one σ := map_one (permHom σ)
  smul_mul σ := map_mul (permHom σ)

theorem perm_smul_def (σ : Equiv.Perm (Fin g)) (x : XPow k B g) : σ • x = permHom σ x := rfl

instance : SMulCommClass (Equiv.Perm (Fin g)) k (XPow k B g) where
  smul_comm σ c x := by simp only [perm_smul_def, map_smul]

variable (k B g)

/-- The coordinate ring of the affine chart `Sym^g X`: the `S_g`-invariants of `X^g`. -/
noncomputable abbrev SymRing : Subalgebra k (XPow k B g) :=
  FixedPoints.subalgebra k (XPow k B g) (Equiv.Perm (Fin g))

variable {k B g}

theorem mem_symRing (x : XPow k B g) : x ∈ SymRing k B g ↔ ∀ σ : Equiv.Perm (Fin g), σ • x = x :=
  Iff.rfl

/-- `S_g` acts on `X^g / Sym^g` with the invariants as base ring (Mathlib's `Algebra.IsInvariant`). -/
instance isInvariant : Algebra.IsInvariant (SymRing k B g) (XPow k B g) (Equiv.Perm (Fin g)) where
  isInvariant x hx := ⟨⟨x, (mem_symRing x).2 hx⟩, rfl⟩

/-- `X^g` is integral over `Sym^g` (the quotient map `X^g → Sym^g` is finite). -/
instance isIntegral : Algebra.IsIntegral (SymRing k B g) (XPow k B g) :=
  Algebra.IsInvariant.isIntegral (SymRing k B g) (XPow k B g) (Equiv.Perm (Fin g))

theorem smul_symRing (σ : Equiv.Perm (Fin g)) (x : SymRing k B g) : σ • (x : XPow k B g) = x :=
  x.2 σ

/-! ### `k`-points of `X^g` are `g`-tuples of `k`-points of `X` -/

/-- The multilinear map `(b_i) ↦ ∏ a_i (b_i)`. -/
noncomputable def ptML (a : Fin g → (B →ₐ[k] k)) : MultilinearMap k (fun _ : Fin g => B) k :=
  (MultilinearMap.mkPiAlgebra k (Fin g) k).compLinearMap (fun i => (a i).toLinearMap)

theorem ptML_apply (a : Fin g → (B →ₐ[k] k)) (b : Fin g → B) : ptML a b = ∏ i, a i (b i) := by
  simp [ptML, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-- The `k`-point of `X^g` with coordinates `a_1, ..., a_g`: `b_1 ⊗ ... ⊗ b_g ↦ ∏ a_i (b_i)`. -/
noncomputable def ptOf (a : Fin g → (B →ₐ[k] k)) : XPow k B g →ₐ[k] k :=
  PiTensorProduct.liftAlgHom (ptML a) (by rw [ptML_apply]; simp)
    (fun x y => by rw [ptML_apply, ptML_apply, ptML_apply, ← Finset.prod_mul_distrib]; simp)

@[simp] theorem ptOf_tprod (a : Fin g → (B →ₐ[k] k)) (b : Fin g → B) :
    ptOf a (PiTensorProduct.tprod k b) = ∏ i, a i (b i) := by
  rw [ptOf, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod, ptML_apply]

/-- The inclusion of the `i`-th factor `B → X^g`, `b ↦ 1 ⊗ ... ⊗ b ⊗ ... ⊗ 1`. -/
noncomputable def inc (i : Fin g) : B →ₐ[k] XPow k B g :=
  PiTensorProduct.singleAlgHom (R := k) (A := fun _ : Fin g => B) i

theorem ptOf_inc (a : Fin g → (B →ₐ[k] k)) (i : Fin g) : (ptOf a).comp (inc i) = a i := by
  ext b
  simp only [inc, AlgHom.comp_apply, PiTensorProduct.singleAlgHom_apply, ptOf_tprod]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem algHom_ext_inc {f h : XPow k B g →ₐ[k] k} (H : ∀ i, f.comp (inc i) = h.comp (inc i)) : f = h :=
  PiTensorProduct.algHom_ext H

/-- `k`-points of `X^g` are `g`-tuples of `k`-points of `X`. -/
noncomputable def ptsEquiv : (Fin g → (B →ₐ[k] k)) ≃ (XPow k B g →ₐ[k] k) where
  toFun := ptOf
  invFun ψ i := ψ.comp (inc i)
  left_inv a := by
    funext i
    exact ptOf_inc a i
  right_inv ψ := by
    apply algHom_ext_inc
    intro i
    exact ptOf_inc (fun j => ψ.comp (inc j)) i

theorem ptsEquiv_apply (a : Fin g → (B →ₐ[k] k)) : ptsEquiv a = ptOf a := rfl

theorem ptsEquiv_symm_apply (ψ : XPow k B g →ₐ[k] k) (i : Fin g) :
    ptsEquiv.symm ψ i = ψ.comp (inc i) := rfl

/-- Permuting the factors permutes the coordinates of a point. -/
theorem ptOf_comp_permHom (a : Fin g → (B →ₐ[k] k)) (τ : Equiv.Perm (Fin g)) :
    (ptOf a).comp (permHom τ) = ptOf (a ∘ τ) := by
  apply AlgHom.toLinearMap_injective
  refine PiTensorProduct.ext (MultilinearMap.ext fun b => ?_)
  simp only [LinearMap.compMultilinearMap_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
    permHom_tprod, ptOf_tprod, Function.comp_apply]
  exact (Equiv.prod_comp τ (fun i => a i (b (τ.symm i)))).symm.trans (by simp)

theorem ptOf_smul (a : Fin g → (B →ₐ[k] k)) (τ : Equiv.Perm (Fin g)) (x : XPow k B g) :
    ptOf a (τ • x) = ptOf (a ∘ τ) x := by
  rw [perm_smul_def, ← ptOf_comp_permHom]; rfl

/-- Points of `Sym^g` coming from `g`-tuples: restrict `ptOf a` to the invariants. -/
noncomputable def symPt (a : Fin g → (B →ₐ[k] k)) : SymRing k B g →ₐ[k] k :=
  (ptOf a).comp (SymRing k B g).val

theorem symPt_comp_perm (a : Fin g → (B →ₐ[k] k)) (τ : Equiv.Perm (Fin g)) :
    symPt (a ∘ τ) = symPt a := by
  ext x
  simp only [symPt, AlgHom.comp_apply, Subalgebra.coe_val]
  rw [← ptOf_smul, smul_symRing]

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacSymA_B =====
section

/-!
# S4-JacSymA, file B: the `k`-points of the chart `Sym^g X` (lemma L8 of S4_COREB_ROUTE.md)

For `k` algebraically closed, every `k`-point of `Sym^g = Spec (⨂ B)^(S_g)` lifts to a `k`-point of `X^g` (lying over,
`X^g` is integral over `Sym^g`), and two lifts differ by a permutation (`Algebra.IsInvariant.exists_smul_of_under_eq`).
Hence `k`-points of `Sym^g` are unordered `g`-tuples of `k`-points of `X`: `symPtsEquiv`.
-/

set_option autoImplicit false

open scoped Pointwise

namespace RamanujanPetersson.JacSym

/-- Two `k`-points with the same kernel are equal. -/
theorem algHom_eq_of_ker_eq {k A : Type*} [Field k] [CommRing A] [Algebra k A] {f h : A →ₐ[k] k}
    (H : RingHom.ker f = RingHom.ker h) : f = h := by
  ext x
  have hx : x - algebraMap k A (f x) ∈ RingHom.ker f := by simp [RingHom.mem_ker]
  rw [H, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply] at hx
  exact (sub_eq_zero.1 hx).symm

/-- The multiset of a tuple. -/
def mset {α : Type*} {n : ℕ} (a : Fin n → α) : Sym α n := ⟨Finset.univ.val.map a, by simp⟩

theorem mset_coe {α : Type*} {n : ℕ} (a : Fin n → α) : (mset a : Multiset α) = Finset.univ.val.map a := rfl

theorem mset_comp_perm {α : Type*} {n : ℕ} (a : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    mset (a ∘ σ) = mset a := by
  apply Sym.coe_injective
  rw [mset_coe, mset_coe, ← Multiset.map_map, Multiset.map_univ_val_equiv]

/-- Tuples with the same multiset of entries differ by a permutation. -/
theorem exists_perm_of_mset_eq {α : Type*} {n : ℕ} (f h : Fin n → α) (hfh : mset f = mset h) :
    ∃ σ : Equiv.Perm (Fin n), h = f ∘ σ := by
  classical
  have e1 : ∀ (u : Fin n → α) (x : α),
      Fintype.card {i // u i = x} = Multiset.count x (Finset.univ.val.map u) := by
    intro u x
    rw [Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun i _ => eq_comm)
  have hc : ∀ x, Fintype.card {i // h i = x} = Fintype.card {i // f i = x} := by
    intro x
    rw [e1, e1, ← mset_coe, ← mset_coe, hfh]
  refine ⟨Equiv.ofFiberEquiv (fun x => Fintype.equivOfCardEq (hc x)), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map _ i).symm

/-- Every unordered `n`-tuple comes from an ordered one. -/
theorem exists_mset_eq {α : Type*} {n : ℕ} (s : Sym α n) : ∃ a : Fin n → α, mset a = s := by
  obtain ⟨m, hm⟩ := s
  induction m using Quotient.inductionOn with
  | h l =>
    have hl : l.length = n := by simpa using hm
    subst hl
    refine ⟨fun i => l.get i, Sym.coe_injective ?_⟩
    rw [mset_coe, Fin.univ_val_map, List.ofFn_get]
    rfl

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {g : ℕ}

theorem symPt_apply (a : Fin g → (B →ₐ[k] k)) (x : SymRing k B g) : symPt a x = ptOf a (x : XPow k B g) :=
  rfl

/-- Transitivity: tuples with the same point of `Sym^g` differ by a permutation. -/
theorem exists_perm_of_symPt_eq (a a' : Fin g → (B →ₐ[k] k)) (h : symPt a = symPt a') :
    ∃ σ : Equiv.Perm (Fin g), a' = a ∘ σ := by
  have := RingHom.ker_isPrime (ptOf a)
  have := RingHom.ker_isPrime (ptOf a')
  obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (SymRing k B g) (XPow k B g)
    (Equiv.Perm (Fin g)) (RingHom.ker (ptOf a)) (RingHom.ker (ptOf a')) (by
      ext x
      simp only [Ideal.under, Ideal.mem_comap, RingHom.mem_ker]
      have hx := congrArg (fun f => f x) h
      simp only [symPt_apply] at hx
      change ptOf a (x : XPow k B g) = 0 ↔ ptOf a' (x : XPow k B g) = 0
      rw [hx])
  refine ⟨σ⁻¹, ptsEquiv.injective (algHom_eq_of_ker_eq ?_)⟩
  rw [ptsEquiv_apply, hσ]
  ext x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, RingHom.mem_ker, RingHom.mem_ker, ptOf_smul,
    ptsEquiv_apply]

theorem mset_eq_of_symPt_eq (a a' : Fin g → (B →ₐ[k] k)) (h : symPt a = symPt a') : mset a = mset a' := by
  obtain ⟨σ, rfl⟩ := exists_perm_of_symPt_eq a a' h
  exact (mset_comp_perm a σ).symm

theorem symPt_eq_of_mset_eq (a a' : Fin g → (B →ₐ[k] k)) (h : mset a = mset a') : symPt a = symPt a' := by
  obtain ⟨σ, rfl⟩ := exists_perm_of_mset_eq a a' h
  exact (symPt_comp_perm a σ).symm

/-- Lifting (needs `k` algebraically closed): every `k`-point of `Sym^g` is the image of a `k`-point of `X^g`. -/
theorem exists_lift [IsAlgClosed k] (φ : SymRing k B g →ₐ[k] k) :
    ∃ ψ : XPow k B g →ₐ[k] k, ψ.comp (SymRing k B g).val = φ := by
  have := RingHom.ker_isPrime φ
  obtain ⟨P, -, hP, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := XPow k B g)
    (RingHom.ker φ) ⊥ (by
      intro x hx
      have : x = 0 := Subtype.ext hx
      simp [this])
  have key : ∀ a : SymRing k B g,
      Ideal.Quotient.mk P (a : XPow k B g) = algebraMap k (XPow k B g ⧸ P) (φ a) := by
    intro a
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq]
    have h1 : a - algebraMap k (SymRing k B g) (φ a) ∈ RingHom.ker φ := by simp [RingHom.mem_ker]
    rw [← hPc, Ideal.mem_comap] at h1
    simpa using h1
  have hint : Algebra.IsIntegral k (XPow k B g ⧸ P) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := SymRing k B g) x
    refine ⟨p.map (φ : SymRing k B g →+* k), hpm.map _, ?_⟩
    have hc : (algebraMap k (XPow k B g ⧸ P)).comp (φ : SymRing k B g →+* k) =
        (Ideal.Quotient.mk P).comp (algebraMap (SymRing k B g) (XPow k B g)) :=
      RingHom.ext fun a => (key a).symm
    rw [Polynomial.eval₂_map, hc, ← Polynomial.hom_eval₂, hp, map_zero]
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := XPow k B g ⧸ P)
  let e : k ≃ₐ[k] XPow k B g ⧸ P := AlgEquiv.ofBijective (Algebra.ofId k (XPow k B g ⧸ P)) hbij
  refine ⟨(e.symm : XPow k B g ⧸ P →ₐ[k] k).comp (Ideal.Quotient.mkₐ k P), ?_⟩
  ext a
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Subalgebra.coe_val]
  rw [key a]
  exact e.symm_apply_apply (φ a)

variable [IsAlgClosed k]

/-- A chosen ordered lift of a `k`-point of `Sym^g`. -/
noncomputable def liftTuple (φ : SymRing k B g →ₐ[k] k) : Fin g → (B →ₐ[k] k) :=
  ptsEquiv.symm (Classical.choose (exists_lift φ))

theorem symPt_liftTuple (φ : SymRing k B g →ₐ[k] k) : symPt (liftTuple φ) = φ := by
  rw [symPt, liftTuple, ← ptsEquiv_apply, Equiv.apply_symm_apply]
  exact Classical.choose_spec (exists_lift φ)

/-- **L8 (points).** For `k` algebraically closed, the `k`-points of the chart `Sym^g X = Spec (⨂ B)^(S_g)` are the
unordered `g`-tuples of `k`-points of `X = Spec B`, i.e. the effective divisors of degree `g` supported on `X`. -/
noncomputable def symPtsEquiv : (SymRing k B g →ₐ[k] k) ≃ Sym (B →ₐ[k] k) g :=
  Equiv.ofBijective (fun φ => mset (liftTuple φ)) ⟨fun φ φ' h => by
      rw [← symPt_liftTuple φ, ← symPt_liftTuple φ']
      exact symPt_eq_of_mset_eq _ _ h,
    fun s => by
      obtain ⟨a, rfl⟩ := exists_mset_eq s
      exact ⟨symPt a, mset_eq_of_symPt_eq _ _ (symPt_liftTuple (symPt a))⟩⟩

theorem symPtsEquiv_symPt (a : Fin g → (B →ₐ[k] k)) : symPtsEquiv (symPt a) = mset a :=
  mset_eq_of_symPt_eq _ _ (symPt_liftTuple (symPt a))

theorem symPtsEquiv_symm_mset (a : Fin g → (B →ₐ[k] k)) : symPtsEquiv.symm (mset a) = symPt a := by
  rw [Equiv.symm_apply_eq, symPtsEquiv_symPt]

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacSymA_C =====
section

/-!
# S4-JacSymA, file C: points of the chart are effective divisors (L8, divisor form)

For `B` of finite type over an algebraically closed field `k`, the `k`-points of `Spec B` are its maximal ideals
(Nullstellensatz). If `B` is a Dedekind domain that is not a field (an affine chart of a smooth curve), these are the
height-one primes, i.e. the prime divisors supported on the chart. Combined with `symPtsEquiv` (file B): the
`k`-points of `Sym^g = Spec (⨂ B)^(S_g)` are the effective divisors of degree `g` supported on the chart.
-/

set_option autoImplicit false

open IsDedekindDomain

namespace RamanujanPetersson.JacSym

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]

theorem ker_isMaximal (φ : B →ₐ[k] k) : (RingHom.ker φ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective φ (fun c => ⟨algebraMap k B c, by simp⟩)

/-- Nullstellensatz: for `B` of finite type over algebraically closed `k`, every maximal ideal is the kernel of a
`k`-point. -/
theorem exists_algHom_ker_eq [IsAlgClosed k] [Algebra.FiniteType k B] (m : Ideal B) [m.IsMaximal] :
    ∃ φ : B →ₐ[k] k, RingHom.ker φ = m := by
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite k (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
  have hbij := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := B ⧸ m)
  let e : k ≃ₐ[k] B ⧸ m := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ m)) hbij
  refine ⟨(e.symm : B ⧸ m →ₐ[k] k).comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- `k`-points of `Spec B` are the maximal ideals of `B` (`B` of finite type over algebraically closed `k`). -/
noncomputable def ptMaxEquiv [IsAlgClosed k] [Algebra.FiniteType k B] : (B →ₐ[k] k) ≃ MaximalSpectrum B :=
  Equiv.ofBijective (fun φ => ⟨RingHom.ker φ, ker_isMaximal φ⟩)
    ⟨fun φ φ' h => algHom_eq_of_ker_eq (congrArg MaximalSpectrum.asIdeal h), fun m => by
      have := m.isMaximal
      obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (k := k) m.asIdeal
      exact ⟨φ, MaximalSpectrum.ext hφ⟩⟩

theorem ptMaxEquiv_asIdeal [IsAlgClosed k] [Algebra.FiniteType k B] (φ : B →ₐ[k] k) :
    (ptMaxEquiv φ).asIdeal = RingHom.ker φ := rfl

/-- For a Dedekind domain `B` of finite type over algebraically closed `k` that is not a field (an affine chart of a
smooth curve), `k`-points of `Spec B` are the prime divisors `HeightOneSpectrum B` supported on the chart. -/
noncomputable def ptDivEquiv [IsAlgClosed k] [Algebra.FiniteType k B] [IsDedekindDomain B] (hB : ¬ IsField B) :
    (B →ₐ[k] k) ≃ HeightOneSpectrum B :=
  ptMaxEquiv.trans (HeightOneSpectrum.equivMaximalSpectrum hB).symm

theorem ptDivEquiv_asIdeal [IsAlgClosed k] [Algebra.FiniteType k B] [IsDedekindDomain B] (hB : ¬ IsField B)
    (φ : B →ₐ[k] k) : (ptDivEquiv hB φ).asIdeal = RingHom.ker φ := rfl

/-- Effective divisors of degree `g` on a type of points (every point of degree one, `k` algebraically closed). -/
def EffDiv (α : Type*) (g : ℕ) : Type _ := {D : α →₀ ℕ // (D.sum fun _ n => n) = g}

/-- Unordered `g`-tuples are effective divisors of degree `g`. -/
noncomputable def symEquivEffDiv (α : Type*) (g : ℕ) [DecidableEq α] : Sym α g ≃ EffDiv α g :=
  Equiv.subtypeEquiv Multiset.toFinsupp.toEquiv (fun s => by
    change Multiset.card s = g ↔ ((Multiset.toFinsupp s).sum fun _ n => n) = g
    have h := Finsupp.card_toMultiset (Multiset.toFinsupp s)
    rw [Multiset.toFinsupp_toMultiset] at h
    rw [h]; exact Iff.rfl)

theorem symEquivEffDiv_apply_coe (α : Type*) (g : ℕ) [DecidableEq α] (s : Sym α g) (x : α) :
    (symEquivEffDiv α g s).1 x = Multiset.count x (s : Multiset α) := by
  exact Multiset.toFinsupp_apply _ x

variable (k B) in
/-- **L8 (divisor form).** For `B` a Dedekind domain of finite type over algebraically closed `k`, not a field (an
affine chart of a smooth curve), the `k`-points of the chart `Sym^g = Spec (⨂ B)^(S_g)` are the effective divisors of
degree `g` supported on the chart. -/
noncomputable def symPtsDivEquiv [IsAlgClosed k] [Algebra.FiniteType k B] [IsDedekindDomain B] (hB : ¬ IsField B)
    (g : ℕ) : (SymRing k B g →ₐ[k] k) ≃ EffDiv (HeightOneSpectrum B) g := by
  classical
  exact symPtsEquiv.trans ((Sym.equivCongr (ptDivEquiv hB)).trans (symEquivEffDiv _ g))

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacSymA_D =====
section

/-!
# S4-JacSymA, file D: `X^g` is integral

For `k` algebraically closed and `B` a finitely generated `k`-algebra that is a domain (an affine chart of an
integral curve), the coordinate ring `XPow k B g = ⨂[k] B` of `X^g` is a domain. Proof: `B ⊗[k] A` is a domain for
every `k`-algebra domain `A` (coordinates in a `k`-basis of `A`, evaluation at `k`-points of `B` and the
Nullstellensatz), and `X^(n+1) → B ⊗ X^n` is injective (it has the left inverse `B ⊗ X^n → X^(n+1)`).
-/

set_option autoImplicit false

open scoped TensorProduct

namespace RamanujanPetersson.JacSym

section liftFam

variable {k : Type*} [CommRing k] {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}
  {S : Type*} [CommRing S] [Algebra k S]

/-- The multilinear map `(b_i) ↦ ∏ f_i (b_i)` into a commutative `k`-algebra `S`. -/
noncomputable def famML (f : Fin n → (B →ₐ[k] S)) : MultilinearMap k (fun _ : Fin n => B) S :=
  (MultilinearMap.mkPiAlgebra k (Fin n) S).compLinearMap (fun i => (f i).toLinearMap)

theorem famML_apply (f : Fin n → (B →ₐ[k] S)) (b : Fin n → B) : famML f b = ∏ i, f i (b i) := by
  simp [famML, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-- The algebra map `X^n → S`, `b_1 ⊗ ... ⊗ b_n ↦ ∏ f_i (b_i)`, of a family of algebra maps `B → S`. -/
noncomputable def liftFam (f : Fin n → (B →ₐ[k] S)) : XPow k B n →ₐ[k] S :=
  PiTensorProduct.liftAlgHom (famML f) (by rw [famML_apply]; simp)
    (fun x y => by rw [famML_apply, famML_apply, famML_apply, ← Finset.prod_mul_distrib]; simp)

@[simp] theorem liftFam_tprod (f : Fin n → (B →ₐ[k] S)) (b : Fin n → B) :
    liftFam f (PiTensorProduct.tprod k b) = ∏ i, f i (b i) := by
  rw [liftFam, PiTensorProduct.liftAlgHom_apply, PiTensorProduct.lift.tprod, famML_apply]

theorem liftFam_inc (f : Fin n → (B →ₐ[k] S)) (i : Fin n) : (liftFam f).comp (inc i) = f i := by
  ext b
  simp only [inc, AlgHom.comp_apply, PiTensorProduct.singleAlgHom_apply, liftFam_tprod]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem liftFam_inc_apply (f : Fin n → (B →ₐ[k] S)) (i : Fin n) (b : B) : liftFam f (inc i b) = f i b := by
  rw [← AlgHom.comp_apply, liftFam_inc]

end liftFam

section cons

variable {k : Type*} [CommRing k] {B : Type*} [CommRing B] [Algebra k B] {n : ℕ}

/-- `B ⊗ X^n → X^(n+1)`: the first factor goes to slot `0`, the others to slots `1, ..., n`. -/
noncomputable def consHom : B ⊗[k] XPow k B n →ₐ[k] XPow k B (n + 1) :=
  Algebra.TensorProduct.lift (inc 0) (liftFam (fun j : Fin n => inc j.succ)) (fun _ _ => Commute.all _ _)

/-- `X^(n+1) → B ⊗ X^n`, `b_0 ⊗ b_1 ⊗ ... ⊗ b_n ↦ b_0 ⊗ (b_1 ⊗ ... ⊗ b_n)`. -/
noncomputable def unconsHom : XPow k B (n + 1) →ₐ[k] B ⊗[k] XPow k B n :=
  liftFam (fun i : Fin (n + 1) => Fin.cases (motive := fun _ => B →ₐ[k] B ⊗[k] XPow k B n)
    (Algebra.TensorProduct.includeLeft (S := k)) (fun j => Algebra.TensorProduct.includeRight.comp (inc j)) i)

theorem consHom_comp_unconsHom :
    (consHom (k := k) (B := B) (n := n)).comp unconsHom = AlgHom.id k (XPow k B (n + 1)) := by
  apply PiTensorProduct.algHom_ext
  intro i
  change consHom.comp (unconsHom.comp (inc i)) = (AlgHom.id k _).comp (inc i)
  rw [unconsHom, liftFam_inc]
  refine Fin.cases ?_ (fun j => ?_) i
  · ext b; simp [consHom]
  · ext b; simp [consHom, liftFam_inc_apply]

theorem unconsHom_injective : Function.Injective (unconsHom (k := k) (B := B) (n := n)) := fun x y hxy => by
  have h := congrArg (consHom (k := k) (B := B) (n := n)) hxy
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, consHom_comp_unconsHom, AlgHom.id_apply, AlgHom.id_apply] at h
  exact h

end cons

section domain

variable {k : Type*} [Field k] [IsAlgClosed k] {B : Type*} [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.FiniteType k B]

/-- Nullstellensatz: a function on `Spec B` vanishing at every `k`-point is zero. -/
theorem eq_zero_of_forall_pt (c : B) (hc : ∀ x : B →ₐ[k] k, x c = 0) : c = 0 := by
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have hj : (⊥ : Ideal B).jacobson = ⊥ := IsJacobsonRing.out' ⊥ Ideal.isPrime_bot.isRadical
  have hc' : c ∈ (⊥ : Ideal B).jacobson := by
    refine Ideal.mem_sInf.2 ?_
    rintro m ⟨-, hm⟩
    have := hm
    obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (k := k) m
    rw [← hφ, RingHom.mem_ker]
    exact hc φ
  rw [hj] at hc'
  exact (Submodule.mem_bot _).1 hc'

variable {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]

/-- Evaluation of the first factor at a `k`-point `x`: `B ⊗ A → A`, `c ⊗ a ↦ x(c) a`. -/
noncomputable def evPt (x : B →ₐ[k] k) : B ⊗[k] A →ₐ[k] A :=
  (Algebra.TensorProduct.lid k A).toAlgHom.comp (Algebra.TensorProduct.map x (AlgHom.id k A))

omit [IsAlgClosed k] [IsDomain B] [Algebra.FiniteType k B] [IsDomain A] in
theorem repr_evPt (x : B →ₐ[k] k) (f : B ⊗[k] A) (i : Module.Free.ChooseBasisIndex k A) :
    (Module.Free.chooseBasis k A).repr (evPt x f) i =
      x ((Algebra.TensorProduct.basis B (Module.Free.chooseBasis k A)).repr f i) := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul c a => simp [evPt, Algebra.TensorProduct.basis_repr_tmul]
  | add f h hf hh => simp [hf, hh]

/-- `B ⊗[k] A` is a domain for every `k`-algebra domain `A` (`k` algebraically closed, `B` a f.g. domain). -/
theorem isDomain_tensor : IsDomain (B ⊗[k] A) := by
  set E := Algebra.TensorProduct.basis B (Module.Free.chooseBasis k A)
  obtain ⟨i₀⟩ := (Module.Free.chooseBasis k A).index_nonempty
  have : Nontrivial (B ⊗[k] A) := nontrivial_of_ne _ _ (E.ne_zero i₀)
  have : NoZeroDivisors (B ⊗[k] A) := by
    refine ⟨fun {f h} hfh => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hf, hh⟩ := hcon
    obtain ⟨i, hi⟩ : ∃ i, E.repr f i ≠ 0 := by
      by_contra H; push Not at H; exact hf (E.repr.injective (by ext i; simp [H]))
    obtain ⟨j, hj⟩ : ∃ j, E.repr h j ≠ 0 := by
      by_contra H; push Not at H; exact hh (E.repr.injective (by ext j; simp [H]))
    obtain ⟨x, hx⟩ : ∃ x : B →ₐ[k] k, x (E.repr f i * E.repr h j) ≠ 0 := by
      by_contra H; push Not at H; exact mul_ne_zero hi hj (eq_zero_of_forall_pt _ H)
    rw [map_mul] at hx
    have h1 : evPt x f ≠ 0 := fun h0 => left_ne_zero_of_mul hx (by rw [← repr_evPt, h0]; simp)
    have h2 : evPt x h ≠ 0 := fun h0 => right_ne_zero_of_mul hx (by rw [← repr_evPt, h0]; simp)
    exact mul_ne_zero h1 h2 (by rw [← map_mul, hfh, map_zero])
  exact NoZeroDivisors.to_isDomain _

variable (k B) in
/-- `X^g` is integral: `XPow k B g` is a domain (`k` algebraically closed, `B` a f.g. `k`-domain). -/
theorem isDomain_xPow (g : ℕ) : IsDomain (XPow k B g) := by
  induction g with
  | zero =>
    have hinv : (Algebra.ofId k (XPow k B 0)).comp (liftFam (S := k) Fin.elim0) = AlgHom.id k _ :=
      PiTensorProduct.algHom_ext (fun i => i.elim0)
    exact Function.Injective.isDomain (liftFam (k := k) (B := B) (S := k) (n := 0) Fin.elim0)
      (Function.LeftInverse.injective (g := Algebra.ofId k (XPow k B 0))
        (fun x => DFunLike.congr_fun hinv x))
  | succ n ih =>
    have := ih
    have := isDomain_tensor (k := k) (B := B) (A := XPow k B n)
    exact Function.Injective.isDomain _ unconsHom_injective

instance (g : ℕ) : IsDomain (XPow k B g) := isDomain_xPow k B g

end domain

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacSymA_E =====
section

/-!
# S4-JacSymA, file E: the function field of `Sym^g X` (L9)

For `k` algebraically closed and `B` a finitely generated `k`-domain, `X^g = Spec (XPow k B g)` is integral (file D),
so it has a function field `K(X^g) = FunXPow k B g`. The symmetric group acts on it, and the fixed field is the
function field `K(Sym^g X) = FunSym k B g` of the chart `Sym^g X = Spec (SymRing k B g)`:
`K(Sym^g X) = K(X^g)^(S_g)` (`fixedPoints_eq_bot`, `mem_range_iff_fixed`).
-/

set_option autoImplicit false

open scoped TensorProduct

namespace RamanujanPetersson.JacSym

variable (k : Type*) [Field k] [IsAlgClosed k] (B : Type*) [CommRing B] [IsDomain B] [Algebra k B]
  [Algebra.FiniteType k B] (g : ℕ)

/-- The function field `K(X^g)`. -/
abbrev FunXPow : Type _ := FractionRing (XPow k B g)

/-- The function field `K(Sym^g X)` of the affine chart `Sym^g X = Spec (SymRing k B g)`. -/
abbrev FunSym : Type _ := FractionRing (SymRing k B g)

variable {k B g}

omit [IsAlgClosed k] [IsDomain B] [Algebra.FiniteType k B] in
instance : SMulCommClass (Equiv.Perm (Fin g)) (SymRing k B g) (XPow k B g) where
  smul_comm σ a x := by
    simp only [Subalgebra.smul_def, smul_eq_mul, smul_mul', smul_symRing]

/-- `S_g` acts on `K(X^g)`, extending the action on `X^g`. -/
noncomputable instance : MulSemiringAction (Equiv.Perm (Fin g)) (FunXPow k B g) :=
  IsFractionRing.mulSemiringAction (Equiv.Perm (Fin g)) (XPow k B g) (FunXPow k B g)

instance : SMulDistribClass (Equiv.Perm (Fin g)) (XPow k B g) (FunXPow k B g) :=
  IsFractionRing.smulDistribClass (Equiv.Perm (Fin g)) (XPow k B g) (FunXPow k B g)

instance : FaithfulSMul (SymRing k B g) (FunXPow k B g) :=
  (faithfulSMul_iff_algebraMap_injective _ _).2 <| by
    rw [IsScalarTower.algebraMap_eq (SymRing k B g) (XPow k B g) (FunXPow k B g)]
    exact (IsFractionRing.injective (XPow k B g) (FunXPow k B g)).comp Subtype.val_injective

/- Shortcut instances: a direct search for these wanders through the subalgebra and tensor-power instances. -/
set_option synthInstance.maxHeartbeats 100000 in
noncomputable instance algSymFunSym : Algebra (SymRing k B g) (FunSym k B g) :=
  inferInstanceAs (Algebra (SymRing k B g) (FractionRing (SymRing k B g)))

noncomputable instance smulSymFunSym : SMul (SymRing k B g) (FunSym k B g) := Algebra.toSMul

/-- `K(Sym^g X) ⊆ K(X^g)`. -/
noncomputable instance algFunSymFunXPow : Algebra (FunSym k B g) (FunXPow k B g) := FractionRing.liftAlgebra _ _

noncomputable instance smulFunSymFunXPow : SMul (FunSym k B g) (FunXPow k B g) := Algebra.toSMul

instance : IsScalarTower (SymRing k B g) (FunSym k B g) (FunXPow k B g) :=
  FractionRing.isScalarTower_liftAlgebra _ _

instance : SMulCommClass (Equiv.Perm (Fin g)) (FunSym k B g) (FunXPow k B g) :=
  IsFractionRing.smulCommClass (Equiv.Perm (Fin g)) (SymRing k B g) (XPow k B g) (FunSym k B g)
    (FunXPow k B g)

/-- L9: `S_g` acts on `K(X^g) / K(Sym^g X)` with invariants exactly `K(Sym^g X)`. -/
instance isInvariant_funField : Algebra.IsInvariant (FunSym k B g) (FunXPow k B g) (Equiv.Perm (Fin g)) :=
  IsFractionRing.isInvariant (Equiv.Perm (Fin g)) (SymRing k B g) (XPow k B g) (FunSym k B g) (FunXPow k B g)

/-- L9, elementwise: a rational function on `X^g` is a rational function on `Sym^g X` iff it is `S_g`-invariant. -/
theorem mem_range_iff_fixed (x : FunXPow k B g) :
    x ∈ Set.range (algebraMap (FunSym k B g) (FunXPow k B g)) ↔ ∀ σ : Equiv.Perm (Fin g), σ • x = x := by
  constructor
  · rintro ⟨y, rfl⟩ σ
    exact smul_algebraMap σ y
  · intro hx
    exact Algebra.IsInvariant.isInvariant x hx

/-- L9: `K(X^g)^(S_g) = K(Sym^g X)` as intermediate fields of `K(X^g) / K(Sym^g X)`. -/
theorem fixedPoints_eq_bot :
    FixedPoints.intermediateField (Equiv.Perm (Fin g)) = (⊥ : IntermediateField (FunSym k B g) (FunXPow k B g)) := by
  ext x
  rw [FixedPoints.mem_intermediateField_iff, IntermediateField.mem_bot, mem_range_iff_fixed]

/-- The algebra map `K(Sym^g X) → K(X^g)` restricts the fraction-field inclusion `Sym^g → X^g`. -/
theorem algebraMap_funSym (a : SymRing k B g) :
    algebraMap (FunSym k B g) (FunXPow k B g) (algebraMap (SymRing k B g) (FunSym k B g) a) =
      algebraMap (XPow k B g) (FunXPow k B g) (a : XPow k B g) := by
  rw [← IsScalarTower.algebraMap_apply (SymRing k B g) (FunSym k B g) (FunXPow k B g),
    IsScalarTower.algebraMap_apply (SymRing k B g) (XPow k B g) (FunXPow k B g)]
  rfl

/-- The `S_g`-action on `K(X^g)` extends the one on `X^g`. -/
theorem smul_algebraMap_xPow (σ : Equiv.Perm (Fin g)) (x : XPow k B g) :
    σ • algebraMap (XPow k B g) (FunXPow k B g) x = algebraMap (XPow k B g) (FunXPow k B g) (σ • x) :=
  (algebraMap.smul' σ x (FunXPow k B g)).symm

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacSymA =====
section

/-!
# S4-JacSymA: affine charts of `Sym^g` of a smooth curve (umbrella)

`X = Spec B` an affine chart of a smooth curve over an algebraically closed field `k`.
* A: `XPow k B g = ⨂[k] B` (coordinate ring of `X^g`), the `S_g`-action, `SymRing k B g = (⨂ B)^(S_g)` (chart of
  `Sym^g X`), `Algebra.IsInvariant`, integrality; `k`-points of `X^g` are `g`-tuples (`ptsEquiv`).
* B, C (L8): `symPtsEquiv : (SymRing k B g →ₐ[k] k) ≃ Sym (B →ₐ[k] k) g` and
  `symPtsDivEquiv : (SymRing k B g →ₐ[k] k) ≃ EffDiv (HeightOneSpectrum B) g` (effective divisors of degree `g`).
* D: `isDomain_xPow`: `X^g` is integral (`B` a f.g. `k`-domain).
* E (L9): `fixedPoints_eq_bot`, `mem_range_iff_fixed`: `K(Sym^g X) = K(X^g)^(S_g)`.
-/

set_option autoImplicit false

end

-- ===== S4.Def_RP_JacSymB_Poly =====
section

/-!
# S4-JacSymB, file A (L10): `Sym^g A^1 = A^g`

`X^g` for `X = A^1` is the polynomial ring in `g` variables (`polyEquiv`), `S_g`-equivariantly (`toMv_smul`), so
`Sym^g A^1 = Spec (k[X]^⊗g)^(S_g)` is the spectrum of the symmetric polynomials, which by the fundamental theorem of
symmetric polynomials is again a polynomial ring in `g` variables (`symPolyEquiv`).
-/

set_option autoImplicit false

open scoped TensorProduct
open Polynomial

namespace RamanujanPetersson.JacSym

section Poly

variable (k : Type*) [CommRing k] (g : ℕ)

/-- `k[X]^⊗g → k[X_1, ..., X_g]`, the `i`-th factor going to the `i`-th variable. -/
noncomputable def toMv : XPow k k[X] g →ₐ[k] MvPolynomial (Fin g) k :=
  liftFam (fun i => Polynomial.aeval (MvPolynomial.X i))

/-- `k[X_1, ..., X_g] → k[X]^⊗g`, `X_i ↦ 1 ⊗ ... ⊗ X ⊗ ... ⊗ 1`. -/
noncomputable def ofMv : MvPolynomial (Fin g) k →ₐ[k] XPow k k[X] g :=
  MvPolynomial.aeval (fun i => inc i Polynomial.X)

theorem toMv_inc (i : Fin g) (p : k[X]) : toMv k g (inc i p) = Polynomial.aeval (MvPolynomial.X i) p := by
  rw [toMv, liftFam_inc_apply]

theorem toMv_comp_ofMv : (toMv k g).comp (ofMv k g) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [ofMv, toMv_inc]

theorem ofMv_comp_toMv : (ofMv k g).comp (toMv k g) = AlgHom.id k _ := by
  apply PiTensorProduct.algHom_ext
  intro i
  apply Polynomial.algHom_ext
  change ofMv k g (toMv k g (inc i Polynomial.X)) = inc i Polynomial.X
  simp [ofMv, toMv_inc]

/-- `X^g = A^g` for `X = A^1`. -/
noncomputable def polyEquiv : XPow k k[X] g ≃ₐ[k] MvPolynomial (Fin g) k :=
  AlgEquiv.ofAlgHom (toMv k g) (ofMv k g) (toMv_comp_ofMv k g) (ofMv_comp_toMv k g)

theorem polyEquiv_apply (x : XPow k k[X] g) : polyEquiv k g x = toMv k g x := rfl

theorem toMv_injective : Function.Injective (toMv k g) := (polyEquiv k g).injective

variable {k g}

theorem permHom_comp_inc {B : Type*} [CommRing B] [Algebra k B] (σ : Equiv.Perm (Fin g)) (i : Fin g) :
    (permHom σ).comp (inc i) = (inc (σ i) : B →ₐ[k] XPow k B g) := by
  ext b
  simp only [inc, AlgHom.comp_apply, PiTensorProduct.singleAlgHom_apply, permHom_tprod]
  congr 1
  funext j
  simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_apply, Equiv.symm_apply_eq]

theorem toMv_comp_permHom (σ : Equiv.Perm (Fin g)) :
    (toMv k g).comp (permHom σ) = (MvPolynomial.rename σ).comp (toMv k g) := by
  apply PiTensorProduct.algHom_ext
  intro i
  apply Polynomial.algHom_ext
  change toMv k g (permHom σ (inc i Polynomial.X)) = MvPolynomial.rename σ (toMv k g (inc i Polynomial.X))
  rw [← AlgHom.comp_apply (permHom σ) (inc i), permHom_comp_inc, toMv_inc, toMv_inc]
  simp

theorem toMv_smul (σ : Equiv.Perm (Fin g)) (x : XPow k k[X] g) :
    toMv k g (σ • x) = MvPolynomial.rename σ (toMv k g x) := by
  rw [perm_smul_def, ← AlgHom.comp_apply, toMv_comp_permHom, AlgHom.comp_apply]

theorem mem_symRing_iff_isSymmetric (x : XPow k k[X] g) :
    x ∈ SymRing k k[X] g ↔ (toMv k g x).IsSymmetric := by
  rw [mem_symRing, MvPolynomial.IsSymmetric]
  refine forall_congr' fun σ => ?_
  rw [← toMv_smul, (toMv_injective k g).eq_iff]

variable (k g)

theorem map_symRing_eq :
    (SymRing k k[X] g).map (toMv k g) = MvPolynomial.symmetricSubalgebra (Fin g) k := by
  ext p
  rw [Subalgebra.mem_map, MvPolynomial.mem_symmetricSubalgebra]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_symRing_iff_isSymmetric x).1 hx
  · intro hp
    refine ⟨ofMv k g p, (mem_symRing_iff_isSymmetric _).2 ?_, ?_⟩
    · rwa [← AlgHom.comp_apply, toMv_comp_ofMv, AlgHom.id_apply]
    · rw [← AlgHom.comp_apply, toMv_comp_ofMv, AlgHom.id_apply]

/-- `Sym^g A^1` is the spectrum of the symmetric polynomials. -/
noncomputable def symEquiv : SymRing k k[X] g ≃ₐ[k] MvPolynomial.symmetricSubalgebra (Fin g) k :=
  ((polyEquiv k g).subalgebraMap (SymRing k k[X] g)).trans (Subalgebra.equivOfEq _ _ (map_symRing_eq k g))

/-- **L10** `Sym^g A^1 = A^g`: the fundamental theorem of symmetric polynomials. -/
noncomputable def symPolyEquiv : SymRing k k[X] g ≃ₐ[k] MvPolynomial (Fin g) k :=
  (symEquiv k g).trans (MvPolynomial.esymmAlgEquiv (Fin g) k (Fintype.card_fin g)).symm

theorem symEquiv_apply (x : SymRing k k[X] g) : (symEquiv k g x : MvPolynomial (Fin g) k) = toMv k g x := rfl

end Poly

end RamanujanPetersson.JacSym

end

-- ===== S4.Def_RP_JacSymB_Map =====
section

/-!
# S4-JacSymB, file B: functoriality of `X^g` and `Sym^g`; surjections stay surjective on invariants

`xMap f : X^g → Y^g` and `symMap f : Sym^g → Sym^g` for an algebra map `f : B → B'`. Over a field, a surjective `f` has a
linear section `s`, and `s^⊗g` is `S_g`-equivariant, so `symMap f` is surjective in every characteristic.
-/

set_option autoImplicit false

open scoped TensorProduct

namespace RamanujanPetersson.JacSym

section Map

variable {k : Type*} [CommRing k] {B : Type*} [CommRing B] [Algebra k B] {B' : Type*} [CommRing B'] [Algebra k B']
  {g : ℕ}

theorem prod_inc (c : Fin g → B) : ∏ i, inc i (c i) = (PiTensorProduct.tprod k c : XPow k B g) := by
  simp only [inc, PiTensorProduct.singleAlgHom_apply]
  rw [← PiTensorProduct.tprod_prod]
  congr 1
  exact Finset.univ_prod_mulSingle c

/-- `X^g → X'^g` induced by `f : B → B'`. -/
noncomputable def xMap (f : B →ₐ[k] B') : XPow k B g →ₐ[k] XPow k B' g := liftFam (fun i => (inc i).comp f)

theorem xMap_inc (f : B →ₐ[k] B') (i : Fin g) : (xMap f).comp (inc i) = (inc i).comp f := liftFam_inc _ i

@[simp] theorem xMap_tprod (f : B →ₐ[k] B') (b : Fin g → B) :
    xMap f (PiTensorProduct.tprod k b) = PiTensorProduct.tprod k (fun i => f (b i)) := by
  rw [xMap, liftFam_tprod, ← prod_inc]
  rfl

theorem xMap_comp_permHom (f : B →ₐ[k] B') (σ : Equiv.Perm (Fin g)) :
    (xMap f).comp (permHom σ) = (permHom σ).comp (xMap f) := by
  apply PiTensorProduct.algHom_ext
  intro i
  change (xMap f).comp ((permHom σ).comp (inc i)) = (permHom σ).comp ((xMap f).comp (inc i))
  rw [permHom_comp_inc, xMap_inc, xMap_inc, ← AlgHom.comp_assoc, permHom_comp_inc]

theorem xMap_smul (f : B →ₐ[k] B') (σ : Equiv.Perm (Fin g)) (x : XPow k B g) :
    xMap f (σ • x) = σ • xMap f x := by
  rw [perm_smul_def, perm_smul_def, ← AlgHom.comp_apply, xMap_comp_permHom, AlgHom.comp_apply]

/-- `Sym^g X → Sym^g X'` induced by `f : B → B'` (on coordinate rings, `Sym^g X' ← ...` contravariantly). -/
noncomputable def symMap (f : B →ₐ[k] B') : SymRing k B g →ₐ[k] SymRing k B' g :=
  ((xMap f).comp (SymRing k B g).val).codRestrict (SymRing k B' g) (fun x => by
    rw [mem_symRing]
    intro σ
    rw [AlgHom.comp_apply, ← xMap_smul]
    exact congrArg _ (smul_symRing σ x))

@[simp] theorem symMap_coe (f : B →ₐ[k] B') (x : SymRing k B g) : (symMap f x : XPow k B' g) = xMap f x := rfl

end Map

section Section

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B] {B' : Type*} [CommRing B'] [Algebra k B']
  {g : ℕ}

/-- `s^⊗g` for a linear map `s`. -/
noncomputable def secMap (s : B' →ₗ[k] B) : XPow k B' g →ₗ[k] XPow k B g := PiTensorProduct.map (fun _ => s)

theorem secMap_smul (s : B' →ₗ[k] B) (σ : Equiv.Perm (Fin g)) (x : XPow k B' g) :
    secMap s (σ • x) = σ • secMap s x := by
  rw [perm_smul_def, perm_smul_def]
  change ((secMap s).comp (permHom σ).toLinearMap) x = ((permHom σ).toLinearMap.comp (secMap s)) x
  congr 1
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro b
  simp [secMap, PiTensorProduct.map_tprod]

theorem xMap_secMap (f : B →ₐ[k] B') (s : B' →ₗ[k] B) (hs : ∀ b, f (s b) = b) (x : XPow k B' g) :
    xMap f (secMap s x) = x := by
  change ((xMap f).toLinearMap.comp (secMap s)) x = (LinearMap.id : XPow k B' g →ₗ[k] XPow k B' g) x
  congr 1
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro b
  simp [secMap, PiTensorProduct.map_tprod, hs]

/-- Surjections of algebras stay surjective on `S_g`-invariants (any characteristic). -/
theorem symMap_surjective (f : B →ₐ[k] B') (hf : Function.Surjective f) :
    Function.Surjective (symMap (g := g) f) := by
  obtain ⟨s, hs⟩ := f.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  have hs' : ∀ b, f (s b) = b := fun b => by simpa using LinearMap.congr_fun hs b
  intro y
  refine ⟨⟨secMap s (y : XPow k B' g), ?_⟩, ?_⟩
  · rw [mem_symRing]
    intro σ
    rw [← secMap_smul, smul_symRing]
  · apply Subtype.ext
    rw [symMap_coe]
    exact xMap_secMap f s hs' _

/-- Kernel of `X^g → X'^g` for a surjection: generated by the coordinate copies of `ker f`. -/
theorem ker_xMap_le (f : B →ₐ[k] B') (hf : Function.Surjective f) :
    RingHom.ker (xMap (g := g) f) ≤ Ideal.span (⋃ l : Fin g, inc l '' (RingHom.ker f : Set B)) := by
  classical
  set J : Ideal (XPow k B g) := Ideal.span (⋃ l : Fin g, inc l '' (RingHom.ker f : Set B))
  obtain ⟨s, hs⟩ := f.toLinearMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hf)
  have hs' : ∀ b, f (s b) = b := fun b => by simpa using LinearMap.congr_fun hs b
  have key : (Ideal.Quotient.mkₐ k J).toLinearMap =
      (Ideal.Quotient.mkₐ k J).toLinearMap.comp ((secMap s).comp (xMap (g := g) f).toLinearMap) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro b
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, xMap_tprod,
      secMap, PiTensorProduct.map_tprod, Ideal.Quotient.mkₐ_eq_mk]
    rw [← prod_inc, ← prod_inc, map_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Ideal.Quotient.eq, ← map_sub]
    refine Ideal.subset_span (Set.mem_iUnion.2 ⟨i, _, ?_, rfl⟩)
    change f _ = 0
    rw [map_sub, hs', sub_self]
  intro t ht
  have h := LinearMap.congr_fun key t
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, (RingHom.mem_ker).1 ht, map_zero,
    Ideal.Quotient.mkₐ_eq_mk] at h
  exact Ideal.Quotient.eq_zero_iff_mem.1 h

end Section

end RamanujanPetersson.JacSym

end


