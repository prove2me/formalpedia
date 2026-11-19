-- Prove2me | Definitions.Def_RPLib_S4_CDPack03
-- name    : RPLib_S4_CDPack03
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:12:44.424602+00:00
-- url     : https://prove2.me/theorems/7f0ac691-e638-412b-a026-fc94f1ab9373
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 3 of 71
-- statement:
--   Part 3 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_PerfectCx_Alg`: S4-PD (5), E2 set-up and E2(a): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ`-free
--   * `Def_RP_PerfectCx_Tensor`: S4-PD (5), E2(c) part 1: the evaluation map `(E ⊗ M)_{Gf} → Z¹(Γ; M)`
--   * `Def_RP_PerfectCx_TensorIso`: S4-PD (5), E2(c) part 2: `(E ⊗ M)_{Gf} ≃ Z¹(Γ; M)`
--   * `Def_RP_PerfectCx_Cx`: S4-PD (5), E3: the cone complex and its free `Λ[Gf]` model
--   * `Def_RP_PerfectCx_CxH`: S4-PD (5), E3: the cohomology of the cone complex
--   * `Def_RP_CupDuality_Cup`: S4-CurveDuality O2a: the cup product `H¹_c(M) × H¹(M') → H²(K(L))` in the truncated cone
--   * `Def_RP_HattoriStallings_SES`: Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules
--   * `Def_RP_PerfectCx_CxIso`: S4-PD (5), E3: `P ⊗_{Λ[Gf]} M ≅ K(M)`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack01
import Definitions.Def_RPLib_S4_CDPack02

/-!
# Curve-duality library package, part 3 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_PerfectCx_Alg`: S4-PD (5), E2 set-up and E2(a): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ`-free
* `Def_RP_PerfectCx_Tensor`: S4-PD (5), E2(c) part 1: the evaluation map `(E ⊗ M)_{Gf} → Z¹(Γ; M)`
* `Def_RP_PerfectCx_TensorIso`: S4-PD (5), E2(c) part 2: `(E ⊗ M)_{Gf} ≃ Z¹(Γ; M)`
* `Def_RP_PerfectCx_Cx`: S4-PD (5), E3: the cone complex and its free `Λ[Gf]` model
* `Def_RP_PerfectCx_CxH`: S4-PD (5), E3: the cohomology of the cone complex
* `Def_RP_CupDuality_Cup`: S4-CurveDuality O2a: the cup product `H¹_c(M) × H¹(M') → H²(K(L))` in the truncated cone
* `Def_RP_HattoriStallings_SES`: Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules
* `Def_RP_PerfectCx_CxIso`: S4-PD (5), E3: `P ⊗_{Λ[Gf]} M ≅ K(M)`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_PerfectCx_Alg =====
section

/-!
# S4-PD (5), E2 set-up and E2(a): the cocycle module `E = Z¹(Γ; Λ[Gf])` is `Λ`-free

`π : G →* Gf` (open kernel, `Gf` finite), `A = Λ[Gf]` (`MonoidAlgebra`) with `G` acting by left multiplication
through `π` (`regRep`), `E = Z¹(Γ; A)` (locally constant cocycles, `S4-CurveCoh`), and `Gf` acting on `E` by right
multiplication by `h⁻¹` on values (`eRep`; the convention of the `S4-HattoriStallings` coinvariants
`(E ⊗ M)_{Gf} = Coinvariants (tprod eRep τ)`).

* `lift_of_values`: under `H2All`, a cocycle with values in a subrepresentation `W` lifts along any equivariant `q`
  onto `W`;
* `free_E`: over a local `Λ` with `𝔪 = (ϖ)`, `ϖⁿ = 0`, `ϖᵐ ≠ 0` (`m < n`), `E` is free (if finite), via
  `free_of_torsion` and the lift along `ϖ • : A → ϖA`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra IsLocalRing

noncomputable section

section Regular

variable (Λ : Type) [CommRing Λ] (Gf : Type) [Group Gf]

/-- `Λ[Gf]` with `Gf` acting by left multiplication. -/
def leftRep : Representation Λ Gf (MonoidAlgebra Λ Gf) where
  toFun x := LinearMap.mulLeft Λ (single x 1)
  map_one' := by
    refine LinearMap.ext fun a => ?_
    show single 1 1 * a = a
    rw [← one_def, one_mul]
  map_mul' x y := by
    refine LinearMap.ext fun a => ?_
    show single (x * y) 1 * a = single x 1 * (single y 1 * a)
    rw [← mul_assoc, single_mul_single, one_mul]

theorem leftRep_apply (x : Gf) (a : MonoidAlgebra Λ Gf) : leftRep Λ Gf x a = single x 1 * a := rfl

theorem finite_A [Finite Λ] [Finite Gf] : Finite (MonoidAlgebra Λ Gf) := by
  haveI : Module.Finite Λ (MonoidAlgebra Λ Gf) := Module.Finite.of_basis (MonoidAlgebra.basis Gf Λ)
  exact Module.finite_of_finite Λ

end Regular

section Lift

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N) (Γ : Subgroup G)

/-- Under `H2All`, a cocycle with values in a subrepresentation `W` lifts along an equivariant `q` onto `W`. -/
theorem lift_of_values {l n : ℕ} (hall : H2All k G Γ l n) [Finite M] (hM : ∀ m : M, (l ^ n) • m = 0)
    (hρ : IsOpen (ρ.ker : Set G)) (q : M →ₗ[k] N) (hq : ∀ (g : G) (m : M), q (ρ g m) = σ g (q m))
    (W : Subrepresentation σ) (hqW : ∀ m, q m ∈ W.toSubmodule)
    (hsurj : ∀ w ∈ W.toSubmodule, ∃ m, q m = w)
    (z : Z1 σ Γ) (hz : ∀ g, (z : Γ → N) g ∈ W.toSubmodule) :
    ∃ c : Z1 ρ Γ, ∀ g, q ((c : Γ → M) g) = (z : Γ → N) g := by
  let q' : M →ₗ[k] W.toSubmodule := q.codRestrict W.toSubmodule hqW
  have hq' : ∀ (g : G) (m : M), q' (ρ g m) = W.toRepresentation g (q' m) := fun g m => Subtype.ext (hq g m)
  have hs' : Function.Surjective q' := fun w => by
    obtain ⟨m, hm⟩ := hsurj w w.2
    exact ⟨m, Subtype.ext hm⟩
  obtain ⟨hlc, hco⟩ := (mem_Z1 σ Γ _).1 z.2
  have hzW : (fun g => (⟨(z : Γ → N) g, hz g⟩ : W.toSubmodule)) ∈ Z1 W.toRepresentation Γ := by
    refine (mem_Z1 _ Γ _).2 ⟨IsLocallyConstant.desc _ Subtype.val hlc Subtype.val_injective,
      fun g h => Subtype.ext ?_⟩
    simpa [toRep_val] using hco g h
  obtain ⟨c, hc⟩ := z1Map_surjective_of_all ρ W.toRepresentation Γ hall hM hρ q' hq' hs' ⟨_, hzW⟩
  refine ⟨c, fun g => ?_⟩
  have := congrArg (fun z : Z1 W.toRepresentation Γ => (((z : Γ → W.toSubmodule) g : W.toSubmodule) : N)) hc
  exact this

theorem nsmul_eq_zero_of_cast {l n : ℕ} (hk : ((l ^ n : ℕ) : k) = 0) (m : M) : (l ^ n) • m = 0 := by
  rw [← Nat.cast_smul_eq_nsmul k, hk, zero_smul]

end Lift

section Cocycles

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G)

variable (Λ) in
/-- `G` acting on `Λ[Gf]` by left multiplication through `π`. -/
def regRep : Representation Λ G (MonoidAlgebra Λ Gf) := (leftRep Λ Gf).comp π

theorem regRep_apply (g : G) (a : MonoidAlgebra Λ Gf) : regRep Λ π g a = single (π g) 1 * a := rfl

theorem isOpen_regRep_ker (hπ : IsOpen (π.ker : Set G)) : IsOpen ((regRep Λ π).ker : Set G) := by
  refine Subgroup.isOpen_mono (fun g hg => ?_) hπ
  rw [MonoidHom.mem_ker] at hg ⊢
  show (leftRep Λ Gf) (π g) = 1
  rw [hg, map_one]

theorem mulRight_regRep (b : MonoidAlgebra Λ Gf) (g : G) (a : MonoidAlgebra Λ Gf) :
    LinearMap.mulRight Λ b (regRep Λ π g a) = regRep Λ π g (LinearMap.mulRight Λ b a) := by
  show single (π g) 1 * a * b = single (π g) 1 * (a * b)
  rw [mul_assoc]

/-- Right multiplication on cocycle values (the right `Λ[Gf]`-module structure of `E`). -/
def eMul (b : MonoidAlgebra Λ Gf) : Z1 (regRep Λ π) Γ →ₗ[Λ] Z1 (regRep Λ π) Γ :=
  z1Map (regRep Λ π) (regRep Λ π) Γ (LinearMap.mulRight Λ b) (mulRight_regRep π b)

theorem eMul_apply (b : MonoidAlgebra Λ Gf) (c : Z1 (regRep Λ π) Γ) (g : Γ) :
    (eMul π Γ b c : Γ → MonoidAlgebra Λ Gf) g = (c : Γ → MonoidAlgebra Λ Gf) g * b := rfl

/-- `Gf` acting on `E = Z¹(Γ; Λ[Gf])` by right multiplication by `h⁻¹` on values. -/
def eRep : Representation Λ Gf (Z1 (regRep Λ π) Γ) where
  toFun h := eMul π Γ (single h⁻¹ 1)
  map_one' := by
    refine LinearMap.ext fun c => Subtype.ext (funext fun g => ?_)
    show (c : Γ → MonoidAlgebra Λ Gf) g * single 1⁻¹ 1 = (c : Γ → MonoidAlgebra Λ Gf) g
    rw [inv_one, ← one_def, mul_one]
  map_mul' x y := by
    refine LinearMap.ext fun c => Subtype.ext (funext fun g => ?_)
    show (c : Γ → MonoidAlgebra Λ Gf) g * single (x * y)⁻¹ 1 =
      (c : Γ → MonoidAlgebra Λ Gf) g * single y⁻¹ 1 * single x⁻¹ 1
    rw [mul_assoc, single_mul_single, mul_inv_rev, one_mul]

theorem eRep_apply (h : Gf) (c : Z1 (regRep Λ π) Γ) (g : Γ) :
    (eRep π Γ h c : Γ → MonoidAlgebra Λ Gf) g = (c : Γ → MonoidAlgebra Λ Gf) g * single h⁻¹ 1 := rfl

/-- The subrepresentation `ϖ • A`. -/
def smulRep (ϖ : Λ) : Subrepresentation (regRep Λ π) where
  toSubmodule := LinearMap.range (LinearMap.lsmul Λ (MonoidAlgebra Λ Gf) ϖ)
  apply_mem_toSubmodule g v hv := by
    obtain ⟨b, rfl⟩ := hv
    exact ⟨regRep Λ π g b, by simp⟩

/-- Coefficientwise: `ϖᵐ`-torsion of `Λ[Gf]` (`m < n`) is divisible by `ϖ`. -/
theorem exists_smul_of_pow_smul [IsLocalRing Λ] [Finite Gf] {ϖ : Λ} (hϖ : maximalIdeal Λ = Ideal.span {ϖ})
    {m : ℕ} (hm : ϖ ^ m ≠ 0) (a : MonoidAlgebra Λ Gf) (ha : ϖ ^ m • a = 0) :
    ∃ b : MonoidAlgebra Λ Gf, a = ϖ • b := by
  have hx : ∀ x : Gf, ∃ y, a.coeff x = ϖ * y := fun x => by
    refine exists_eq_mul_of_not_isUnit hϖ fun hu => hm ?_
    have h1 : (ϖ ^ m • a).coeff x = 0 := by rw [ha]; rfl
    rw [coeff_smul_apply, smul_eq_mul] at h1
    simpa using (hu.mul_left_eq_zero).1 h1
  choose y hy using hx
  refine ⟨ofCoeff (Finsupp.equivFunOnFinite.symm y), ?_⟩
  ext x
  rw [coeff_smul_apply, hy x, smul_eq_mul]
  rfl

theorem coe_smul_Z1 (r : Λ) (c : Z1 (regRep Λ π) Γ) (g : Γ) :
    ((r • c : Z1 (regRep Λ π) Γ) : Γ → MonoidAlgebra Λ Gf) g = r • (c : Γ → MonoidAlgebra Λ Gf) g := rfl

/-- **E2(a)**: `E = Z¹(Γ; Λ[Gf])` is `Λ`-free (given `H² = 0` and finiteness of `E`). -/
theorem free_E [IsLocalRing Λ] [Finite Λ] [Finite Gf] {ϖ : Λ} (hϖ : maximalIdeal Λ = Ideal.span {ϖ}) {n : ℕ}
    (hn : ϖ ^ n = 0) (hn' : ∀ m < n, ϖ ^ m ≠ 0) {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
    (hall : H2All Λ G Γ l N) (hπ : IsOpen (π.ker : Set G)) [Module.Finite Λ (Z1 (regRep Λ π) Γ)] :
    Module.Free Λ (Z1 (regRep Λ π) Γ) := by
  haveI := finite_A Λ Gf
  refine free_of_torsion hϖ hn fun m hm z hz => ?_
  have hzv : ∀ g, (z : Γ → MonoidAlgebra Λ Gf) g ∈ (smulRep π ϖ).toSubmodule := fun g => by
    have h1 : ϖ ^ m • (z : Γ → MonoidAlgebra Λ Gf) g = 0 := by
      rw [← coe_smul_Z1, hz]
      rfl
    obtain ⟨b, hb⟩ := exists_smul_of_pow_smul hϖ (hn' m hm) _ h1
    exact ⟨b, by simp [hb]⟩
  obtain ⟨c, hc⟩ := lift_of_values (regRep Λ π) (regRep Λ π) Γ hall (nsmul_eq_zero_of_cast hΛ)
    (isOpen_regRep_ker π hπ) (LinearMap.lsmul Λ (MonoidAlgebra Λ Gf) ϖ) (fun g a => by simp)
    (smulRep π ϖ) (fun a => ⟨a, rfl⟩) (fun w hw => hw) z hzv
  refine ⟨c, Subtype.ext (funext fun g => ?_)⟩
  rw [coe_smul_Z1, ← hc g]
  rfl

end Cocycles

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_PerfectCx_Tensor =====
section

/-!
# S4-PD (5), E2(c) part 1: the evaluation map `(E ⊗ M)_{Gf} → Z¹(Γ; M)`

For `τ : Representation Λ Gf M` and `E = Z¹(Γ; Λ[Gf])`, `Phi : Coinvariants (tprod eRep τ) → Z¹(Γ; M)`,
`⟦c ⊗ m⟧ ↦ (g ↦ c(g) · m)` (`a · m = asAlgebraHom τ a m`), and the balancedness
`⟦(c · a) ⊗ m⟧ = ⟦c ⊗ (a · m)⟧` (`mk_eMul_tmul`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra TensorProduct

noncomputable section

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G)
  {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)

theorem act_single_mul (x : Gf) (a : MonoidAlgebra Λ Gf) (m : M) :
    τ.asAlgebraHom (single x 1 * a) m = τ x (τ.asAlgebraHom a m) := by
  rw [map_mul, Module.End.mul_apply, Representation.asAlgebraHom_single_one]

/-- `c ↦ (g ↦ c(g) · m)`. -/
def evalZ1 (m : M) : Z1 (regRep Λ π) Γ →ₗ[Λ] Z1 (τ.comp π) Γ :=
  z1Map (regRep Λ π) (τ.comp π) Γ ((LinearMap.applyₗ m).comp τ.asAlgebraHom.toLinearMap)
    (fun g a => act_single_mul τ (π g) a m)

theorem evalZ1_apply (m : M) (c : Z1 (regRep Λ π) Γ) (g : Γ) :
    (evalZ1 π Γ τ m c : Γ → M) g = τ.asAlgebraHom ((c : Γ → MonoidAlgebra Λ Gf) g) m := rfl

/-- `c ⊗ m ↦ (g ↦ c(g) · m)` on `E ⊗[Λ] M`. -/
def phi0 : Z1 (regRep Λ π) Γ ⊗[Λ] M →ₗ[Λ] Z1 (τ.comp π) Γ :=
  TensorProduct.lift (LinearMap.mk₂ Λ (fun c m => evalZ1 π Γ τ m c)
    (fun c c' m => map_add _ c c') (fun r c m => map_smul _ r c)
    (fun c m m' => Subtype.ext (funext fun g =>
      map_add (τ.asAlgebraHom ((c : Γ → MonoidAlgebra Λ Gf) g)) m m'))
    (fun r c m => Subtype.ext (funext fun g =>
      map_smul (τ.asAlgebraHom ((c : Γ → MonoidAlgebra Λ Gf) g)) r m)))

theorem phi0_tmul (c : Z1 (regRep Λ π) Γ) (m : M) (g : Γ) :
    (phi0 π Γ τ (c ⊗ₜ m) : Γ → M) g = τ.asAlgebraHom ((c : Γ → MonoidAlgebra Λ Gf) g) m := rfl

theorem phi0_inv (h : Gf) : phi0 π Γ τ ∘ₗ ((eRep π Γ).tprod τ) h = phi0 π Γ τ := by
  refine TensorProduct.ext' fun c m => Subtype.ext (funext fun g => ?_)
  rw [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul, phi0_tmul, phi0_tmul,
    eRep_apply, map_mul, Module.End.mul_apply, Representation.asAlgebraHom_single_one]
  have hinv : τ h⁻¹ (τ h m) = m := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hinv]

/-- The left factor `E` is a submodule: its `AddCommMonoid` is not syntactically `AddCommGroup.toAddCommMonoid`. -/
instance instAddCommGroupTensorE : AddCommGroup (Z1 (regRep Λ π) Γ ⊗[Λ] M) := TensorProduct.addCommGroup

/-- **E2(c) map**: `Phi : (E ⊗ M)_{Gf} → Z¹(Γ; M)`, `⟦c ⊗ m⟧ ↦ (g ↦ c(g) · m)`. -/
def Phi : Representation.Coinvariants ((eRep (Λ := Λ) π Γ).tprod τ) →ₗ[Λ] Z1 (τ.comp π) Γ :=
  Representation.Coinvariants.lift _ (phi0 π Γ τ) (phi0_inv π Γ τ)

theorem Phi_mk_tmul (c : Z1 (regRep Λ π) Γ) (m : M) (g : Γ) :
    (Phi π Γ τ (Representation.Coinvariants.mk _ (c ⊗ₜ m)) : Γ → M) g =
      τ.asAlgebraHom ((c : Γ → MonoidAlgebra Λ Gf) g) m := rfl

theorem eMul_add (a b : MonoidAlgebra Λ Gf) (D : Z1 (regRep Λ π) Γ) :
    eMul π Γ (a + b) D = eMul π Γ a D + eMul π Γ b D :=
  Subtype.ext (funext fun g => mul_add ((D : Γ → MonoidAlgebra Λ Gf) g) a b)

theorem eMul_smul (r : Λ) (a : MonoidAlgebra Λ Gf) (D : Z1 (regRep Λ π) Γ) :
    eMul π Γ (r • a) D = r • eMul π Γ a D :=
  Subtype.ext (funext fun g => mul_smul_comm r ((D : Γ → MonoidAlgebra Λ Gf) g) a)

/-- Balancedness: `⟦(c · a) ⊗ m⟧ = ⟦c ⊗ (a · m)⟧` in `(E ⊗ M)_{Gf}`. -/
theorem mk_eMul_tmul (a : MonoidAlgebra Λ Gf) (D : Z1 (regRep Λ π) Γ) (m : M) :
    Representation.Coinvariants.mk ((eRep (Λ := Λ) π Γ).tprod τ) (eMul π Γ a D ⊗ₜ m) =
      Representation.Coinvariants.mk ((eRep (Λ := Λ) π Γ).tprod τ) (D ⊗ₜ τ.asAlgebraHom a m) := by
  induction a using MonoidAlgebra.induction_on with
  | of x =>
    have h1 : eMul π Γ (of Λ Gf x) D = eRep π Γ x⁻¹ D := by
      refine Subtype.ext (funext fun g => ?_)
      rw [eMul_apply, eRep_apply, inv_inv, of_apply]
    have hinv : τ x⁻¹ (τ x m) = m := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [h1, Representation.asAlgebraHom_of]
    refine (Representation.Coinvariants.mk_eq_iff _).2
      (Representation.Coinvariants.mem_ker_of_eq x⁻¹ (D ⊗ₜ τ x m) _ ?_)
    rw [Representation.tprod_apply, TensorProduct.map_tmul, hinv]
  | add a b ha hb =>
    simp only [eMul_add, add_tmul, map_add, ha, hb, LinearMap.add_apply, tmul_add]
  | smul r a ha =>
    simp only [eMul_smul, ← smul_tmul', map_smul, ha, LinearMap.smul_apply, tmul_smul]

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_PerfectCx_TensorIso =====
section

/-!
# S4-PD (5), E2(c) part 2: `(E ⊗ M)_{Gf} ≃ Z¹(Γ; M)`

Under `H2All` (exactness of `Z¹(Γ; -)` on finite `lᴺ`-torsion modules), the evaluation map `Phi` of part 1 is
bijective (`tensorEquiv`) and natural in `M` (`Phi_natural`).
* surjective: lift a cocycle along `qMap : (M → Λ[Gf]) → M`, `(a_m) ↦ Σ_m a_m · m`;
* injective: a family `(c_m)` killed by `Phi` assembles to a cocycle with values in `K = ker qMap`; it lifts along
  `combMap : (K → Λ[Gf]) → K`, `(d_k) ↦ Σ_k d_k k`, and balancedness (`mk_eMul_tmul`) kills `⟦Σ_m c_m ⊗ m⟧`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra TensorProduct

noncomputable section

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G)

section Pi

variable (ι : Type)

variable (Λ) in
/-- `G` acting on `ι → Λ[Gf]` by left multiplication through `π` in each coordinate. -/
def piRep : Representation Λ G (ι → MonoidAlgebra Λ Gf) where
  toFun g := LinearMap.pi fun i =>
    (regRep Λ π g).comp (LinearMap.proj i : (ι → MonoidAlgebra Λ Gf) →ₗ[Λ] MonoidAlgebra Λ Gf)
  map_one' := by
    refine LinearMap.ext fun f => funext fun i => ?_
    show regRep Λ π 1 (f i) = f i
    rw [map_one]
    rfl
  map_mul' x y := by
    refine LinearMap.ext fun f => funext fun i => ?_
    show regRep Λ π (x * y) (f i) = regRep Λ π x (regRep Λ π y (f i))
    rw [map_mul]
    rfl

theorem piRep_apply (g : G) (f : ι → MonoidAlgebra Λ Gf) (i : ι) :
    piRep Λ π ι g f i = regRep Λ π g (f i) := rfl

theorem isOpen_piRep_ker (hπ : IsOpen (π.ker : Set G)) : IsOpen ((piRep Λ π ι).ker : Set G) := by
  refine Subgroup.isOpen_mono (fun g hg => ?_) hπ
  rw [MonoidHom.mem_ker] at hg ⊢
  refine LinearMap.ext fun f => funext fun i => ?_
  show single (π g) 1 * f i = f i
  rw [hg, ← one_def, one_mul]

/-- The `i`-th coordinate of a cocycle with values in `ι → Λ[Gf]`. -/
def projZ1 (i : ι) : Z1 (piRep Λ π ι) Γ →ₗ[Λ] Z1 (regRep Λ π) Γ :=
  z1Map (piRep Λ π ι) (regRep Λ π) Γ
    (LinearMap.proj i : (ι → MonoidAlgebra Λ Gf) →ₗ[Λ] MonoidAlgebra Λ Gf) (fun _ _ => rfl)

theorem projZ1_apply (i : ι) (c : Z1 (piRep Λ π ι) Γ) (g : Γ) :
    (projZ1 π Γ ι i c : Γ → MonoidAlgebra Λ Gf) g = (c : Γ → ι → MonoidAlgebra Λ Gf) g i := rfl

theorem single_regRep [DecidableEq ι] (i : ι) (g : G) (a : MonoidAlgebra Λ Gf) :
    LinearMap.single Λ (fun _ : ι => MonoidAlgebra Λ Gf) i (regRep Λ π g a) =
      piRep Λ π ι g (LinearMap.single Λ (fun _ : ι => MonoidAlgebra Λ Gf) i a) := by
  refine funext fun j => ?_
  rw [piRep_apply, LinearMap.single_apply, LinearMap.single_apply]
  by_cases h : j = i
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

/-- `c ↦ (g ↦ Pi.single i (c g))` on cocycles. -/
def singleZ1 [DecidableEq ι] (i : ι) : Z1 (regRep Λ π) Γ →ₗ[Λ] Z1 (piRep Λ π ι) Γ :=
  z1Map (regRep Λ π) (piRep Λ π ι) Γ (LinearMap.single Λ (fun _ : ι => MonoidAlgebra Λ Gf) i)
    (single_regRep π ι i)

/-- The cocycle `g ↦ (c_i g)_i` assembled from a finite family of cocycles. -/
def assemble [Fintype ι] [DecidableEq ι] (c : ι → Z1 (regRep Λ π) Γ) : Z1 (piRep Λ π ι) Γ :=
  ∑ i, singleZ1 π Γ ι i (c i)

theorem assemble_apply [Fintype ι] [DecidableEq ι] (c : ι → Z1 (regRep Λ π) Γ) (g : Γ) (i : ι) :
    (assemble π Γ ι c : Γ → ι → MonoidAlgebra Λ Gf) g i = (c i : Γ → MonoidAlgebra Λ Gf) g := by
  rw [assemble, Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
  exact (Finset.sum_pi_single i (fun j => (c j : Γ → MonoidAlgebra Λ Gf) g) Finset.univ).trans
    (if_pos (Finset.mem_univ i))

end Pi

section QMap

variable {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)

/-- `(a_m)_m ↦ Σ_m a_m · m`. -/
def qMap [Fintype M] : (M → MonoidAlgebra Λ Gf) →ₗ[Λ] M :=
  ∑ m : M, ((LinearMap.applyₗ m).comp τ.asAlgebraHom.toLinearMap).comp
    (LinearMap.proj m : (M → MonoidAlgebra Λ Gf) →ₗ[Λ] MonoidAlgebra Λ Gf)

theorem qMap_apply [Fintype M] (f : M → MonoidAlgebra Λ Gf) :
    qMap τ f = ∑ m : M, τ.asAlgebraHom (f m) m := by
  rw [qMap, LinearMap.sum_apply]
  rfl

theorem qMap_equiv [Fintype M] (g : G) (f : M → MonoidAlgebra Λ Gf) :
    qMap τ (piRep Λ π M g f) = (τ.comp π) g (qMap τ f) := by
  rw [qMap_apply, qMap_apply, map_sum]
  exact Finset.sum_congr rfl fun m _ => act_single_mul τ (π g) (f m) m

theorem qMap_single [Fintype M] [DecidableEq M] (m : M) : qMap τ (Pi.single m 1) = m := by
  rw [qMap_apply, Fintype.sum_eq_single m fun m' hm' => by
    rw [Pi.single_eq_of_ne hm', map_zero, LinearMap.zero_apply], Pi.single_eq_same, map_one,
    Module.End.one_apply]

/-- `K = ker qMap`, a subrepresentation of `M → Λ[Gf]`. -/
def qKer [Fintype M] : Subrepresentation (piRep Λ π M) :=
  kerRep (piRep Λ π M) (τ.comp π) (qMap τ) (qMap_equiv π τ)

theorem mem_qKer [Fintype M] (f : M → MonoidAlgebra Λ Gf) : f ∈ (qKer π τ).toSubmodule ↔ qMap τ f = 0 :=
  LinearMap.mem_ker

end QMap

section Comb

variable {ι ι' : Type} [Fintype ι]

/-- `(d_i)_i ↦ Σ_i d_i v_i` (left multiplication in each coordinate). -/
def combMap (v : ι → ι' → MonoidAlgebra Λ Gf) :
    (ι → MonoidAlgebra Λ Gf) →ₗ[Λ] (ι' → MonoidAlgebra Λ Gf) :=
  LinearMap.pi fun j => ∑ i, (LinearMap.mulRight Λ (v i j)).comp
    (LinearMap.proj i : (ι → MonoidAlgebra Λ Gf) →ₗ[Λ] MonoidAlgebra Λ Gf)

theorem combMap_apply (v : ι → ι' → MonoidAlgebra Λ Gf) (d : ι → MonoidAlgebra Λ Gf) (j : ι') :
    combMap v d j = ∑ i, d i * v i j := by
  rw [combMap, LinearMap.pi_apply, LinearMap.sum_apply]
  rfl

theorem combMap_equiv (v : ι → ι' → MonoidAlgebra Λ Gf) (g : G) (d : ι → MonoidAlgebra Λ Gf) :
    combMap v (piRep Λ π ι g d) = piRep Λ π ι' g (combMap v d) := by
  refine funext fun j => ?_
  rw [combMap_apply, piRep_apply, combMap_apply, regRep_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [piRep_apply, regRep_apply, mul_assoc]

theorem combMap_single [DecidableEq ι] (v : ι → ι' → MonoidAlgebra Λ Gf) (i₀ : ι) :
    combMap v (Pi.single i₀ 1) = v i₀ := by
  refine funext fun j => ?_
  rw [combMap_apply, Fintype.sum_eq_single i₀ fun i hi => by rw [Pi.single_eq_of_ne hi, zero_mul],
    Pi.single_eq_same, one_mul]

theorem qMap_combMap {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M) [Fintype M]
    (v : ι → M → MonoidAlgebra Λ Gf) (d : ι → MonoidAlgebra Λ Gf) :
    qMap τ (combMap v d) = ∑ i, τ.asAlgebraHom (d i) (qMap τ (v i)) := by
  simp only [qMap_apply, combMap_apply, map_sum, LinearMap.sum_apply, map_mul, Module.End.mul_apply]
  exact Finset.sum_comm

end Comb

section Iso

variable {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)

variable (Λ M) in
/-- `(c_m)_m ↦ Σ_m c_m ⊗ m`. -/
def Theta [Fintype M] : (M → Z1 (regRep Λ π) Γ) →ₗ[Λ] Z1 (regRep Λ π) Γ ⊗[Λ] M :=
  ∑ m : M, (TensorProduct.mk Λ (Z1 (regRep Λ π) Γ) M).flip m ∘ₗ
    (LinearMap.proj m : (M → Z1 (regRep Λ π) Γ) →ₗ[Λ] Z1 (regRep Λ π) Γ)

theorem Theta_apply [Fintype M] (c : M → Z1 (regRep Λ π) Γ) : Theta Λ π Γ M c = ∑ m : M, c m ⊗ₜ m := by
  rw [Theta, LinearMap.sum_apply]
  rfl

theorem Theta_surjective [Fintype M] [DecidableEq M] : Function.Surjective (Theta Λ π Γ M) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul e m =>
    refine ⟨Pi.single m e, ?_⟩
    rw [Theta_apply, Fintype.sum_eq_single m fun m' hm' => by rw [Pi.single_eq_of_ne hm', zero_tmul],
      Pi.single_eq_same]
  | add x y hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨c + d, by rw [map_add, hc, hd]⟩

theorem Phi_mk_Theta [Fintype M] (c : M → Z1 (regRep Λ π) Γ) (g : Γ) :
    (Phi π Γ τ (Representation.Coinvariants.mk _ (Theta Λ π Γ M c)) : Γ → M) g =
      qMap τ (fun m => (c m : Γ → MonoidAlgebra Λ Gf) g) := by
  rw [Theta_apply, map_sum, map_sum, Submodule.coe_sum, Finset.sum_apply, qMap_apply]
  rfl

theorem mk_sum_tmul [Fintype M] (D : Z1 (regRep Λ π) Γ) (f : M → MonoidAlgebra Λ Gf) :
    ∑ m : M, Representation.Coinvariants.mk ((eRep (Λ := Λ) π Γ).tprod τ) (D ⊗ₜ τ.asAlgebraHom (f m) m) =
      Representation.Coinvariants.mk ((eRep (Λ := Λ) π Γ).tprod τ) (D ⊗ₜ qMap τ f) := by
  rw [qMap_apply, tmul_sum, map_sum]

/-- **E2(c), surjectivity**: every cocycle `Γ → M` is `Phi` of a coinvariant class. -/
theorem Phi_surjective [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
    (hall : H2All Λ G Γ l N) (hπ : IsOpen (π.ker : Set G)) : Function.Surjective (Phi π Γ τ) := by
  classical
  haveI := Fintype.ofFinite M
  have := finite_A Λ Gf
  intro z
  obtain ⟨C, hC⟩ := z1Map_surjective_of_all (piRep Λ π M) (τ.comp π) Γ hall (nsmul_eq_zero_of_cast hΛ)
    (isOpen_piRep_ker π M hπ) (qMap τ) (qMap_equiv π τ) (fun m => ⟨Pi.single m 1, qMap_single τ m⟩) z
  refine ⟨Representation.Coinvariants.mk _ (Theta Λ π Γ M fun m => projZ1 π Γ M m C),
    Subtype.ext (funext fun g => ?_)⟩
  rw [Phi_mk_Theta, ← hC]
  rfl

/-- **E2(c), injectivity** of `Phi`. -/
theorem Phi_injective [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
    (hall : H2All Λ G Γ l N) (hπ : IsOpen (π.ker : Set G)) : Function.Injective (Phi π Γ τ) := by
  classical
  haveI := Fintype.ofFinite M
  have := finite_A Λ Gf
  refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
  obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective _ u
  obtain ⟨c, rfl⟩ := Theta_surjective π Γ x
  have hCK : ∀ g, (assemble π Γ M c : Γ → M → MonoidAlgebra Λ Gf) g ∈ (qKer π τ).toSubmodule := fun g => by
    rw [mem_qKer]
    have h1 : (Phi π Γ τ (Representation.Coinvariants.mk _ (Theta Λ π Γ M c)) : Γ → M) g = 0 := by
      rw [hu]
      rfl
    rw [Phi_mk_Theta] at h1
    have h2 : (assemble π Γ M c : Γ → M → MonoidAlgebra Λ Gf) g = fun m => (c m : Γ → MonoidAlgebra Λ Gf) g :=
      funext fun m => assemble_apply π Γ M c g m
    rw [h2]
    exact h1
  haveI : Fintype (qKer π τ).toSubmodule := Fintype.ofFinite _
  obtain ⟨D, hD⟩ := lift_of_values (piRep Λ π (qKer π τ).toSubmodule) (piRep Λ π M) Γ hall
    (nsmul_eq_zero_of_cast hΛ) (isOpen_piRep_ker π _ hπ)
    (combMap fun k : (qKer π τ).toSubmodule => (k : M → MonoidAlgebra Λ Gf))
    (combMap_equiv π fun k : (qKer π τ).toSubmodule => (k : M → MonoidAlgebra Λ Gf)) (qKer π τ)
    (fun d => (mem_qKer π τ _).2 (by
      rw [qMap_combMap]
      exact Finset.sum_eq_zero fun k _ => by rw [(mem_qKer π τ _).1 k.2, map_zero]))
    (fun w hw => ⟨Pi.single ⟨w, hw⟩ 1, combMap_single _ _⟩) (assemble π Γ M c) hCK
  have hc : ∀ m, c m = ∑ k : (qKer π τ).toSubmodule,
      eMul π Γ ((k : M → MonoidAlgebra Λ Gf) m) (projZ1 π Γ (qKer π τ).toSubmodule k D) :=
    fun m => Subtype.ext (funext fun g => by
      rw [← assemble_apply π Γ M c g m, ← hD g, combMap_apply, Submodule.coe_sum, Finset.sum_apply]
      rfl)
  rw [Theta_apply]
  simp_rw [hc, sum_tmul, map_sum, mk_eMul_tmul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  have hk := mk_sum_tmul π Γ τ (projZ1 π Γ (qKer π τ).toSubmodule k D) (k : M → MonoidAlgebra Λ Gf)
  rw [(mem_qKer π τ _).1 k.2, tmul_zero, map_zero] at hk
  exact hk

/-- **E2(c) headline**: `(E ⊗_Λ M)_{Gf} ≃ Z¹(Γ; M)` for finite `M` (`E = Z¹(Γ; Λ[Gf])`), given `H² = 0` on `Γ`. -/
def tensorEquiv [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
    (hall : H2All Λ G Γ l N) (hπ : IsOpen (π.ker : Set G)) :
    Representation.Coinvariants ((eRep (Λ := Λ) π Γ).tprod τ) ≃ₗ[Λ] Z1 (τ.comp π) Γ :=
  LinearEquiv.ofBijective (Phi π Γ τ) ⟨Phi_injective π Γ τ hΛ hall hπ, Phi_surjective π Γ τ hΛ hall hπ⟩

theorem tensorEquiv_apply [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
    (hall : H2All Λ G Γ l N) (hπ : IsOpen (π.ker : Set G))
    (u : Representation.Coinvariants ((eRep (Λ := Λ) π Γ).tprod τ)) :
    tensorEquiv π Γ τ hΛ hall hπ u = Phi π Γ τ u := rfl

theorem asAlgebraHom_natural {M' : Type} [AddCommGroup M'] [Module Λ M'] {τ' : Representation Λ Gf M'}
    (f : Representation.IntertwiningMap τ τ') (a : MonoidAlgebra Λ Gf) (m : M) :
    f (τ.asAlgebraHom a m) = τ'.asAlgebraHom a (f m) := by
  induction a using MonoidAlgebra.induction_on with
  | of x =>
    rw [Representation.asAlgebraHom_of, Representation.asAlgebraHom_of]
    exact LinearMap.congr_fun (f.isIntertwining' x) m
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | smul r a ha => simp only [map_smul, LinearMap.smul_apply, ha]

/-- **Naturality** of `Phi` in `M`. -/
theorem Phi_natural {M' : Type} [AddCommGroup M'] [Module Λ M'] {τ' : Representation Λ Gf M'}
    (f : Representation.IntertwiningMap τ τ')
    (u : Representation.Coinvariants ((eRep (Λ := Λ) π Γ).tprod τ)) :
    Phi π Γ τ' (Representation.Coinvariants.map _ _ (f.lTensor (eRep (Λ := Λ) π Γ)) u) =
      z1Map (τ.comp π) (τ'.comp π) Γ f.toLinearMap (fun g m => LinearMap.congr_fun (f.isIntertwining' (π g)) m) (Phi π Γ τ u) := by
  obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c m =>
    refine Subtype.ext (funext fun g => ?_)
    rw [Representation.Coinvariants.map_mk, Representation.IntertwiningMap.lTensor_apply, Phi_mk_tmul,
      z1Map_apply, Phi_mk_tmul]
    exact (asAlgebraHom_natural τ f _ m).symm
  | add x y hx hy => simp only [map_add, hx, hy]

end Iso

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_PerfectCx_Cx =====
section

/-!
# S4-PD (5), E3: the cone complex and its free `Λ[Gf]` model

For a representation `ρ` of `G` with open kernel, `Γ ≤ G` and boundary subgroups `I : S → Subgroup G`, the cone
complex `K(M) : M → Z¹(Γ; M) × (S → M) → Π_s Z¹(Γ ⊓ I s; M)` (`cx0`, `cx1`; `cx1_comp_cx0`), natural in the
coefficients (`cx0_natural`, `cx1_natural`). At `ρ = regRep Λ π` (`A = Λ[Gf]`) the right `Gf`-actions are the
naturality maps of right multiplication, so `d0 = cx0`, `d1 = cx1` are `Gf`-equivariant (`d0_equiv`, `d1_equiv`) and
the terms `A`, `E_Γ × A^S`, `Π_s E_s` are projective once the `E`'s are (`isProj_rho1`, `isProj_rho2`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings

noncomputable section

section Generic

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {N : Type} [AddCommGroup N] [Module k N]
  (ρ : Representation k G M) (σ : Representation k G N) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

/-- The coboundary `m ↦ (g ↦ ρ g m - m)` as a locally constant cocycle on `Γ'`. -/
def cob (hρ : IsOpen (ρ.ker : Set G)) (Γ' : Subgroup G) : M →ₗ[k] Z1 ρ Γ' where
  toFun m := ⟨fun g => ρ g m - m, (mem_Z1 ρ Γ' _).2 ⟨(lcRep_of_isOpen ρ Γ' hρ m).sub (IsLocallyConstant.const m),
    fun g h => by
      simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub]
      abel⟩⟩
  map_add' m m' := Subtype.ext (funext fun g => by
    show ρ g (m + m') - (m + m') = (ρ g m - m) + (ρ g m' - m')
    rw [map_add]
    abel)
  map_smul' r m := Subtype.ext (funext fun g => by
    show ρ g (r • m) - r • m = r • (ρ g m - m)
    rw [map_smul, smul_sub])

theorem cob_apply (hρ : IsOpen (ρ.ker : Set G)) (Γ' : Subgroup G) (m : M) (g : Γ') :
    (cob ρ hρ Γ' m : Γ' → M) g = ρ g m - m := rfl

/-- Restriction of cocycles along `Γ' ≤ Γ`. -/
def res {Γ' : Subgroup G} (h : Γ' ≤ Γ) : Z1 ρ Γ →ₗ[k] Z1 ρ Γ' where
  toFun c := ⟨fun g => (c : Γ → M) ⟨g.1, h g.2⟩, (mem_Z1 ρ Γ' _).2
    ⟨((mem_Z1 ρ Γ _).1 c.2).1.comp_continuous (continuous_subtype_val.subtype_mk _),
      fun g g' => ((mem_Z1 ρ Γ _).1 c.2).2 ⟨g.1, h g.2⟩ ⟨g'.1, h g'.2⟩⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem res_apply {Γ' : Subgroup G} (h : Γ' ≤ Γ) (c : Z1 ρ Γ) (g : Γ') :
    (res ρ Γ h c : Γ' → M) g = (c : Γ → M) ⟨g.1, h g.2⟩ := rfl

variable (hρ : IsOpen (ρ.ker : Set G)) (hσ : IsOpen (σ.ker : Set G))

variable (S) in
/-- `d⁰ m = (dm, (m)_s)`. -/
def cx0 : M →ₗ[k] Z1 ρ Γ × (S → M) := (cob ρ hρ Γ).prod (LinearMap.pi fun _ => LinearMap.id)

/-- `d¹ (c, b) = (c|_{Γ ⊓ I s} - d b_s)_s`. -/
def cx1 : Z1 ρ Γ × (S → M) →ₗ[k] ((s : S) → Z1 ρ (Γ ⊓ I s)) :=
  LinearMap.pi fun s => res ρ Γ inf_le_left ∘ₗ LinearMap.fst k _ _ -
    cob ρ hρ (Γ ⊓ I s) ∘ₗ LinearMap.proj s ∘ₗ LinearMap.snd k _ _

theorem cx0_apply (m : M) : cx0 ρ Γ S hρ m = (cob ρ hρ Γ m, fun _ => m) := rfl

theorem cx1_apply (p : Z1 ρ Γ × (S → M)) (s : S) (g : ↥(Γ ⊓ I s)) :
    (cx1 ρ Γ I hρ p s : ↥(Γ ⊓ I s) → M) g = (p.1 : Γ → M) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ - (ρ g (p.2 s) - p.2 s) := rfl

theorem cx1_comp_cx0 : cx1 ρ Γ I hρ ∘ₗ cx0 ρ Γ S hρ = 0 :=
  LinearMap.ext fun _ => funext fun _ => Subtype.ext (funext fun _ => sub_self _)

variable (q : M →ₗ[k] N) (hq : ∀ (g : G) (m : M), q (ρ g m) = σ g (q m))

/-- The degree-1 term of `K` is functorial in the coefficients. -/
def K1map : Z1 ρ Γ × (S → M) →ₗ[k] Z1 σ Γ × (S → N) :=
  (z1Map ρ σ Γ q hq).prodMap (LinearMap.piMap fun _ => q)

/-- The degree-2 term of `K` is functorial in the coefficients. -/
def K2map : ((s : S) → Z1 ρ (Γ ⊓ I s)) →ₗ[k] ((s : S) → Z1 σ (Γ ⊓ I s)) :=
  LinearMap.piMap fun s => z1Map ρ σ (Γ ⊓ I s) q hq

theorem cx0_natural : cx0 σ Γ S hσ ∘ₗ q = K1map ρ σ Γ q hq ∘ₗ cx0 ρ Γ S hρ :=
  LinearMap.ext fun m => Prod.ext (Subtype.ext (funext fun g => by
    show σ g (q m) - q m = q (ρ g m - m)
    rw [map_sub, hq])) rfl

theorem cx1_natural : cx1 σ Γ I hσ ∘ₗ K1map ρ σ Γ q hq = K2map ρ σ Γ I q hq ∘ₗ cx1 ρ Γ I hρ :=
  LinearMap.ext fun p => funext fun s => Subtype.ext (funext fun g => by
    show q ((p.1 : Γ → M) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩) - (σ g (q (p.2 s)) - q (p.2 s)) =
      q ((p.1 : Γ → M) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ - (ρ g (p.2 s) - p.2 s))
    rw [map_sub, map_sub, hq])

end Generic

section Model

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  (hπ : IsOpen (π.ker : Set G))

variable (Λ S) in
/-- `Gf` on `P¹ = E_Γ × A^S` (right multiplication by `h⁻¹`). -/
def rho1 : Representation Λ Gf (Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) :=
  (eRep π Γ).prod (repPi fun _ : S => rRep Λ Gf)

variable (Λ) in
/-- `Gf` on `P² = Π_s E_s`, `E_s = Z¹(Γ ⊓ I s; A)`. -/
def rho2 : Representation Λ Gf ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :=
  repPi fun s => eRep π (Γ ⊓ I s)

variable (Λ S) in
/-- `d⁰ : P⁰ = A → P¹`. -/
def d0 : MonoidAlgebra Λ Gf →ₗ[Λ] Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf) :=
  cx0 (regRep Λ π) Γ S (isOpen_regRep_ker π hπ)

variable (Λ) in
/-- `d¹ : P¹ → P²`. -/
def d1 : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf) →ₗ[Λ] ((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) :=
  cx1 (regRep Λ π) Γ I (isOpen_regRep_ker π hπ)

theorem d1_comp_d0 : d1 Λ π Γ I hπ ∘ₗ d0 Λ π Γ S hπ = 0 := cx1_comp_cx0 _ _ _ _

theorem d0_equiv : IsEquivariant (rRep Λ Gf) (rho1 Λ π Γ S) (d0 Λ π Γ S hπ) := fun h =>
  (cx0_natural (regRep Λ π) (regRep Λ π) Γ (S := S) (isOpen_regRep_ker π hπ) (isOpen_regRep_ker π hπ)
    (LinearMap.mulRight Λ (single h⁻¹ 1)) (mulRight_regRep π _))

theorem d1_equiv : IsEquivariant (rho1 Λ π Γ S) (rho2 Λ π Γ I) (d1 Λ π Γ I hπ) := fun h =>
  (cx1_natural (regRep Λ π) (regRep Λ π) Γ I (isOpen_regRep_ker π hπ) (isOpen_regRep_ker π hπ)
    (LinearMap.mulRight Λ (single h⁻¹ 1)) (mulRight_regRep π _))

theorem isProj_rho1 [Fintype Gf] (hE : IsProj (eRep (Λ := Λ) π Γ)) :
    IsProj (rho1 Λ π Γ S) :=
  isProj_prod hE (isProj_pi fun _ => isProj_rRep)

theorem isProj_rho2 [Fintype Gf] (hE : ∀ s, IsProj (eRep (Λ := Λ) π (Γ ⊓ I s))) : IsProj (rho2 Λ π Γ I) :=
  isProj_pi hE

end Model

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_PerfectCx_CxH =====
section

/-!
# S4-PD (5), E3: the cohomology of the cone complex

For the cone complex `K(M) : M → Z¹(Γ; M) × M^S → Π_s Z¹(Γ ⊓ I s; M)` (`cx0`, `cx1`):
* `H⁰(K) = 0` when `S` is nonempty (`cx0_injective`, `ker_cx0`);
* `ker d¹ ≃ Z1c` (`kerEquivZ1c`), carrying `im d⁰` onto `B1c` (`map_range_cx0`), hence
  `im d⁰ = B1c` inside `Z1c` (`cx0c`, `range_cx0c`), so `H¹(K) ≃ H1c ρ Γ I` (`h1Equiv`), the compactly supported `H¹` of S4-CurveCoh;
* `H²(K) := coker d¹` (`H2K`), identified with the cone `H²` in E4.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] (ρ : Representation k G M) (Γ : Subgroup G) {S : Type}
  (I : S → Subgroup G) (hρ : IsOpen (ρ.ker : Set G))

/-- `ker d¹ → Z1c`, `(c, b) ↦ (c, b)`. -/
def kerToZ1c : LinearMap.ker (cx1 ρ Γ I hρ) →ₗ[k] Z1c ρ Γ I where
  toFun p := ⟨((p.1.1 : Γ → M), p.1.2), (mem_Z1c ρ Γ I _).2 ⟨p.1.1.2, fun s g hg => by
    have h : ((cx1 ρ Γ I hρ p.1 s : ↥(Γ ⊓ I s) → M)) ⟨g.1, Subgroup.mem_inf.2 ⟨g.2, hg⟩⟩ = 0 := by
      rw [LinearMap.mem_ker.1 p.2]
      rfl
    rw [cx1_apply] at h
    exact sub_eq_zero.1 h⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `Z1c → ker d¹`, `(c, b) ↦ (c, b)`. -/
def z1cToKer : Z1c ρ Γ I →ₗ[k] LinearMap.ker (cx1 ρ Γ I hρ) where
  toFun p := ⟨(⟨p.1.1, ((mem_Z1c ρ Γ I _).1 p.2).1⟩, p.1.2), LinearMap.mem_ker.2 (funext fun s =>
    Subtype.ext (funext fun g => by
      rw [cx1_apply]
      exact sub_eq_zero.2 (((mem_Z1c ρ Γ I _).1 p.2).2 s ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩
        (Subgroup.mem_inf.1 g.2).2)))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `ker d¹ ≃ Z1c`. -/
def kerEquivZ1c : LinearMap.ker (cx1 ρ Γ I hρ) ≃ₗ[k] Z1c ρ Γ I :=
  LinearEquiv.ofLinearMap (kerToZ1c ρ Γ I hρ) (z1cToKer ρ Γ I hρ) (LinearMap.ext fun _ => rfl)
    (LinearMap.ext fun _ => rfl)

theorem kerEquivZ1c_apply (p : LinearMap.ker (cx1 ρ Γ I hρ)) :
    ((kerEquivZ1c ρ Γ I hρ p : Z1c ρ Γ I) : (Γ → M) × (S → M)) = ((p.1.1 : Γ → M), p.1.2) := rfl

/-- `im d⁰` corresponds to the relative coboundaries `B1c`. -/
theorem map_range_cx0 :
    ((LinearMap.range (cx0 ρ Γ S hρ)).comap (LinearMap.ker (cx1 ρ Γ I hρ)).subtype).map
      (kerEquivZ1c ρ Γ I hρ : LinearMap.ker (cx1 ρ Γ I hρ) →ₗ[k] Z1c ρ Γ I) =
      (B1c ρ Γ I).comap (Z1c ρ Γ I).subtype := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext x
  simp only [Submodule.mem_comap, LinearMap.mem_range, Submodule.subtype_apply,
    LinearEquiv.coe_coe, mem_B1c]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨x.2, m, fun g => ?_, fun s => ?_⟩
    · exact (congrArg (fun p : Z1 ρ Γ × (S → M) => (p.1 : Γ → M) g) hm).symm
    · exact (congrArg (fun p : Z1 ρ Γ × (S → M) => p.2 s) hm).symm
  · rintro ⟨-, m, hm, hm'⟩
    exact ⟨m, Prod.ext (Subtype.ext (funext fun g => (hm g).symm)) (funext fun s => (hm' s).symm)⟩

theorem cx0_mem_ker (m : M) : cx0 ρ Γ S hρ m ∈ LinearMap.ker (cx1 ρ Γ I hρ) := by
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, cx1_comp_cx0, LinearMap.zero_apply]

/-- `d⁰` landing in `Z1c ≃ ker d¹`: `m ↦ (dm, (m)_s)`. -/
def cx0c : M →ₗ[k] Z1c ρ Γ I :=
  (kerEquivZ1c ρ Γ I hρ).toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.ker (cx1 ρ Γ I hρ)) (cx0 ρ Γ S hρ) (cx0_mem_ker ρ Γ I hρ)

theorem cx0c_apply (m : M) :
    ((cx0c ρ Γ I hρ m : Z1c ρ Γ I) : (Γ → M) × (S → M)) = (fun g : Γ => ρ g m - m, fun _ => m) := rfl

/-- **Exactness at `H¹`**: the image of `d⁰` in `Z1c ≃ ker d¹` is exactly `B1c`. -/
theorem range_cx0c : LinearMap.range (cx0c ρ Γ I hρ) = (B1c ρ Γ I).comap (Z1c ρ Γ I).subtype := by
  rw [cx0c, LinearMap.range_comp, LinearMap.range_codRestrict]
  exact map_range_cx0 ρ Γ I hρ

/-- **`H¹` of the cone complex is `H¹_c`**: `H¹(K(M)) = ker d¹ / im d⁰ ≃ Z1c / im d⁰ ≃ H1c ρ Γ I`. -/
def h1Equiv : (Z1c ρ Γ I ⧸ LinearMap.range (cx0c ρ Γ I hρ)) ≃ₗ[k] H1c ρ Γ I :=
  Submodule.quotEquivOfEq _ _ (range_cx0c ρ Γ I hρ)

theorem h1Equiv_mk (p : Z1c ρ Γ I) :
    h1Equiv ρ Γ I hρ (Submodule.Quotient.mk p) = H1c.mk ρ Γ I p := rfl

variable (S) in
/-- `H⁰(K(M)) = 0` for nonempty `S`: `d⁰` is injective. -/
theorem cx0_injective [Nonempty S] : Function.Injective (cx0 ρ Γ S hρ) := fun _ _ h =>
  congrArg (fun p : Z1 ρ Γ × (S → M) => p.2 (Classical.arbitrary S)) h

variable (S) in
theorem ker_cx0 [Nonempty S] : LinearMap.ker (cx0 ρ Γ S hρ) = ⊥ :=
  LinearMap.ker_eq_bot.2 (cx0_injective ρ Γ S hρ)

/-- `H²(K(M)) = coker d¹`. -/
abbrev H2K : Type := ((s : S) → Z1 ρ (Γ ⊓ I s)) ⧸ LinearMap.range (cx1 ρ Γ I hρ)

end

end PerfectCx
end RamanujanPetersson

end

-- ===== S4.Def_RP_CupDuality_Cup =====
section

/-!
# S4-CurveDuality O2a: the cup product `H¹_c(M) × H¹(M') → H²(K(L))` in the truncated cone

For an equivariant bilinear `β : M × M' → L`, `ρ'` with open kernel and `H²(Γ, L) = 0` (`H2Van σ Γ ⊤`):
for `(c, m) ∈ Z1c` and `d ∈ Z1` choose `u` with `δu = c ∪ d` (`(c ∪ d)(g, h) = β (c g) (g · d h)`), and put
`cup((c, m), d) := [s ↦ (g ↦ β m_s (d g) - u g)|_{Γ ⊓ I s}] ∈ H2K σ Γ I`. It is independent of `u`, bilinear,
and vanishes on `B1c` and on `B1`: `cupPair : H1c ρ Γ I →ₗ H1 ρ' Γ →ₗ H2K σ Γ I`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace CupDuality

open CurveCoh PerfectCx

noncomputable section

variable {k : Type} [CommRing k] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [Module k M] {M' : Type} [AddCommGroup M'] [Module k M']
  {L : Type} [AddCommGroup L] [Module k L]
  (ρ : Representation k G M) (ρ' : Representation k G M') (σ : Representation k G L)
  (β : M →ₗ[k] M' →ₗ[k] L) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)

/-- The cup product of 1-cochains, `(c ∪ d)(g, h) = β (c g) (g · d h)`. -/
def cupCochain (c : Γ → M) (d : Γ → M') : Γ × Γ → L := fun x => β (c x.1) (ρ' x.1 (d x.2))

/-- Hypotheses for the cup product: `β` equivariant, open kernels, `H²(Γ, L) = 0`. -/
structure CupHyp : Prop where
  equiv : ∀ (g : G) (x : M) (y : M'), β (ρ g x) (ρ' g y) = σ g (β x y)
  open' : IsOpen (ρ'.ker : Set G)
  openL : IsOpen (σ.ker : Set G)
  van : H2Van σ Γ ⊤

/-- `u` is a primitive of `c ∪ d`: `c ∪ d = δu` (locally constant). -/
def IsPrim (c : Γ → M) (d : Γ → M') (u : Γ → L) : Prop :=
  IsLocallyConstant u ∧ ∀ g h : Γ, cupCochain ρ' β Γ c d (g, h) = σ g (u h) - u (g * h) + u g

/-- The boundary cochains `g ↦ β m_s (d g) - u g` on `Γ ⊓ I s`. -/
def cupBd (p : (Γ → M) × (S → M)) (d : Γ → M') (u : Γ → L) (s : S) : ↥(Γ ⊓ I s) → L :=
  fun g => β (p.2 s) (d ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩) - u ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩

variable {ρ ρ' σ β Γ I}

theorem cupCochain_cocycle (H : CupHyp ρ ρ' σ β Γ) {c : Γ → M} {d : Γ → M'} (hc : c ∈ Z1 ρ Γ)
    (hd : d ∈ Z1 ρ' Γ) (g h j : Γ) :
    cupCochain ρ' β Γ c d (g * h, j) + cupCochain ρ' β Γ c d (g, h) =
      σ g (cupCochain ρ' β Γ c d (h, j)) + cupCochain ρ' β Γ c d (g, h * j) := by
  show β (c (g * h)) (ρ' (g * h : Γ) (d j)) + β (c g) (ρ' g (d h)) =
      σ g (β (c h) (ρ' h (d j))) + β (c g) (ρ' g (d (h * j)))
  rw [((mem_Z1 ρ Γ c).1 hc).2 g h, ((mem_Z1 ρ' Γ d).1 hd).2 h j, ← H.equiv]
  simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_add, LinearMap.add_apply]
  abel

theorem cupCochain_lc (H : CupHyp ρ ρ' σ β Γ) {c : Γ → M} {d : Γ → M'} (hc : IsLocallyConstant c)
    (hd : IsLocallyConstant d) : IsLocallyConstant (cupCochain ρ' β Γ c d) :=
  IsLocallyConstant.comp₂ (hc.comp_continuous continuous_fst)
    (lc_act_comp ρ' Γ (lcRep_of_isOpen ρ' Γ H.open') hd) fun x y => β x y

theorem exists_prim (H : CupHyp ρ ρ' σ β Γ) {c : Γ → M} {d : Γ → M'} (hc : c ∈ Z1 ρ Γ)
    (hd : d ∈ Z1 ρ' Γ) : ∃ u, IsPrim ρ' σ β Γ c d u := by
  obtain ⟨b, hb, -, hb'⟩ := H.van (cupCochain ρ' β Γ c d)
    (cupCochain_lc H ((mem_Z1 ρ Γ c).1 hc).1 ((mem_Z1 ρ' Γ d).1 hd).1) (fun _ => Submodule.mem_top)
    (cupCochain_cocycle H hc hd)
  exact ⟨b, hb, hb'⟩

theorem cupBd_mem (H : CupHyp ρ ρ' σ β Γ) {p : (Γ → M) × (S → M)} (hp : p ∈ Z1c ρ Γ I) {d : Γ → M'}
    (hd : d ∈ Z1 ρ' Γ) {u : Γ → L} (hu : IsPrim ρ' σ β Γ p.1 d u) (s : S) :
    cupBd β Γ I p d u s ∈ Z1 σ (Γ ⊓ I s) := by
  have hi : Continuous fun g : ↥(Γ ⊓ I s) => (⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ : Γ) :=
    continuous_subtype_val.subtype_mk _
  refine (mem_Z1 σ (Γ ⊓ I s) _).2 ⟨?_, ?_⟩
  · exact ((((mem_Z1 ρ' Γ d).1 hd).1.comp_continuous hi).comp (β (p.2 s))).sub
      (hu.1.comp_continuous hi)
  rintro ⟨g, hg⟩ ⟨h, hh⟩
  obtain ⟨hgΓ, hgI⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨hhΓ, -⟩ := Subgroup.mem_inf.1 hh
  have e1 : d (⟨g, hgΓ⟩ * ⟨h, hhΓ⟩) = d ⟨g, hgΓ⟩ + ρ' g (d ⟨h, hhΓ⟩) :=
    ((mem_Z1 ρ' Γ d).1 hd).2 _ _
  have e3 : p.1 ⟨g, hgΓ⟩ = ρ g (p.2 s) - p.2 s := ((mem_Z1c ρ Γ I p).1 hp).2 s ⟨g, hgΓ⟩ hgI
  have e4 := H.equiv g (p.2 s) (d ⟨h, hhΓ⟩)
  have e2' : u (⟨g, hgΓ⟩ * ⟨h, hhΓ⟩) =
      σ g (u ⟨h, hhΓ⟩) + u ⟨g, hgΓ⟩ - β (p.1 ⟨g, hgΓ⟩) (ρ' g (d ⟨h, hhΓ⟩)) := by
    have e2 : β (p.1 ⟨g, hgΓ⟩) (ρ' g (d ⟨h, hhΓ⟩)) =
        σ g (u ⟨h, hhΓ⟩) - u (⟨g, hgΓ⟩ * ⟨h, hhΓ⟩) + u ⟨g, hgΓ⟩ := hu.2 _ _
    rw [e2]; abel
  change β (p.2 s) (d (⟨g, hgΓ⟩ * ⟨h, hhΓ⟩)) - u (⟨g, hgΓ⟩ * ⟨h, hhΓ⟩) =
    (β (p.2 s) (d ⟨g, hgΓ⟩) - u ⟨g, hgΓ⟩) + σ g (β (p.2 s) (d ⟨h, hhΓ⟩) - u ⟨h, hhΓ⟩)
  rw [e1, e2', e3]
  simp only [map_add, map_sub, LinearMap.sub_apply]
  rw [e4]
  abel

/-- The boundary cocycles of the cup product (for a chosen primitive `u`). -/
def cupZ (H : CupHyp ρ ρ' σ β Γ) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) (u : Γ → L)
    (hu : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d u) : (s : S) → Z1 σ (Γ ⊓ I s) :=
  fun s => ⟨cupBd β Γ I p d u s, cupBd_mem H p.2 d.2 hu s⟩

theorem cupZ_apply (H : CupHyp ρ ρ' σ β Γ) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) (u : Γ → L)
    (hu : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d u) (s : S) (g : ↥(Γ ⊓ I s)) :
    (cupZ H p d u hu s : ↥(Γ ⊓ I s) → L) g =
      β ((p : (Γ → M) × (S → M)).2 s) ((d : Γ → M') ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩) -
        u ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ := rfl

theorem cupZ_sub_mem (H : CupHyp ρ ρ' σ β Γ) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) {u₁ u₂ : Γ → L}
    (h₁ : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d u₁)
    (h₂ : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d u₂) :
    cupZ H p d u₁ h₁ - cupZ H p d u₂ h₂ ∈ LinearMap.range (cx1 σ Γ I H.openL) := by
  refine ⟨(⟨u₂ - u₁, (mem_Z1 σ Γ _).2 ⟨h₂.1.sub h₁.1, fun g h => ?_⟩⟩, 0), ?_⟩
  · have a := h₁.2 g h
    have b := h₂.2 g h
    have hab : σ g (u₂ h) - u₂ (g * h) + u₂ g - (σ g (u₁ h) - u₁ (g * h) + u₁ g) = 0 := by
      rw [← b, ← a, sub_self]
    simp only [Pi.sub_apply, map_sub]
    rw [← sub_eq_zero, ← neg_eq_zero, ← hab]
    abel
  · funext s
    apply Subtype.ext
    funext g
    rw [cx1_apply]
    simp only [Pi.sub_apply, Submodule.coe_sub, cupZ_apply, Pi.zero_apply, map_zero,
      sub_zero]
    abel

/-- The cup product of cocycles, as a class in `H2K`. -/
def cupH (H : CupHyp ρ ρ' σ β Γ) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) : H2K σ Γ I H.openL :=
  Submodule.Quotient.mk (cupZ H p d _
    (exists_prim H ((mem_Z1c ρ Γ I _).1 p.2).1 d.2).choose_spec)

theorem cupH_eq (H : CupHyp ρ ρ' σ β Γ) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) (u : Γ → L)
    (hu : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d u) :
    cupH H p d = Submodule.Quotient.mk (cupZ H p d u hu) := by
  rw [cupH, Submodule.Quotient.eq]
  exact cupZ_sub_mem H p d _ hu


/-! ## Bilinearity -/

theorem prim_add_left {c₁ c₂ : Γ → M} {d : Γ → M'} {u₁ u₂ : Γ → L} (h₁ : IsPrim ρ' σ β Γ c₁ d u₁)
    (h₂ : IsPrim ρ' σ β Γ c₂ d u₂) : IsPrim ρ' σ β Γ (c₁ + c₂) d (u₁ + u₂) := by
  refine ⟨h₁.1.add h₂.1, fun g h => ?_⟩
  have a : β (c₁ g) (ρ' g (d h)) = σ g (u₁ h) - u₁ (g * h) + u₁ g := h₁.2 g h
  have b : β (c₂ g) (ρ' g (d h)) = σ g (u₂ h) - u₂ (g * h) + u₂ g := h₂.2 g h
  show β (c₁ g + c₂ g) (ρ' g (d h)) = σ g (u₁ h + u₂ h) - (u₁ (g * h) + u₂ (g * h)) + (u₁ g + u₂ g)
  simp only [map_add, LinearMap.add_apply]
  rw [a, b]; abel

theorem prim_smul_left (a : k) {c : Γ → M} {d : Γ → M'} {u : Γ → L} (h : IsPrim ρ' σ β Γ c d u) :
    IsPrim ρ' σ β Γ (a • c) d (a • u) := by
  refine ⟨h.1.comp (a • ·), fun g j => ?_⟩
  have e : β (c g) (ρ' g (d j)) = σ g (u j) - u (g * j) + u g := h.2 g j
  show β (a • c g) (ρ' g (d j)) = σ g (a • u j) - a • u (g * j) + a • u g
  simp only [map_smul, LinearMap.smul_apply]
  rw [e, smul_add, smul_sub]

theorem prim_add_right {c : Γ → M} {d₁ d₂ : Γ → M'} {u₁ u₂ : Γ → L} (h₁ : IsPrim ρ' σ β Γ c d₁ u₁)
    (h₂ : IsPrim ρ' σ β Γ c d₂ u₂) : IsPrim ρ' σ β Γ c (d₁ + d₂) (u₁ + u₂) := by
  refine ⟨h₁.1.add h₂.1, fun g h => ?_⟩
  have a : β (c g) (ρ' g (d₁ h)) = σ g (u₁ h) - u₁ (g * h) + u₁ g := h₁.2 g h
  have b : β (c g) (ρ' g (d₂ h)) = σ g (u₂ h) - u₂ (g * h) + u₂ g := h₂.2 g h
  show β (c g) (ρ' g (d₁ h + d₂ h)) = σ g (u₁ h + u₂ h) - (u₁ (g * h) + u₂ (g * h)) + (u₁ g + u₂ g)
  simp only [map_add]
  rw [a, b]; abel

theorem prim_smul_right (a : k) {c : Γ → M} {d : Γ → M'} {u : Γ → L} (h : IsPrim ρ' σ β Γ c d u) :
    IsPrim ρ' σ β Γ c (a • d) (a • u) := by
  refine ⟨h.1.comp (a • ·), fun g j => ?_⟩
  have e : β (c g) (ρ' g (d j)) = σ g (u j) - u (g * j) + u g := h.2 g j
  show β (c g) (ρ' g (a • d j)) = σ g (a • u j) - a • u (g * j) + a • u g
  simp only [map_smul]
  rw [e, smul_add, smul_sub]

variable (H : CupHyp ρ ρ' σ β Γ)

theorem cupH_add_left (p₁ p₂ : Z1c ρ Γ I) (d : Z1 ρ' Γ) :
    cupH H (p₁ + p₂) d = cupH H p₁ d + cupH H p₂ d := by
  obtain ⟨u₁, h₁⟩ := exists_prim H ((mem_Z1c ρ Γ I _).1 p₁.2).1 d.2
  obtain ⟨u₂, h₂⟩ := exists_prim H ((mem_Z1c ρ Γ I _).1 p₂.2).1 d.2
  rw [cupH_eq H p₁ d u₁ h₁, cupH_eq H p₂ d u₂ h₂, cupH_eq H (p₁ + p₂) d (u₁ + u₂) (prim_add_left h₁ h₂),
    ← Submodule.Quotient.mk_add]
  congr 1
  funext s; apply Subtype.ext; funext g
  simp only [Pi.add_apply, Submodule.coe_add, cupZ_apply, Prod.snd_add, map_add, LinearMap.add_apply]
  abel

theorem cupH_smul_left (a : k) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) :
    cupH H (a • p) d = a • cupH H p d := by
  obtain ⟨u, h⟩ := exists_prim H ((mem_Z1c ρ Γ I _).1 p.2).1 d.2
  rw [cupH_eq H p d u h, cupH_eq H (a • p) d (a • u) (prim_smul_left a h), ← Submodule.Quotient.mk_smul]
  congr 1
  funext s; apply Subtype.ext; funext g
  simp only [Pi.smul_apply, Submodule.coe_smul, cupZ_apply, Prod.smul_snd, Pi.smul_apply, map_smul,
    LinearMap.smul_apply, smul_sub]

theorem cupH_add_right (p : Z1c ρ Γ I) (d₁ d₂ : Z1 ρ' Γ) :
    cupH H p (d₁ + d₂) = cupH H p d₁ + cupH H p d₂ := by
  obtain ⟨u₁, h₁⟩ := exists_prim H ((mem_Z1c ρ Γ I _).1 p.2).1 d₁.2
  obtain ⟨u₂, h₂⟩ := exists_prim H ((mem_Z1c ρ Γ I _).1 p.2).1 d₂.2
  rw [cupH_eq H p d₁ u₁ h₁, cupH_eq H p d₂ u₂ h₂, cupH_eq H p (d₁ + d₂) (u₁ + u₂) (prim_add_right h₁ h₂),
    ← Submodule.Quotient.mk_add]
  congr 1
  funext s; apply Subtype.ext; funext g
  simp only [Pi.add_apply, Submodule.coe_add, cupZ_apply, map_add]
  abel

theorem cupH_smul_right (a : k) (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) :
    cupH H p (a • d) = a • cupH H p d := by
  obtain ⟨u, h⟩ := exists_prim H ((mem_Z1c ρ Γ I _).1 p.2).1 d.2
  rw [cupH_eq H p d u h, cupH_eq H p (a • d) (a • u) (prim_smul_right a h), ← Submodule.Quotient.mk_smul]
  congr 1
  funext s; apply Subtype.ext; funext g
  simp only [Pi.smul_apply, Submodule.coe_smul, cupZ_apply, map_smul, smul_sub]

/-! ## Vanishing on coboundaries -/

theorem cupH_B1c (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) (hp : (p : (Γ → M) × (S → M)) ∈ B1c ρ Γ I) :
    cupH H p d = 0 := by
  obtain ⟨-, m, h1, h2⟩ := (mem_B1c ρ Γ I _).1 hp
  have hu : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d (fun g => β m ((d : Γ → M') g)) := by
    refine ⟨((mem_Z1 ρ' Γ _).1 d.2).1.comp (β m), fun g h => ?_⟩
    have e1 : (d : Γ → M') (g * h) = (d : Γ → M') g + ρ' g ((d : Γ → M') h) := ((mem_Z1 ρ' Γ _).1 d.2).2 g h
    show β ((p : (Γ → M) × (S → M)).1 g) (ρ' g ((d : Γ → M') h)) =
      σ g (β m ((d : Γ → M') h)) - β m ((d : Γ → M') (g * h)) + β m ((d : Γ → M') g)
    rw [h1 g, e1, ← H.equiv]
    simp only [map_add, map_sub, LinearMap.sub_apply]
    abel
  have hz : cupZ H p d _ hu = 0 := by
    funext s; apply Subtype.ext; funext g
    rw [cupZ_apply, h2 s, sub_self]
    rfl
  rw [cupH_eq H p d _ hu, hz, Submodule.Quotient.mk_zero]

theorem cupH_B1 (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) (hd : (d : Γ → M') ∈ B1 ρ' Γ) :
    cupH H p d = 0 := by
  obtain ⟨-, y, hy⟩ := (mem_B1 ρ' Γ _).1 hd
  obtain ⟨hpZ, hpI⟩ := (mem_Z1c ρ Γ I _).1 p.2
  have hc := (mem_Z1 ρ Γ _).1 hpZ
  have hu : IsPrim ρ' σ β Γ (p : (Γ → M) × (S → M)).1 d
      (fun g => -β ((p : (Γ → M) × (S → M)).1 g) (ρ' g y)) := by
    refine ⟨IsLocallyConstant.comp₂ hc.1 (lcRep_of_isOpen ρ' Γ H.open' y) fun x z => -β x z,
      fun g h => ?_⟩
    have e1 := hc.2 g h
    show β ((p : (Γ → M) × (S → M)).1 g) (ρ' g ((d : Γ → M') h)) =
      σ g (-β ((p : (Γ → M) × (S → M)).1 h) (ρ' h y)) -
        -β ((p : (Γ → M) × (S → M)).1 (g * h)) (ρ' (g * h : Γ) y) +
        -β ((p : (Γ → M) × (S → M)).1 g) (ρ' g y)
    rw [hy h, e1, map_neg, ← H.equiv]
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_add, map_sub, LinearMap.add_apply]
    abel
  rw [cupH_eq H p d _ hu, Submodule.Quotient.mk_eq_zero]
  refine ⟨(0, fun s => -β ((p : (Γ → M) × (S → M)).2 s) y), ?_⟩
  funext s; apply Subtype.ext; funext ⟨g, hg⟩
  obtain ⟨hgΓ, hgI⟩ := Subgroup.mem_inf.1 hg
  have e3 : (p : (Γ → M) × (S → M)).1 ⟨g, hgΓ⟩ = ρ g ((p : (Γ → M) × (S → M)).2 s) -
      (p : (Γ → M) × (S → M)).2 s := hpI s ⟨g, hgΓ⟩ hgI
  have e4 := H.equiv g ((p : (Γ → M) × (S → M)).2 s) y
  rw [cx1_apply, cupZ_apply]
  change (0 : Γ → L) ⟨g, hgΓ⟩ - (σ g (-β ((p : (Γ → M) × (S → M)).2 s) y) -
      -β ((p : (Γ → M) × (S → M)).2 s) y) =
    β ((p : (Γ → M) × (S → M)).2 s) ((d : Γ → M') ⟨g, hgΓ⟩) -
      -β ((p : (Γ → M) × (S → M)).1 ⟨g, hgΓ⟩) (ρ' g y)
  rw [hy, e3]
  simp only [Pi.zero_apply, map_neg, map_sub, LinearMap.sub_apply]
  rw [e4]
  abel

/-! ## The cup product on cohomology -/

/-- The cup product on cocycles, bilinear. -/
def cupZZ : Z1c ρ Γ I →ₗ[k] Z1 ρ' Γ →ₗ[k] H2K σ Γ I H.openL :=
  LinearMap.mk₂ k (cupH H) (cupH_add_left H) (cupH_smul_left H) (cupH_add_right H) (cupH_smul_right H)

/-- **The cup product** `H¹_c(Γ, {I_s}; M) × H¹(Γ, M') → H²(K(L))`. -/
def cupPair : H1c ρ Γ I →ₗ[k] H1 ρ' Γ →ₗ[k] H2K σ Γ I H.openL :=
  ((B1c ρ Γ I).comap (Z1c ρ Γ I).subtype).liftQ
    (((B1 ρ' Γ).comap (Z1 ρ' Γ).subtype).liftQ (cupZZ H).flip
      (fun d hd => LinearMap.ext fun p => cupH_B1 H p d hd)).flip
    (fun p hp => Submodule.linearMap_qext _ (LinearMap.ext fun d => cupH_B1c H p d hp))

theorem cupPair_mk (p : Z1c ρ Γ I) (d : Z1 ρ' Γ) :
    cupPair H (H1c.mk ρ Γ I p) (H1.mk ρ' Γ d) = cupH H p d := rfl

end

end CupDuality
end RamanujanPetersson

end

-- ===== S4.Def_RP_HattoriStallings_SES =====
section

/-!
# Hattori–Stallings traces, part A2: averaging, lifts, splittings, additivity, permutation modules

* `avg ρ σ f = ∑_g σ g ∘ f ∘ ρ g⁻¹` is always equivariant; `IsHigman ρ E ↔ avg ρ ρ E = id`.
* `exists_equivariant_lift`: a projective (Higman) representation lifts equivariantly along
  equivariant surjections.
* `exists_equivariant_splitting`: a short exact sequence with projective quotient splits equivariantly.
* `hs_ses`: additivity of the HS trace on short exact sequences (and the sub is projective).
* `isHigman_of_basis`, `isProj_permRep`: permutation modules of free `G`-sets are projective.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson.HattoriStallings

open LinearMap

section Avg

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {Q : Type*} [AddCommGroup Q] [Module R Q]
variable {T : Type*} [AddCommGroup T] [Module R T]
variable {ρ : Representation R G P} {σ : Representation R G Q} {τ : Representation R G T}

/-- Averaging `∑_g σ g ∘ f ∘ ρ g⁻¹` (the Reynolds operator without the division by `|G|`). -/
noncomputable def avg (ρ : Representation R G P) (σ : Representation R G Q) (f : P →ₗ[R] Q) :
    P →ₗ[R] Q :=
  ∑ g : G, σ g ∘ₗ f ∘ₗ ρ g⁻¹

lemma avg_apply (f : P →ₗ[R] Q) (v : P) : avg ρ σ f v = ∑ g : G, σ g (f (ρ g⁻¹ v)) := by
  simp [avg, LinearMap.sum_apply]

lemma isHigman_iff_avg (E : P →ₗ[R] P) : IsHigman ρ E ↔ avg ρ ρ E = LinearMap.id := Iff.rfl

lemma isEquivariant_avg (f : P →ₗ[R] Q) : IsEquivariant ρ σ (avg ρ σ f) := by
  refine isEquivariant_iff.2 fun x v => ?_
  rw [avg_apply, avg_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft x⁻¹) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulLeft]
  rw [rep_apply_apply ρ, rep_apply_apply σ, show x * (x⁻¹ * g) = g by group,
    show (x⁻¹ * g)⁻¹ = g⁻¹ * x by group]

lemma IsEquivariant.comp_avg {π : Q →ₗ[R] T} (hπ : IsEquivariant σ τ π) (f : P →ₗ[R] Q) :
    π ∘ₗ avg ρ σ f = avg ρ τ (π ∘ₗ f) := by
  ext v
  simp [avg_apply, map_sum, hπ.apply]

lemma IsEquivariant.avg_comp {u : P →ₗ[R] Q} (hu : IsEquivariant ρ σ u) (f : P →ₗ[R] P) :
    avg ρ σ (u ∘ₗ f) = u ∘ₗ avg ρ ρ f := by
  ext v
  simp [avg_apply, map_sum, hu.apply]

lemma IsEquivariant.avg_comp_right {i : Q →ₗ[R] P} (hi : IsEquivariant σ ρ i) (f : P →ₗ[R] T) :
    avg σ τ (f ∘ₗ i) = avg ρ τ f ∘ₗ i := by
  ext v
  simp [avg_apply, hi.apply]

/-- Equivariant lifting property of a Higman representation along equivariant surjections. -/
theorem exists_equivariant_lift [Module.Projective R P] {E : P →ₗ[R] P} (hE : IsHigman ρ E)
    {π : Q →ₗ[R] T} (hπ : IsEquivariant σ τ π) (hsurj : Function.Surjective π)
    {u : P →ₗ[R] T} (hu : IsEquivariant ρ τ u) :
    ∃ h : P →ₗ[R] Q, IsEquivariant ρ σ h ∧ π ∘ₗ h = u := by
  obtain ⟨w, hw⟩ := Module.projective_lifting_property π u hsurj
  refine ⟨avg ρ σ (w ∘ₗ E), isEquivariant_avg _, ?_⟩
  have hE' : avg ρ ρ E = LinearMap.id := hE
  rw [hπ.comp_avg, ← LinearMap.comp_assoc, hw, hu.avg_comp, hE', LinearMap.comp_id]

/-- An equivariant retract of a Higman representation is Higman. -/
theorem IsHigman.retract {E : P →ₗ[R] P} (hE : IsHigman ρ E) {i : Q →ₗ[R] P} {r : P →ₗ[R] Q}
    (hi : IsEquivariant σ ρ i) (hr : IsEquivariant ρ σ r) (hri : r ∘ₗ i = LinearMap.id) :
    IsHigman σ (r ∘ₗ E ∘ₗ i) := by
  refine LinearMap.ext fun v => ?_
  have key := hE.apply (i v)
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
  calc ∑ h : G, σ h (r (E (i (σ h⁻¹ v)))) = r (∑ h : G, ρ h (E (ρ h⁻¹ (i v)))) := by
        simp [map_sum, hr.apply, hi.apply]
    _ = v := by rw [key]; exact LinearMap.congr_fun hri v

theorem IsProj.retract (hρ : IsProj ρ) {i : Q →ₗ[R] P} {r : P →ₗ[R] Q}
    (hi : IsEquivariant σ ρ i) (hr : IsEquivariant ρ σ r) (hri : r ∘ₗ i = LinearMap.id) :
    IsProj σ :=
  let ⟨_, hE⟩ := hρ
  ⟨_, hE.retract hi hr hri⟩

end Avg

section SES

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P' : Type*} [AddCommGroup P'] [Module R P'] {P : Type*} [AddCommGroup P] [Module R P]
variable {P'' : Type*} [AddCommGroup P''] [Module R P'']
variable {ρ' : Representation R G P'} {ρ : Representation R G P} {ρ'' : Representation R G P''}

/-- A short exact sequence of representations with projective (Higman) quotient splits equivariantly. -/
theorem exists_equivariant_splitting [Module.Projective R P''] (hρ'' : IsProj ρ'')
    {i : P' →ₗ[R] P} {π : P →ₗ[R] P''} (hi : IsEquivariant ρ' ρ i) (hπ : IsEquivariant ρ ρ'' π)
    (hinj : Function.Injective i) (hsurj : Function.Surjective π)
    (hex : LinearMap.range i = LinearMap.ker π) :
    ∃ (s : P'' →ₗ[R] P) (r : P →ₗ[R] P'), IsEquivariant ρ'' ρ s ∧ IsEquivariant ρ ρ' r ∧
      π ∘ₗ s = LinearMap.id ∧ r ∘ₗ i = LinearMap.id ∧ i ∘ₗ r + s ∘ₗ π = LinearMap.id := by
  obtain ⟨E'', hE''⟩ := hρ''
  obtain ⟨s, hsE, hπs⟩ := exists_equivariant_lift hE'' hπ hsurj (isEquivariant_id (ρ := ρ''))
  have hπs' : ∀ w, π (s w) = w := fun w => LinearMap.congr_fun hπs w
  let k : P →ₗ[R] P := LinearMap.id - s ∘ₗ π
  have hkr : ∀ v, k v ∈ LinearMap.range i := by
    intro v
    rw [hex, LinearMap.mem_ker]
    simp [k, hπs']
  let e := LinearEquiv.ofInjective i hinj
  let r : P →ₗ[R] P' :=
    e.symm.toLinearMap ∘ₗ k.codRestrict (LinearMap.range i) hkr
  have hir : ∀ v, i (r v) = v - s (π v) := by
    intro v
    have h1 := LinearEquiv.ofInjective_apply (f := i) (h := hinj)
      (e.symm (k.codRestrict (LinearMap.range i) hkr v))
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [show r v = e.symm (k.codRestrict (LinearMap.range i) hkr v) from rfl, ← h1]
    simp [k]
  have hπi : ∀ v', π (i v') = 0 := by
    intro v'
    have : i v' ∈ LinearMap.ker π := hex ▸ LinearMap.mem_range_self i v'
    exact this
  refine ⟨s, r, hsE, ?_, hπs, ?_, ?_⟩
  · refine isEquivariant_iff.2 fun x v => hinj ?_
    rw [hir, hi.apply, hir, hπ.apply, hsE.apply, map_sub]
  · refine LinearMap.ext fun v' => hinj ?_
    rw [LinearMap.comp_apply, hir, hπi, map_zero, sub_zero, LinearMap.id_apply]
  · refine LinearMap.ext fun v => ?_
    simp [hir]

/-- Over a local ring a retract of a free finite module is free and finite (so the sub of an exact
sequence of free finite `R`-modules is automatically free). -/
theorem free_finite_of_retract [IsLocalRing R] [Module.Free R P] [Module.Finite R P]
    {i : P' →ₗ[R] P} {r : P →ₗ[R] P'}
    (hri : r ∘ₗ i = LinearMap.id) : Module.Free R P' ∧ Module.Finite R P' := by
  have : Module.Projective R P' := Module.Projective.of_split i r hri
  have : Module.Finite R P' :=
    Module.Finite.of_surjective r (fun v' => ⟨i v', LinearMap.congr_fun hri v'⟩)
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

variable [Module.Free R P'] [Module.Finite R P'] [Module.Free R P] [Module.Finite R P]
  [Module.Free R P''] [Module.Finite R P'']

/-- **Additivity of the Hattori–Stallings trace on short exact sequences.** For an exact sequence
`0 → P' → P → P'' → 0` of representations on free finite modules, with `P` and `P''` projective
over `R[G]`, the sub `P'` is projective and `hs P φ = hs P' φ' + hs P'' φ''` for compatible
equivariant endomorphisms. -/
theorem hs_ses (hρ : IsProj ρ) (hρ'' : IsProj ρ'')
    {i : P' →ₗ[R] P} {π : P →ₗ[R] P''} (hi : IsEquivariant ρ' ρ i) (hπ : IsEquivariant ρ ρ'' π)
    (hinj : Function.Injective i) (hsurj : Function.Surjective π)
    (hex : LinearMap.range i = LinearMap.ker π)
    {φ' : P' →ₗ[R] P'} {φ : P →ₗ[R] P} {φ'' : P'' →ₗ[R] P''}
    (hφ : IsEquivariant ρ ρ φ) (hφ'' : IsEquivariant ρ'' ρ'' φ'')
    (h1 : φ ∘ₗ i = i ∘ₗ φ') (h2 : π ∘ₗ φ = φ'' ∘ₗ π) :
    IsProj ρ' ∧ hs ρ φ = hs ρ' φ' + hs ρ'' φ'' := by
  obtain ⟨s, r, hsE, hr, hπs, hri, hsum⟩ :=
    exists_equivariant_splitting hρ'' hi hπ hinj hsurj hex
  have hρ' : IsProj ρ' := hρ.retract hi hr hri
  refine ⟨hρ', ?_⟩
  have hdec : φ = i ∘ₗ (r ∘ₗ φ) + (s ∘ₗ φ'') ∘ₗ π := by
    have e1 : (s ∘ₗ φ'') ∘ₗ π = s ∘ₗ (π ∘ₗ φ) := by
      rw [h2, LinearMap.comp_assoc]
    rw [e1, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc, ← LinearMap.add_comp, hsum,
      LinearMap.id_comp]
  have hA : hs ρ (i ∘ₗ (r ∘ₗ φ)) = hs ρ' φ' := by
    rw [hs_comp_comm hρ hρ' (r ∘ₗ φ) i (hr.comp hφ) hi, LinearMap.comp_assoc, h1,
      ← LinearMap.comp_assoc, hri, LinearMap.id_comp]
  have hB : hs ρ ((s ∘ₗ φ'') ∘ₗ π) = hs ρ'' φ'' := by
    rw [hs_comp_comm hρ hρ'' π (s ∘ₗ φ'') hπ (hsE.comp hφ''), ← LinearMap.comp_assoc, hπs,
      LinearMap.id_comp]
  conv_lhs => rw [hdec]
  rw [hs_add hρ (hi.comp (hr.comp hφ)) ((hsE.comp hφ'').comp hπ), hA, hB]

end SES

section Perm

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [Fintype G]
variable {P : Type*} [AddCommGroup P] [Module R P] {ρ : Representation R G P}

open Classical in
/-- Higman datum of a module with a basis permuted by `G` with free orbits and a transversal `S`. -/
theorem isHigman_of_basis {ι : Type*} [MulAction G ι] (b : Module.Basis ι R P)
    (hb : ∀ (g : G) (i : ι), ρ g (b i) = b (g • i)) (S : Set ι)
    (hS : ∀ i, ∃! g : G, g⁻¹ • i ∈ S) :
    IsHigman ρ (b.constr R (fun i => if i ∈ S then b i else 0)) := by
  refine b.ext fun i => ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
  simp_rw [hb, Module.Basis.constr_basis]
  obtain ⟨g, hg, huniq⟩ := hS i
  rw [Finset.sum_eq_single g]
  · rw [if_pos hg, hb, smul_inv_smul]
  · intro h _ hne
    rw [if_neg (fun hh => hne (huniq h hh)), map_zero]
  · simp

variable (R G) in
/-- The permutation representation of a finite `G`-set `X` on `X → R`: `(g • f) x = f (g⁻¹ • x)`. -/
noncomputable def permRep (X : Type*) [MulAction G X] : Representation R G (X → R) where
  toFun g := LinearMap.funLeft R R (fun x => g⁻¹ • x)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_smul]

lemma permRep_apply {X : Type*} [MulAction G X] (g : G) (f : X → R) (x : X) :
    permRep R G X g f x = f (g⁻¹ • x) := rfl

lemma permRep_single {X : Type*} [MulAction G X] [DecidableEq X] (g : G) (x : X) (r : R) :
    permRep R G X g (Pi.single x r) = Pi.single (g • x) r := by
  ext y
  simp only [permRep_apply, Pi.single_apply, inv_smul_eq_iff]

/-- **The permutation module of a finite free `G`-set is projective over `R[G]`.** -/
theorem isProj_permRep {X : Type*} [Finite X] [MulAction G X]
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) : IsProj (permRep R G X) := by
  classical
  let rep : X → X := fun x => (Quotient.mk'' x : Quotient (MulAction.orbitRel G X)).out
  have hrep : ∀ x, ∃ g : G, g • x = rep x := fun x =>
    MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.mk_out' x))
  have hrep_smul : ∀ (g : G) (x : X), rep (g • x) = rep x := fun g x =>
    congrArg Quotient.out
      (Quotient.sound' (MulAction.orbitRel_apply.2 (MulAction.mem_orbit x g)) :
        (Quotient.mk'' (g • x) : Quotient (MulAction.orbitRel G X)) = Quotient.mk'' x)
  let S : Set X := {x | rep x = x}
  refine ⟨_, isHigman_of_basis (Pi.basisFun R X) (fun g x => ?_) S fun x => ?_⟩
  · simp [Pi.basisFun_apply, permRep_single]
  · obtain ⟨g, hg⟩ := hrep x
    refine ⟨g⁻¹, ?_, ?_⟩
    · show rep ((g⁻¹)⁻¹ • x) = (g⁻¹)⁻¹ • x
      rw [inv_inv, hrep_smul]
      exact hg.symm
    · intro h hh
      have hh' : rep (h⁻¹ • x) = h⁻¹ • x := hh
      have e2 : h⁻¹ • x = g • x := by rw [← hh', hrep_smul, hg]
      have e3 : (g⁻¹ * h⁻¹) • x = x := by rw [mul_smul, e2, inv_smul_smul]
      have h4 := mul_eq_one_iff_eq_inv.1 (hfree _ _ e3)
      rw [inv_inv] at h4
      exact h4.symm

/-- The regular representation is projective. -/
theorem isProj_permRep_self : IsProj (permRep R G G) :=
  isProj_permRep fun g x hx => by simpa using hx

end Perm

end RamanujanPetersson.HattoriStallings

end

-- ===== S4.Def_RP_PerfectCx_CxIso =====
section

/-!
# S4-PD (5), E3: `P ⊗_{Λ[Gf]} M ≅ K(M)`

For a finite `Gf`-representation `τ` on `M` (pulled back to `G` along `π`), the coinvariants of the free model
`P = [A → E_Γ × A^S → Π_s E_s]` tensored with `M` are identified termwise with the cone complex
`K(M) = [M → Z¹(Γ; M) × M^S → Π_s Z¹(Γ ⊓ I s; M)]` (`coinvA`, `iso1`, `iso2`), and the identifications commute with
the differentials (`iso1_map_d0`, `iso2_map_d1`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RamanujanPetersson
namespace PerfectCx

open CurveCoh MonoidAlgebra HattoriStallings Representation TensorProduct

noncomputable section

variable {Λ : Type} [CommRing Λ] {Gf : Type} [Group Gf] {G : Type} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (π : G →* Gf) (Γ : Subgroup G) {S : Type} (I : S → Subgroup G)
  (hπ : IsOpen (π.ker : Set G))
  {M : Type} [AddCommGroup M] [Module Λ M] (τ : Representation Λ Gf M)

theorem isOpen_comp_ker (hπ : IsOpen (π.ker : Set G)) : IsOpen ((τ.comp π).ker : Set G) := by
  refine Subgroup.isOpen_mono (fun g hg => ?_) hπ
  rw [MonoidHom.mem_ker] at hg ⊢
  show τ (π g) = 1
  rw [hg, map_one]

variable (Λ S) in
/-- `d⁰` as an intertwining map. -/
def d0I : IntertwiningMap (rRep Λ Gf) (rho1 Λ π Γ S) := ⟨d0 Λ π Γ S hπ, d0_equiv π Γ hπ⟩

variable (Λ) in
/-- `d¹` as an intertwining map. -/
def d1I : IntertwiningMap (rho1 Λ π Γ S) (rho2 Λ π Γ I) := ⟨d1 Λ π Γ I hπ, d1_equiv π Γ I hπ⟩

theorem d0I_apply (a : MonoidAlgebra Λ Gf) : d0I Λ π Γ S hπ a = d0 Λ π Γ S hπ a := rfl

theorem d1I_apply (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) : d1I Λ π Γ I hπ p = d1 Λ π Γ I hπ p := rfl

theorem d0I_fst_apply (a : MonoidAlgebra Λ Gf) (g : Γ) :
    ((d0I Λ π Γ S hπ a).1 : Γ → MonoidAlgebra Λ Gf) g = single (π g) 1 * a - a := rfl

theorem d0I_snd_apply (a : MonoidAlgebra Λ Gf) (s : S) : (d0I Λ π Γ S hπ a).2 s = a := rfl

theorem d1I_val_apply (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) (s : S) (g : ↥(Γ ⊓ I s)) :
    ((d1I Λ π Γ I hπ p s : ↥(Γ ⊓ I s) → MonoidAlgebra Λ Gf)) g =
      (p.1 : Γ → MonoidAlgebra Λ Gf) ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ - (single (π g) 1 * p.2 s - p.2 s) := rfl

theorem cx0_fst_apply' {ρ : Representation Λ G M} (hρ : IsOpen (ρ.ker : Set G)) (m : M) (g : Γ) :
    ((cx0 ρ Γ S hρ m).1 : Γ → M) g = ρ g m - m := rfl

theorem cx0_snd_apply' {ρ : Representation Λ G M} (hρ : IsOpen (ρ.ker : Set G)) (m : M) (s : S) :
    (cx0 ρ Γ S hρ m).2 s = m := rfl

/-- `P¹` contains a submodule factor: fix the `AddCommGroup` of `P¹ ⊗ M`. -/
instance instAddCommGroupTensorP1 : AddCommGroup ((Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) ⊗[Λ] M) :=
  TensorProduct.addCommGroup

/-- `P²` is a product of submodules: fix the `AddCommGroup` of `P² ⊗ M`. -/
instance instAddCommGroupTensorP2 : AddCommGroup (((s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) ⊗[Λ] M) :=
  TensorProduct.addCommGroup

variable [Finite Λ] [Finite Gf] [Finite M] {l N : ℕ} (hΛ : ((l ^ N : ℕ) : Λ) = 0)
  (hall : H2All Λ G Γ l N) (hallI : ∀ s, H2All Λ G (Γ ⊓ I s) l N)

variable (S) in
/-- `(P¹ ⊗ M)_{Gf} ≃ Z¹(Γ; M) × M^S`. -/
def iso1 [Fintype S] [DecidableEq S] :
    Coinvariants ((rho1 Λ π Γ S).tprod τ) ≃ₗ[Λ] Z1 (τ.comp π) Γ × (S → M) :=
  coinvProd τ (eRep π Γ) (repPi fun _ : S => rRep Λ Gf) ≪≫ₗ
    (tensorEquiv π Γ τ hΛ hall hπ).prodCongr
      (coinvPi τ (fun _ : S => rRep Λ Gf) ≪≫ₗ LinearEquiv.piCongrRight fun _ => coinvA τ)

/-- `(P² ⊗ M)_{Gf} ≃ Π_s Z¹(Γ ⊓ I s; M)`. -/
def iso2 [Fintype S] [DecidableEq S] :
    Coinvariants ((rho2 Λ π Γ I).tprod τ) ≃ₗ[Λ] ((s : S) → Z1 (τ.comp π) (Γ ⊓ I s)) :=
  coinvPi τ (fun s => eRep (Λ := Λ) π (Γ ⊓ I s)) ≪≫ₗ
    LinearEquiv.piCongrRight fun s => tensorEquiv π (Γ ⊓ I s) τ hΛ (hallI s) hπ

variable (S) in
theorem iso1_mk_tmul [Fintype S] [DecidableEq S] (p : Z1 (regRep Λ π) Γ × (S → MonoidAlgebra Λ Gf)) (m : M) :
    iso1 π Γ S hπ τ hΛ hall (Coinvariants.mk _ (p ⊗ₜ m)) =
      (Phi π Γ τ (Coinvariants.mk _ (p.1 ⊗ₜ m)), fun s => τ.asAlgebraHom (p.2 s) m) := rfl

theorem iso2_mk_tmul [Fintype S] [DecidableEq S] (p : (s : S) → Z1 (regRep Λ π) (Γ ⊓ I s)) (m : M) (s : S) :
    iso2 π Γ I hπ τ hΛ hallI (Coinvariants.mk _ (p ⊗ₜ m)) s = Phi π (Γ ⊓ I s) τ (Coinvariants.mk _ (p s ⊗ₜ m)) := rfl

variable (S) in
/-- The degree-0 square: `iso1 ∘ (d⁰ ⊗ M) = d⁰_K ∘ coinvA`. -/
theorem iso1_map_d0 [Fintype S] [DecidableEq S] (u : Coinvariants ((rRep Λ Gf).tprod τ)) :
    iso1 π Γ S hπ τ hΛ hall (Coinvariants.map _ _ ((d0I Λ π Γ S hπ).rTensor τ) u) =
      cx0 (τ.comp π) Γ S (isOpen_comp_ker π τ hπ) (coinvA τ u) := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a m =>
    simp only [Coinvariants.map_mk, IntertwiningMap.rTensor_apply, iso1_mk_tmul, coinvA_mk_tmul]
    refine Prod.ext (Subtype.ext (funext fun g => ?_)) (funext fun s => ?_)
    · simp only [Phi_mk_tmul, d0I_fst_apply, cx0_fst_apply', map_sub, LinearMap.sub_apply, act_single_mul,
        MonoidHom.comp_apply]
    · simp only [d0I_snd_apply, cx0_snd_apply']
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The degree-1 square: `iso2 ∘ (d¹ ⊗ M) = d¹_K ∘ iso1`. -/
theorem iso2_map_d1 [Fintype S] [DecidableEq S] (u : Coinvariants ((rho1 Λ π Γ S).tprod τ)) :
    iso2 π Γ I hπ τ hΛ hallI (Coinvariants.map _ _ ((d1I Λ π Γ I hπ).rTensor τ) u) =
      cx1 (τ.comp π) Γ I (isOpen_comp_ker π τ hπ) (iso1 π Γ S hπ τ hΛ hall u) := by
  obtain ⟨x, rfl⟩ := Coinvariants.mk_surjective _ u
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul p m =>
    refine funext fun s => Subtype.ext (funext fun g => ?_)
    simp only [Coinvariants.map_mk, IntertwiningMap.rTensor_apply, iso1_mk_tmul, iso2_mk_tmul, Phi_mk_tmul,
      d1I_val_apply, cx1_apply, map_sub, LinearMap.sub_apply, act_single_mul, MonoidHom.comp_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (S) in
theorem iso1_comp_d0 [Fintype S] [DecidableEq S] :
    (iso1 π Γ S hπ τ hΛ hall).toLinearMap ∘ₗ Coinvariants.map _ _ ((d0I Λ π Γ S hπ).rTensor τ) =
      cx0 (τ.comp π) Γ S (isOpen_comp_ker π τ hπ) ∘ₗ (coinvA τ).toLinearMap :=
  LinearMap.ext (iso1_map_d0 π Γ S hπ τ hΛ hall)

theorem iso2_comp_d1 [Fintype S] [DecidableEq S] :
    (iso2 π Γ I hπ τ hΛ hallI).toLinearMap ∘ₗ Coinvariants.map _ _ ((d1I Λ π Γ I hπ).rTensor τ) =
      cx1 (τ.comp π) Γ I (isOpen_comp_ker π τ hπ) ∘ₗ (iso1 π Γ S hπ τ hΛ hall).toLinearMap :=
  LinearMap.ext (iso2_map_d1 π Γ I hπ τ hΛ hall hallI)

end

end PerfectCx
end RamanujanPetersson

end


