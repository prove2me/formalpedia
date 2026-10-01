-- Prove2me | Definitions.Def_ChapterMackeyQuasiInvariant
-- name    : ChapterMackeyQuasiInvariant
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:22:53.648132+00:00
-- url     : https://prove2.me/theorems/6410670e-cc2e-423f-84d3-0ccde0ecb953
-- title:
--   Chapter MackeyQuasiInvariant
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterMackeyQuasiInvariant.lean`): generated def bundle for ChapterMackeyQuasiInvariant. See BookProof/ChapterMackeyQuasiInvariant.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMackeyQuasiInvariant.lean

import Mathlib


/-!
# Mackey's induced system of imprimitivity over a *continuous* base

`BookProof.ChapterMackeyImprimitivity` and `BookProof.ChapterMackeyGeneralBase` treat a
**discrete** base: the projection-valued measure is a family of projections indexed by the
points of the base, and the induced space is an `ℓ²`-space.  The honest boundary recorded
there is that the *measure-theoretic* base — a `G`-space `X` carrying a **quasi-invariant**
measure `μ`, which is the situation of Mackey's theorem for continuous groups — was not
formalized.  This file removes that boundary for the construction (the "induced" direction):
it builds Mackey's induced representation on `L²(X, μ; K)` for an arbitrary quasi-invariant
measure and an arbitrary measurable unitary cocycle, and proves that, together with
multiplication by indicator functions, it **is** a system of imprimitivity based on `X`.

## The set-up

* `QuasiInvariant μ G` — the action of `G` on `X` is by measurable maps and each translate
  `g_*μ` is absolutely continuous with respect to `μ`.  (The condition is imposed for every
  `g`, hence for `g⁻¹` as well, so all the translates are *equivalent* to `μ`.)
* `dens μ g = d(g_*μ)/dμ` — the Radon–Nikodym cocycle.  `lintegral_dens_mul` is the change
  of variables `∫ (dens μ g) φ dμ = ∫ φ(g • x) dμ`; `dens_one` and `dens_mul` are the
  cocycle identities `dens μ 1 = 1` and `dens μ (gk) x = dens μ g x · dens μ k (g⁻¹ x)`
  (both `μ`-a.e.), proved from the uniqueness of Radon–Nikodym derivatives.
* `UnitaryCocycle μ L` — a measurable cocycle `L : G → X → (K ≃ₗᵢ[ℂ] K)` of unitaries of the
  fibre `K`, i.e. `L 1 x = 1` and `L (gk) x = L g x ∘ L k (g⁻¹ x)`.  The trivial cocycle
  (`unitaryCocycle_one`) is an instance, so nothing here is vacuous.

## Results

* `vmap` — the induced representation
  `(V g f)(x) = √(dens μ g x) · L g x (f (g⁻¹ x))`
  on `L²(X, μ; K)`: additive (`vmap_add`), `ℂ`-linear (`vmap_smul`), **isometric**
  (`vmap_norm`) and a representation of the group (`vmap_one`, `vmap_mul`).  The square root
  of the Radon–Nikodym cocycle is exactly what makes `V g` isometric, and `V g⁻¹` is its
  inverse, so each `V g` is unitary (`inducedRep`).
* `proj E` — multiplication by the indicator of a measurable set `E`, a projection of
  `L²(X, μ; K)`: `proj_idem`, `proj_inter`, `proj_univ`, `proj_empty`, `proj_symm`
  (self-adjointness) and `proj_add_of_disjoint` (additivity).
* **`inducedSystem_covariance`** — the covariance relation `V g P(E) V(g)⁻¹ = P(g · E)`.
* **`mackey_inducedSystem_continuous`** — the headline: the pair `(V, P)` is a system of
  imprimitivity based on the continuous base `X`, for every quasi-invariant measure and
  every measurable unitary cocycle.
* `quasiInvariant_of_invariant`, `dens_eq_one_of_invariant` — an invariant measure is
  quasi-invariant with cocycle `1`, so the construction contains the classical induced
  representation on `L²` of an invariant measure.

Everything is `sorry`-free and uses only the standard axioms.
-/

open MeasureTheory Measure

namespace BookProof.ChapterMackeyQuasiInvariant

variable {G X K : Type*} [Group G] [MeasurableSpace X] [MulAction G X]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-! ## The Radon–Nikodym cocycle of a quasi-invariant measure -/

/-- The action of `g` as a measurable equivalence of `X`. -/
def actEquiv (hm : ∀ g : G, Measurable fun x : X => g • x) (g : G) : X ≃ᵐ X where
  toFun := fun x => g • x
  invFun := fun x => g⁻¹ • x
  left_inv := by intro x; simp [smul_smul]
  right_inv := by intro x; simp [smul_smul]
  measurable_toFun := hm g
  measurable_invFun := hm g⁻¹

/-- A measure `μ` on a `G`-space `X` is *quasi-invariant* when the action is measurable and
every translate of `μ` is absolutely continuous with respect to `μ`.  (Applying the
condition to `g` and to `g⁻¹` shows all the translates are equivalent to `μ`.) -/
structure QuasiInvariant (μ : Measure X) (G : Type*) [Group G] [MulAction G X] : Prop where
  measurable : ∀ g : G, Measurable fun x : X => g • x
  ac : ∀ g : G, (μ.map fun x : X => g • x) ≪ μ

/-- The action of `g` is quasi measure preserving. -/
theorem quasiMeasurePreserving {μ : Measure X} (h : QuasiInvariant μ G) (g : G) :
    Measure.QuasiMeasurePreserving (fun x : X => g • x) μ μ :=
  ⟨h.measurable g, h.ac g⟩

/-- The Radon–Nikodym cocycle `dens μ g = d(g_*μ)/dμ` of a quasi-invariant measure. -/
noncomputable def dens (μ : Measure X) (g : G) : X → ENNReal :=
  (μ.map fun x : X => g • x).rnDeriv μ

theorem measurable_dens (μ : Measure X) (g : G) : Measurable (dens μ g) :=
  Measure.measurable_rnDeriv _ _

/-- **Change of variables.**  `∫ (dens μ g) · φ dμ = ∫ φ(g • ·) dμ`. -/
theorem lintegral_dens_mul (μ : Measure X) [SigmaFinite μ]
    (h : QuasiInvariant μ G) (g : G) {φ : X → ENNReal} (hφ : Measurable φ) :
    ∫⁻ x, dens μ g x * φ x ∂μ = ∫⁻ x, φ (g • x) ∂μ := by
  have hsf : SigmaFinite (μ.map fun x : X => g • x) := (actEquiv h.measurable g).sigmaFinite_map
  calc ∫⁻ x, dens μ g x * φ x ∂μ
      = ∫⁻ x, φ x ∂(μ.withDensity (dens μ g)) := by
        rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_dens μ g) hφ]; rfl
    _ = ∫⁻ x, φ x ∂(μ.map fun x : X => g • x) := by
        rw [dens, Measure.withDensity_rnDeriv_eq _ _ (h.ac g)]
    _ = ∫⁻ x, φ (g • x) ∂μ := lintegral_map hφ (h.measurable g)

/-- Change of variables for an almost-everywhere measurable integrand. -/
theorem lintegral_dens_mul₀ (μ : Measure X) [SigmaFinite μ]
    (h : QuasiInvariant μ G) (g : G) {φ : X → ENNReal} (hφ : AEMeasurable φ μ) :
    ∫⁻ x, dens μ g x * φ x ∂μ = ∫⁻ x, φ (g • x) ∂μ := by
  have h1 : ∫⁻ x, dens μ g x * φ x ∂μ = ∫⁻ x, dens μ g x * hφ.mk φ x ∂μ :=
    lintegral_congr_ae (hφ.ae_eq_mk.mono fun x hx => by dsimp only; rw [hx])
  have h2 : ∫⁻ x, φ (g • x) ∂μ = ∫⁻ x, hφ.mk φ (g • x) ∂μ :=
    lintegral_congr_ae ((quasiMeasurePreserving h g).ae_eq_comp hφ.ae_eq_mk)
  rw [h1, h2, lintegral_dens_mul μ h g hφ.measurable_mk]

theorem dens_one (μ : Measure X) [SigmaFinite μ] :
    dens μ (1 : G) =ᵐ[μ] fun _ => 1 := by
  have hmap : (μ.map fun x : X => (1 : G) • x) = μ := by
    simp only [one_smul]; exact Measure.map_id
  rw [dens, hmap]
  exact Measure.rnDeriv_self μ

/-- **The cocycle identity** `dens μ (gk) x = dens μ g x · dens μ k (g⁻¹ x)`. -/
theorem dens_mul (μ : Measure X) [SigmaFinite μ] (h : QuasiInvariant μ G) (g k : G) :
    dens μ (g * k) =ᵐ[μ] fun x => dens μ g x * dens μ k (g⁻¹ • x) := by
  have hk' : Measurable fun x : X => dens μ k (g⁻¹ • x) :=
    (measurable_dens μ k).comp (h.measurable g⁻¹)
  have hD : Measurable fun x => dens μ g x * dens μ k (g⁻¹ • x) := (measurable_dens μ g).mul hk'
  have hmeasure : (μ.map fun x : X => (g * k) • x)
      = μ.withDensity (fun x => dens μ g x * dens μ k (g⁻¹ • x)) := by
    refine (Measure.ext_of_lintegral _ ?_).symm
    intro φ hφ
    rw [lintegral_withDensity_eq_lintegral_mul _ hD hφ]
    have step1 : ∫⁻ x, ((fun x => dens μ g x * dens μ k (g⁻¹ • x)) * φ) x ∂μ
        = ∫⁻ x, dens μ g x * (fun y => dens μ k (g⁻¹ • y) * φ y) x ∂μ :=
      lintegral_congr fun x => by simp [mul_assoc]
    rw [step1, lintegral_dens_mul μ h g (φ := fun y => dens μ k (g⁻¹ • y) * φ y) (hk'.mul hφ)]
    have step2 : ∫⁻ x, dens μ k (g⁻¹ • g • x) * φ (g • x) ∂μ
        = ∫⁻ x, dens μ k x * (fun y => φ (g • y)) x ∂μ :=
      lintegral_congr fun x => by simp [smul_smul]
    rw [step2, lintegral_dens_mul μ h k (φ := fun y => φ (g • y)) (hφ.comp (h.measurable g)),
      lintegral_map hφ (h.measurable (g * k))]
    exact lintegral_congr fun x => by rw [mul_smul]
  rw [dens, hmeasure]
  exact Measure.rnDeriv_withDensity μ hD

theorem dens_lt_top (μ : Measure X) [SigmaFinite μ] (h : QuasiInvariant μ G) (g : G) :
    ∀ᵐ x ∂μ, dens μ g x < ⊤ := by
  have : SigmaFinite (μ.map fun x : X => g • x) := (actEquiv h.measurable g).sigmaFinite_map
  exact Measure.rnDeriv_lt_top _ _

/-! ## The square root of the cocycle -/

/-- The real square root of the Radon–Nikodym cocycle: the factor that makes the induced
representation isometric. -/
noncomputable def sqrtDens (μ : Measure X) (g : G) (x : X) : ℝ :=
  Real.sqrt (dens μ g x).toReal

theorem sqrtDens_nonneg (μ : Measure X) (g : G) (x : X) : 0 ≤ sqrtDens μ g x :=
  Real.sqrt_nonneg _

theorem measurable_sqrtDens (μ : Measure X) (g : G) : Measurable (sqrtDens μ g) :=
  (Measurable.ennreal_toReal (measurable_dens μ g)).sqrt

theorem ofReal_sqrtDens_sq (μ : Measure X) [SigmaFinite μ] (h : QuasiInvariant μ G) (g : G) :
    ∀ᵐ x ∂μ, ENNReal.ofReal (sqrtDens μ g x ^ 2) = dens μ g x := by
  filter_upwards [dens_lt_top μ h g] with x hx
  rw [sqrtDens, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]

theorem sqrtDens_one (μ : Measure X) [SigmaFinite μ] :
    sqrtDens μ (1 : G) =ᵐ[μ] fun _ => (1 : ℝ) := by
  filter_upwards [dens_one (G := G) μ] with x hx
  simp [sqrtDens, hx]

theorem sqrtDens_mul (μ : Measure X) [SigmaFinite μ] (h : QuasiInvariant μ G) (g k : G) :
    sqrtDens μ (g * k) =ᵐ[μ] fun x => sqrtDens μ g x * sqrtDens μ k (g⁻¹ • x) := by
  have hfin : ∀ᵐ x ∂μ, dens μ k (g⁻¹ • x) < ⊤ :=
    (quasiMeasurePreserving h g⁻¹).ae (dens_lt_top μ h k)
  filter_upwards [dens_mul μ h g k, dens_lt_top μ h g, hfin] with x hx _ _
  rw [sqrtDens, sqrtDens, sqrtDens, hx, ENNReal.toReal_mul,
    Real.sqrt_mul ENNReal.toReal_nonneg]

/-! ## Measurable unitary cocycles -/

/-- A `ℂ`-linear isometry commutes with real scalars. -/
theorem isometry_real_smul (T : K ≃ₗᵢ[ℂ] K) (r : ℝ) (v : K) : T (r • v) = r • T v := by
  simp [← Complex.coe_smul, map_smul]

theorem isometry_enorm_map (T : K ≃ₗᵢ[ℂ] K) (v : K) : ‖T v‖ₑ = ‖v‖ₑ := by
  simp [enorm_eq_nnnorm]

/-- A measurable cocycle of unitaries of the fibre `K`: `L 1 x = 1`,
`L (g k) x = L g x ∘ L k (g⁻¹ x)`, and composition with `L g` preserves almost-everywhere
strong measurability (automatic when `L` is jointly measurable and `K` is separable). -/
structure UnitaryCocycle (μ : Measure X) (L : G → X → (K ≃ₗᵢ[ℂ] K)) : Prop where
  one : ∀ (x : X) (v : K), L 1 x v = v
  mul : ∀ (g k : G) (x : X) (v : K), L (g * k) x v = L g x (L k (g⁻¹ • x) v)
  aesm : ∀ (g : G) (f : X → K), AEStronglyMeasurable f μ →
    AEStronglyMeasurable (fun x => L g x (f x)) μ



/-! ## The induced representation -/

variable (μ : Measure X) (L : G → X → (K ≃ₗᵢ[ℂ] K))

/-- The induced representation, at the level of functions:
`(V g f)(x) = √(dens μ g x) · L g x (f (g⁻¹ x))`. -/
noncomputable def vfun (g : G) (f : X → K) : X → K :=
  fun x => sqrtDens μ g x • L g x (f (g⁻¹ • x))

variable {μ L}

theorem aestronglyMeasurable_vfun [SigmaFinite μ] (h : QuasiInvariant μ G)
    (hL : UnitaryCocycle μ L) (g : G) {f : X → K} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (vfun μ L g f) μ := by
  have h1 : AEStronglyMeasurable (fun x => f (g⁻¹ • x)) μ :=
    hf.comp_quasiMeasurePreserving (quasiMeasurePreserving h g⁻¹)
  have h2 : AEStronglyMeasurable (fun x => L g x (f (g⁻¹ • x))) μ := hL.aesm g _ h1
  exact ((measurable_sqrtDens μ g).aestronglyMeasurable).smul h2

/-- The isometry identity, in the form of an equality of `ℒ²`-integrals. -/
theorem lintegral_enorm_vfun [SigmaFinite μ] (h : QuasiInvariant μ G)
    (g : G) {f : X → K} (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖vfun μ L g f x‖ₑ ^ (2 : ℕ) ∂μ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ := by
  have hφ : AEMeasurable (fun x => ‖f x‖ₑ ^ (2 : ℕ)) μ := hf.enorm.pow_const _
  have hφ' : AEMeasurable (fun x => ‖f (g⁻¹ • x)‖ₑ ^ (2 : ℕ)) μ :=
    hφ.comp_quasiMeasurePreserving (quasiMeasurePreserving h g⁻¹)
  have step1 : ∫⁻ x, ‖vfun μ L g f x‖ₑ ^ (2 : ℕ) ∂μ
      = ∫⁻ x, dens μ g x * ‖f (g⁻¹ • x)‖ₑ ^ (2 : ℕ) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [ofReal_sqrtDens_sq μ h g] with x hx
    rw [vfun, enorm_smul, mul_pow, Real.enorm_of_nonneg (sqrtDens_nonneg μ g x),
      ← ENNReal.ofReal_pow (sqrtDens_nonneg μ g x), hx, isometry_enorm_map]
  rw [step1, lintegral_dens_mul₀ μ h g hφ']
  refine lintegral_congr fun x => ?_
  simp [smul_smul]

theorem memLp_vfun [SigmaFinite μ] (h : QuasiInvariant μ G)
    (hL : UnitaryCocycle μ L) (g : G) {f : X → K} (hf : MemLp f 2 μ) :
    MemLp (vfun μ L g f) 2 μ := by
  refine ⟨aestronglyMeasurable_vfun h hL g hf.1, ?_⟩
  have h2 := hf.2
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h2 ⊢
  have c1 : ∀ (u : X → K), ∫⁻ x, ‖u x‖ₑ ^ (2 : ENNReal).toReal ∂μ
      = ∫⁻ x, ‖u x‖ₑ ^ (2:ℕ) ∂μ := by
    intro u
    refine lintegral_congr fun x => ?_
    rw [show ((2 : ENNReal).toReal) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  rw [c1] at h2 ⊢
  rw [lintegral_enorm_vfun (L := L) h g hf.1]
  exact h2

/-- The induced representation on `L²(X, μ; K)`. -/
noncomputable def vmap [SigmaFinite μ] (h : QuasiInvariant μ G) (hL : UnitaryCocycle μ L)
    (g : G) (f : Lp K 2 μ) : Lp K 2 μ :=
  (memLp_vfun h hL g (Lp.memLp f)).toLp _

theorem vmap_coeFn [SigmaFinite μ] (h : QuasiInvariant μ G) (hL : UnitaryCocycle μ L)
    (g : G) (f : Lp K 2 μ) :
    (vmap h hL g f : X → K) =ᵐ[μ] vfun μ L g (f : X → K) :=
  MemLp.coeFn_toLp _

theorem vmap_add [SigmaFinite μ] (h : QuasiInvariant μ G) (hL : UnitaryCocycle μ L)
    (g : G) (f₁ f₂ : Lp K 2 μ) :
    vmap h hL g (f₁ + f₂) = vmap h hL g f₁ + vmap h hL g f₂ := by
  refine Lp.ext ?_
  have h1 := vmap_coeFn h hL g (f₁ + f₂)
  have h2 := Lp.coeFn_add (vmap h hL g f₁) (vmap h hL g f₂)
  have h3 := vmap_coeFn h hL g f₁
  have h4 := vmap_coeFn h hL g f₂
  have h5 := (quasiMeasurePreserving h g⁻¹).ae_eq_comp (Lp.coeFn_add f₁ f₂)
  filter_upwards [h1, h2, h3, h4, h5] with x a1 a2 a3 a4 a5
  simp only [Function.comp_apply, Pi.add_apply] at a2 a5
  rw [a1, a2, a3, a4]
  simp only [vfun, a5, map_add, smul_add]

theorem vmap_smul [SigmaFinite μ] (h : QuasiInvariant μ G) (hL : UnitaryCocycle μ L)
    (g : G) (c : ℂ) (f : Lp K 2 μ) :
    vmap h hL g (c • f) = c • vmap h hL g f := by
  refine Lp.ext ?_
  have h1 := vmap_coeFn h hL g (c • f)
  have h2 := Lp.coeFn_smul c (vmap h hL g f)
  have h3 := vmap_coeFn h hL g f
  have h5 := (quasiMeasurePreserving h g⁻¹).ae_eq_comp (Lp.coeFn_smul c f)
  filter_upwards [h1, h2, h3, h5] with x a1 a2 a3 a5
  simp only [Function.comp_apply, Pi.smul_apply] at a2 a5
  rw [a1, a2, a3]
  simp only [vfun, a5, map_smul]
  exact smul_comm _ _ _

theorem vmap_norm [SigmaFinite μ] (h : QuasiInvariant μ G) (hL : UnitaryCocycle μ L)
    (g : G) (f : Lp K 2 μ) : ‖vmap h hL g f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  have hco : eLpNorm (vmap h hL g f : X → K) 2 μ = eLpNorm (vfun μ L g (f : X → K)) 2 μ :=
    eLpNorm_congr_ae (vmap_coeFn h hL g f)
  rw [hco, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  have c1 : ∀ (u : X → K), ∫⁻ x, ‖u x‖ₑ ^ (2 : ENNReal).toReal ∂μ
      = ∫⁻ x, ‖u x‖ₑ ^ (2:ℕ) ∂μ := by
    intro u
    refine lintegral_congr fun x => ?_
    rw [show ((2 : ENNReal).toReal) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  rw [c1, c1]
  exact lintegral_enorm_vfun (L := L) h g (Lp.aestronglyMeasurable f)

theorem vmap_one [SigmaFinite μ] (h : QuasiInvariant μ G) (hL : UnitaryCocycle μ L)
    (f : Lp K 2 μ) : vmap h hL (1 : G) f = f := by
  refine Lp.ext ?_
  filter_upwards [vmap_coeFn h hL (1 : G) f, sqrtDens_one (G := G) μ] with x e1 e2
  rw [e1]
  simp only [vfun, e2, one_smul, hL.one x, inv_one, one_smul]

theorem vmap_mul [SigmaFinite μ] (h : QuasiInvariant μ G) (hL : UnitaryCocycle μ L)
    (g k : G) (f : Lp K 2 μ) :
    vmap h hL g (vmap h hL k f) = vmap h hL (g * k) f := by
  refine Lp.ext ?_
  have e1 := vmap_coeFn h hL g (vmap h hL k f)
  have e2 := vmap_coeFn h hL (g * k) f
  have e3 := (quasiMeasurePreserving h g⁻¹).ae_eq_comp (vmap_coeFn h hL k f)
  filter_upwards [e1, e2, e3, sqrtDens_mul μ h g k] with x a1 a2 a3 a4
  simp only [Function.comp_apply] at a3
  rw [a1, a2]
  simp only [vfun]
  rw [a3]
  simp only [vfun, a4, isometry_real_smul, smul_smul, hL.mul g k x,
    show (g * k)⁻¹ • x = k⁻¹ • g⁻¹ • x by rw [mul_inv_rev, mul_smul]]

/-! ## The projection-valued measure -/

/-- Multiplication by the indicator of a measurable set: the projection-valued measure of
the induced system. -/
noncomputable def proj (μ : Measure X) {E : Set X} (hE : MeasurableSet E) (f : Lp K 2 μ) :
    Lp K 2 μ :=
  ((Lp.memLp f).indicator hE).toLp _















/-! ## Covariance -/





/-! ## The headline -/



/-- Each `V g` is a **unitary** of `L²(X, μ; K)`: a surjective linear isometry, with inverse
`V g⁻¹`. -/
noncomputable def inducedRep [SigmaFinite μ] (h : QuasiInvariant μ G)
    (hL : UnitaryCocycle μ L) (g : G) : Lp K 2 μ ≃ₗᵢ[ℂ] Lp K 2 μ where
  toFun := vmap h hL g
  invFun := vmap h hL g⁻¹
  map_add' := vmap_add h hL g
  map_smul' := vmap_smul h hL g
  left_inv := by
    intro f
    rw [vmap_mul h hL g⁻¹ g f, inv_mul_cancel, vmap_one h hL]
  right_inv := by
    intro f
    rw [vmap_mul h hL g g⁻¹ f, mul_inv_cancel, vmap_one h hL]
  norm_map' := vmap_norm h hL g



/-! ## Invariant measures are quasi-invariant -/





end BookProof.ChapterMackeyQuasiInvariant


