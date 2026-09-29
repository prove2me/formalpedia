-- Prove2me | solution 1 for AlgebraicGeometry.AdmissibleAlgebra.exists_forall_sub_tmul_mem_span_pow_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/23e27eca-dcb7-5b3f-860f-abcf5a4741b3

import Mathlib
import Theorems.Thm_AlgebraicGeometry_AdmissibleAlgebra_fixedPoints_isAdicComplete_and_finite_and_finiteType
import Theorems.Thm_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_cocycle_pow_smul_eq_coboundary
import Theorems.Thm_AlgebraicGeometry_AdmissibleAlgebra_forall_pow_smul_mem_range_rTensor_of_flat
import Theorems.Thm_AlgebraicGeometry_AdmissibleAlgebra_exists_smul_eq_sub_of_forall_smul_sub_mem_span_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_sub_tmul_mem_span_pow_of_flat

set_option autoImplicit false

open TensorProduct

namespace W2ALG

namespace NoethWs7

theorem isNoetherianRing_of_isAdicComplete_of_quotient
    (R : Type) [CommRing R] (ϖ : R) (hc : IsAdicComplete (Ideal.span {ϖ}) R)
    (hN : IsNoetherianRing (R ⧸ Ideal.span {ϖ})) : IsNoetherianRing R := by
  classical
  obtain ⟨I, hI⟩ : ∃ I : Ideal R, Ideal.span {ϖ} = I := ⟨_, rfl⟩
  rw [hI] at hc hN
  haveI := hN
  have hpow : ∀ n : ℕ, (I ^ n • ⊤ : Submodule R R) = I ^ n := fun n => by rw [smul_eq_mul, Ideal.mul_top]
  have hImem : ∀ {n : ℕ} {x : R}, x ∈ I ^ n ↔ ∃ t, x = ϖ ^ n * t := fun {n x} => by
    rw [← hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨fun ⟨t, ht⟩ => ⟨t, by rw [← ht, mul_comm]⟩, fun ⟨t, ht⟩ => ⟨t, by rw [ht, mul_comm]⟩⟩
  apply IsNoetherianRing.of_prime
  intro P hP

  set mk := Ideal.Quotient.mk I with hmk
  obtain ⟨S, hS⟩ := (isNoetherianRing_iff_ideal_fg (R ⧸ I)).1 hN (P.map mk)
  have hlift : ∀ s : ↥S, ∃ g : R, g ∈ P ∧ mk g = (s : R ⧸ I) := fun s => by
    have : (s : R ⧸ I) ∈ P.map mk := by rw [← hS]; exact Ideal.subset_span s.2
    obtain ⟨g, hg, hgs⟩ := (Ideal.mem_map_iff_of_surjective mk Ideal.Quotient.mk_surjective).1 this
    exact ⟨g, hg, hgs⟩
  choose g hgP hgmk using hlift
  set G : Ideal R := Ideal.span (Set.range g) with hG
  have hGP : G ≤ P := Ideal.span_le.2 (by rintro _ ⟨s, rfl⟩; exact hgP s)
  have hmapG : G.map mk = P.map mk := by
    rw [hG, Ideal.map_span, ← hS]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩; rw [hgmk]; exact s.2
    · intro hy; exact ⟨g ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, hgmk ⟨y, hy⟩⟩

  have hPGI : P ≤ G ⊔ I := by
    calc P ≤ (P.map mk).comap mk := Ideal.le_comap_map
      _ = (G.map mk).comap mk := by rw [hmapG]
      _ = G ⊔ I := by
        rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

  have hstep0 : ∀ x ∈ P, ∃ (c : ↥S → R) (x' : R), x = (∑ i, c i * g i) + ϖ * x' := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hPGI hx)
    obtain ⟨c, rfl⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hy
    rw [← hI] at hz
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨c, t, by rw [mul_comm]⟩
  by_cases hϖ : ϖ ∈ P
  ·
    have hIP : I ≤ P := by
      rw [← hI, Ideal.span_le]; simpa using hϖ
    have hPeq : P = G ⊔ I := le_antisymm hPGI (sup_le hGP hIP)
    rw [hPeq]
    refine Submodule.FG.sup ⟨Finset.univ.image g, ?_⟩ ⟨{ϖ}, ?_⟩
    · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    · rw [Finset.coe_singleton]; exact hI
  ·
    have hstep : ∀ x : ↥P, ∃ (c : ↥S → R) (x' : ↥P), x.1 = (∑ i, c i * g i) + ϖ * x'.1 := by
      intro x
      obtain ⟨c, x', hx'⟩ := hstep0 x x.2
      have hx'P : x' ∈ P := by
        have hmem : ϖ * x' ∈ P := by
          have : ϖ * x' = x - ∑ i, c i * g i := by rw [hx']; ring
          rw [this]
          exact P.sub_mem x.2 (P.sum_mem fun i _ => P.mul_mem_left _ (hgP i))
        exact ((hP.mem_or_mem hmem).resolve_left hϖ)
      exact ⟨c, ⟨x', hx'P⟩, hx'⟩
    choose cf nx hnx using hstep
    suffices hPG : P ≤ G by
      rw [le_antisymm hPG hGP]
      exact ⟨Finset.univ.image g, by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
    intro p hp

    let sq : ℕ → ↥P := fun k => nx^[k] ⟨p, hp⟩
    have sq_zero : sq 0 = ⟨p, hp⟩ := rfl
    have sq_succ : ∀ k, sq (k + 1) = nx (sq k) := fun k => Function.iterate_succ_apply' nx k _
    let A : ↥S → ℕ → R := fun i k => ∑ j ∈ Finset.range k, ϖ ^ j * cf (sq j) i

    have hinv : ∀ k, p = (∑ i, A i k * g i) + ϖ ^ k * (sq k).1 := by
      intro k
      induction k with
      | zero => simp [A, sq_zero]
      | succ k ih =>
        have h := hnx (sq k)
        have e1 : ∑ i, A i (k + 1) * g i = ∑ i, A i k * g i + ∑ i, ϖ ^ k * cf (sq k) i * g i := by
          simp only [A, Finset.sum_range_succ, add_mul, Finset.sum_add_distrib]
        have e2 : ∑ i, ϖ ^ k * cf (sq k) i * g i = ϖ ^ k * ∑ i, cf (sq k) i * g i := by
          rw [Finset.mul_sum]; simp only [mul_assoc]
        rw [ih, e1, e2, sq_succ, h, pow_succ]
        ring

    have hA : ∀ (i : ↥S) {m n : ℕ}, m ≤ n → A i m ≡ A i n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
      intro i m n hmn
      rw [SModEq.sub_mem, hpow]
      have : A i m - A i n = -(∑ j ∈ Finset.Ico m n, ϖ ^ j * cf (sq j) i) := by
        simp only [A]
        rw [← Finset.sum_range_add_sum_Ico _ hmn]; ring
      rw [this]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
      have hmj : m ≤ j := (Finset.mem_Ico.1 hj).1
      exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hmj (Ideal.pow_mem_pow (hI ▸ Ideal.subset_span rfl) j))

    have hL : ∀ i : ↥S, ∃ L : R, ∀ n, A i n ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] :=
      fun i => hc.toIsPrecomplete.prec' (A i) (hA i)
    choose L hLspec using hL

    have hzero : p - ∑ i, L i * g i = 0 := by
      apply hc.toIsHausdorff.haus'
      intro n
      rw [SModEq.sub_mem, sub_zero, hpow]
      have e : p - ∑ i, L i * g i = ϖ ^ n * (sq n).1 + ∑ i, (A i n - L i) * g i := by
        conv_lhs => rw [hinv n]
        simp only [sub_mul, Finset.sum_sub_distrib]; ring
      rw [e]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hI ▸ Ideal.subset_span rfl) n))
        (Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ ?_)
      have := hLspec i n
      rw [SModEq.sub_mem, hpow] at this
      exact this
    rw [sub_eq_zero] at hzero
    rw [hzero, hG]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

end NoethWs7

theorem isNoetherianRing_and_finite_fixedPoints
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (R : Type) [CommRing R] [Algebra 𝒪 R]
    (hRc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (hRtf : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0)
    (hRft : Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}))
    (G : Type) [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R] :
    IsNoetherianRing ↥(FixedPoints.subalgebra 𝒪 R G) ∧ Module.Finite ↥(FixedPoints.subalgebra 𝒪 R G) R := by
  obtain ⟨hAc, hfin, hAft, -⟩ :=
    AlgebraicGeometry.AdmissibleAlgebra.fixedPoints_isAdicComplete_and_finite_and_finiteType 𝒪 hdvr π hπ hcomplete R hRc hRtf
      hRft G
  refine ⟨?_, hfin⟩
  haveI : IsDiscreteValuationRing 𝒪 := hdvr
  haveI : IsNoetherianRing 𝒪 := inferInstance
  haveI := hAft
  haveI : IsNoetherianRing (↥(FixedPoints.subalgebra 𝒪 R G) ⧸
      Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π}) :=
    Algebra.FiniteType.isNoetherianRing 𝒪 _
  exact NoethWs7.isNoetherianRing_of_isAdicComplete_of_quotient _ _ hAc this

section Bar

variable (A : Type) [CommRing A] (R : Type) [CommRing R] [Algebra A R] (G : Type) [Group G] [MulSemiringAction G R]
  [SMulCommClass G A R]

def d0 : R →ₗ[A] (G → R) where
  toFun z g := g • z - z
  map_add' z z' := funext fun g => by
    show g • (z + z') - (z + z') = (g • z - z) + (g • z' - z')
    rw [smul_add]; abel
  map_smul' a z := funext fun g => by
    show g • (a • z) - a • z = a • (g • z - z)
    rw [smul_sub, smul_comm]

def d1 : (G → R) →ₗ[A] (G × G → R) where
  toFun y gh := gh.1 • y gh.2 - y (gh.1 * gh.2) + y gh.1
  map_add' y y' := funext fun gh => by
    show gh.1 • (y gh.2 + y' gh.2) - (y (gh.1 * gh.2) + y' (gh.1 * gh.2)) + (y gh.1 + y' gh.1) =
      (gh.1 • y gh.2 - y (gh.1 * gh.2) + y gh.1) + (gh.1 • y' gh.2 - y' (gh.1 * gh.2) + y' gh.1)
    rw [smul_add]; abel
  map_smul' a y := funext fun gh => by
    show gh.1 • (a • y gh.2) - a • y (gh.1 * gh.2) + a • y gh.1 = a • (gh.1 • y gh.2 - y (gh.1 * gh.2) + y gh.1)
    rw [smul_add, smul_sub, smul_comm]

theorem d0_apply (z : R) (g : G) : d0 A R G z g = g • z - z := rfl

theorem d1_apply (y : G → R) (gh : G × G) : d1 A R G y gh = gh.1 • y gh.2 - y (gh.1 * gh.2) + y gh.1 := rfl

theorem d1_comp_d0 : (d1 A R G).comp (d0 A R G) = 0 := by
  ext z gh
  rw [LinearMap.comp_apply, d1_apply, d0_apply, d0_apply, d0_apply, LinearMap.zero_apply, Pi.zero_apply, smul_sub, mul_smul]
  abel

theorem exact_linearMap_d0 (hA : ∀ z : R, (∀ g : G, g • z = z) → z ∈ Set.range (algebraMap A R))
    (hA' : ∀ (a : A) (g : G), g • algebraMap A R a = algebraMap A R a) :
    Function.Exact (Algebra.linearMap A R) (d0 A R G) := by
  intro z
  constructor
  · intro hz
    obtain ⟨a, ha⟩ := hA z (fun g => sub_eq_zero.1 (by rw [← d0_apply A R G z g, hz, Pi.zero_apply]))
    exact ⟨a, by rw [Algebra.linearMap_apply, ha]⟩
  · rintro ⟨a, rfl⟩
    funext g
    rw [d0_apply, Pi.zero_apply, Algebra.linearMap_apply, hA', sub_self]

end Bar

section BC

variable (A : Type) [CommRing A] (R : Type) [CommRing R] [Algebra A R] (G : Type) [Group G] [MulSemiringAction G R]
  [SMulCommClass G A R] (A' : Type) [CommRing A'] [Algebra A A']

noncomputable def σ (g : G) : R ⊗[A] A' →ₐ[A] R ⊗[A] A' :=
  Algebra.TensorProduct.map (MulSemiringAction.toAlgHom A R g) (AlgHom.id A A')

theorem σ_tmul (g : G) (r : R) (s : A') : σ A R G A' g (r ⊗ₜ[A] s) = (g • r) ⊗ₜ[A] s := by
  simp [σ, Algebra.TensorProduct.map_tmul]

theorem σ_one (z : R ⊗[A] A') : σ A R G A' 1 z = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul r s => rw [σ_tmul, one_smul]
  | add x y hx hy => rw [map_add, hx, hy]

theorem σ_mul (g h : G) (z : R ⊗[A] A') : σ A R G A' (g * h) z = σ A R G A' g (σ A R G A' h z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r s => rw [σ_tmul, σ_tmul, σ_tmul, mul_smul]
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

@[reducible] noncomputable def act : MulSemiringAction G (R ⊗[A] A') where
  smul g z := σ A R G A' g z
  one_smul z := σ_one A R G A' z
  mul_smul g h z := σ_mul A R G A' g h z
  smul_zero g := map_zero _
  smul_add g x y := map_add _ x y
  smul_one g := map_one _
  smul_mul g x y := map_mul _ x y

variable [Fintype G] [DecidableEq G]

theorem piLeft_tmul {ι : Type} [Fintype ι] [DecidableEq ι] (f : ι → R) (s : A') (i : ι) :
    TensorProduct.piLeft A A' (fun _ : ι => R) (f ⊗ₜ[A] s) i = f i ⊗ₜ[A] s := by
  simp [TensorProduct.piLeft]

theorem piLeft_rTensor_d0 (z : R ⊗[A] A') (g : G) :
    TensorProduct.piLeft A A' (fun _ : G => R) (LinearMap.rTensor A' (d0 A R G) z) g = σ A R G A' g z - z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply, sub_zero]
  | tmul r s => rw [LinearMap.rTensor_tmul, piLeft_tmul, d0_apply, σ_tmul, TensorProduct.sub_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; abel

theorem piLeft_rTensor_d1 (n : (G → R) ⊗[A] A') (gh : G × G) :
    TensorProduct.piLeft A A' (fun _ : G × G => R) (LinearMap.rTensor A' (d1 A R G) n) gh =
      σ A R G A' gh.1 (TensorProduct.piLeft A A' (fun _ : G => R) n gh.2) -
        TensorProduct.piLeft A A' (fun _ : G => R) n (gh.1 * gh.2) + TensorProduct.piLeft A A' (fun _ : G => R) n gh.1 := by
  induction n using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply, sub_zero, add_zero]
  | tmul f s => rw [LinearMap.rTensor_tmul, piLeft_tmul, d1_apply, piLeft_tmul, piLeft_tmul, piLeft_tmul, σ_tmul,
      TensorProduct.add_tmul, TensorProduct.sub_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]; abel

theorem rTensor_linearMap_eq (α : A ⊗[A] A') :
    LinearMap.rTensor A' (Algebra.linearMap A R) α = (1 : R) ⊗ₜ[A] (TensorProduct.lid A A' α) := by
  induction α using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero]
  | tmul a s => rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, TensorProduct.lid_tmul, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  | add x y hx hy => rw [map_add, hx, hy, map_add, TensorProduct.tmul_add]

end BC

theorem main_generic (A : Type) [CommRing A] (R : Type) [CommRing R] [Algebra A R] (G : Type) [Group G] [Finite G]
    [MulSemiringAction G R] [SMulCommClass G A R] [IsNoetherianRing A] [Module.Finite A R]
    (hA : ∀ z : R, (∀ g : G, g • z = z) → z ∈ Set.range (algebraMap A R))
    (hA' : ∀ (a : A) (g : G), g • algebraMap A R a = algebraMap A R a)
    (πA : A) (hnzd : ∀ x : R, algebraMap A R πA * x = 0 → x = 0) :
    ∃ e : ℕ, ∀ (A' : Type) [CommRing A'] [Algebra A A'] [Module.Flat A A']
      (ρ : G → (R ⊗[A] A' →+ R ⊗[A] A'))
      (_hρ : ∀ (g : G) (r : R) (s : A'), ρ g (r ⊗ₜ s) = (g • r) ⊗ₜ s)
      (m : ℕ) (x : R ⊗[A] A'),
      (∀ g : G, ρ g x - x ∈ Ideal.span {(algebraMap A R πA ^ (m + e)) ⊗ₜ[A] (1 : A')}) →
      ∃ w : A', x - (1 : R) ⊗ₜ[A] w ∈ Ideal.span {(algebraMap A R πA ^ m) ⊗ₜ[A] (1 : A')} := by
  classical
  haveI : Fintype G := Fintype.ofFinite G

  obtain ⟨e, he⟩ := AlgebraicGeometry.AdmissibleAlgebra.exists_forall_cocycle_pow_smul_eq_coboundary
    (B := A) (R := R) (G := G) πA
  refine ⟨e, ?_⟩
  intro A' _ _ _ ρ hρ m x hx

  letI := act A R G A'
  have hsmul : ∀ (g : G) (z : R ⊗[A] A'), g • z = σ A R G A' g z := fun g z => rfl
  have hρσ : ∀ (g : G) (z : R ⊗[A] A'), ρ g z = g • z := by
    intro g z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, smul_zero]
    | tmul r s => rw [hρ, hsmul, σ_tmul]
    | add z₁ z₂ h₁ h₂ => rw [map_add, h₁, h₂, smul_add]

  have ht1 : algebraMap A (R ⊗[A] A') πA = (algebraMap A R πA) ⊗ₜ[A] (1 : A') := by
    rw [Algebra.TensorProduct.algebraMap_apply]
  have htk : ∀ k : ℕ, (algebraMap A R πA ^ k) ⊗ₜ[A] (1 : A') = ((algebraMap A R πA) ⊗ₜ[A] (1 : A')) ^ k := by
    intro k; rw [Algebra.TensorProduct.tmul_pow, one_pow]

  have htinv : ∀ g : G, g • ((algebraMap A R πA) ⊗ₜ[A] (1 : A')) = (algebraMap A R πA) ⊗ₜ[A] (1 : A') := by
    intro g
    rw [hsmul, σ_tmul, hA']

  have hinjR : Function.Injective (πA • (LinearMap.id : R →ₗ[A] R)) := by
    intro r r' h
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, LinearMap.id_apply, Algebra.smul_def,
      Algebra.smul_def] at h
    have h2 : algebraMap A R πA * (r - r') = 0 := by rw [mul_sub, h, sub_self]
    exact sub_eq_zero.1 (hnzd _ h2)
  have hinj : Function.Injective (LinearMap.rTensor A' (πA • (LinearMap.id : R →ₗ[A] R))) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hinjR
  have hmulz : ∀ z : R ⊗[A] A', LinearMap.rTensor A' (πA • (LinearMap.id : R →ₗ[A] R)) z =
      (algebraMap A R πA) ⊗ₜ[A] (1 : A') * z := by
    intro z
    rw [LinearMap.rTensor_smul, LinearMap.rTensor_id, LinearMap.smul_apply, LinearMap.id_apply, Algebra.smul_def, ht1]
  have ht0 : ∀ z : R ⊗[A] A', (algebraMap A R πA) ⊗ₜ[A] (1 : A') * z = 0 → z = 0 := by
    intro z hz
    exact hinj (by rw [hmulz, hmulz, mul_zero]; exact hz)

  have hH1 : ∀ y : G → R ⊗[A] A', (∀ g h : G, y (g * h) = g • y h + y g) →
      (∃ (k : ℕ) (z : R ⊗[A] A'), ∀ g : G, ((algebraMap A R πA) ⊗ₜ[A] (1 : A')) ^ k * y g = g • z - z) →
      ∃ z : R ⊗[A] A', ∀ g : G, ((algebraMap A R πA) ⊗ₜ[A] (1 : A')) ^ e * y g = g • z - z := by
    intro y hy ⟨k, z, hz⟩
    let EL := TensorProduct.piLeft A A' (fun _ : G => R)
    let EL2 := TensorProduct.piLeft A A' (fun _ : G × G => R)
    let n : (G → R) ⊗[A] A' := EL.symm y
    have hEn : EL n = y := EL.apply_symm_apply y

    have hn : LinearMap.rTensor A' (d1 A R G) n = 0 := by
      apply EL2.injective
      rw [LinearEquiv.map_zero]
      funext gh
      rw [piLeft_rTensor_d1, Pi.zero_apply, hEn, ← hsmul, hy gh.1 gh.2]
      abel

    have hkn : ∃ k : ℕ, πA ^ k • n ∈ LinearMap.range (LinearMap.rTensor A' (d0 A R G)) := by
      refine ⟨k, LinearMap.mem_range.2 ⟨z, EL.injective ?_⟩⟩
      funext g
      rw [piLeft_rTensor_d0, LinearEquiv.map_smul, Pi.smul_apply, hEn, Algebra.smul_def, map_pow, ht1, hz g, hsmul]

    have hA2 : ∀ n₀ : G → R, d1 A R G n₀ = 0 → (∃ k : ℕ, πA ^ k • n₀ ∈ LinearMap.range (d0 A R G)) →
        πA ^ e • n₀ ∈ LinearMap.range (d0 A R G) := by
      intro n₀ hn₀ ⟨k₀, hk₀⟩
      obtain ⟨z₀, hz₀⟩ := LinearMap.mem_range.1 hk₀
      have hcoc : ∀ g h : G, n₀ (g * h) = g • n₀ h + n₀ g := by
        intro g h
        have := congrFun hn₀ (g, h)
        rw [d1_apply, Pi.zero_apply] at this
        linear_combination (exp := 1) -this
      obtain ⟨z₁, hz₁⟩ := he n₀ hcoc ⟨k₀, z₀, fun g => by
        have := congrFun hz₀ g; rw [d0_apply, Pi.smul_apply] at this; exact this.symm⟩
      exact LinearMap.mem_range.2 ⟨z₁, funext fun g => by rw [d0_apply, Pi.smul_apply, hz₁ g]⟩
    have hA3 := AlgebraicGeometry.AdmissibleAlgebra.forall_pow_smul_mem_range_rTensor_of_flat
      (d0 A R G) (d1 A R G) (d1_comp_d0 A R G) πA e hA2 A' n hn hkn
    obtain ⟨z', hz'⟩ := LinearMap.mem_range.1 hA3
    refine ⟨z', fun g => ?_⟩
    have := congrFun (congrArg EL hz') g
    rw [piLeft_rTensor_d0, LinearEquiv.map_smul, Pi.smul_apply, hEn, Algebra.smul_def, map_pow, ht1] at this
    rw [hsmul]
    exact this.symm

  have hx' : ∀ g : G, g • x - x ∈ Ideal.span {((algebraMap A R πA) ⊗ₜ[A] (1 : A')) ^ (m + e)} := by
    intro g; rw [← hρσ, ← htk]; exact hx g
  obtain ⟨w, hwinv, hw⟩ := AlgebraicGeometry.AdmissibleAlgebra.exists_smul_eq_sub_of_forall_smul_sub_mem_span_pow
    ((algebraMap A R πA) ⊗ₜ[A] (1 : A')) htinv ht0 e hH1 (m + e) (Nat.le_add_left e m) x hx'
  rw [Nat.add_sub_cancel] at hw

  have hex : Function.Exact (LinearMap.rTensor A' (Algebra.linearMap A R)) (LinearMap.rTensor A' (d0 A R G)) :=
    Module.Flat.rTensor_exact A' (exact_linearMap_d0 A R G hA hA')
  have hw0 : LinearMap.rTensor A' (d0 A R G) w = 0 := by
    apply (TensorProduct.piLeft A A' (fun _ : G => R)).injective
    rw [LinearEquiv.map_zero]
    funext g
    rw [piLeft_rTensor_d0, Pi.zero_apply, ← hsmul, hwinv g, sub_self]
  obtain ⟨α, hα⟩ := (hex w).1 hw0
  refine ⟨TensorProduct.lid A A' α, ?_⟩
  rw [← rTensor_linearMap_eq, hα, htk]
  exact hw

end W2ALG

open W2ALG in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (R : Type) [CommRing R] [Algebra 𝒪 R]
    (hRc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (hRtf : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0)
    (hRft : Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}))
    (G : Type) [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R] :
    ∃ e : ℕ, ∀ (A' : Type) [CommRing A'] [Algebra ↥(FixedPoints.subalgebra 𝒪 R G) A']
      [Module.Flat ↥(FixedPoints.subalgebra 𝒪 R G) A']
      (ρ : G → (R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A' →+ R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A'))
      (_hρ : ∀ (g : G) (r : R) (s : A'), ρ g (r ⊗ₜ s) = (g • r) ⊗ₜ s)
      (m : ℕ) (x : R ⊗[↥(FixedPoints.subalgebra 𝒪 R G)] A'),
      (∀ g : G, ρ g x - x ∈ Ideal.span {(algebraMap 𝒪 R π ^ (m + e)) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')}) →
      ∃ w : A', x - (1 : R) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] w ∈
        Ideal.span {(algebraMap 𝒪 R π ^ m) ⊗ₜ[↥(FixedPoints.subalgebra 𝒪 R G)] (1 : A')} := by
  haveI hGA : SMulCommClass G ↥(FixedPoints.subalgebra 𝒪 R G) R :=
    ⟨fun g b r => by show g • ((b : R) * r) = (b : R) * (g • r); rw [smul_mul', b.2 g]⟩
  obtain ⟨hNoeth, hfin⟩ := isNoetherianRing_and_finite_fixedPoints 𝒪 hdvr π hπ hcomplete R hRc hRtf hRft G
  haveI := hNoeth
  haveI := hfin
  exact main_generic ↥(FixedPoints.subalgebra 𝒪 R G) R G (fun z hz => ⟨⟨z, hz⟩, rfl⟩) (fun a g => a.2 g) (algebraMap 𝒪 ↥(FixedPoints.subalgebra 𝒪 R G) π)
    (fun x hx => hRtf x hx)

end S_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_sub_tmul_mem_span_pow_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_exists_forall_sub_tmul_mem_span_pow_of_flat (solution)
