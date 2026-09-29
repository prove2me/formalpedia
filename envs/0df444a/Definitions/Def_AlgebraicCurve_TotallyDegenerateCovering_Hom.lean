-- Prove2me | Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
-- name    : AlgebraicCurve_TotallyDegenerateCovering_Hom
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/9dddb40e-cffc-5bf3-9096-2869dd7f1585
-- title:
--   Finite morphisms of degeneracy data and totally degenerate coverings
-- statement:
--   Two layers of morphisms are introduced. First, [`CerednikDrinfeld.DegeneracyData.FiniteHom D₁ D₂`](../def/AlgebraicCurve_TotallyDegenerateCovering_Hom.html#L35) is a structure whose data are maps $\mu_V\colon V_1\to V_2$, $\mu_E\colon E_1\to E_2$ with $a_2(\mu_E e)=\mu_V(a_1 e)$ and $b_2(\mu_E e)=\mu_V(b_1 e)$, together with local degrees $d\colon E_1\to\mathbb N_{>0}$, $d_V\colon V_1\to\mathbb N_{>0}$ and a global degree $n\in\mathbb N_{>0}$, subject to three conditions carried as fields: the width law $w_2(\mu_E e)=d(e)\,w_1(e)$; harmonicity at both ends, i.e. $\sum_{a_1(e)=v,\ \mu_E(e)=e'} d(e)=d_V(v)$ whenever $a_2(e')=\mu_V(v)$, and likewise with $b$ for $a$; and $\sum_{\mu_V(v)=v'} d_V(v)=n$ for every $v'$. No injectivity is assumed; surjectivity of $\mu_V$ and $\mu_E$, and the fibre law $\sum_{\mu_E(e)=e'}d(e)=n$, are deduced. On the ribbon kernels $Z_i=\ker (a_i)_*\cap\ker (b_i)_*\subseteq\mathbb Z^{E_i}$ the module defines $\mu_*$, $(\mu_*x)(e')=\sum_{\mu_E(e)=e'}x(e)$, and $\mu^*$, $(\mu^*y)(e)=d(e)\,y(\mu_E e)$, shows both preserve the kernels, and proves the symmetry of the width pairing $\langle x,y\rangle=\sum_e w(e)x_ey_e$, the projection formula $\langle\mu_*x,y\rangle_2=\langle x,\mu^*y\rangle_1$ in both slot orders, $\langle\mu^*x,\mu^*y\rangle_1=n\langle x,y\rangle_2$ and $\mu_*\mu^*=n$, along with identity and composite morphisms (degrees and $n$ multiply).
--
--   Second, for an extension $F_j\subseteq F_k$ over $L$, `PlaceOver P Q` says that the valuation subring of $P$ on $F_k$ contracts along $F_j\to F_k$ to that of $Q$; when the two fields coincide this forces $P=Q$. `TotallyDegenerateCovering.Hom 𝒞k 𝒞j` extends a `FiniteHom` between the underlying degeneracy data (edges $=$ annuli, $a,b=\mathrm{src},\mathrm{tgt}$, $w=$ width) by: preservation of the side function, contraction of chart integer rings, the requirement that places lying over send chart and outer-annulus domains into the corresponding domains downstairs, and the ramification law $v_A(Q(\text{param}_{\mu_E e}))=v_A(P(\text{param}_e))^{d(e)}$; consequences include the analogous law for annulus moduli. `DegreeMatches` is the condition $n=[F_k:F_j]$, verified for the identity morphism.
--
--   **Relation to Mathlib.** Mathlib has no notion of degeneracy data, ribbon kernels or semistable coverings; these are the project's own. The linear maps are built from Mathlib's `Matrix.mulVecLin` and `LinearMap.restrict`, the place condition from `ValuationSubring.comap`, and the degree condition compares the structure's `degTotal` with `Module.finrank`.
--
--   **Where it is used.** These morphisms provide the combinatorial functoriality used on the Čerednik–Drinfeld side: a finite map of totally degenerate curves induces push-forward and pull-back on the cycle lattices of the dual graphs, compatible with the width (monodromy) pairings, which is what allows character lattices and component groups of the Jacobians to be compared across coverings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_TotallyDegenerateCovering_Hom.lean

import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

open Finset

variable {E₁ V₁ E₂ V₂ : Type*} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] [DecidableEq E₂] [DecidableEq V₂]

theorem pushforward_apply_eq_sum_filter {E V : Type*} [Fintype E] [DecidableEq V] (f : E → V) (x : E → ℤ) (v : V) :
    CerednikDrinfeld.pushforward f x v = ∑ e ∈ univ.filter (fun e => f e = v), x e := by
  simp [CerednikDrinfeld.pushforward, Matrix.mulVec, dotProduct, degeneracyMatrix, Finset.sum_filter]

theorem pushforward_pushforward {E E' V : Type*} [Fintype E] [Fintype E'] [DecidableEq E'] [DecidableEq V]
    (g : E → E') (f : E' → V) (x : E → ℤ) :
    CerednikDrinfeld.pushforward f (CerednikDrinfeld.pushforward g x) = CerednikDrinfeld.pushforward (f ∘ g) x := by
  ext v
  rw [pushforward_apply_eq_sum_filter, pushforward_apply_eq_sum_filter,
    ← sum_fiberwise_of_maps_to (s := univ.filter (fun e => (f ∘ g) e = v)) (t := univ.filter (fun e' => f e' = v))
      (g := g) (fun e he => by simpa using he)]
  refine sum_congr rfl fun e' he' => ?_
  rw [pushforward_apply_eq_sum_filter, filter_filter]
  have hv := (mem_filter.mp he').2
  refine sum_congr (filter_congr fun e _ => ?_) fun _ _ => rfl
  simp only [Function.comp_apply]
  exact ⟨fun h => ⟨by rw [h]; exact hv, h⟩, fun h => h.2⟩

theorem ribbonGram_comm {E V : Type*} [Fintype E] [DecidableEq V] (D : DegeneracyData E V) (x y : ↥(ribbonKernel D)) :
    ribbonGram D x y = ribbonGram D y x := by
  simp only [ribbonGram_apply, mul_comm (x.1 _) (y.1 _)]

structure DegeneracyData.FiniteHom (D₁ : DegeneracyData E₁ V₁) (D₂ : DegeneracyData E₂ V₂) where

  mapV : V₁ → V₂

  mapE : E₁ → E₂

  a_mapE : ∀ e, D₂.a (mapE e) = mapV (D₁.a e)

  b_mapE : ∀ e, D₂.b (mapE e) = mapV (D₁.b e)

  deg : E₁ → ℕ+

  degV : V₁ → ℕ+

  degTotal : ℕ+

  w_mapE : ∀ e, D₂.w (mapE e) = deg e * D₁.w e

  sum_deg_a : ∀ (v : V₁) (e' : E₂), D₂.a e' = mapV v →
    ∑ e ∈ univ.filter (fun e => D₁.a e = v ∧ mapE e = e'), (deg e : ℕ) = degV v

  sum_deg_b : ∀ (v : V₁) (e' : E₂), D₂.b e' = mapV v →
    ∑ e ∈ univ.filter (fun e => D₁.b e = v ∧ mapE e = e'), (deg e : ℕ) = degV v

  sum_degV : ∀ v' : V₂, ∑ v ∈ univ.filter (fun v => mapV v = v'), (degV v : ℕ) = degTotal

namespace DegeneracyData.FiniteHom

variable {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂} (μ : D₁.FiniteHom D₂)

theorem sum_deg_fibre (e' : E₂) : ∑ e ∈ univ.filter (fun e => μ.mapE e = e'), (μ.deg e : ℕ) = μ.degTotal := by
  rw [← μ.sum_degV (D₂.a e'),
    ← sum_fiberwise_of_maps_to (s := univ.filter (fun e => μ.mapE e = e'))
      (t := univ.filter (fun v => μ.mapV v = D₂.a e')) (g := D₁.a)
      (fun e he => by simp only [mem_filter, mem_univ, true_and] at he ⊢; rw [← μ.a_mapE, he])]
  refine sum_congr rfl fun v hv => ?_
  rw [filter_filter, ← μ.sum_deg_a v e' (mem_filter.mp hv).2.symm]
  exact sum_congr (filter_congr fun _ _ => and_comm) fun _ _ => rfl

theorem mapV_surjective : Function.Surjective μ.mapV := fun v' => by
  by_contra h
  have h0 : ∑ v ∈ univ.filter (fun v => μ.mapV v = v'), (μ.degV v : ℕ) = 0 :=
    sum_eq_zero fun v hv => absurd ⟨v, (mem_filter.mp hv).2⟩ h
  rw [μ.sum_degV] at h0
  exact (μ.degTotal).ne_zero h0

theorem mapE_surjective : Function.Surjective μ.mapE := fun e' => by
  by_contra h
  have h0 : ∑ e ∈ univ.filter (fun e => μ.mapE e = e'), (μ.deg e : ℕ) = 0 :=
    sum_eq_zero fun e he => absurd ⟨e, (mem_filter.mp he).2⟩ h
  rw [μ.sum_deg_fibre] at h0
  exact (μ.degTotal).ne_zero h0

def pullbackFun : (E₂ → ℤ) →ₗ[ℤ] (E₁ → ℤ) :=
  LinearMap.pi fun e => (μ.deg e : ℤ) • LinearMap.proj (μ.mapE e)

@[simp] theorem pullbackFun_apply (y : E₂ → ℤ) (e : E₁) : μ.pullbackFun y e = (μ.deg e : ℤ) * y (μ.mapE e) := rfl

variable [Fintype E₂]

private theorem pushforward_deg_mul {a₁ : E₁ → V₁} {a₂ : E₂ → V₂} (ha : ∀ e, a₂ (μ.mapE e) = μ.mapV (a₁ e))
    (hsum : ∀ (v : V₁) (e' : E₂), a₂ e' = μ.mapV v →
      ∑ e ∈ univ.filter (fun e => a₁ e = v ∧ μ.mapE e = e'), (μ.deg e : ℕ) = μ.degV v)
    (y : E₂ → ℤ) (v : V₁) :
    CerednikDrinfeld.pushforward a₁ (fun e => (μ.deg e : ℤ) * y (μ.mapE e)) v =
      (μ.degV v : ℤ) * CerednikDrinfeld.pushforward a₂ y (μ.mapV v) := by
  rw [pushforward_apply_eq_sum_filter, pushforward_apply_eq_sum_filter, mul_sum,
    ← sum_fiberwise_of_maps_to (s := univ.filter (fun e => a₁ e = v)) (t := univ.filter (fun e' => a₂ e' = μ.mapV v))
      (g := μ.mapE) (fun e he => by simp only [mem_filter, mem_univ, true_and] at he ⊢; rw [ha, he])]
  refine sum_congr rfl fun e' he' => ?_
  rw [filter_filter, ← hsum v e' (mem_filter.mp he').2, Nat.cast_sum, sum_mul]
  exact sum_congr rfl fun e he => by rw [(mem_filter.mp he).2.2]

def pushforward : ↥(ribbonKernel D₁) →ₗ[ℤ] ↥(ribbonKernel D₂) :=
  (CerednikDrinfeld.pushforward μ.mapE).restrict fun x hx => by
    rw [mem_ribbonKernel] at hx ⊢
    have h : ∀ {f₁ : E₁ → V₁} {f₂ : E₂ → V₂}, (∀ e, f₂ (μ.mapE e) = μ.mapV (f₁ e)) →
        CerednikDrinfeld.pushforward f₁ x = 0 →
        CerednikDrinfeld.pushforward f₂ (CerednikDrinfeld.pushforward μ.mapE x) = 0 := fun hf h0 => by
      rw [pushforward_pushforward, show _ ∘ μ.mapE = μ.mapV ∘ _ from funext hf, ← pushforward_pushforward, h0,
        map_zero]
    intro i
    fin_cases i
    · exact h μ.a_mapE (hx 0)
    · exact h μ.b_mapE (hx 1)

@[simp] theorem pushforward_apply (x : ↥(ribbonKernel D₁)) (e' : E₂) :
    (μ.pushforward x : E₂ → ℤ) e' = ∑ e ∈ univ.filter (fun e => μ.mapE e = e'), (x : E₁ → ℤ) e :=
  pushforward_apply_eq_sum_filter _ _ _

def pullback : ↥(ribbonKernel D₂) →ₗ[ℤ] ↥(ribbonKernel D₁) :=
  μ.pullbackFun.restrict fun y hy => by
    rw [mem_ribbonKernel] at hy ⊢
    intro i
    fin_cases i
    · ext v
      change CerednikDrinfeld.pushforward D₁.a (fun e => (μ.deg e : ℤ) * y (μ.mapE e)) v = 0
      rw [μ.pushforward_deg_mul μ.a_mapE μ.sum_deg_a, show CerednikDrinfeld.pushforward D₂.a y = 0 from hy 0,
        Pi.zero_apply, mul_zero]
    · ext v
      change CerednikDrinfeld.pushforward D₁.b (fun e => (μ.deg e : ℤ) * y (μ.mapE e)) v = 0
      rw [μ.pushforward_deg_mul μ.b_mapE μ.sum_deg_b, show CerednikDrinfeld.pushforward D₂.b y = 0 from hy 1,
        Pi.zero_apply, mul_zero]

@[simp] theorem pullback_apply (y : ↥(ribbonKernel D₂)) (e : E₁) :
    (μ.pullback y : E₁ → ℤ) e = (μ.deg e : ℤ) * (y : E₂ → ℤ) (μ.mapE e) := rfl

theorem ribbonGram_pushforward (x : ↥(ribbonKernel D₁)) (y : ↥(ribbonKernel D₂)) :
    ribbonGram D₂ (μ.pushforward x) y = ribbonGram D₁ x (μ.pullback y) := by
  simp only [ribbonGram_apply, pushforward_apply, pullback_apply, sum_mul, mul_sum]
  rw [← sum_fiberwise (s := (univ : Finset E₁)) (g := μ.mapE)]
  refine sum_congr rfl fun e' _ => sum_congr rfl fun e he => ?_
  rw [← (mem_filter.mp he).2, μ.w_mapE, PNat.mul_coe, Nat.cast_mul]
  ring

theorem ribbonGram_pullback_left (y : ↥(ribbonKernel D₂)) (x : ↥(ribbonKernel D₁)) :
    ribbonGram D₁ (μ.pullback y) x = ribbonGram D₂ y (μ.pushforward x) := by
  rw [ribbonGram_comm, ← ribbonGram_pushforward, ribbonGram_comm]

theorem ribbonGram_pullback (x y : ↥(ribbonKernel D₂)) :
    ribbonGram D₁ (μ.pullback x) (μ.pullback y) = (μ.degTotal : ℤ) * ribbonGram D₂ x y := by
  simp only [ribbonGram_apply, pullback_apply, mul_sum]
  rw [← sum_fiberwise (s := (univ : Finset E₁)) (g := μ.mapE)]
  refine sum_congr rfl fun e' _ => ?_
  rw [← μ.sum_deg_fibre e', Nat.cast_sum, sum_mul]
  refine sum_congr rfl fun e he => ?_
  rw [← (mem_filter.mp he).2, μ.w_mapE, PNat.mul_coe, Nat.cast_mul]
  ring

theorem pushforward_pullback (y : ↥(ribbonKernel D₂)) : μ.pushforward (μ.pullback y) = (μ.degTotal : ℤ) • y := by
  apply Subtype.ext
  funext e'
  rw [pushforward_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ← μ.sum_deg_fibre e', Nat.cast_sum, sum_mul]
  exact sum_congr rfl fun e he => by rw [pullback_apply, (mem_filter.mp he).2]

section IdComp

omit [Fintype E₂]

protected def id (D : DegeneracyData E₁ V₁) [DecidableEq E₁] : D.FiniteHom D where
  mapV := id
  mapE := id
  a_mapE _ := rfl
  b_mapE _ := rfl
  deg _ := 1
  degV _ := 1
  degTotal := 1
  w_mapE e := (one_mul _).symm
  sum_deg_a v e' h := by
    rw [sum_eq_single_of_mem e' (mem_filter.mpr ⟨mem_univ _, h, rfl⟩)
      (fun e he hne => absurd (mem_filter.mp he).2.2 hne)]
  sum_deg_b v e' h := by
    rw [sum_eq_single_of_mem e' (mem_filter.mpr ⟨mem_univ _, h, rfl⟩)
      (fun e he hne => absurd (mem_filter.mp he).2.2 hne)]
  sum_degV v' := by
    rw [sum_eq_single_of_mem (s := univ.filter fun v => id v = v') v' (mem_filter.mpr ⟨mem_univ _, rfl⟩)
      (fun v hv hne => absurd (mem_filter.mp hv).2 hne)]

variable {E₃ V₃ : Type*} [Fintype E₂] [Fintype V₂] [DecidableEq E₃] [DecidableEq V₃] {D₃ : DegeneracyData E₃ V₃}

def comp (ν : D₂.FiniteHom D₃) (μ : D₁.FiniteHom D₂) : D₁.FiniteHom D₃ where
  mapV := ν.mapV ∘ μ.mapV
  mapE := ν.mapE ∘ μ.mapE
  a_mapE e := by simp only [Function.comp_apply, ν.a_mapE, μ.a_mapE]
  b_mapE e := by simp only [Function.comp_apply, ν.b_mapE, μ.b_mapE]
  deg e := μ.deg e * ν.deg (μ.mapE e)
  degV v := μ.degV v * ν.degV (μ.mapV v)
  degTotal := μ.degTotal * ν.degTotal
  w_mapE e := by simp only [Function.comp_apply, ν.w_mapE, μ.w_mapE]; rw [mul_assoc, mul_left_comm]
  sum_deg_a v e'' h := by
    rw [← sum_fiberwise_of_maps_to (t := univ.filter (fun e' => D₂.a e' = μ.mapV v ∧ ν.mapE e' = e''))
      (g := μ.mapE) (fun e he => by
        simp only [mem_filter, mem_univ, true_and, Function.comp_apply] at he ⊢
        exact ⟨by rw [μ.a_mapE, he.1], he.2⟩),
      PNat.mul_coe, ← ν.sum_deg_a (μ.mapV v) e'' h, mul_sum]
    refine sum_congr rfl fun e' he' => ?_
    rw [filter_filter, ← μ.sum_deg_a v e' (mem_filter.mp he').2.1, sum_mul]
    refine sum_congr (filter_congr fun e _ => ?_) fun e he => by rw [PNat.mul_coe, (mem_filter.mp he).2.2]
    simp only [Function.comp_apply]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by rw [h.2]; exact (mem_filter.mp he').2.2⟩, h.2⟩⟩
  sum_deg_b v e'' h := by
    rw [← sum_fiberwise_of_maps_to (t := univ.filter (fun e' => D₂.b e' = μ.mapV v ∧ ν.mapE e' = e''))
      (g := μ.mapE) (fun e he => by
        simp only [mem_filter, mem_univ, true_and, Function.comp_apply] at he ⊢
        exact ⟨by rw [μ.b_mapE, he.1], he.2⟩),
      PNat.mul_coe, ← ν.sum_deg_b (μ.mapV v) e'' h, mul_sum]
    refine sum_congr rfl fun e' he' => ?_
    rw [filter_filter, ← μ.sum_deg_b v e' (mem_filter.mp he').2.1, sum_mul]
    refine sum_congr (filter_congr fun e _ => ?_) fun e he => by rw [PNat.mul_coe, (mem_filter.mp he).2.2]
    simp only [Function.comp_apply]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, by rw [h.2]; exact (mem_filter.mp he').2.2⟩, h.2⟩⟩
  sum_degV v'' := by
    rw [← sum_fiberwise_of_maps_to (t := univ.filter (fun v' => ν.mapV v' = v'')) (g := μ.mapV)
      (fun v hv => by simpa using hv), PNat.mul_coe, ← ν.sum_degV v'', mul_sum]
    refine sum_congr rfl fun v' hv' => ?_
    rw [filter_filter, ← μ.sum_degV v', sum_mul]
    refine sum_congr (filter_congr fun v _ => ?_) fun v hv => by rw [PNat.mul_coe, (mem_filter.mp hv).2]
    simp only [Function.comp_apply]
    exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact (mem_filter.mp hv').2, h⟩⟩

@[simp] theorem comp_mapE (ν : D₂.FiniteHom D₃) (μ : D₁.FiniteHom D₂) (e : E₁) :
    (ν.comp μ).mapE e = ν.mapE (μ.mapE e) := rfl
@[simp] theorem comp_deg (ν : D₂.FiniteHom D₃) (μ : D₁.FiniteHom D₂) (e : E₁) :
    (ν.comp μ).deg e = μ.deg e * ν.deg (μ.mapE e) := rfl

end IdComp

end DegeneracyData.FiniteHom

end CerednikDrinfeld

namespace AlgebraicCurve

namespace TotallyDegenerateCovering

open CerednikDrinfeld

variable {L : Type} [Field L] {A : ValuationSubring L} {ϖ : A}
variable {Fj Fk : Type} [Field Fj] [Field Fk] [Algebra L Fj] [Algebra L Fk] [Algebra Fj Fk]

def PlaceOver (P : Place L Fk) (Q : Place L Fj) : Prop :=
  P.toValuationSubring.comap (algebraMap Fj Fk) = Q.toValuationSubring

variable [IsScalarTower L Fj Fk]

structure Hom [IsScalarTower L Fj Fk] (𝒞k : TotallyDegenerateCovering A Fk ϖ) (𝒞j : TotallyDegenerateCovering A Fj ϖ)
    extends DegeneracyData.FiniteHom 𝒞k.toDegeneracyData 𝒞j.toDegeneracyData where

  side_mapV : ∀ v, 𝒞j.side (mapV v) = 𝒞k.side v

  integers_comap : ∀ v, (𝒞k.chart v).integers.comap (algebraMap Fj Fk) = (𝒞j.chart (mapV v)).integers

  dom_chart : ∀ (v : 𝒞k.V) (P : Place L Fk) (Q : Place L Fj), PlaceOver P Q →
    P ∈ (𝒞k.chart v).dom → Q ∈ (𝒞j.chart (mapV v)).dom

  dom_ann : ∀ (e : 𝒞k.E) (P : Place L Fk) (Q : Place L Fj), PlaceOver P Q →
    P ∈ (𝒞k.annOut e).dom → Q ∈ (𝒞j.annOut (mapE e)).dom

  valuation_evalAt_param : ∀ (e : 𝒞k.E) (P : Place L Fk) (Q : Place L Fj), PlaceOver P Q → P ∈ (𝒞k.annOut e).dom →
    A.valuation (Q.evalAt (𝒞j.annOut (mapE e)).param) = A.valuation (P.evalAt (𝒞k.annOut e).param) ^ (deg e : ℕ)

namespace Hom

variable {𝒞k : TotallyDegenerateCovering A Fk ϖ} {𝒞j : TotallyDegenerateCovering A Fj ϖ} (μ : 𝒞k.Hom 𝒞j)

theorem src_mapE (e : 𝒞k.E) : 𝒞j.src (μ.mapE e) = μ.mapV (𝒞k.src e) := μ.a_mapE e
theorem tgt_mapE (e : 𝒞k.E) : 𝒞j.tgt (μ.mapE e) = μ.mapV (𝒞k.tgt e) := μ.b_mapE e

theorem width_mapE (e : 𝒞k.E) : 𝒞j.width (μ.mapE e) = μ.deg e * 𝒞k.width e := μ.w_mapE e

theorem valuation_modulus_mapE (e : 𝒞k.E) :
    A.valuation ((𝒞j.annOut (μ.mapE e)).modulus : L) = A.valuation ((𝒞k.annOut e).modulus : L) ^ (μ.deg e : ℕ) := by
  rw [𝒞j.valuation_modulus, 𝒞k.valuation_modulus, ← pow_mul, μ.width_mapE, PNat.mul_coe, mul_comm]

def DegreeMatches : Prop := (μ.degTotal : ℕ) = Module.finrank Fj Fk

theorem degreeMatches_iff : μ.DegreeMatches ↔ (μ.degTotal : ℕ) = Module.finrank Fj Fk := Iff.rfl

theorem pullback_apply_eq_zero {y : ↥(ribbonKernel 𝒞j.toDegeneracyData)} {e : 𝒞k.E}
    (h : (y : 𝒞j.E → ℤ) (μ.mapE e) = 0) : (μ.pullback y : 𝒞k.E → ℤ) e = 0 := by
  rw [μ.pullback_apply, h, mul_zero]

theorem eq_of_placeOver {F : Type} [Field F] [Algebra L F] {P Q : Place L F} (h : PlaceOver P Q) : P = Q :=
  Place.ext ((SetLike.ext fun _ => Iff.rfl).trans h)

protected def id {F : Type} [Field F] [Algebra L F] (𝒞 : TotallyDegenerateCovering A F ϖ) : 𝒞.Hom 𝒞 where
  toFiniteHom := DegeneracyData.FiniteHom.id 𝒞.toDegeneracyData
  side_mapV _ := rfl
  integers_comap _ := SetLike.ext fun _ => Iff.rfl
  dom_chart _ _ _ h hP := eq_of_placeOver h ▸ hP
  dom_ann _ _ _ h hP := eq_of_placeOver h ▸ hP
  valuation_evalAt_param _ _ _ h _ := by rw [← eq_of_placeOver h]; exact (pow_one _).symm

theorem degreeMatches_id {F : Type} [Field F] [Algebra L F] (𝒞 : TotallyDegenerateCovering A F ϖ) :
    (Hom.id 𝒞).DegreeMatches := (Module.finrank_self F).symm

end Hom

end TotallyDegenerateCovering

end AlgebraicCurve

end


