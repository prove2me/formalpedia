-- Prove2me | Definitions.Def_Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine
-- name    : Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/f19bdf16-47fe-5156-9650-d086f6e9d2a2
-- title:
--   Fibre ring localised at a prime versus Bq​/pBq​
-- statement:
--   Throughout, $B$ is an algebra over a commutative ring $A$, $\mathfrak p$ is a prime of $A$, $\mathfrak q$ is a prime of $B$ lying over $\mathfrak p$ (the `LiesOver` hypothesis, i.e. $\mathfrak p$ is the contraction of $\mathfrak q$), $Q$ is a prime of the fibre ring $\mathfrak p.\mathrm{Fiber}\,B = \kappa(\mathfrak p)\otimes_A B$, and $B_\mathfrak{q}$ is any ring $Bq$ realised as the localisation of $B$ at $\mathfrak q$. The target ring is always $Bq$ modulo the ideal obtained by pushing $\mathfrak pB$ forward along $B\to Bq$, i.e. $B_\mathfrak{q}/\mathfrak pB_\mathfrak{q}$.
--
--   The comparison map is assembled in three steps. [`kmfloorsGlue_quotLeg`](../def/Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine.html#L83) is the ring homomorphism $A/\mathfrak p\to B_\mathfrak{q}/\mathfrak pB_\mathfrak{q}$ induced by $A\to B\to B_\mathfrak{q}$, legitimate because $\mathfrak p$ dies in the quotient. [`kmfloorsGlue_quotLeg_units`](../def/Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine.html#L100) records that it sends non-zero-divisors of $A/\mathfrak p$ to units (here the lying-over hypothesis is used), so it extends by [`kmfloorsGlue_residueLeg`](../def/Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine.html#L116) to the residue field $\kappa(\mathfrak p)$, the total quotient ring of $A/\mathfrak p$. Together with $B\to B_\mathfrak{q}/\mathfrak pB_\mathfrak{q}$ this yields [`kmfloorsGlue_fiberEval`](../def/Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine.html#L135), a ring homomorphism $\kappa(\mathfrak p)\otimes_A B\to B_\mathfrak{q}/\mathfrak pB_\mathfrak{q}$ with $x\otimes b\mapsto \mathrm{residueLeg}(x)\cdot\overline b$. Under the hypothesis that $Q$ contracts to $\mathfrak q$ along $b\mapsto 1\otimes b$, [`kmfloorsGlue_isLocalization_fiberEval`](../def/Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine.html#L185) asserts that this homomorphism exhibits $B_\mathfrak{q}/\mathfrak pB_\mathfrak{q}$ as a localisation of the fibre ring at the complement of $Q$; [`kmfloorsGlue_fiberLocalizationAtPrimeQuotientEquiv`](../def/Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine.html#L281) converts this into a ring isomorphism $(\kappa(\mathfrak p)\otimes_AB)_Q\cong B_\mathfrak{q}/\mathfrak pB_\mathfrak{q}$, and [`kmfloorsGlue_isRegularLocalRing_localizationQuotient_iff`](../def/Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine.html#L297) transports regularity across it in both directions.
--
--   Supporting lemmas: $\mathfrak p$ maps to $0$ in the fibre, $1\otimes w=0$ for $w\in\mathfrak pB$, elements outside $\mathfrak p$ become units in the fibre, and $b\in\mathfrak q\iff 1\otimes b\in Q$. [`kmfloorsGlue_maximalIdeal_map_eq`](../def/Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine.html#L335) states that for $A_\mathfrak{p}$ and any ring map $A_\mathfrak{p}\to B_\mathfrak{q}$ compatible with the maps from $A$, the image ideal of the maximal ideal of $A_\mathfrak{p}$ is exactly $\mathfrak pB_\mathfrak{q}$. Finally, test cases: for $B=A$ the fibre ring is a domain isomorphic to $\kappa(\mathfrak p)$, its zero ideal contracts to $\mathfrak p$, and the isomorphism specialises to $\kappa(\mathfrak p)\cong A_\mathfrak p/\mathfrak pA_\mathfrak p$, instantiated at $(\mathbb Z,(3))$; a contrasting computation shows that extending $(3)$ to the localisation of $\mathbb Z$ at $(0)$ gives the unit ideal.
--
--   **Relation to Mathlib.** The fibre ring $\kappa(\mathfrak p)\otimes_A B$ and the residue field $\kappa(\mathfrak p)$ are Mathlib's `Ideal.Fiber` and `Ideal.ResidueField`; the comparison homomorphism to $B_\mathfrak{q}/\mathfrak pB_\mathfrak{q}$, the localisation property and the resulting isomorphism are the project's own.
--
--   **Where it is used.** These identifications are used in the commutative-algebra layer to compute local rings of fibres of an algebra map as quotients of localisations, and in particular to transfer regularity of such local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_KmfloorsGlueFiberLocalizationQuotientEngine.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

universe u v w

open TensorProduct

section FiberTeeth

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (p : Ideal A) [p.IsPrime]

theorem kmfloorsGlue_map_algebraMap_fiber_eq_bot :
    p.map (algebraMap A (p.Fiber B)) = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro a ha
  have h0 : algebraMap A p.ResidueField a = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr ha
  rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply A p.ResidueField (p.Fiber B), h0,
    map_zero]

theorem kmfloorsGlue_one_tmul_eq_zero_of_mem_map
    (w : B) (hw : w ∈ p.map (algebraMap A B)) :
    (1 : p.ResidueField) ⊗ₜ[A] w = 0 := by
  have hle : p.map (algebraMap A B) ≤ RingHom.ker
      (Algebra.TensorProduct.includeRight
        (R := A) (A := p.ResidueField) (B := B)).toRingHom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have h0 : algebraMap A p.ResidueField a = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr ha
    show (1 : p.ResidueField) ⊗ₜ[A] (algebraMap A B a) = 0
    calc (1 : p.ResidueField) ⊗ₜ[A] (algebraMap A B a)
        = algebraMap A (p.Fiber B) a := (Algebra.TensorProduct.algebraMap_apply' a).symm
      _ = 0 := by
          rw [IsScalarTower.algebraMap_apply A p.ResidueField (p.Fiber B), h0, map_zero]
  have hker := hle hw
  rw [RingHom.mem_ker] at hker
  simpa using hker

theorem kmfloorsGlue_isUnit_algebraMap_fiber_of_notMem
    (r : A) (hr : r ∉ p) : IsUnit (algebraMap A (p.Fiber B) r) := by
  rw [IsScalarTower.algebraMap_apply A p.ResidueField (p.Fiber B)]
  exact (isUnit_iff_ne_zero.mpr
    fun h0 => hr (Ideal.algebraMap_residueField_eq_zero.mp h0)).map _

theorem kmfloorsGlue_mem_iff_one_tmul_mem
    (q : Ideal B) (Q : Ideal (p.Fiber B))
    (hQq : Q.comap (Algebra.TensorProduct.includeRight
      (R := A) (A := p.ResidueField) (B := B)).toRingHom = q) (b : B) :
    b ∈ q ↔ (1 : p.ResidueField) ⊗ₜ[A] b ∈ Q := by
  conv_lhs => rw [← hQq]
  rw [Ideal.mem_comap]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply]

end FiberTeeth

theorem kmfloorsGlue_comp_kills
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (Bq : Type w) [CommRing Bq] [Algebra B Bq]
    (a : A) (ha : a ∈ p) :
    ((Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))).comp
      ((algebraMap B Bq).comp (algebraMap A B))) a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha))

theorem kmfloorsGlue_isUnit_mk_of_notMem
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (q : Ideal B) [q.IsPrime]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (b : B) (hb : b ∉ q) :
    IsUnit (Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
      (algebraMap B Bq b)) :=
  (IsLocalization.map_units (M := q.primeCompl) Bq ⟨b, hb⟩).map (Ideal.Quotient.mk _)

noncomputable def kmfloorsGlue_quotLeg
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (Bq : Type w) [CommRing Bq] [Algebra B Bq] :
    A ⧸ p →+* Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq) :=
  Ideal.Quotient.lift p
    ((Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))).comp
      ((algebraMap B Bq).comp (algebraMap A B)))
    (kmfloorsGlue_comp_kills p Bq)

theorem kmfloorsGlue_quotLeg_mk
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) (Bq : Type w) [CommRing Bq] [Algebra B Bq] (a : A) :
    kmfloorsGlue_quotLeg p Bq (Ideal.Quotient.mk p a) =
      Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
        (algebraMap B Bq (algebraMap A B a)) :=
  rfl

theorem kmfloorsGlue_quotLeg_units
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (y : nonZeroDivisors (A ⧸ p)) : IsUnit (kmfloorsGlue_quotLeg (B := B) p Bq y) := by
  have hpq : p = q.comap (algebraMap A B) := Ideal.LiesOver.over
  obtain ⟨y, hy⟩ := y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ha : a ∉ p := fun h =>
    (mem_nonZeroDivisors_iff_ne_zero.mp hy) (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  have hb : algebraMap A B a ∉ q := fun hin =>
    ha (by rw [hpq]; exact Ideal.mem_comap.mpr hin)
  show IsUnit (kmfloorsGlue_quotLeg (B := B) p Bq (Ideal.Quotient.mk p a))
  rw [kmfloorsGlue_quotLeg_mk]
  exact kmfloorsGlue_isUnit_mk_of_notMem p q Bq (algebraMap A B a) hb

noncomputable def kmfloorsGlue_residueLeg
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q] :
    p.ResidueField →+* Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq) :=
  IsLocalization.lift (M := nonZeroDivisors (A ⧸ p)) (kmfloorsGlue_quotLeg_units p q Bq)

theorem kmfloorsGlue_residueLeg_algebraMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q] (a : A) :
    kmfloorsGlue_residueLeg p q Bq (algebraMap A p.ResidueField a) =
      Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
        (algebraMap B Bq (algebraMap A B a)) := by
  show IsLocalization.lift (M := nonZeroDivisors (A ⧸ p)) (kmfloorsGlue_quotLeg_units p q Bq)
      (algebraMap A p.ResidueField a) = _
  rw [IsScalarTower.algebraMap_apply A (A ⧸ p) p.ResidueField, IsLocalization.lift_eq,
    Ideal.Quotient.algebraMap_eq, kmfloorsGlue_quotLeg_mk]

noncomputable def kmfloorsGlue_fiberEval
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q] :
    p.Fiber B →+* Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq) :=
  letI : Algebra A Bq := ((algebraMap B Bq).comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B Bq := IsScalarTower.of_algebraMap_eq' rfl
  (Algebra.TensorProduct.productMap
    { toRingHom := kmfloorsGlue_residueLeg p q Bq
      commutes' := fun a => by
        show kmfloorsGlue_residueLeg p q Bq (algebraMap A p.ResidueField a) = _
        rw [kmfloorsGlue_residueLeg_algebraMap]
        rfl }
    (IsScalarTower.toAlgHom A B
      (Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq)))).toRingHom

theorem kmfloorsGlue_fiberEval_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (x : p.ResidueField) (b : B) :
    kmfloorsGlue_fiberEval p q Bq (x ⊗ₜ[A] b) =
      kmfloorsGlue_residueLeg p q Bq x *
        Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
          (algebraMap B Bq b) :=
  rfl

theorem kmfloorsGlue_fiberEval_one_tmul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (b : B) :
    kmfloorsGlue_fiberEval p q Bq ((1 : p.ResidueField) ⊗ₜ[A] b) =
      Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
        (algebraMap B Bq b) := by
  rw [kmfloorsGlue_fiberEval_tmul, map_one, one_mul]

theorem kmfloorsGlue_fiberEval_algebraMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (a : A) :
    kmfloorsGlue_fiberEval p q Bq (algebraMap A (p.Fiber B) a) =
      Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
        (algebraMap B Bq (algebraMap A B a)) := by
  rw [Algebra.TensorProduct.algebraMap_apply, kmfloorsGlue_fiberEval_tmul,
    kmfloorsGlue_residueLeg_algebraMap, map_one, map_one, mul_one]

section Engine

theorem kmfloorsGlue_isLocalization_fiberEval
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Q : Ideal (p.Fiber B)) [Q.IsPrime]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (hQq : Q.comap (Algebra.TensorProduct.includeRight
      (R := A) (A := p.ResidueField) (B := B)).toRingHom = q) :
    @IsLocalization (p.Fiber B) _ Q.primeCompl
      (Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq)) _
      (kmfloorsGlue_fiberEval p q Bq).toAlgebra := by
  have hQp : Q.IsPrime := inferInstance
  letI : Algebra (p.Fiber B)
      (Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq)) :=
    (kmfloorsGlue_fiberEval p q Bq).toAlgebra
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  ·
    rintro ⟨x, hx⟩
    obtain ⟨r, hr, s, hrs⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p x
    have hu : IsUnit (algebraMap A (p.Fiber B) r) :=
      kmfloorsGlue_isUnit_algebraMap_fiber_of_notMem p r hr
    have h1s : (1 : p.ResidueField) ⊗ₜ[A] s ∉ Q := by
      intro hmem'
      rw [← hrs, Algebra.smul_def] at hmem'
      rcases hQp.mem_or_mem hmem' with h | h
      · exact hQp.ne_top (Q.eq_top_of_isUnit_mem h hu)
      · exact hx h
    have hs : s ∉ q := fun hsq =>
      h1s ((kmfloorsGlue_mem_iff_one_tmul_mem p q Q hQq s).mp hsq)
    show IsUnit (kmfloorsGlue_fiberEval p q Bq x)
    have hchain :
        Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
            (algebraMap B Bq (algebraMap A B r)) * kmfloorsGlue_fiberEval p q Bq x =
          kmfloorsGlue_fiberEval p q Bq ((1 : p.ResidueField) ⊗ₜ[A] s) := by
      rw [← kmfloorsGlue_fiberEval_algebraMap p q Bq r, ← map_mul, ← Algebra.smul_def,
        hrs]
    have hprod : IsUnit
        (Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
          (algebraMap B Bq (algebraMap A B r)) * kmfloorsGlue_fiberEval p q Bq x) := by
      rw [hchain, kmfloorsGlue_fiberEval_one_tmul]
      exact kmfloorsGlue_isUnit_mk_of_notMem p q Bq s hs
    exact isUnit_of_mul_isUnit_right hprod
  ·
    intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (M := q.primeCompl) (S := Bq) w
    refine ⟨⟨(1 : p.ResidueField) ⊗ₜ[A] b,
      ⟨(1 : p.ResidueField) ⊗ₜ[A] (s : B),
        fun hc => s.2 ((kmfloorsGlue_mem_iff_one_tmul_mem p q Q hQq (s : B)).mpr hc)⟩⟩, ?_⟩
    show Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
        (IsLocalization.mk' Bq b s) *
        kmfloorsGlue_fiberEval p q Bq ((1 : p.ResidueField) ⊗ₜ[A] (s : B)) =
      kmfloorsGlue_fiberEval p q Bq ((1 : p.ResidueField) ⊗ₜ[A] b)
    rw [kmfloorsGlue_fiberEval_one_tmul, kmfloorsGlue_fiberEval_one_tmul, ← map_mul,
      IsLocalization.mk'_spec]
  ·
    intro x y hxy
    replace hxy : kmfloorsGlue_fiberEval p q Bq x = kmfloorsGlue_fiberEval p q Bq y := hxy
    obtain ⟨r, hr, s, hrs⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p (x - y)
    have hd : kmfloorsGlue_fiberEval p q Bq (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hs0 : Ideal.Quotient.mk ((p.map (algebraMap A B)).map (algebraMap B Bq))
        (algebraMap B Bq s) = 0 := by
      rw [← kmfloorsGlue_fiberEval_one_tmul p q Bq s, ← hrs, Algebra.smul_def, map_mul,
        hd, mul_zero]
    have hsJ : algebraMap B Bq s ∈ (p.map (algebraMap A B)).map (algebraMap B Bq) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hs0
    obtain ⟨⟨j, u⟩, hju⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (M := q.primeCompl) (S := Bq)).mp hsJ
    have h0 : algebraMap B Bq (s * (u : B) - (j : B)) = 0 := by
      rw [map_sub, map_mul, hju, sub_self]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (M := q.primeCompl)
      (S := Bq) (s * (u : B) - (j : B))).mp h0
    rw [mul_sub, sub_eq_zero] at hm
    have hvs : (((u : B) * (m : B)) * s) ∈ p.map (algebraMap A B) := by
      have hveq : ((u : B) * (m : B)) * s = (m : B) * (s * (u : B)) := by ring
      rw [hveq, hm]
      exact Ideal.mul_mem_left _ _ j.2
    have hzero : (1 : p.ResidueField) ⊗ₜ[A] (((u : B) * (m : B)) * s) = 0 :=
      kmfloorsGlue_one_tmul_eq_zero_of_mem_map p _ hvs
    have hv : (u : B) * (m : B) ∈ q.primeCompl := q.primeCompl.mul_mem u.2 m.2
    have hc : ((1 : p.ResidueField) ⊗ₜ[A] ((u : B) * (m : B))) * (x - y) = 0 := by
      have hu := kmfloorsGlue_isUnit_algebraMap_fiber_of_notMem (B := B) p r hr
      refine (hu.mul_right_eq_zero).mp ?_
      have hswap : algebraMap A (p.Fiber B) r *
          (((1 : p.ResidueField) ⊗ₜ[A] ((u : B) * (m : B))) * (x - y)) =
          ((1 : p.ResidueField) ⊗ₜ[A] ((u : B) * (m : B))) *
            (algebraMap A (p.Fiber B) r * (x - y)) := by ring
      rw [hswap, ← Algebra.smul_def, hrs, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      exact hzero
    refine ⟨⟨(1 : p.ResidueField) ⊗ₜ[A] ((u : B) * (m : B)),
      fun hQm => hv
        ((kmfloorsGlue_mem_iff_one_tmul_mem p q Q hQq ((u : B) * (m : B))).mpr hQm)⟩, ?_⟩
    rw [mul_sub] at hc
    exact sub_eq_zero.mp hc

noncomputable def kmfloorsGlue_fiberLocalizationAtPrimeQuotientEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Q : Ideal (p.Fiber B)) [Q.IsPrime]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (hQq : Q.comap (Algebra.TensorProduct.includeRight
      (R := A) (A := p.ResidueField) (B := B)).toRingHom = q) :
    Localization.AtPrime Q ≃+*
      Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq) :=
  letI : Algebra (p.Fiber B)
      (Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq)) :=
    (kmfloorsGlue_fiberEval p q Bq).toAlgebra
  haveI := kmfloorsGlue_isLocalization_fiberEval p q Q Bq hQq
  (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
    (Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq))).toRingEquiv

theorem kmfloorsGlue_isRegularLocalRing_localizationQuotient_iff
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (Q : Ideal (p.Fiber B)) [Q.IsPrime]
    (Bq : Type w) [CommRing Bq] [Algebra B Bq] [IsLocalization.AtPrime Bq q]
    (hQq : Q.comap (Algebra.TensorProduct.includeRight
      (R := A) (A := p.ResidueField) (B := B)).toRingHom = q) :
    IsRegularLocalRing (Localization.AtPrime Q) ↔
      IsRegularLocalRing (Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq)) := by
  letI : Algebra (p.Fiber B)
      (Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq)) :=
    (kmfloorsGlue_fiberEval p q Bq).toAlgebra
  haveI := kmfloorsGlue_isLocalization_fiberEval p q Q Bq hQq
  constructor
  · intro h
    haveI := h
    exact IsRegularLocalRing.of_ringEquiv
      (R := Localization.AtPrime Q)
      (R' := Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq))
      ((IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
        (Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq))).toRingEquiv)
  · intro h
    haveI := h
    exact IsRegularLocalRing.of_ringEquiv
      (R := Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq))
      (R' := Localization.AtPrime Q)
      ((IsLocalization.algEquiv Q.primeCompl
        (Bq ⧸ (p.map (algebraMap A B)).map (algebraMap B Bq))
        (Localization.AtPrime Q)).toRingEquiv)

end Engine

section Bridge

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (p : Ideal A) [p.IsPrime]
variable (Bq : Type w) [CommRing Bq] [Algebra B Bq]

theorem kmfloorsGlue_maximalIdeal_map_eq
    (Ap : Type w) [CommRing Ap] [Algebra A Ap] [IsLocalization.AtPrime Ap p]
    [IsLocalRing Ap] (g : Ap →+* Bq)
    (hg : g.comp (algebraMap A Ap) = (algebraMap B Bq).comp (algebraMap A B)) :
    (IsLocalRing.maximalIdeal Ap).map g =
      (p.map (algebraMap A B)).map (algebraMap B Bq) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p Ap, Ideal.map_map, hg,
    ← Ideal.map_map]

end Bridge

section SatGates

variable {A : Type u} [CommRing A]

theorem kmfloorsGlue_satGate_identityChart_isDomain (p : Ideal A) [p.IsPrime] :
    IsDomain (p.Fiber A) :=
  MulEquiv.isDomain p.ResidueField
    (Algebra.TensorProduct.rid A A p.ResidueField).toRingEquiv.toMulEquiv

theorem kmfloorsGlue_satGate_identityChart_comap (p : Ideal A) [p.IsPrime] :
    (⊥ : Ideal (p.Fiber A)).comap (Algebra.TensorProduct.includeRight
      (R := A) (A := p.ResidueField) (B := A)).toRingHom = p := by
  ext b
  rw [Ideal.mem_comap, Ideal.mem_bot]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply]
  constructor
  · intro h0
    have hrid : (Algebra.TensorProduct.rid A A p.ResidueField)
        ((1 : p.ResidueField) ⊗ₜ[A] b) = 0 := by
      rw [h0, map_zero]
    rw [Algebra.TensorProduct.rid_tmul, ← Algebra.algebraMap_eq_smul_one] at hrid
    exact Ideal.algebraMap_residueField_eq_zero.mp hrid
  · intro hb
    have hmem : (algebraMap A A b) ∈ p.map (algebraMap A A) := Ideal.mem_map_of_mem _ hb
    have h := kmfloorsGlue_one_tmul_eq_zero_of_mem_map p (algebraMap A A b) hmem
    simpa using h

theorem kmfloorsGlue_satGate_identityChart (p : Ideal A) [p.IsPrime] :
    haveI : IsDomain (p.Fiber A) := kmfloorsGlue_satGate_identityChart_isDomain p
    haveI : (⊥ : Ideal (p.Fiber A)).IsPrime := Ideal.isPrime_bot
    Nonempty (Localization.AtPrime (⊥ : Ideal (p.Fiber A)) ≃+*
      Localization.AtPrime p ⧸
        (p.map (algebraMap A A)).map (algebraMap A (Localization.AtPrime p))) := by
  haveI : IsDomain (p.Fiber A) := kmfloorsGlue_satGate_identityChart_isDomain p
  haveI : (⊥ : Ideal (p.Fiber A)).IsPrime := Ideal.isPrime_bot
  haveI : p.LiesOver p := ⟨by rw [Ideal.under_def, Algebra.algebraMap_self, Ideal.comap_id]⟩
  exact ⟨kmfloorsGlue_fiberLocalizationAtPrimeQuotientEquiv p p ⊥
    (Localization.AtPrime p) (kmfloorsGlue_satGate_identityChart_comap p)⟩

instance kmfloorsGlue_int_three_isPrime : (Ideal.span {(3 : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_three

theorem kmfloorsGlue_satGate_production_chartPair_int_three :
    haveI : IsDomain ((Ideal.span {(3 : ℤ)}).Fiber ℤ) :=
      kmfloorsGlue_satGate_identityChart_isDomain (Ideal.span {(3 : ℤ)})
    haveI : (⊥ : Ideal ((Ideal.span {(3 : ℤ)}).Fiber ℤ)).IsPrime := Ideal.isPrime_bot
    Nonempty (Localization.AtPrime (⊥ : Ideal ((Ideal.span {(3 : ℤ)}).Fiber ℤ)) ≃+*
      Localization.AtPrime (Ideal.span {(3 : ℤ)}) ⧸
        ((Ideal.span {(3 : ℤ)}).map (algebraMap ℤ ℤ)).map
          (algebraMap ℤ (Localization.AtPrime (Ideal.span {(3 : ℤ)})))) :=
  kmfloorsGlue_satGate_identityChart (Ideal.span {(3 : ℤ)})

end SatGates

instance kmfloorsGlue_int_bot_isPrime : (⊥ : Ideal ℤ).IsPrime := Ideal.isPrime_bot

theorem kmfloorsGlue_falsifGate_wrongPrime_targetCollapses :
    ((Ideal.span {(3 : ℤ)}).map (algebraMap ℤ ℤ)).map
      (algebraMap ℤ (Localization.AtPrime (⊥ : Ideal ℤ))) = ⊤ := by
  have h3 : (3 : ℤ) ∉ (⊥ : Ideal ℤ) := by simp
  have hmem : algebraMap ℤ (Localization.AtPrime (⊥ : Ideal ℤ)) 3 ∈
      ((Ideal.span {(3 : ℤ)}).map (algebraMap ℤ ℤ)).map
        (algebraMap ℤ (Localization.AtPrime (⊥ : Ideal ℤ))) :=
    Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.subset_span rfl))
  have hunit : IsUnit (algebraMap ℤ (Localization.AtPrime (⊥ : Ideal ℤ)) 3) :=
    IsLocalization.map_units (M := (⊥ : Ideal ℤ).primeCompl)
      (Localization.AtPrime (⊥ : Ideal ℤ)) ⟨3, h3⟩
  exact Ideal.eq_top_of_isUnit_mem _ hmem hunit

/--
info: 'kmfloorsGlue_map_algebraMap_fiber_eq_bot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmfloorsGlue_map_algebraMap_fiber_eq_bot

/--
info: 'kmfloorsGlue_one_tmul_eq_zero_of_mem_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmfloorsGlue_one_tmul_eq_zero_of_mem_map

/--
info: 'kmfloorsGlue_isUnit_algebraMap_fiber_of_notMem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmfloorsGlue_isUnit_algebraMap_fiber_of_notMem

/--
info: 'kmfloorsGlue_mem_iff_one_tmul_mem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmfloorsGlue_mem_iff_one_tmul_mem

/--
info: 'kmfloorsGlue_fiberEval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmfloorsGlue_fiberEval

/--
info: 'kmfloorsGlue_isLocalization_fiberEval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmfloorsGlue_isLocalization_fiberEval

/--
info: 'kmfloorsGlue_fiberLocalizationAtPrimeQuotientEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmfloorsGlue_fiberLocalizationAtPrimeQuotientEquiv

/--
info: 'kmfloorsGlue_isRegularLocalRing_localizationQuotient_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmfloorsGlue_isRegularLocalRing_localizationQuotient_iff

/--
info: 'kmfloorsGlue_maximalIdeal_map_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmfloorsGlue_maximalIdeal_map_eq

/--
info: 'kmfloorsGlue_satGate_identityChart' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmfloorsGlue_satGate_identityChart

/--
info: 'kmfloorsGlue_satGate_production_chartPair_int_three' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmfloorsGlue_satGate_production_chartPair_int_three

/--
info: 'kmfloorsGlue_falsifGate_wrongPrime_targetCollapses' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms kmfloorsGlue_falsifGate_wrongPrime_targetCollapses

end


