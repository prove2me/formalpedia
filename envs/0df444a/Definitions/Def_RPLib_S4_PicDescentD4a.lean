-- Prove2me | Definitions.Def_RPLib_S4_PicDescentD4a
-- name    : RPLib_S4_PicDescentD4a
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:28:29.833317+00:00
-- url     : https://prove2.me/theorems/489508f3-b667-4e35-b9b8-775971172b72
-- title:
--   Places of the ring pair $A \to L \otimes A$: contraction and degrees
-- statement:
--   For Dedekind domains $A \to A' \cong L \otimes_{\mathbb{F}_q} A$ with $L/\mathbb{F}_q$ finite, the file defines the contraction $w \mapsto w \cap A$ of places, proves that orders agree, $\operatorname{ord}_{w \cap A}(f) = \operatorname{ord}_w(f)$, that fibres are finite and nonempty, that $$\deg(w \cap A)\, f(w) = [L : \mathbb{F}_q]\, \deg_L(w), \qquad \sum_{w \cap A = v} \deg_L(w) = \deg v,$$ and that $\operatorname{Gal}(L/\mathbb{F}_q)$ acts on places compatibly with contraction and orders, transitively on fibres.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapter 8; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009), Section 3.6

import Definitions.Def_RPLib_S4_PicDescentD3

/-!
# S4-PicDescent, part D4a: places of a ring pair `A → A' ≃ L ⊗ A`, generic

Setting of D3 (Dedekind `A`, `A'`, finite `L`).
* `cont w = w ∩ A` (contraction); `ord_cont`: `ord_{cont w} f = ord_w f'`; fibres finite (`finite_cont`)
  and nonempty (`exists_cont_eq`); `deg_cont_mul`: `deg (cont w) · f(w) = [L : Fq] · deg_L w`;
  `sum_deg_cont`: `Σ_{cont w = v} deg_L w = deg v`.
* Galois: `cont_pullH`, `ord_pullH` (`ord_{τ⁻¹ w} f = ord_w (gal τ f)`), `pullH_pullH`, `pullH_one`,
  `plEquiv`, `exists_pullH_of_cont_eq` (transitivity on fibres).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace RamanujanPetersson.PicDescent

section PairPlaces

variable {Fq : Type*} [Field Fq] {L : Type*} [Field L] [Algebra Fq L]
  {F : Type*} [Field F] [Algebra Fq F] {F' : Type*} [Field F'] [Algebra L F'] [Algebra F F']
  [Algebra Fq F'] [IsScalarTower Fq F F'] [IsScalarTower Fq L F']
  {ι : Type*} [Fintype ι] {c : Module.Basis ι Fq L}
  (hli : LinearIndependent F fun j => algebraMap L F' (c j))
  (hsp : ⊤ ≤ Submodule.span F (Set.range fun j => algebraMap L F' (c j)))
  {A : Type*} [CommRing A] [Algebra Fq A] [Algebra A F] [IsScalarTower Fq A F]
  {A' : Type*} [CommRing A'] [Algebra L A'] [Algebra A' F'] [IsScalarTower L A' F']
  (hA : Function.Injective (algebraMap A F)) (hA' : Function.Injective (algebraMap A' F'))
  (hc : ∀ f : ι → F, (∑ j, f j • algebraMap L F' (c j)) ∈ (algebraMap A' F').range ↔
    ∀ j, f j ∈ (algebraMap A F).range)
  [Algebra A A'] [Algebra A F'] [IsScalarTower A F F'] [IsScalarTower A A' F']
  [IsDedekindDomain A] [IsDedekindDomain A'] [Finite L]

include hli hsp hA hA' hc in
theorem isIntegral_AA' : Algebra.IsIntegral A A' := by
  haveI := moduleFinite hli hsp hA hA' hc
  exact Algebra.IsIntegral.of_finite A A'

/-- The contraction `w ↦ w ∩ A`. -/
noncomputable def cont (w : HeightOneSpectrum A') : HeightOneSpectrum A :=
  haveI := isIntegral_AA' hli hsp hA hA' hc
  w.under A

theorem cont_asIdeal (w : HeightOneSpectrum A') :
    (cont hli hsp hA hA' hc w).asIdeal = w.asIdeal.comap (algebraMap A A') := rfl

/-- **Orders agree**: `ord_{w ∩ A} f = ord_w f'`. -/
theorem ord_cont [IsFractionRing A F] [IsFractionRing A' F'] [Algebra.IsSeparable Fq L]
    (w : HeightOneSpectrum A') (f : F) :
    Places.ord (cont hli hsp hA hA' hc w) f = Places.ord w (algebraMap F F' f) := by
  haveI := isIntegral_AA' hli hsp hA hA' hc
  haveI := isTorsionFree hA hA'
  haveI := formallyUnramified hli hsp hA hA' hc
  haveI := moduleFinite hli hsp hA hA' hc
  unfold Places.ord
  rw [show (cont hli hsp hA hA' hc w).valuation F f = w.valuation F' (algebraMap F F' f) from
    valuation_under w f]

theorem finite_cont (v : HeightOneSpectrum A) :
    {w : HeightOneSpectrum A' | cont hli hsp hA hA' hc w = v}.Finite := by
  haveI := isIntegral_AA' hli hsp hA hA' hc
  haveI := isTorsionFree hA hA'
  exact finite_under v

theorem exists_cont_eq (v : HeightOneSpectrum A) : ∃ w : HeightOneSpectrum A', cont hli hsp hA hA' hc w = v := by
  haveI := isIntegral_AA' hli hsp hA hA' hc
  haveI := isTorsionFree hA hA'
  exact exists_under_eq v

theorem deg_cont_mul [Fintype Fq] [Fintype L] [Places.FiniteQuot A] [Places.FiniteQuot A']
    (w : HeightOneSpectrum A') :
    Places.deg Fq (cont hli hsp hA hA' hc w) * w.asIdeal.inertiaDeg A =
      Module.finrank Fq L * Places.deg L w := by
  haveI := isIntegral_AA' hli hsp hA hA' hc
  haveI := isTorsionFree hA hA'
  haveI := moduleFinite hli hsp hA hA' hc
  have h1 := card_quot_pow (A := A) w
  rw [Places.card_residue_eq Fq (w.under A), Places.card_residue_eq L w, Module.card_eq_pow_finrank (K := Fq) (V := L),
    ← pow_mul, ← pow_mul] at h1
  exact Nat.pow_right_injective (Fintype.one_lt_card (α := Fq)) h1

/-- **`Σ_{w | v} deg_L w = deg v`**. -/
theorem sum_deg_cont [Fintype Fq] [Fintype L] [Places.FiniteQuot A] [Places.FiniteQuot A']
    [Algebra.IsSeparable Fq L] (v : HeightOneSpectrum A) :
    ∑ w ∈ (finite_cont hli hsp hA hA' hc v).toFinset, Places.deg L w = Places.deg Fq v := by
  haveI := isIntegral_AA' hli hsp hA hA' hc
  haveI := isTorsionFree hA hA'
  haveI := moduleFinite hli hsp hA hA' hc
  haveI := moduleFree hli hsp hA hA' hc
  haveI := formallyUnramified hli hsp hA hA' hc
  have hk : 0 < Module.finrank Fq L := Module.finrank_pos
  have hs : ∑ w ∈ (finite_cont hli hsp hA hA' hc v).toFinset, w.asIdeal.inertiaDeg A =
      Module.finrank Fq L := by
    rw [← finrank_A_A' hli hsp hA hA' hc]
    exact sum_inertiaDeg v
  apply Nat.eq_of_mul_eq_mul_left hk
  rw [Finset.mul_sum]
  calc ∑ w ∈ (finite_cont hli hsp hA hA' hc v).toFinset, Module.finrank Fq L * Places.deg L w
      = ∑ w ∈ (finite_cont hli hsp hA hA' hc v).toFinset, Places.deg Fq v * w.asIdeal.inertiaDeg A := by
        refine Finset.sum_congr rfl fun w hw => ?_
        have hw' : cont hli hsp hA hA' hc w = v := by
          have h2 := (Set.Finite.mem_toFinset _).1 hw
          exact h2
        rw [← deg_cont_mul hli hsp hA hA' hc w, hw']
    _ = Module.finrank Fq L * Places.deg Fq v := by rw [← Finset.mul_sum, hs, mul_comm]

theorem cont_pullH (τ : L ≃ₐ[Fq] L) (w : HeightOneSpectrum A') :
    cont hli hsp hA hA' hc (pullH (galA' hli hsp hA hA' hc τ) w) = cont hli hsp hA hA' hc w := by
  apply HeightOneSpectrum.ext
  ext a
  show galA' hli hsp hA hA' hc τ (algebraMap A A' a) ∈ w.asIdeal ↔ algebraMap A A' a ∈ w.asIdeal
  rw [galA'_algebraMap]

/-- **Transport of orders**: `ord_{τ⁻¹ w} f = ord_w (gal τ f)`. -/
theorem ord_pullH [IsFractionRing A' F'] (τ : L ≃ₐ[Fq] L) (w : HeightOneSpectrum A') (f : F') :
    Places.ord (pullH (galA' hli hsp hA hA' hc τ) w) f = Places.ord w (gal hli hsp τ f) := by
  unfold Places.ord
  rw [valuation_pullH (galA' hli hsp hA hA' hc τ) (gal hli hsp τ).toRingEquiv
    (fun b => algebraMap_galA' hli hsp hA hA' hc τ b) w f]
  rfl

theorem pullH_pullH (τ1 τ2 : L ≃ₐ[Fq] L) (w : HeightOneSpectrum A') :
    pullH (galA' hli hsp hA hA' hc τ1) (pullH (galA' hli hsp hA hA' hc τ2) w) =
      pullH (galA' hli hsp hA hA' hc (τ2 * τ1)) w := by
  apply HeightOneSpectrum.ext
  ext y
  have e : galA' hli hsp hA hA' hc (τ2 * τ1) y =
      galA' hli hsp hA hA' hc τ2 (galA' hli hsp hA hA' hc τ1 y) :=
    DFunLike.congr_fun ((galA'Hom hli hsp hA hA' hc).map_mul τ2 τ1) y
  show galA' hli hsp hA hA' hc τ2 (galA' hli hsp hA hA' hc τ1 y) ∈ w.asIdeal ↔
    galA' hli hsp hA hA' hc (τ2 * τ1) y ∈ w.asIdeal
  rw [e]

theorem pullH_one (w : HeightOneSpectrum A') : pullH (galA' hli hsp hA hA' hc 1) w = w := by
  apply HeightOneSpectrum.ext
  ext y
  have e : galA' hli hsp hA hA' hc 1 y = y := DFunLike.congr_fun (galA'Hom hli hsp hA hA' hc).map_one y
  show galA' hli hsp hA hA' hc 1 y ∈ w.asIdeal ↔ y ∈ w.asIdeal
  rw [e]

/-- `w ↦ τ⁻¹ w` as a bijection of places. -/
noncomputable def plEquiv (τ : L ≃ₐ[Fq] L) : HeightOneSpectrum A' ≃ HeightOneSpectrum A' where
  toFun := pullH (galA' hli hsp hA hA' hc τ)
  invFun := pullH (galA' hli hsp hA hA' hc τ⁻¹)
  left_inv w := by
    show pullH _ (pullH _ w) = w
    rw [pullH_pullH, mul_inv_cancel, pullH_one]
  right_inv w := by
    show pullH _ (pullH _ w) = w
    rw [pullH_pullH, inv_mul_cancel, pullH_one]

theorem plEquiv_apply (τ : L ≃ₐ[Fq] L) (w : HeightOneSpectrum A') :
    plEquiv hli hsp hA hA' hc τ w = pullH (galA' hli hsp hA hA' hc τ) w := rfl

/-- **Transitivity**: places with the same contraction are `Gal(L/Fq)`-conjugate. -/
theorem exists_pullH_of_cont_eq (w1 w2 : HeightOneSpectrum A')
    (h : cont hli hsp hA hA' hc w1 = cont hli hsp hA hA' hc w2) :
    ∃ τ : L ≃ₐ[Fq] L, w2 = pullH (galA' hli hsp hA hA' hc τ) w1 :=
  exists_pullH_of_under_eq hli hsp hA hA' hc w1 w2 (congrArg HeightOneSpectrum.asIdeal h)

end PairPlaces

end RamanujanPetersson.PicDescent


