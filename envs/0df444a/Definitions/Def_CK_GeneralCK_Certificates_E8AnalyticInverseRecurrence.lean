-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8AnalyticInverseRecurrence
-- name    : CK_GeneralCK_Certificates_E8AnalyticInverseRecurrence
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:02:04.38836+00:00
-- url     : https://prove2.me/theorems/f17db361-a1a7-45d8-b388-373ba44595f0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8AnalyticInverseRecurrence` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8AnalyticInverseRecurrence` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8AnalyticInverseRecurrence` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8AnalyticInverseRecurrence (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8AnalyticInverseRecurrence.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8AnalyticCoefficientBoxes
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Substitution

-- ===== source module GeneralCK.Certificates.E8AnalyticInverseRecurrence =====
section

/-! Exact coefficient recurrence for a locally inverse analytic series. -/

namespace GeneralCK.Certificates.E8AnalyticInverseRecurrence

open E8AnalyticGerm E8AnalyticCoefficientBoxes
open Filter

private theorem deriv_xParam_zero_ne : deriv xParam 0 ≠ 0 := by
  rw [hasDerivAt_xParam_zero.deriv]
  norm_num

/-- Bias coordinate as an analytic function of the contact coordinate `x`. -/
noncomputable def xBiasGerm : ℂ → ℂ :=
  analyticAt_xParam.hasStrictDerivAt.localInverse xParam
    (deriv xParam 0) 0 deriv_xParam_zero_ne

@[simp] theorem xBiasGerm_zero : xBiasGerm 0 = 0 := by
  have h := analyticAt_xParam.hasStrictDerivAt.eventually_left_inverse deriv_xParam_zero_ne
  simpa [xBiasGerm] using h.self_of_nhds

theorem analyticAt_xBiasGerm : AnalyticAt ℂ xBiasGerm 0 := by
  simpa [xBiasGerm] using
    analyticAt_xParam.analyticAt_localInverse deriv_xParam_zero_ne

/-- The analytic E8 slope as a germ in the contact coordinate. -/
noncomputable def thetaGerm (x : ℂ) : ℂ := thetaParam (xBiasGerm x)

@[simp] theorem thetaGerm_zero : thetaGerm 0 = 0 := by simp [thetaGerm]

theorem analyticAt_thetaGerm : AnalyticAt ℂ thetaGerm 0 :=
  analyticAt_thetaParam.comp_of_eq analyticAt_xBiasGerm xBiasGerm_zero

/-- The contact-coordinate slope germ is locally inverse to `qGerm`. -/
theorem eventually_thetaGerm_qGerm :
    ∀ᶠ y in nhds (0 : ℂ), thetaGerm (qGerm y) = y := by
  have hleft := analyticAt_xParam.hasStrictDerivAt.eventually_left_inverse
    deriv_xParam_zero_ne
  change ∀ᶠ x in nhds (0 : ℂ), xBiasGerm (xParam x) = x at hleft
  have hbias : Tendsto biasGerm (nhds (0 : ℂ)) (nhds 0) := by
    simpa using analyticAt_biasGerm.continuousAt.tendsto
  have hpull := hbias.eventually hleft
  filter_upwards [hpull, eventually_thetaParam_biasGerm] with y hxy htheta
  rw [thetaGerm, qGerm, hxy, htheta]

/-- Factorial-normalized Taylor coefficients of the analytic slope germ. -/
noncomputable def thetaTaylorCoeff (n : ℕ) : ℂ :=
  iteratedDeriv n thetaGerm 0 / n.factorial

def powCoeff (q : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, n => if n = 0 then 1 else 0
  | k + 1, n =>
      ∑ i ∈ Finset.range (n + 1), q i * powCoeff q k (n - i)

def composeCoeff (theta q : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), theta k * powCoeff q k n

def targetCoeff (n : ℕ) : ℂ := if n = 1 then 1 else 0

/-- The scalar coefficient of Mathlib's formal multilinear composition. -/
noncomputable def formalComposeCoeff (theta q : ℕ → ℂ) (n : ℕ) : ℂ :=
  ((FormalMultilinearSeries.ofScalars ℂ theta).comp
    (FormalMultilinearSeries.ofScalars ℂ q)).coeff n

/-- Mathlib's analytic composition theorem, uniqueness of local power series,
and the local inverse identity give the exact inverse-series coefficients. -/
theorem formalComposeCoeff_theta_q (n : ℕ) :
    formalComposeCoeff thetaTaylorCoeff qTaylorCoeff n = targetCoeff n := by
  have htheta := analyticAt_thetaGerm.hasFPowerSeriesAt
  rw [← qGerm_zero] at htheta
  have hcomp := htheta.comp analyticAt_qGerm.hasFPowerSeriesAt
  have hid := (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) 0).hasFPowerSeriesAt
  have hseries := hcomp.eq_formalMultilinearSeries_of_eventually hid (by
    simpa only [Function.comp_apply, id_eq] using eventually_thetaGerm_qGerm)
  have hcoeff := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hseries
  rw [qGerm_zero] at hcoeff
  change formalComposeCoeff thetaTaylorCoeff qTaylorCoeff n =
    (FormalMultilinearSeries.ofScalars ℂ
      (fun m => iteratedDeriv m (id : ℂ → ℂ) 0 / m.factorial)).coeff n at hcoeff
  rcases n with (_ | _ | n)
  · simpa [formalComposeCoeff, thetaTaylorCoeff, qTaylorCoeff, targetCoeff,
      iteratedDeriv_id] using hcoeff
  · simpa [formalComposeCoeff, thetaTaylorCoeff, qTaylorCoeff, targetCoeff,
      iteratedDeriv_id] using hcoeff
  · simpa [formalComposeCoeff, thetaTaylorCoeff, qTaylorCoeff, targetCoeff,
      iteratedDeriv_id] using hcoeff

/-- The recursive coefficient convolution is the coefficient of a power of
the corresponding ordinary formal power series. -/
theorem powCoeff_eq_powerSeries_coeff (q : ℕ → ℂ) (k n : ℕ) :
    powCoeff q k n = PowerSeries.coeff n ((PowerSeries.mk q) ^ k) := by
  induction k generalizing n with
  | zero => simp [powCoeff]
  | succ k ih =>
      rw [pow_succ', PowerSeries.coeff_mul]
      simp only [powCoeff, PowerSeries.coeff_mk, ih]
      symm
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => q i * PowerSeries.coeff j ((PowerSeries.mk q) ^ k)) n

private theorem powerSeries_coeff_pow_eq_zero_of_lt
    (q : ℕ → ℂ) (hq : q 0 = 0) {k n : ℕ} (h : n < k) :
    PowerSeries.coeff n ((PowerSeries.mk q) ^ k) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  apply lt_of_lt_of_le (WithTop.coe_lt_coe.mpr h)
  apply PowerSeries.le_order_pow_of_constantCoeff_eq_zero
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_mk]
  exact hq

/-- The executable convolution is precisely ordinary formal power-series
substitution whenever the inner series has zero constant coefficient. -/
theorem composeCoeff_eq_powerSeries_subst_coeff
    (theta q : ℕ → ℂ) (hq : q 0 = 0) (n : ℕ) :
    composeCoeff theta q n =
      PowerSeries.coeff n ((PowerSeries.mk theta).subst (PowerSeries.mk q)) := by
  have hs : PowerSeries.HasSubst (PowerSeries.mk q) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_mk]
      exact hq)
  rw [PowerSeries.coeff_subst' hs]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp only [composeCoeff, PowerSeries.coeff_mk, smul_eq_mul,
      powCoeff_eq_powerSeries_coeff]
  · intro k hk
    simp only [Function.mem_support] at hk
    apply Finset.mem_coe.mpr
    apply Finset.mem_range.mpr
    by_contra hkn
    have hnk : n < k := by omega
    rw [powerSeries_coeff_pow_eq_zero_of_lt q hq hnk, smul_zero] at hk
    exact hk rfl

noncomputable def posTuples (k n : Nat) : Finset (Fin k → Nat) :=
  (Finset.Nat.antidiagonalTuple k n).filter fun v => ∀ i, 0 < v i

noncomputable def posLists (k n : Nat) : Finset (List Nat) :=
  (posTuples k n).map ⟨List.ofFn, List.ofFn_injective⟩

noncomputable def listComposition {n : Nat} (l : List Nat)
    (hsum : l.sum = n) (hpos : ∀ x ∈ l, 0 < x) : Composition n where
  blocks := l
  blocks_pos := by intro i hi; exact hpos i hi
  blocks_sum := hsum

lemma blocks_mem_posLists {n : Nat} (c : Composition n) : c.blocks ∈ posLists c.length n := by
  rw [posLists, Finset.mem_map]
  refine ⟨c.blocksFun, ?_, c.ofFn_blocksFun⟩
  rw [posTuples, Finset.mem_filter]
  exact ⟨Finset.Nat.mem_antidiagonalTuple.mpr c.sum_blocksFun,
    fun i => c.one_le_blocksFun i⟩

noncomputable def tupleOfPosList {k n : Nat} (l : List Nat)
    (h : l ∈ posLists k n) : Fin k → Nat :=
  Classical.choose (Finset.mem_map.mp h)

lemma tupleOfPosList_mem {k n : Nat} (l : List Nat) (h : l ∈ posLists k n) :
    tupleOfPosList l h ∈ posTuples k n :=
  (Classical.choose_spec (Finset.mem_map.mp h)).1

lemma ofFn_tupleOfPosList {k n : Nat} (l : List Nat) (h : l ∈ posLists k n) :
    List.ofFn (tupleOfPosList l h) = l :=
  (Classical.choose_spec (Finset.mem_map.mp h)).2

lemma sum_composition_eq_sigma_posLists (theta q : Nat → Complex) (n : Nat) :
    (∑ c : Composition n, theta c.length * ∏ i, q (c.blocksFun i)) =
      ∑ p ∈ (Finset.range (n+1)).sigma (fun k => posLists k n),
        theta p.1 * (p.2.map q).prod := by
  refine Finset.sum_bij' (fun c _ => ⟨c.length, c.blocks⟩)
    (fun p hp => by
      simp only [Finset.mem_sigma] at hp
      let v := tupleOfPosList p.2 hp.2
      have hvl := ofFn_tupleOfPosList p.2 hp.2
      have hv' := tupleOfPosList_mem p.2 hp.2
      rw [posTuples, Finset.mem_filter] at hv'
      refine listComposition p.2 ?_ ?_
      · rw [← hvl, List.sum_ofFn]
        exact Finset.Nat.mem_antidiagonalTuple.mp hv'.1
      · intro x hx
        rw [← hvl, List.mem_ofFn] at hx
        rcases hx with ⟨i, rfl⟩
        exact hv'.2 i) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp [blocks_mem_posLists, Composition.length_le]
  · intro p hp
    exact Finset.mem_univ _
  · intro c hc
    apply Composition.ext
    simp [listComposition]
  · intro p hp
    simp only [Finset.mem_sigma] at hp
    let v := tupleOfPosList p.2 hp.2
    have hvl := ofFn_tupleOfPosList p.2 hp.2
    have hv' := tupleOfPosList_mem p.2 hp.2
    rw [posTuples, Finset.mem_filter] at hv'
    apply Sigma.ext
    · change p.2.length = p.1
      rw [← hvl, List.length_ofFn]
    · rfl
  · intro c hc
    rw [← c.ofFn_blocksFun, List.map_ofFn, List.prod_ofFn]
    rfl

private lemma sum_map_flatMap {α β M : Type*} [AddCommMonoid M]
    (l : List α) (f : α → List β) (g : β → M) :
    ((l.flatMap f).map g).sum = (l.map fun x => ((f x).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

private lemma sum_map_mul_left {α R : Type*} [Semiring R]
    (a : R) (l : List α) (f : α → R) :
    (l.map fun x => a * f x).sum = a * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, mul_add]

lemma powCoeff_eq_antidiagonalTuple (q : Nat → Complex) (k n : Nat) :
    powCoeff q k n = ∑ v ∈ Finset.Nat.antidiagonalTuple k n, ∏ i, q (v i) := by
  change powCoeff q k n =
    ((List.Nat.antidiagonalTuple k n).map fun v => ∏ i, q (v i)).sum
  induction k generalizing n with
  | zero => cases n <;> simp [powCoeff, List.Nat.antidiagonalTuple]
  | succ k ih =>
      simp only [powCoeff, List.Nat.antidiagonalTuple]
      rw [sum_map_flatMap]
      simp only [List.map_map, Fin.prod_univ_succ, ih]
      simp only [List.Nat.antidiagonal, List.map_map]
      change
        ((List.range (n + 1)).map fun x =>
          q x * ((List.Nat.antidiagonalTuple k (n - x)).map
            fun v => ∏ i, q (v i)).sum).sum =
        ((List.range (n + 1)).map fun x =>
          ((List.Nat.antidiagonalTuple k (n - x)).map
            fun v => q x * ∏ i, q (v i)).sum).sum
      apply congrArg List.sum
      apply List.map_congr_left
      intro x hx
      symm
      exact sum_map_mul_left (q x) _ _

lemma powCoeff_eq_posTuples (q : Nat → Complex) (hq : q 0 = 0) (k n : Nat) :
    powCoeff q k n = ∑ v ∈ posTuples k n, ∏ i, q (v i) := by
  rw [powCoeff_eq_antidiagonalTuple, posTuples, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hp : ∀ i, 0 < v i
  · simp [hp]
  · simp only [hp, ↓reduceIte]
    push Not at hp
    rcases hp with ⟨i, hi⟩
    have hi0 : v i = 0 := by omega
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi0, hq]

lemma formalComposeCoeff_eq_sum_compositions (theta q : Nat → Complex) (n : Nat) :
    formalComposeCoeff theta q n =
      ∑ c : Composition n, theta c.length * ∏ i, q (c.blocksFun i) := by
  simp only [formalComposeCoeff, FormalMultilinearSeries.coeff,
    FormalMultilinearSeries.comp]
  rw [show (∑ c : Composition n,
      (FormalMultilinearSeries.ofScalars Complex theta).compAlongComposition
        (FormalMultilinearSeries.ofScalars Complex q) c) (1) =
      ∑ c : Composition n,
        ((FormalMultilinearSeries.ofScalars Complex theta).compAlongComposition
          (FormalMultilinearSeries.ofScalars Complex q) c) (1) by simp]
  apply Finset.sum_congr rfl
  intro c hc
  rw [FormalMultilinearSeries.compAlongComposition_apply,
    FormalMultilinearSeries.ofScalars, smul_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, smul_eq_mul]
  congr 1
  rw [← List.prod_ofFn]
  apply congrArg List.prod
  rw [List.ofFn_inj]
  ext i
  simp [FormalMultilinearSeries.applyComposition,
    FormalMultilinearSeries.ofScalars, Function.comp_def]

lemma composeCoeff_eq_formalComposeCoeff (theta q : Nat → Complex)
    (hq : q 0 = 0) (n : Nat) :
    composeCoeff theta q n = formalComposeCoeff theta q n := by
  rw [formalComposeCoeff_eq_sum_compositions]
  rw [sum_composition_eq_sigma_posLists]
  rw [composeCoeff]
  calc
    ∑ k ∈ Finset.range (n + 1), theta k * powCoeff q k n =
        ∑ k ∈ Finset.range (n + 1), theta k *
          (∑ v ∈ posTuples k n, ∏ i, q (v i)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [powCoeff_eq_posTuples q hq]
    _ = ∑ k ∈ Finset.range (n + 1), ∑ v ∈ posTuples k n,
          theta k * ∏ i, q (v i) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mul_sum]
    _ = ∑ p ∈ (Finset.range (n+1)).sigma (fun k => posTuples k n),
          theta p.1 * ∏ i, q (p.2 i) :=
            Finset.sum_sigma' _ _ _
    _ = ∑ p ∈ (Finset.range (n+1)).sigma (fun k => posLists k n),
          theta p.1 * (p.2.map q).prod := by
            refine Finset.sum_bij'
              (fun p hp => ⟨p.1, List.ofFn p.2⟩)
              (fun p hp => by
                simp only [Finset.mem_sigma] at hp
                exact ⟨p.1, tupleOfPosList p.2 hp.2⟩) ?_ ?_ ?_ ?_ ?_
            · intro p hp
              simp only [Finset.mem_sigma] at hp ⊢
              exact ⟨hp.1, Finset.mem_map.mpr ⟨p.2, hp.2, rfl⟩⟩
            · intro p hp
              simp only [Finset.mem_sigma] at hp ⊢
              exact ⟨hp.1, tupleOfPosList_mem p.2 hp.2⟩
            · intro p hp
              rcases p with ⟨k, v⟩
              simp only [Finset.mem_sigma] at hp
              have hlist : List.ofFn v ∈ posLists k n :=
                Finset.mem_map.mpr ⟨v, hp.2, rfl⟩
              change (⟨k, tupleOfPosList (List.ofFn v) hlist⟩ :
                Σ k, Fin k → Nat) = ⟨k, v⟩
              refine Sigma.ext
                (x := (⟨k, tupleOfPosList (List.ofFn v) hlist⟩ : Σ k, Fin k → Nat))
                (y := (⟨k, v⟩ : Σ k, Fin k → Nat)) rfl ?_
              apply heq_of_eq
              apply List.ofFn_injective
              exact ofFn_tupleOfPosList (List.ofFn v) hlist
            · intro p hp
              rcases p with ⟨k, l⟩
              simp only [Finset.mem_sigma] at hp
              change (⟨k, List.ofFn (tupleOfPosList l hp.2)⟩ :
                Σ _k, List Nat) = ⟨k, l⟩
              refine Sigma.ext
                (x := (⟨k, List.ofFn (tupleOfPosList l hp.2)⟩ : Σ _k, List Nat))
                (y := (⟨k, l⟩ : Σ _k, List Nat)) rfl ?_
              exact heq_of_eq (ofFn_tupleOfPosList l hp.2)
            · intro p hp
              rw [List.map_ofFn, List.prod_ofFn]
              rfl

/-- The analytic inverse identity supplies every formal composition
coefficient needed by the degree-15 certificate. -/
theorem formalComposeCoeff_theta_q_through_fifteen :
    ∀ n, n ≤ 15 →
      formalComposeCoeff thetaTaylorCoeff qTaylorCoeff n = targetCoeff n := by
  intro n _hn
  exact formalComposeCoeff_theta_q n

/-- The executable convolution coefficients of the two analytic inverse
germs compose to the identity, at every degree. -/
theorem composeCoeff_theta_q (n : ℕ) :
    composeCoeff thetaTaylorCoeff qTaylorCoeff n = targetCoeff n := by
  rw [composeCoeff_eq_formalComposeCoeff thetaTaylorCoeff qTaylorCoeff
    qTaylorCoeff_zero]
  exact formalComposeCoeff_theta_q n

/-- In particular, all executable composition equations required through
degree 15 hold without numerical assumptions. -/
theorem composeCoeff_theta_q_through_fifteen :
    ∀ n, n ≤ 15 →
      composeCoeff thetaTaylorCoeff qTaylorCoeff n = targetCoeff n := by
  intro n _hn
  exact composeCoeff_theta_q n

def remainderCoeff (theta q : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ (Finset.range (n + 1)).erase 1,
    theta k * powCoeff q k n

noncomputable def inverseStep (theta q : ℕ → ℂ) (n : ℕ) : ℂ :=
  (targetCoeff n - remainderCoeff theta q n) / theta 1

theorem powCoeff_one (q : ℕ → ℂ) (n : ℕ) :
    powCoeff q 1 n = q n := by
  simp only [powCoeff]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b hb hbn
    have hlt : b < n := by
      have := Finset.mem_range.mp hb
      omega
    simp [show n-b ≠ 0 by omega]
  · simp

theorem powCoeff_ratCast (q : ℕ → ℚ) (k n : ℕ) :
    powCoeff (fun i => (q i : ℂ)) k n = (E8InverseJet.powCoeff q k n : ℂ) := by
  induction k generalizing n with
  | zero => by_cases h : n = 0 <;> simp [powCoeff, E8InverseJet.powCoeff, h]
  | succ k ih =>
      simp only [powCoeff, E8InverseJet.powCoeff]
      push_cast
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih]

theorem composeCoeff_ratCast (theta q : ℕ → ℚ) (n : ℕ) :
    composeCoeff (fun i => (theta i : ℂ)) (fun i => (q i : ℂ)) n =
      (E8InverseJet.composeCoeff theta q n : ℂ) := by
  simp only [composeCoeff, E8InverseJet.composeCoeff]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [powCoeff_ratCast]

/-- The executable exact-rational inverse checker supplies the same
composition identities after canonical embedding into `ℂ`. -/
theorem inverseJetCheck_complex_sound {order : ℕ} {theta q : ℕ → ℚ}
    (h : E8InverseJet.inverseJetCheck order theta q = true)
    {n : ℕ} (hn : n ≤ order) :
    composeCoeff (fun i => (theta i : ℂ)) (fun i => (q i : ℂ)) n =
      targetCoeff n := by
  rw [composeCoeff_ratCast,
    E8InverseJet.inverseJetCheck_sound h hn]
  by_cases hn1 : n = 1 <;> simp [targetCoeff, E8InverseJet.targetCoeff, hn1]

/-- In a composition identity, the coefficient of degree `n` is affine in
the new inverse coefficient `q n`; every other term is retained exactly in
`remainderCoeff`. -/
theorem composeCoeff_eq_remainder_add_linear
    (theta q : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    composeCoeff theta q n =
      remainderCoeff theta q n + theta 1 * q n := by
  have hmem : 1 ∈ Finset.range (n+1) := by simp [show 0 < n by omega]
  rw [composeCoeff, ← Finset.sum_erase_add _ _ hmem]
  simp [remainderCoeff, powCoeff_one]

/-- Exact inverse-series recurrence. This statement is independent of any
floating-point approximation and applies uniformly at every positive order. -/
theorem coefficient_eq_inverseStep
    {theta q : ℕ → ℂ} {n : ℕ} (hn : 1 ≤ n)
    (htheta : theta 1 ≠ 0)
    (hcomp : composeCoeff theta q n = targetCoeff n) :
    q n = inverseStep theta q n := by
  rw [composeCoeff_eq_remainder_add_linear theta q hn] at hcomp
  unfold inverseStep
  apply (eq_div_iff htheta).2
  linear_combination hcomp

/-- One premise containing the analytic composition identities yields every
odd source coefficient recurrence from degree seven through degree fifteen. -/
theorem odd_coefficients_seven_to_fifteen_eq_inverseStep
    {theta q : ℕ → ℂ} (htheta : theta 1 ≠ 0)
    (hcomp : ∀ n, n ≤ 15 → composeCoeff theta q n = targetCoeff n) :
    q 7 = inverseStep theta q 7 ∧
    q 9 = inverseStep theta q 9 ∧
    q 11 = inverseStep theta q 11 ∧
    q 13 = inverseStep theta q 13 ∧
    q 15 = inverseStep theta q 15 := by
  exact ⟨coefficient_eq_inverseStep (by norm_num) htheta (hcomp 7 (by norm_num)),
    coefficient_eq_inverseStep (by norm_num) htheta (hcomp 9 (by norm_num)),
    coefficient_eq_inverseStep (by norm_num) htheta (hcomp 11 (by norm_num)),
    coefficient_eq_inverseStep (by norm_num) htheta (hcomp 13 (by norm_num)),
    coefficient_eq_inverseStep (by norm_num) htheta (hcomp 15 (by norm_num))⟩

/-- Exact q7 source-box handoff once the recurrence expression has been
bounded by rational arithmetic. -/
theorem q7_in_sourceBox_of_inverseStep
    {theta : ℕ → ℂ}
    (htheta : theta 1 ≠ 0)
    (hcomp : composeCoeff theta qTaylorCoeff 7 = targetCoeff 7)
    (hstep :
      ‖inverseStep theta qTaylorCoeff 7 - (sourceCenter 7 : ℂ)‖ ≤
        (sourceHalfWidth 7 : ℝ)) :
    ‖qTaylorCoeff 7 - (sourceCenter 7 : ℂ)‖ ≤
      (sourceHalfWidth 7 : ℝ) := by
  rw [coefficient_eq_inverseStep (by norm_num) htheta hcomp]
  exact hstep

end GeneralCK.Certificates.E8AnalyticInverseRecurrence

end


