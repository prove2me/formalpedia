-- Prove2me | Definitions.Def_RPLib_S3_DWSOCC
-- name    : RPLib_S3_DWSOCC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T18:06:20.784199+00:00
-- url     : https://prove2.me/theorems/1f140e68-09f8-473e-a284-da46a1cb9581
-- title:
--   Weight-two Ramanujan-Petersson library: DWSOrdinary (i) conditional on `TateIsogenyPrimeToP`
-- statement:
--   DWSOrdinary (i) conditional on `TateIsogenyPrimeToP`.
--
--   * `card_fib_le` : the trace-`t` pairs of content `f` number at most `#redPrim(D/f²) · L_f / s(D/f²)`:
--     their curves lie in `#Pic` classes (`exists_quotClass_of_tate`), each class inside one `yclSet`
--     (`isoFq_iff_of_quotClass`, `IsoFq.exists_vc`), and `#yclSet · s ≤ L_f` (`card_ycl_mul_sD_le`).
--   * **`pairCount_le_ellCount`** : `p ∤ t ⇒ pairCount F M t ≤ ellCount M 1 t q`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOCA
import Definitions.Def_RPLib_S3_DWSOCB

/-!
# S3-DWS-Ordinary, part CC: **DWSOrdinary (i)** conditional on `TateIsogenyPrimeToP`

* `card_fib_le` : the trace-`t` pairs of content `f` number at most `#redPrim(D/f²) · L_f / s(D/f²)`:
  their curves lie in `#Pic` classes (`exists_quotClass_of_tate`), each class inside one `yclSet`
  (`isoFq_iff_of_quotClass`, `IsoFq.exists_vc`), and `#yclSet · s ≤ L_f` (`card_ycl_mul_sD_le`).
* **`pairCount_le_ellCount`** : `p ∤ t ⇒ pairCount F M t ≤ ellCount M 1 t q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine RPLib.TateNF

namespace RamanujanPetersson.S3.DWSO

open RPLib.Weil RPLib.Isog RPLib.Hasse RPLib.DWS RamanujanPetersson.Hurwitz

section Main

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {L : Type} [Field L] [Algebra F L] [IsAlgClosed L]
  [DecidableEq L] [Algebra.IsAlgebraic F L]

theorem card_fib_le (hT : TateIsogenyPrimeToP.{0}) (p : ℕ) [Fact p.Prime] [CharP F p] {M : ℕ} [NeZero M]
    (hM4 : 4 ≤ M) (hM : (M : F) ≠ 0) {t : ℤ} (hpt : ¬ (p : ℤ) ∣ t) (f : ℤ) (s : Finset (TS F M t))
    (hs : ∀ x ∈ s, ∃ d : OrdData x.W L, d.f = f) :
    s.card * QA.sD ((t ^ 2 - 4 * (Fintype.card F : ℤ)) / f ^ 2) ≤
      (redPrim ((t ^ 2 - 4 * (Fintype.card F : ℤ)) / f ^ 2)).card *
        Lval M t f ((t ^ 2 - 4 * (Fintype.card F : ℤ)) / f ^ 2) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  obtain ⟨d₀, rfl⟩ := hs x₀ hx₀
  have hD₀ := d₀.disc_neg
  have hdiv₀ := div_eq_of_ord d₀
  rw [TS.trace_W] at hdiv₀
  rw [hdiv₀]
  have hdisc : ∀ x ∈ s, ∀ d : OrdData x.W L, d.f = d₀.f →
      tr d.w ^ 2 + 4 * -(deg d.w : ℤ) = tr d₀.w ^ 2 + 4 * -(deg d₀.w : ℤ) := by
    intro x _ d hdf
    have h1 := div_eq_of_ord d
    rw [TS.trace_W, hdf] at h1
    exact h1.symm.trans hdiv₀
  have hord : ∀ x : TS F M t, ¬ ((ringChar F : ℤ) ∣ RPLib.EllFq.trace x.W) := fun x => by
    rw [ringChar.eq F p, TS.trace_W]; exact hpt
  have hπ₀ : d₀.toOAct.ι (⟨d₀.b, d₀.f⟩ : Ord d₀) = piE x₀.W L := by
    rw [OrdData.toOAct_ι]; exact θ_pi d₀
  have hπF : (((⟨d₀.b, d₀.f⟩ : Ord d₀).im.natAbs : ℕ) : F) ≠ 0 := by
    show ((d₀.f.natAbs : ℕ) : F) ≠ 0
    intro h
    rw [CharP.cast_eq_zero_iff F p] at h
    exact not_dvd_f_of_ord d₀ (by rw [TS.trace_W]; exact hpt) (Int.ofNat_dvd_left.mpr h)
  have hcls : ∀ x ∈ s, ∃ c : QA.PicQ hD₀, QuotClass x.W hD₀ d₀.toOAct c := by
    intro x hx
    obtain ⟨d, hdf⟩ := hs x hx
    have hd := hdisc x hx d hdf
    obtain ⟨k, hk⟩ := two_dvd_sub_of_disc hd.symm
    have hb : tr d.w = tr d₀.w + 2 * k := by linarith
    have ha : -(deg d.w : ℤ) = -(deg d₀.w : ℤ) - k ^ 2 - tr d₀.w * k := by
      rw [hb] at hd; linarith
    have hre : 2 * (d₀.b - k * d₀.f) = 2 * d.b := by
      have h1 := d₀.htr
      have h2 := d.htr
      rw [TS.trace_W] at h1
      rw [TS.trace_W, hdf, hb] at h2
      linear_combination h2 - h1
    have hπ₁ : (oactComap d.toOAct (shiftEquiv k hb ha)).ι (⟨d₀.b, d₀.f⟩ : Ord d₀) = piE x.W L := by
      rw [oactComap_ι, shiftEquiv_mk, OrdData.toOAct_ι, ← θ_pi d]
      congr 1
      ext
      · exact mul_left_cancel₀ two_ne_zero hre
      · exact hdf.symm
    have hcard : Nat.card x₀.W.toAffine.Point = Nat.card x.W.toAffine.Point :=
      (numPoints_eq_iff_trace_eq x₀.W x.W).mpr (by rw [TS.trace_W, TS.trace_W])
    exact exists_quotClass_of_tate hT hcard (hord x₀) hD₀ hπ₀ hπ₁ hπF
  haveI : Nonempty (QA.PicQ hD₀) := ⟨(hcls x₀ hx₀).choose⟩
  choose! g hg using hcls
  haveI : Finite (Classes (tr d₀.w ^ 2 + 4 * -(deg d₀.w : ℤ))) :=
    Finite.of_surjective _ (toClass_bijective _).2
  haveI : Finite (QA.PicQ hD₀) := Finite.of_equiv _ (QA.classesEquivPic hD₀)
  letI := Fintype.ofFinite (QA.PicQ hD₀)
  have hcardT : (Finset.univ : Finset (QA.PicQ hD₀)).card =
      (redPrim (tr d₀.w ^ 2 + 4 * -(deg d₀.w : ℤ))).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, QA.card_picQ_eq hD₀,
      ← Nat.card_congr (Equiv.ofBijective _ (toClass_bijective _)), Nat.card_eq_fintype_card,
      Fintype.card_coe]
  have hfib : ∀ x ∈ s, (s.filter (fun y => g y = g x)).card * QA.sD (tr d₀.w ^ 2 + 4 * -(deg d₀.w : ℤ)) ≤
      Lval M t d₀.f (tr d₀.w ^ 2 + 4 * -(deg d₀.w : ℤ)) := by
    intro x hx
    obtain ⟨d, hdf⟩ := hs x hx
    have hle : (s.filter (fun y => g y = g x)).card ≤ Nat.card (yclSet x.W M) := by
      apply card_filter_le_ycl
      intro y hy
      rw [Finset.mem_filter] at hy
      exact IsoFq.exists_vc ((isoFq_iff_of_quotClass hD₀ (hg x hx) (hg y hy.1)).mpr hy.2.symm)
    have hb := card_ycl_mul_sD_le d hM4 hM
    rw [TS.trace_W, hdf, hdisc x hx d hdf] at hb
    exact (Nat.mul_le_mul_right _ hle).trans hb
  have hsD := sD_pos (tr d₀.w ^ 2 + 4 * -(deg d₀.w : ℤ))
  have h := card_le_of_fibers s g Finset.univ (fun x _ => Finset.mem_univ _) _
    (fun x hx => (Nat.le_div_iff_mul_le hsD).mpr (hfib x hx))
  rw [hcardT] at h
  calc s.card * QA.sD _ ≤ (redPrim _).card * (Lval M t d₀.f _ / QA.sD _) * QA.sD _ :=
        Nat.mul_le_mul_right _ h
    _ = (redPrim _).card * (Lval M t d₀.f _ / QA.sD _ * QA.sD _) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)

end Main

/-- **DWSOrdinary (i), conditional on Tate.** For `p ∤ t`: `#{(E,P)/F_q : a_E = t} ≤ ellCount_M(1, t, q)`. -/
theorem pairCount_le_ellCount (hT : TateIsogenyPrimeToP.{0}) {p : ℕ} [Fact p.Prime] {m : ℕ}
    (F : Type) [Field F] [Fintype F] [DecidableEq F] (hq : Fintype.card F = p ^ m) {M : ℕ} [NeZero M]
    (hM4 : 4 ≤ M) (hpM : ¬ p ∣ M) {t : ℤ} (hpt : ¬ (p : ℤ) ∣ t) :
    (pairCount F M t : ℚ) ≤ ellCount M 1 t (p ^ m) := by
  classical
  have : CharP F p := charP_of_card_eq_prime_pow hq
  have hMF : (M : F) ≠ 0 := fun h => hpM ((CharP.cast_eq_zero_iff F p M).mp h)
  have hord : ∀ x : TS F M t, ¬ ((ringChar F : ℤ) ∣ RPLib.EllFq.trace x.W) := fun x => by
    rw [ringChar.eq F p, TS.trace_W]; exact hpt
  have hd : ∀ x : TS F M t, Nonempty (OrdData x.W (AlgebraicClosure F)) := fun x => exists_ordData (hord x)
  have hpc : pairCount F M t = (Finset.univ : Finset (TS F M t)).card := by
    rw [pairCount, Finset.card_univ, Nat.card_eq_fintype_card]
  have hmaps : ∀ x ∈ (Finset.univ : Finset (TS F M t)),
      (Classical.choice (hd x)).f ∈ fset (t ^ 2 - 4 * ((p ^ m : ℕ) : ℤ)) := by
    intro x _
    have h := f_mem_fset_of_ord (Classical.choice (hd x))
    rwa [TS.trace_W, hq] at h
  rw [hpc, ellCount_eq_sum, Finset.card_eq_sum_card_fiberwise (fun x hx => hmaps x hx), Nat.cast_sum]
  apply Finset.sum_le_sum
  intro f _
  have h := card_fib_le (L := AlgebraicClosure F) hT p hM4 hMF hpt f
    (Finset.univ.filter (fun x => (Classical.choice (hd x)).f = f))
    (fun x hx => ⟨Classical.choice (hd x), (Finset.mem_filter.mp hx).2⟩)
  rw [hq] at h
  rw [le_div_iff₀ (by exact_mod_cast sD_pos _)]
  exact_mod_cast h

end RamanujanPetersson.S3.DWSO


