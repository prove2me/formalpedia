-- Prove2me | Definitions.Def_RPLib_S4_CDPack31
-- name    : RPLib_S4_CDPack31
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T08:08:27.484197+00:00
-- url     : https://prove2.me/theorems/8cb86403-4cf5-43bf-84bc-073e7d323ed1
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 31 of 71
-- statement:
--   Part 31 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_GenNu`: S4-JacLaw, file O9 (part GenNu): existence of `ν`-data good at a given point
--   * `Def_RP_JacLaw_GenNS`: S4-JacLaw, file O9e (G4 GenNS): nonspecial sets of points
--   * `Def_RP_JacComplete_PicMv`: The Jacobian (unit S4-JacComplete), part `PicMv` (L20: generators of `Pic⁰` by the moving lemma)
--   * `Def_RP_JacComplete_AJSurj`: The Jacobian (unit S4-JacComplete), part `AJSurj` (L19 route AJ: K-point surjectivity of `Σ [Q_i] - g [P0]`)
--   * `Def_RP_JacFrob_SigPl`: S4-JacFrob, part SigPl: `σ_*` on places, divisors and `Pic` of `F-bar / k-bar`
--   * `Def_RP_JacFrob_BrR`: S4-JacFrob, part BrR (bridge 1): the rings of the levels `F_N` inside those of `F-bar`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack28
import Definitions.Def_RPLib_S4_CDPack26
import Definitions.Def_RPLib_S4_CDPack28c
import Definitions.Def_RPLib_S4_CDPack25
import Definitions.Def_RPLib_S4_CDPack24

/-!
# Curve-duality library package, part 31 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_GenNu`: S4-JacLaw, file O9 (part GenNu): existence of `ν`-data good at a given point
* `Def_RP_JacLaw_GenNS`: S4-JacLaw, file O9e (G4 GenNS): nonspecial sets of points
* `Def_RP_JacComplete_PicMv`: The Jacobian (unit S4-JacComplete), part `PicMv` (L20: generators of `Pic⁰` by the moving lemma)
* `Def_RP_JacComplete_AJSurj`: The Jacobian (unit S4-JacComplete), part `AJSurj` (L19 route AJ: K-point surjectivity of `Σ [Q_i] - g [P0]`)
* `Def_RP_JacFrob_SigPl`: S4-JacFrob, part SigPl: `σ_*` on places, divisors and `Pic` of `F-bar / k-bar`
* `Def_RP_JacFrob_BrR`: S4-JacFrob, part BrR (bridge 1): the rings of the levels `F_N` inside those of `F-bar`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_GenNu =====
section

/-!
# S4-JacLaw, file O9 (part GenNu): existence of `ν`-data good at a given point

* `crossVec_ne_zero_of_finrank_ker`: an `m × (m+1)` matrix with kernel of dimension `≤ 1` has a nonzero cofactor vector.
* `crossVec_evMat_ne_zero`: if every element of `L` vanishing at `a_1..a_d` is a multiple of `s ≠ 0`, the evaluation
  matrix of a basis of `L` has a nonzero cofactor vector.
* `exists_dual_sep`, `exists_lift_li`: separating functionals, lifts of a basis of `B/(s)`.
* `NuData.good_ne_zero_of`: the four factors of `good` at `symPt a` from hyperplane, independence and separation data.
* `exists_nuData`: given `Hn ≥ 0` at infinity of degree `d + g`, `s` with exact pole divisor `Hn`, distinct points
  `a_1..a_d` such that `L(Hn) ∩ B` vanishing at them is the line of `s`, and the `d + g` zeros `Z` of `s`, there is
  `D : NuData` with `D.Hn = Hn`, `symPt a D.good ≠ 0` and `D.sec (symPt a) = c • s`, `c ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

section AbsNu

variable {k : Type*} [Field k]

theorem crossVec_ne_zero_of_finrank_ker {m : ℕ} (M : Matrix (Fin m) (Fin (m + 1)) k)
    (hk : finrank k (LinearMap.ker M.mulVecLin) ≤ 1) : crossVec M ≠ 0 := by
  intro hc
  have hsing : ∀ v : Fin (m + 1) → k, ∃ x : Fin (m + 1) → k, x ≠ 0 ∧ x ∈ LinearMap.ker M.mulVecLin ∧
      v ⬝ᵥ x = 0 := by
    intro v
    have hdet : (Matrix.of (Fin.cons v (fun i => M i) : Fin (m + 1) → Fin (m + 1) → k)).det = 0 := by
      rw [det_cons, hc]
      simp
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine ⟨x, hx0, ?_, ?_⟩
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      funext i
      have := congr_fun hx i.succ
      simpa [Matrix.mulVec] using this
    · have := congr_fun hx 0
      simpa [Matrix.mulVec] using this
  obtain ⟨x0, hx00, hx0k, -⟩ := hsing 0
  obtain ⟨u, hu⟩ := finrank_le_one_iff.mp hk
  have hu0 : (u : Fin (m + 1) → k) ≠ 0 := by
    intro h0
    obtain ⟨c, hc'⟩ := hu ⟨x0, hx0k⟩
    apply hx00
    have := congrArg Subtype.val hc'
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact this.symm
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hu0
  obtain ⟨x, hxne, hxk, hxv⟩ := hsing (Pi.single j 1)
  obtain ⟨c, hcx⟩ := hu ⟨x, hxk⟩
  have hx' : x = c • (u : Fin (m + 1) → k) := by
    have := congrArg Subtype.val hcx
    simpa using this.symm
  rw [hx', single_dotProduct, one_mul, Pi.smul_apply, smul_eq_mul] at hxv
  rcases mul_eq_zero.mp hxv with h | h
  · exact hxne (by rw [hx', h, zero_smul])
  · exact hj h

theorem crossVec_evMat_ne_zero {B : Type*} [CommRing B] [Algebra k B] {d : ℕ} {L : Submodule k B}
    (b : Basis (Fin (d + 1)) k L) (a : Fin d → (B →ₐ[k] k)) {s : B} (hsL : s ∈ L) (hs0 : s ≠ 0)
    (hrank : ∀ t ∈ L, (∀ i, a i t = 0) → ∃ c : k, t = c • s) :
    crossVec (evMat a (fun l => (b l : B))) ≠ 0 := by
  apply crossVec_ne_zero_of_finrank_ker
  have hv0 : b.equivFun ⟨s, hsL⟩ ≠ 0 := by
    intro h0
    apply hs0
    have h1 : (⟨s, hsL⟩ : L) = 0 := b.equivFun.injective (by rw [map_zero]; exact h0)
    exact congrArg Subtype.val h1
  have hle : LinearMap.ker (evMat a (fun l => (b l : B))).mulVecLin ≤ k ∙ b.equivFun ⟨s, hsL⟩ := by
    intro y hy
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hy
    have ht : ((b.equivFun.symm y : L) : B) = ∑ l, y l • (b l : B) := by
      simp only [Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul]
    have hz : ∀ i, a i (b.equivFun.symm y : L) = 0 := by
      intro i
      have h1 := congr_fun hy i
      simp only [Matrix.mulVec, dotProduct, evMat, Matrix.of_apply, Pi.zero_apply] at h1
      rw [ht, map_sum]
      refine (Finset.sum_congr rfl fun l _ => ?_).trans h1
      rw [map_smul, smul_eq_mul, mul_comm]
    obtain ⟨c, hc⟩ := hrank _ (b.equivFun.symm y).2 hz
    rw [Submodule.mem_span_singleton]
    refine ⟨c, ?_⟩
    have h2 : b.equivFun.symm y = c • (⟨s, hsL⟩ : L) := Subtype.ext hc
    calc c • b.equivFun ⟨s, hsL⟩ = b.equivFun (c • (⟨s, hsL⟩ : L)) := (map_smul b.equivFun c _).symm
      _ = b.equivFun (b.equivFun.symm y) := by rw [h2]
      _ = y := b.equivFun.apply_symm_apply y
  calc finrank k (LinearMap.ker (evMat a (fun l => (b l : B))).mulVecLin) ≤
        finrank k (k ∙ b.equivFun ⟨s, hsL⟩) := Submodule.finrank_mono hle
    _ = 1 := finrank_span_singleton hv0

theorem exists_kerData {B : Type*} [CommRing B] [Algebra k B] {d : ℕ} (L : Submodule k B)
    (hL : FiniteDimensional k L) (hfr : finrank k L = d + 1) (a : Fin d → (B →ₐ[k] k)) (ha : Function.Injective a)
    {s : B} (hsL : s ∈ L) (hs0 : s ≠ 0) (hrank : ∀ t ∈ L, (∀ i, a i t = 0) → ∃ c : k, t = c • s) :
    ∃ (h : Fin (d + 1) → B) (χ : Fin d → B) (l0 : Fin (d + 1)), (∀ l, h l ∈ L) ∧ LinearIndependent k h ∧
      symPt a (kerVec k χ h l0) ≠ 0 ∧ ∃ c : k, c ≠ 0 ∧ sPt a χ h = c • s := by
  let b := finBasisSub L hL hfr
  have hcross := crossVec_evMat_ne_zero b a hsL hs0 hrank
  obtain ⟨χ, hχ⟩ := exists_delta a ha
  have hdetχ : (evMat a χ).det = 1 := by
    have he1 : evMat a χ = 1 := by
      ext i m
      rw [evMat, Matrix.of_apply, hχ, Matrix.one_apply]
    rw [he1, Matrix.det_one]
  obtain ⟨l0, hl0⟩ : ∃ l0, crossVec (evMat a (fun l => (b l : B))) l0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hcross (funext hc)
  have hker : symPt a (kerVec k χ (fun l => (b l : B)) l0) ≠ 0 := by
    rw [symPt_kerVec, hdetχ, one_mul]
    exact hl0
  have hli : LinearIndependent k (fun l => (b l : B)) :=
    b.linearIndependent.map' L.subtype (Submodule.ker_subtype _)
  have hS0 := sPt_ne_zero hli hker
  have hSmem : sPt a χ (fun l => (b l : B)) ∈ L :=
    Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (b l).2
  obtain ⟨c, hc⟩ := hrank _ hSmem (apply_sPt a χ _)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hS0 hc
  exact ⟨fun l => (b l : B), χ, l0, fun l => (b l).2, hli, hker, c, hc0, hc⟩

theorem exists_dual_sep {B : Type*} [AddCommGroup B] [Module k B] {n : ℕ} (h : Fin n → B) (W : Submodule k B)
    (v : Fin n → k) (hv : ∑ l, v l • h l ∉ W) :
    ∃ f : (Fin n → k) →ₗ[k] k, f v ≠ 0 ∧ ∀ y : Fin n → k, ∑ l, y l • h l ∈ W → f y = 0 := by
  set P : Submodule k (Fin n → k) := W.comap (Fintype.linearCombination k h) with hP
  have hvP : v ∉ P := hv
  obtain ⟨f, hf, hfP⟩ := P.exists_dual_map_eq_bot_of_notMem hvP inferInstance
  refine ⟨f, hf, fun y hy => ?_⟩
  have h1 : f y ∈ P.map f := Submodule.mem_map_of_mem (p := P) hy
  rw [hfP, Submodule.mem_bot] at h1
  exact h1

theorem exists_lift_li {B : Type*} [CommRing B] [Algebra k B] (s : B) (hfin : Module.Finite k (B ⧸ Ideal.span {s}))
    {N : ℕ} (hN : finrank k (B ⧸ Ideal.span {s}) = N) :
    ∃ e : Fin N → B, LinearIndependent k (fun i => Ideal.Quotient.mkₐ k (Ideal.span {s}) (e i)) := by
  let bq := Module.finBasisOfFinrankEq k (B ⧸ Ideal.span {s}) hN
  choose e he using fun i => Ideal.Quotient.mkₐ_surjective k (Ideal.span {s}) (bq i)
  refine ⟨e, ?_⟩
  have h1 : (fun i => Ideal.Quotient.mkₐ k (Ideal.span {s}) (e i)) = bq := funext he
  rw [h1]
  exact bq.linearIndependent

theorem famDet_res_ne_zero {B : Type*} [CommRing B] [Algebra k B] {S : Type*} [CommRing S] [Algebra k S] {n : ℕ}
    (c : Fin n → S) (h : Fin n → B) {L L' : Submodule k B} (hhL : ∀ l, ∀ y ∈ L', h l * y ∈ L) {a N : ℕ}
    (α : Basis (Fin a) k L') (β : Basis (Fin a ⊕ Fin N) k L) {e : Fin N → B} (he : ∀ i, e i ∈ L) (w : B)
    (hw : ∀ i, w * e i ∈ L) (x : S →ₐ[k] k) (hfin : Module.Finite k (B ⧸ Ideal.span {secAt c h x}))
    (hP : x (famPres c h hhL α β he) ≠ 0)
    (hli : LinearIndependent k fun i => Ideal.Quotient.mkₐ k (Ideal.span {secAt c h x}) (e i))
    (hcard : finrank k (B ⧸ Ideal.span {secAt c h x}) = N) (Z : Finset (B →ₐ[k] k))
    (hZ : ∀ φ ∈ Z, φ (secAt c h x) = 0) (hZc : Z.card = N) (hw0 : Set.InjOn (fun φ : B →ₐ[k] k => φ w) Z) :
    resultant ((famDet c h hhL α β he w hw).map x.toRingHom) (derivative ((famDet c h hhL α β he w hw).map
      x.toRingHom)) N N ≠ 0 := by
  have hmap := map_famDet_eq_li c h hhL α β he w hw x hfin hP hli hcard
  have hchar : LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {secAt c h x})
      (Ideal.Quotient.mkₐ k (Ideal.span {secAt c h x}) w)) = ∏ φ ∈ Z, (X - C (φ w)) :=
    charpoly_eq_prod_of_card (secAt c h x) Z hZ hfin (hZc.trans hcard.symm) w
  have hres := resultant_prod_ne_zero Z w hw0 hP
  rw [hZc] at hres
  rw [hmap]
  erw [hchar]
  exact hres

end AbsNu

section GenNu

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem notMem_Linf_of_exactPoleH {s : Places.Rfin K F} {Hn : Places.Divisor K F} (hs0 : s ≠ 0)
    (hs : ExactPoleH s Hn) (P' : HeightOneSpectrum (Places.Rinf K F)) : s ∉ Linf K F (Hn - ptInf P') := by
  have hs' : incB K F s ≠ 0 := fun h => hs0 (incB_injective (h.trans (map_zero _).symm))
  intro hm
  rw [mem_Linf, mem_LFK hs', Finsupp.le_def] at hm
  have h1 := hm (Sum.inr P')
  have h2 := hs P'
  simp [ptInf] at h1
  omega

theorem divDeg_nsmul (D : Places.Divisor K F) (n : ℕ) :
    Places.Divisor.deg (n • D) = n * Places.Divisor.deg D := by
  induction n with
  | zero => simp [Places.Divisor.deg]
  | succ n ih => rw [succ_nsmul, PlacesK.Divisor.deg_add, ih]; push_cast; ring

variable [IsAlgClosed K]

namespace NuData

variable {d : ℕ} (D : NuData K F d)

/-- **`good` at `symPt a`** from its four ingredients. -/
theorem good_ne_zero_of (a : Fin d → (Places.Rfin K F →ₐ[K] K))
    (hker : symPt a (kerVec K D.χ D.h D.l0) ≠ 0)
    (hlam : ∀ P', D.lam P' (fun l => symPt a (kerVec K D.χ D.h l)) ≠ 0)
    (hli : LinearIndependent K fun i => Ideal.Quotient.mkₐ K (Ideal.span {sPt a D.χ D.h}) (D.e i))
    (Z : Finset (Places.Rfin K F →ₐ[K] K)) (hZ : ∀ φ ∈ Z, φ (sPt a D.χ D.h) = 0)
    (hZc : Z.card = d + genusFK K F) (hw0 : Set.InjOn (fun φ : Places.Rfin K F →ₐ[K] K => φ D.w0) Z) :
    symPt a D.good ≠ 0 := by
  have hs0 : D.sec (symPt a) ≠ 0 := by rw [sec_symPt]; exact sPt_ne_zero D.h_li hker
  have hnot : ∀ P', D.sec (symPt a) ∉ Linf K F (D.Hn - ptInf P') := fun P' hm =>
    hlam P' (D.lam_spec P' _ hm)
  have hex : ExactPoleH (D.sec (symPt a)) D.Hn := exactPoleH_of_not_mem hs0 (D.sec_mem _) hnot
  have hfr : finrank K (Places.Rfin K F ⧸ Ideal.span {D.sec (symPt a)}) = d + genusFK K F := by
    have h := finrank_quot_of_exactPoleH hs0 D.Hn_inf hex
    rw [D.Hn_deg] at h
    exact_mod_cast h
  have hfin : Module.Finite K (Places.Rfin K F ⧸ Ideal.span {D.sec (symPt a)}) := PlacesK.FDQ.finite _ hs0
  have hpres : symPt a (D.pres D.w0) ≠ 0 := by
    rw [NuData.pres, map_famPres]
    exact presDet_ne_zero_of_linIndep (D.sec (symPt a)) _ (D.α D.w0) (D.β D.w0) (D.he D.w0) hs0 hli
  have hres : symPt a (resultant (D.det D.w0) (derivative (D.det D.w0)) (d + genusFK K F)
      (d + genusFK K F)) ≠ 0 := by
    intro h0
    have h1 : resultant ((D.det D.w0).map (symPt a).toRingHom)
        (derivative ((D.det D.w0).map (symPt a).toRingHom)) (d + genusFK K F) (d + genusFK K F) = 0 := by
      rw [derivative_map, resultant_map_map]
      exact h0
    exact famDet_res_ne_zero (kerVec K D.χ D.h) D.h (D.hhL D.w0) (D.α D.w0) (D.β D.w0) (D.he D.w0) D.w0
      (D.hw D.w0) (symPt a) hfin hpres hli hfr Z hZ hZc hw0 h1
  rw [NuData.good, map_mul, map_mul, map_mul, map_prod]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero hker ?_) hpres) hres
  rw [Finset.prod_ne_zero_iff]
  intro P' _
  rw [lamS_apply]
  exact hlam P'

end NuData

set_option maxHeartbeats 400000 in
/-- **Existence of `ν`-data good at a point** (G2). -/
theorem exists_nuData {d : ℕ} (hdg : genusFK K F ≤ d + 1) {Hn : Places.Divisor K F} (hHn : IsInf Hn)
    (hHn0 : 0 ≤ Hn) (hdeg : Places.Divisor.deg Hn = ((d + genusFK K F : ℕ) : ℤ))
    {s : Places.Rfin K F} (hs0 : s ≠ 0) (hs : ExactPoleH s Hn)
    (a : Fin d → (Places.Rfin K F →ₐ[K] K)) (ha : Function.Injective a)
    (hrank : ∀ t ∈ Linf K F Hn, (∀ i, a i t = 0) → ∃ c : K, t = c • s)
    (Z : Finset (Places.Rfin K F →ₐ[K] K)) (hZ : ∀ φ ∈ Z, φ s = 0) (hZc : Z.card = d + genusFK K F) :
    ∃ D : NuData K F d, D.Hn = Hn ∧ symPt a D.good ≠ 0 ∧ ∃ c : K, c ≠ 0 ∧ sPt a D.χ D.h = c • s := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have hfr : finrank K (Linf K F Hn) = d + 1 := by
    have h1 := finrank_Linf_eq hk hHn (by rw [hdeg]; push_cast; omega)
    rw [hdeg] at h1
    push_cast at h1
    omega
  have hsmem : s ∈ Linf K F Hn := mem_Linf_of_exactPoleH hHn hs
  obtain ⟨h, χ, l0, hmem, hli, hker, c, hc0, hc⟩ :=
    exists_kerData (Linf K F Hn) (finiteDimensional_Linf _) hfr a ha hsmem hs0 hrank
  have hS0 : sPt a χ h ≠ 0 := sPt_ne_zero hli hker
  have hSmem : sPt a χ h ∈ Linf K F Hn := by
    rw [hc]
    exact Submodule.smul_mem _ _ hsmem
  have hnot : ∀ P', sPt a χ h ∉ Linf K F (Hn - ptInf P') := by
    intro P' hm
    apply notMem_Linf_of_exactPoleH hs0 hs P'
    have := Submodule.smul_mem _ c⁻¹ hm
    rwa [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  have hex : ExactPoleH (sPt a χ h) Hn := exactPoleH_of_not_mem hS0 hSmem hnot
  have hfin : Module.Finite K (Places.Rfin K F ⧸ Ideal.span {sPt a χ h}) := PlacesK.FDQ.finite _ hS0
  have hfrq : finrank K (Places.Rfin K F ⧸ Ideal.span {sPt a χ h}) = d + genusFK K F := by
    have h1 := finrank_quot_of_exactPoleH hS0 hHn hex
    rw [hdeg] at h1
    exact_mod_cast h1
  obtain ⟨e, he⟩ := exists_lift_li (sPt a χ h) hfin hfrq
  choose lam hlam1 hlam2 using fun P' => exists_dual_sep h (Linf K F (Hn - ptInf P'))
    (fun l => symPt a (kerVec K χ h l)) (hnot P')
  obtain ⟨w0, hw0⟩ := exists_injOn (K := K) Z
  obtain ⟨G, hG0, hGinf, hGe⟩ : ∃ G : Places.Divisor K F, 0 ≤ G ∧ IsInf G ∧
      ∀ i, poleDiv (K := K) (incB K F (e i)) ≤ G :=
    ⟨∑ i, poleDiv (K := K) (incB K F (e i)), Finset.sum_nonneg fun i _ => le_sup_right,
      Finset.sum_induction _ IsInf (fun _ _ h1 h2 => h1.add h2) (fun _ => by simp) fun i _ => isInf_poleDiv (e i),
      fun i => Finset.single_le_sum (f := fun j => poleDiv (K := K) (incB K F (e j))) (fun j _ => le_sup_right)
        (Finset.mem_univ i)⟩
  refine ⟨⟨Hn, hHn, hdeg, h, hmem, hli, χ, l0, lam, hlam2, Hn + G + (2 * genusFK K F) • Hn,
    (hHn.add hGinf).add (hHn.nsmul _), ?_, e, fun i => ?_, w0⟩, rfl, ?_, c, hc0, hc⟩
  · have e1 : Hn + G + (2 * genusFK K F) • Hn - Hn = G + (2 * genusFK K F) • Hn := by abel
    rw [e1, PlacesK.Divisor.deg_add, divDeg_nsmul, hdeg]
    have h0 := deg_nonneg_of_nonneg hG0
    push_cast
    nlinarith [sq_nonneg ((genusFK K F : ℤ) - 1), sq_nonneg (genusFK K F : ℤ),
      mul_nonneg (Nat.cast_nonneg (α := ℤ) (genusFK K F)) (Nat.cast_nonneg (α := ℤ) d)]
  · refine Linf_mono ?_ (mem_Linf_poleDiv (e i))
    have h1 : poleDiv (K := K) (incB K F (e i)) ≤ G := hGe i
    have h2 : G ≤ Hn + G := le_add_of_nonneg_left hHn0
    have h3 : Hn + G ≤ Hn + G + (2 * genusFK K F) • Hn := le_add_of_nonneg_right (nsmul_nonneg hHn0 _)
    exact h1.trans (h2.trans h3)
  · exact NuData.good_ne_zero_of _ a hker hlam1 he Z (fun φ hφ => by
      show φ (sPt a χ h) = 0
      rw [hc, map_smul, hZ φ hφ, smul_zero]) hZc hw0

end GenNu

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacLaw_GenNS =====
section

/-!
# S4-JacLaw, file O9e (G4 GenNS): nonspecial sets of points

Pure Riemann-Roch on `L(D) = LFK K F D` (no chart algebra):
* `LFK_inf`: `L(D1 ⊓ D2) = L(D1) ⊓ L(D2)`; `ellFK_mono`; `ellFK_step`:
  `ℓ(D + P) + ℓ(D') ≤ ℓ(D' + P) + ℓ(D)` for `D ≤ D'`, `D'(P) = D(P)`.
* `Zdiv_empty`, `Zdiv_insert`, `deg_Zdiv` (`deg (Zdiv S) = #S`); `one_mem_LFK`; `const_of_ellFK_eq_one`.
* the greedy step `exists_add_nonspecial`, `exists_nonspecial_card`;
* `IsNS C` (every `f ∈ L(Zdiv C)` is a constant, the `hC` input of `hrank_of_const`);
  **`exists_nonspecial_avoid`**: a pool `T` with `2g + #X ≤ #T + 1` contains a nonspecial `g`-set disjoint from `X`;
  **`exists_four_nonspecial`**: a pool with `5g ≤ #T + 1` contains four pairwise disjoint nonspecial `g`-sets.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

section GenNS

open Classical

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

theorem ellFK_def (D : Places.Divisor K F) : ellFK K F D = finrank K (LFK K F D) := rfl

theorem LFK_inf (D1 D2 : Places.Divisor K F) : LFK K F (D1 ⊓ D2) = LFK K F D1 ⊓ LFK K F D2 := by
  ext f
  show f ∈ (ffDataK K F).LD (D1 ⊓ D2) ↔ f ∈ (ffDataK K F).LD D1 ⊓ (ffDataK K F).LD D2
  rw [Submodule.mem_inf, Data.mem_LD, Data.mem_LD, Data.mem_LD]
  constructor
  · intro h
    refine ⟨fun i => (h i).trans ?_, fun i => (h i).trans ?_⟩
    · rw [Finsupp.inf_apply, WithZero.exp_le_exp]; exact inf_le_left
    · rw [Finsupp.inf_apply, WithZero.exp_le_exp]; exact inf_le_right
  · rintro ⟨h1, h2⟩ i
    rw [Finsupp.inf_apply]
    rcases le_total (D1 i) (D2 i) with h | h
    · rw [inf_of_le_left h]; exact h1 i
    · rw [inf_of_le_right h]; exact h2 i

theorem ellFK_mono {D D' : Places.Divisor K F} (h : D ≤ D') : ellFK K F D ≤ ellFK K F D' := by
  have := finiteDimensional_LFK (K := K) (F := F) D'
  rw [ellFK_def, ellFK_def]
  exact Submodule.finrank_mono ((ffDataK K F).LD_mono h)

/-- The dimension step: `ℓ(D + P) + ℓ(D') ≤ ℓ(D' + P) + ℓ(D)` for `D ≤ D'` with `D'(P) = D(P)`. -/
theorem ellFK_step {D D' : Places.Divisor K F} (P : Places.Place K F) (hle : D ≤ D') (hP : D' P = D P) :
    ellFK K F (D + Finsupp.single P 1) + ellFK K F D' ≤ ellFK K F (D' + Finsupp.single P 1) + ellFK K F D := by
  have hinf : (D + Finsupp.single P 1) ⊓ D' = D := by
    ext Q
    rw [Finsupp.inf_apply, Finsupp.add_apply]
    by_cases hQ : Q = P
    · rw [hQ, Finsupp.single_eq_same, hP]
      exact inf_of_le_right (by omega)
    · rw [Finsupp.single_apply, if_neg (Ne.symm hQ), add_zero]
      exact inf_of_le_left (hle Q)
  have h0 : (0 : Places.Divisor K F) ≤ Finsupp.single P 1 := Finsupp.single_nonneg.2 zero_le_one
  have hsup : LFK K F (D + Finsupp.single P 1) ⊔ LFK K F D' ≤ LFK K F (D' + Finsupp.single P 1) :=
    sup_le ((ffDataK K F).LD_mono (add_le_add hle le_rfl))
      ((ffDataK K F).LD_mono (le_add_of_nonneg_right h0))
  have := finiteDimensional_LFK (K := K) (F := F) (D + Finsupp.single P 1)
  have := finiteDimensional_LFK (K := K) (F := F) D'
  have := finiteDimensional_LFK (K := K) (F := F) (D' + Finsupp.single P 1)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LFK K F (D + Finsupp.single P 1)) (LFK K F D')
  rw [← LFK_inf, hinf] at h1
  have h2 := Submodule.finrank_mono hsup
  rw [ellFK_def, ellFK_def, ellFK_def, ellFK_def]
  omega

variable [IsAlgClosed K]

theorem Zdiv_empty : Zdiv (∅ : Finset (Places.Rfin K F →ₐ[K] K)) = 0 := Finset.sum_empty

theorem Zdiv_insert {S : Finset (Places.Rfin K F →ₐ[K] K)} {φ : Places.Rfin K F →ₐ[K] K} (h : φ ∉ S) :
    Zdiv (insert φ S) = Zdiv S + Finsupp.single (Sum.inl (ptP φ)) 1 := by
  unfold Zdiv
  rw [Finset.sum_insert h, add_comm]

theorem one_mem_LFK {D : Places.Divisor K F} (hD : 0 ≤ D) : (1 : F) ∈ LFK K F D := by
  have h : (1 : F) ∈ LFK K F 0 := by
    rw [LFK_zero_eq]
    exact (Subalgebra.mem_toSubmodule _).2 (Subalgebra.one_mem _)
  exact (ffDataK K F).LD_mono hD h

/-- `ℓ(D) = 1` for `D ≥ 0`: every element of `L(D)` is a constant. -/
theorem const_of_ellFK_eq_one {D : Places.Divisor K F} (hD : 0 ≤ D) (h : ellFK K F D = 1) :
    ∀ f ∈ LFK K F D, ∃ c : K, f = algebraMap K F c := by
  intro f hf
  have h1 : (⟨1, one_mem_LFK hD⟩ : LFK K F D) ≠ 0 := fun e => one_ne_zero (congrArg Subtype.val e)
  rw [ellFK_def] at h
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ h1).1 h ⟨f, hf⟩
  refine ⟨c, ?_⟩
  have e : c • (1 : F) = f := congrArg Subtype.val hc
  rw [← e, Algebra.smul_def, mul_one]

variable (K F) in
/-- `C` is nonspecial: `L(Zdiv C)` is the constants. -/
def IsNS (C : Finset (Places.Rfin K F →ₐ[K] K)) : Prop :=
  ∀ f ∈ LFK K F (Zdiv C), ∃ c : K, f = algebraMap K F c

theorem ellFK_union_ge {C T : Finset (Places.Rfin K F →ₐ[K] K)} (hCT : Disjoint C T)
    (h1 : ellFK K F (Zdiv C) = 1) (h2 : ∀ P ∈ T, 2 ≤ ellFK K F (Zdiv (insert P C))) :
    ∀ S ⊆ T, 1 + S.card ≤ ellFK K F (Zdiv (C ∪ S)) := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; rw [Finset.union_empty, Finset.card_empty, h1]
  | insert P S hP ih =>
    intro hS
    have hPT : P ∈ T := hS (Finset.mem_insert_self P S)
    have hST : S ⊆ T := (Finset.subset_insert P S).trans hS
    have hPC : P ∉ C := Finset.disjoint_right.1 hCT hPT
    have hPCS : P ∉ C ∪ S := by
      rw [Finset.mem_union]; exact fun h => h.elim hPC hP
    have hle : Zdiv C ≤ Zdiv (C ∪ S) := by
      rw [Zdiv_union (Finset.disjoint_of_subset_right hST hCT)]
      exact le_add_of_nonneg_right (Zdiv_nonneg S)
    have hval : Zdiv (C ∪ S) (Sum.inl (ptP P)) = Zdiv C (Sum.inl (ptP P)) := by
      rw [Zdiv_inl_ptP, Zdiv_inl_ptP, if_neg hPCS, if_neg hPC]
    have key := ellFK_step (Sum.inl (ptP P)) hle hval
    rw [← Zdiv_insert hPC, ← Zdiv_insert hPCS, h1] at key
    rw [Finset.union_insert, Finset.card_insert_of_notMem hP]
    have := ih hST
    have := h2 P hPT
    omega

theorem deg_Zdiv (S : Finset (Places.Rfin K F →ₐ[K] K)) : (Zdiv S).deg = (S.card : ℤ) := by
  induction S using Finset.induction_on with
  | empty =>
    rw [Zdiv_empty, Finset.card_empty]
    simp [Places.Divisor.deg]
  | insert a S ha ih =>
    have hd : Places.Place.deg (Sum.inl (ptP a) : Places.Place K F) = 1 := deg_eq_one (K := K) (ptP a)
    rw [Zdiv_insert ha, PlacesK.Divisor.deg_add, ih, PlacesK.Divisor.deg_single, hd,
      Finset.card_insert_of_notMem ha]
    push_cast; ring

theorem ellFK_zero' : ellFK K F 0 = 1 := ellFK_zero_of_bot constField_eq_bot'

/-- **Greedy step**: a nonspecial `C` with `#C < g` and a disjoint pool `T` with `#C + #T ≥ 2g - 1`
has a point `P ∈ T` with `C + P` nonspecial. -/
theorem exists_add_nonspecial {C T : Finset (Places.Rfin K F →ₐ[K] K)} (hCT : Disjoint C T)
    (h1 : ellFK K F (Zdiv C) = 1) (hC : C.card < genusFK K F) (hT : 2 * genusFK K F ≤ C.card + T.card + 1) :
    ∃ P ∈ T, ellFK K F (Zdiv (insert P C)) = 1 := by
  by_contra hne0
  have hne : ∀ P ∈ T, ellFK K F (Zdiv (insert P C)) ≠ 1 := fun P hP h => hne0 ⟨P, hP, h⟩
  have h2 : ∀ P ∈ T, 2 ≤ ellFK K F (Zdiv (insert P C)) := by
    intro P hP
    have := hne P hP
    have hPC : P ∉ C := Finset.disjoint_right.1 hCT hP
    have hm : ellFK K F (Zdiv C) ≤ ellFK K F (Zdiv (insert P C)) := ellFK_mono (by
      rw [Zdiv_insert hPC]; exact le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one))
    omega
  have hge := ellFK_union_ge hCT h1 h2 T (Finset.Subset.refl T)
  have hdeg : (Zdiv (C ∪ T)).deg = ((C.card + T.card : ℕ) : ℤ) := by
    rw [deg_Zdiv, Finset.card_union_of_disjoint hCT]
  have hrr := ellFK_eq_of_deg (constField_eq_bot' (K := K) (F := F)) (D := Zdiv (C ∪ T))
    (by rw [hdeg]; push_cast; omega)
  rw [hdeg] at hrr
  push_cast at hrr
  omega

theorem exists_nonspecial_card (T : Finset (Places.Rfin K F →ₐ[K] K)) (hT : 2 * genusFK K F ≤ T.card + 1) :
    ∀ i ≤ genusFK K F, ∃ C ⊆ T, C.card = i ∧ ellFK K F (Zdiv C) = 1 := by
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨∅, Finset.empty_subset _, Finset.card_empty, by rw [Zdiv_empty]; exact ellFK_zero'⟩
  | succ i ih =>
    intro hi
    obtain ⟨C, hCT, hCc, hC1⟩ := ih (by omega)
    have hdis : Disjoint C (T \ C) := Finset.disjoint_sdiff
    have hcard : (T \ C).card + C.card = T.card := Finset.card_sdiff_add_card_eq_card hCT
    obtain ⟨P, hP, hP1⟩ := exists_add_nonspecial hdis hC1 (by omega) (by omega)
    rw [Finset.mem_sdiff] at hP
    exact ⟨insert P C, Finset.insert_subset hP.1 hCT, by rw [Finset.card_insert_of_notMem hP.2, hCc], hP1⟩

/-- **A nonspecial `g`-set avoiding `X`** inside any pool `T` with `2g + #X ≤ #T + 1`. -/
theorem exists_nonspecial_avoid (T X : Finset (Places.Rfin K F →ₐ[K] K))
    (hT : 2 * genusFK K F + X.card ≤ T.card + 1) :
    ∃ C ⊆ T, Disjoint C X ∧ C.card = genusFK K F ∧ IsNS K F C := by
  have h := Finset.le_card_sdiff X T
  obtain ⟨C, hC, hCc, hC1⟩ := exists_nonspecial_card (T \ X) (by omega) _ le_rfl
  refine ⟨C, fun x hx => (Finset.mem_sdiff.1 (hC hx)).1,
    Finset.disjoint_left.2 fun x hx hxX => (Finset.mem_sdiff.1 (hC hx)).2 hxX, hCc,
    const_of_ellFK_eq_one (Zdiv_nonneg C) hC1⟩

/-- **Four pairwise disjoint nonspecial `g`-sets** in any pool `T` with `5g ≤ #T + 1`. -/
theorem exists_four_nonspecial (T : Finset (Places.Rfin K F →ₐ[K] K)) (hT : 5 * genusFK K F ≤ T.card + 1) :
    ∃ a b E c : Finset (Places.Rfin K F →ₐ[K] K), a ⊆ T ∧ b ⊆ T ∧ E ⊆ T ∧ c ⊆ T ∧
      a.card = genusFK K F ∧ b.card = genusFK K F ∧ E.card = genusFK K F ∧ c.card = genusFK K F ∧
      Disjoint a b ∧ Disjoint a E ∧ Disjoint a c ∧ Disjoint b E ∧ Disjoint b c ∧ Disjoint E c ∧
      IsNS K F a ∧ IsNS K F b ∧ IsNS K F E ∧ IsNS K F c := by
  obtain ⟨a, ha, -, hac, haN⟩ := exists_nonspecial_avoid T ∅ (by rw [Finset.card_empty]; omega)
  obtain ⟨b, hb, hba, hbc, hbN⟩ := exists_nonspecial_avoid T a (by omega)
  obtain ⟨E, hE, hEab, hEc, hEN⟩ := exists_nonspecial_avoid T (a ∪ b)
    (by have := Finset.card_union_le a b; omega)
  obtain ⟨c, hc, hcabE, hcc, hcN⟩ := exists_nonspecial_avoid T (a ∪ b ∪ E)
    (by have := Finset.card_union_le (a ∪ b) E; have := Finset.card_union_le a b; omega)
  simp only [Finset.disjoint_union_right] at hEab hcabE
  exact ⟨a, b, E, c, ha, hb, hE, hc, hac, hbc, hEc, hcc, hba.symm, hEab.1.symm, hcabE.1.1.symm,
    hEab.2.symm, hcabE.1.2.symm, hcabE.2.symm, haN, hbN, hEN, hcN⟩

end GenNS

end RamanujanPetersson.JacLaw

end

-- ===== S4.Def_RP_JacComplete_PicMv =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `PicMv` (L20: generators of `Pic⁰` by the moving lemma)

Over an algebraically closed `K`:
* `placeDeg_one`, `deg_single_one`, `eq_zero_of_nonneg_of_deg` (an effective divisor of degree `0` is `0`);
* `exists_move` (Riemann-Roch moving lemma): for a finite set `S` of places, `P ∈ S` and `Q0 ∉ S` there is `h ≠ 0` with
  `div h = E + P - (2g+1) Q0`, `E ≥ 0` vanishing on `S`;
* `pic0_le_of_gen`: a subgroup `R` of `Pic` containing `[v] - [Q0]` for all `v ∉ S` contains `Pic⁰`;
* `clsK_eq_zero_of_genus_zero`: for `g = 0` every degree-`0` class is trivial.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacLaw RamanujanPetersson.RR

section PicMv

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem placeDeg_one (v : Places.Place K F) : v.deg = 1 := by
  rcases v with P | P
  · exact deg_eq_one (K := K) P
  · exact deg_eq_one (K := K) P

theorem deg_single_one (v : Places.Place K F) :
    Places.Divisor.deg (Finsupp.single v (1 : ℤ) : Places.Divisor K F) = 1 := by
  rw [PlacesK.Divisor.deg_single, placeDeg_one]; norm_num

theorem deg_single' (v : Places.Place K F) (n : ℤ) :
    Places.Divisor.deg (Finsupp.single v n : Places.Divisor K F) = n := by
  rw [PlacesK.Divisor.deg_single, placeDeg_one]; norm_num

/-- An effective divisor of degree `0` is `0`. -/
theorem eq_zero_of_nonneg_of_deg {E : Places.Divisor K F} (hE : 0 ≤ E) (hd : E.deg = 0) : E = 0 := by
  have h1 : E.deg = ∑ v ∈ E.support, E v := by
    rw [Places.Divisor.deg, Finsupp.sum]
    exact Finset.sum_congr rfl fun v _ => by rw [placeDeg_one]; simp
  rw [h1] at hd
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => by simpa using Finsupp.le_def.1 hE v)).1 hd
  ext v
  rw [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hv
  exact hv (h2 v (Finsupp.mem_support_iff.2 hv))

/-- **Moving lemma** (Riemann-Roch): `div h = E + P - (2g+1) Q0` with `E ≥ 0` vanishing on `S`. -/
theorem exists_move (S : Finset (Places.Place K F)) {P Q0 : Places.Place K F} (hP : P ∈ S) (hQ0 : Q0 ∉ S) :
    ∃ h : F, h ≠ 0 ∧ ∃ E : Places.Divisor K F, 0 ≤ E ∧ (∀ v ∈ S, E v = 0) ∧
      PlacesK.div h = E + Finsupp.single P 1 - Finsupp.single Q0 (2 * (genusFK K F : ℤ) + 1) := by
  classical
  set D : Places.Divisor K F := Finsupp.single Q0 (2 * (genusFK K F : ℤ) + 1) - Finsupp.single P 1 with hD
  have hdegD : D.deg = 2 * (genusFK K F : ℤ) := by
    rw [hD, PlacesK.Divisor.deg_sub, deg_single', deg_single']; ring
  have hk := constField_eq_bot' (K := K) (F := F)
  have hell : (ellFK K F D : ℤ) = genusFK K F + 1 := by
    rw [ellFK_eq_of_deg hk (by rw [hdegD]; omega), hdegD]; ring
  have hellv : ∀ v : Places.Place K F, (ellFK K F (D - Finsupp.single v 1) : ℤ) = genusFK K F := by
    intro v
    have hd : (D - Finsupp.single v 1).deg = 2 * (genusFK K F : ℤ) - 1 := by
      rw [PlacesK.Divisor.deg_sub, hdegD, deg_single_one]
    rw [ellFK_eq_of_deg hk (by rw [hd]), hd]; ring
  let p : S → Submodule K (LFK K F D) := fun v =>
    (LFK K F (D - Finsupp.single v.1 1)).comap (LFK K F D).subtype
  have hne : ∀ v : S, p v ≠ ⊤ := by
    intro v hv
    have hle : LFK K F D ≤ LFK K F (D - Finsupp.single v.1 1) := by
      intro x hx
      have hm : (⟨x, hx⟩ : LFK K F D) ∈ p v := by rw [hv]; exact Submodule.mem_top
      exact Submodule.mem_comap.1 hm
    have := finiteDimensional_LFK (K := K) (F := F) (D - Finsupp.single v.1 1)
    have h1 := Submodule.finrank_mono hle
    have e1 := ellFK_def (K := K) (F := F) D
    have e2 := ellFK_def (K := K) (F := F) (D - Finsupp.single v.1 1)
    have h2 := hellv v.1
    omega
  obtain ⟨⟨h, hhD⟩, hh⟩ : ∃ x : LFK K F D, ∀ v : S, x ∉ p v := by
    by_contra hcon
    push_neg at hcon
    have hcov : ⋃ v, (p v : Set (LFK K F D)) = Set.univ :=
      Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (hcon x)
    obtain ⟨v, hv⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
    exact hne v hv
  have hh' : ∀ v ∈ S, h ∉ LFK K F (D - Finsupp.single v 1) := fun v hv hm =>
    hh ⟨v, hv⟩ (Submodule.mem_comap.2 hm)
  have h0 : h ≠ 0 := fun e => hh' P hP (e ▸ Submodule.zero_mem _)
  have hE := (mem_LFK h0).1 hhD
  refine ⟨h, h0, PlacesK.div h + D, hE, ?_, by rw [hD]; abel⟩
  intro v hv
  have hn := hh' v hv
  rw [mem_LFK h0] at hn
  by_contra hne0
  apply hn
  rw [Finsupp.le_def] at hE ⊢
  intro w
  have hw0 := hE w
  simp only [Finsupp.coe_add, Finsupp.coe_sub, Finsupp.coe_zero, Pi.add_apply, Pi.sub_apply,
    Pi.zero_apply] at hw0 hne0 ⊢
  by_cases hw : w = v
  · subst hw
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hw)]
    omega

/-- `D ↦ [D] - deg D • [Q0]`. -/
noncomputable def clsQ (Q0 : Places.Place K F) : Places.Divisor K F →+ PicK K F :=
  AddMonoidHom.mk' (fun D => clsK K F D - D.deg • clsK K F (Finsupp.single Q0 1)) fun D E => by
    have h1 : clsK K F (D + E) = clsK K F D + clsK K F E := QuotientAddGroup.mk_add _ D E
    beta_reduce
    rw [h1, PlacesK.Divisor.deg_add, add_zsmul]
    abel

theorem clsQ_apply (Q0 : Places.Place K F) (D : Places.Divisor K F) :
    clsQ Q0 D = clsK K F D - D.deg • clsK K F (Finsupp.single Q0 1) := rfl

/-- **Generators of `Pic⁰`**: a subgroup containing `[v] - [Q0]` for every `v ∉ S` contains `Pic⁰`. -/
theorem pic0_le_of_gen (R : AddSubgroup (PicK K F)) (Q0 : Places.Place K F) (S : Finset (Places.Place K F))
    (hQ0 : Q0 ∉ S)
    (hU : ∀ v, v ∉ S → clsK K F (Finsupp.single v 1) - clsK K F (Finsupp.single Q0 1) ∈ R) :
    Pic0K K F ≤ R := by
  classical
  let R' : AddSubgroup (Places.Divisor K F) := R.comap (clsQ Q0)
  have hsing : ∀ v, v ∉ S → Finsupp.single v (1 : ℤ) ∈ R' := fun v hv => by
    show clsQ Q0 (Finsupp.single v 1) ∈ R
    rw [clsQ_apply, deg_single_one, one_zsmul]
    exact hU v hv
  have hsupp : ∀ E : Places.Divisor K F, (∀ v ∈ S, E v = 0) → E ∈ R' := by
    intro E hE
    rw [← Finsupp.sum_single E]
    refine AddSubmonoidClass.finsuppSum_mem R' E _ fun v hv => ?_
    rw [← Finsupp.smul_single_one]
    exact R'.zsmul_mem (hsing v fun hvS => hv (hE v hvS)) _
  have hdiv : ∀ h : F, h ≠ 0 → PlacesK.div h ∈ R' := fun h hh => by
    show clsQ Q0 (PlacesK.div h) ∈ R
    rw [clsQ_apply, PlacesK.deg_div hh, zero_zsmul, sub_zero]
    have : clsK K F (PlacesK.div h) = 0 := (QuotientAddGroup.eq_zero_iff _).2 (div_mem_PrincK K F hh)
    rw [this]
    exact R.zero_mem
  have hQ : Finsupp.single Q0 (1 : ℤ) ∈ R' := by
    show clsQ Q0 _ ∈ R
    rw [clsQ_apply, deg_single_one, one_zsmul, sub_self]
    exact R.zero_mem
  have hall : ∀ P, Finsupp.single P (1 : ℤ) ∈ R' := by
    intro P
    by_cases hPQ : P = Q0
    · rw [hPQ]; exact hQ
    obtain ⟨h, hh, E, -, hES, he⟩ := exists_move (insert P S) (Finset.mem_insert_self P S)
      (by rw [Finset.mem_insert, not_or]; exact ⟨Ne.symm hPQ, hQ0⟩)
    have hE : E ∈ R' := hsupp E fun v hv => hES v (Finset.mem_insert_of_mem hv)
    have key : Finsupp.single P (1 : ℤ) =
        PlacesK.div h - E + Finsupp.single Q0 (2 * (genusFK K F : ℤ) + 1) := by
      rw [he]; abel
    rw [key]
    refine R'.add_mem (R'.sub_mem (hdiv h hh) hE) ?_
    rw [← Finsupp.smul_single_one]
    exact R'.zsmul_mem hQ _
  intro c hc
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hD : D.deg = 0 := by rw [← degPicK_clsK]; exact (mem_Pic0K K F).1 hc
  have hDR : D ∈ R' := by
    rw [← Finsupp.sum_single D]
    refine AddSubmonoidClass.finsuppSum_mem R' D _ fun v _ => ?_
    rw [← Finsupp.smul_single_one]
    exact R'.zsmul_mem (hall v) _
  have h3 : clsQ Q0 D ∈ R := hDR
  rw [clsQ_apply, hD, zero_zsmul, sub_zero] at h3
  exact h3

/-- For `g = 0` every class of degree `0` is trivial. -/
theorem clsK_eq_zero_of_genus_zero (hg : genusFK K F = 0) {D : Places.Divisor K F} (hD : D.deg = 0) :
    clsK K F D = 0 := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have hell : (ellFK K F D : ℤ) = 1 := by
    rw [ellFK_eq_of_deg hk (by rw [hD, hg]; norm_num), hD, hg]; norm_num
  have hpos : LFK K F D ≠ ⊥ := by
    intro hb
    have e := ellFK_def (K := K) (F := F) D
    rw [hb, finrank_bot] at e
    omega
  obtain ⟨h, hhD, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpos
  have hz : PlacesK.div h + D = 0 := eq_zero_of_nonneg_of_deg ((mem_LFK h0).1 hhD)
    (by rw [PlacesK.Divisor.deg_add, PlacesK.deg_div h0, hD, add_zero])
  have hD' : D = PlacesK.div h⁻¹ := by
    rw [divK_inv K h0, ← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact hz
  exact (QuotientAddGroup.eq_zero_iff D).2 ⟨h⁻¹, inv_ne_zero h0, hD'.symm⟩

end PicMv

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacComplete_AJSurj =====
section

/-!
# The Jacobian (unit S4-JacComplete), part `AJSurj` (L19 route AJ: K-point surjectivity of `Σ [Q_i] - g [P0]`)

Over an algebraically closed `K`, with `g` the genus:
* `exists_sum_single_of_nonneg`: an effective divisor of degree `n` is a sum of `n` places;
* **`exists_eff_rep P0 hc`**: every class `c ∈ Pic⁰` is `Σ_{i < g} [t_i] - g • [P0]` (Riemann's inequality).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Module

namespace RamanujanPetersson.JacComplete

open RamanujanPetersson.JacLaw RamanujanPetersson.RR

section AJSurj

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem deg_zero' : Places.Divisor.deg (0 : Places.Divisor K F) = 0 := Finsupp.sum_zero_index

/-- An effective divisor of degree `n` is a sum of `n` places. -/
theorem exists_sum_single_of_nonneg : ∀ (n : ℕ) {D : Places.Divisor K F}, 0 ≤ D → D.deg = n →
    ∃ t : Fin n → Places.Place K F, D = ∑ i, Finsupp.single (t i) (1 : ℤ)
  | 0, D, hD, hd => ⟨Fin.elim0, by
      rw [eq_zero_of_nonneg_of_deg hD (by simpa using hd)]; simp⟩
  | n + 1, D, hD, hd => by
    classical
    have hne : D ≠ 0 := by
      rintro rfl
      rw [deg_zero'] at hd
      omega
    obtain ⟨v, hv⟩ : ∃ v, D v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (Finsupp.ext h)
    have hv0 : 0 ≤ D v := by
      have := Finsupp.le_def.1 hD v
      simpa using this
    have hD' : 0 ≤ D - Finsupp.single v 1 := by
      rw [Finsupp.le_def]
      intro w
      have hw0 := Finsupp.le_def.1 hD w
      simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_sub, Pi.sub_apply] at hw0 ⊢
      by_cases hw : w = v
      · subst hw
        rw [Finsupp.single_eq_same]
        omega
      · rw [Finsupp.single_apply, if_neg (Ne.symm hw)]
        omega
    have hd' : (D - Finsupp.single v 1).deg = ((n : ℕ) : ℤ) := by
      rw [PlacesK.Divisor.deg_sub, hd, deg_single_one]
      push_cast
      ring
    obtain ⟨t, ht⟩ := exists_sum_single_of_nonneg n hD' hd'
    refine ⟨Fin.cons v t, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← ht]
    abel

/-- **Every class in `Pic⁰` is `Σ_{i < g} [t_i] - g • [P0]`** (Riemann's inequality `ℓ(D + g P0) ≥ 1`). -/
theorem exists_eff_rep (P0 : Places.Place K F) {c : PicK K F} (hc : c ∈ Pic0K K F) :
    ∃ t : Fin (genusFK K F) → Places.Place K F,
      c = ∑ i, clsK K F (Finsupp.single (t i) 1) -
        (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) := by
  obtain ⟨D0, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hD0 : D0.deg = 0 := by rw [← degPicK_clsK]; exact (mem_Pic0K K F).1 hc
  set E : Places.Divisor K F := D0 + Finsupp.single P0 (genusFK K F : ℤ) with hEdef
  have hdE : E.deg = genusFK K F := by
    rw [hEdef, PlacesK.Divisor.deg_add, hD0, deg_single', zero_add]
  have hk := constField_eq_bot' (K := K) (F := F)
  have hell := riemann_inequalityFK' hk E
  have hpos : LFK K F E ≠ ⊥ := by
    intro hb
    have e := ellFK_def (K := K) (F := F) E
    rw [hb, finrank_bot] at e
    rw [hdE, e] at hell
    push_cast at hell
    omega
  obtain ⟨f, hfE, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hpos
  have hD := (mem_LFK hf0).1 hfE
  obtain ⟨t, ht⟩ := exists_sum_single_of_nonneg (genusFK K F) hD
    (by rw [PlacesK.Divisor.deg_add, PlacesK.deg_div hf0, hdE, zero_add])
  refine ⟨t, ?_⟩
  have hadd : ∀ A B : Places.Divisor K F, clsK K F (A + B) = clsK K F A + clsK K F B :=
    fun A B => QuotientAddGroup.mk_add _ A B
  have h1 : clsK K F (PlacesK.div f) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 (div_mem_PrincK K F hf0)
  have h2 : clsK K F (∑ i, Finsupp.single (t i) (1 : ℤ)) = ∑ i, clsK K F (Finsupp.single (t i) 1) :=
    map_sum (QuotientAddGroup.mk' (PrincK K F)) _ _
  have h3 : clsK K F (Finsupp.single P0 (genusFK K F : ℤ)) =
      (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) := by
    rw [← Finsupp.smul_single_one]
    exact map_zsmul (QuotientAddGroup.mk' (PrincK K F)) _ _
  have h4 : clsK K F (PlacesK.div f + E) =
      clsK K F D0 + (genusFK K F : ℤ) • clsK K F (Finsupp.single P0 1) := by
    rw [hadd, h1, zero_add, hEdef, hadd, h3]
  rw [ht, h2] at h4
  rw [h4]
  abel

end AJSurj

end RamanujanPetersson.JacComplete

end

-- ===== S4.Def_RP_JacFrob_SigPl =====
section

/-!
# S4-JacFrob, part SigPl: `σ_*` on places, divisors and `Pic` of `F-bar / k-bar`

* `frK : k-bar ≃+* k-bar`, `c ↦ c ^ q`; `ratFr ρ` and `oinfMap ρ`: a ring endomorphism `ρ` of `K`
  acting coefficientwise on `K(x)` and on `O_∞(K)`;
* `sigRfin, sigRinf`: the arithmetic Frobenius `σ` preserves `Rfin` and `Rinf` (semilinearly);
* `sigPl : Place ≃ Place` with `ord_sigPl : (sigPl P).ord f = P.ord (σ⁻¹ f)` (so `sigPl = σ_*`);
* `sigD := Finsupp.domCongr sigPl` with `div_sig : div (σ f) = sigD (div f)` and `deg_sigD`;
* `sigPic : PicK ≃+ PicK` with `sigPic_mk`, `degPicK_sigPic`, `sigPic_mem_Pic0K`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places RamanujanPetersson.JacComplete

section Generic

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]

/-- A ring endomorphism of `K` acting on the coefficients of `K(x)`. -/
noncomputable def ratFr (ρ : K →+* K) : RatFunc K →+* RatFunc K :=
  RatFunc.mapRingHom (Polynomial.mapRingHom ρ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (Polynomial.map_injective _ ρ.injective))

theorem ratFr_div (ρ : K →+* K) (p d : K[X]) :
    ratFr ρ (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) d) =
      algebraMap K[X] (RatFunc K) (p.map ρ) / algebraMap K[X] (RatFunc K) (d.map ρ) :=
  RatFunc.map_apply_div _ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (Polynomial.map_injective _ ρ.injective)) p d

theorem ratFr_algebraMap (ρ : K →+* K) (p : K[X]) :
    ratFr ρ (algebraMap K[X] (RatFunc K) p) = algebraMap K[X] (RatFunc K) (p.map ρ) := by
  have h := ratFr_div ρ p 1
  rwa [map_one, div_one, Polynomial.map_one, map_one, div_one] at h

theorem ratFr_mem_Oinf (ρ : K →+* K) {g : RatFunc K} (hg : g ∈ Oinf K) : ratFr ρ g ∈ Oinf K := by
  by_cases h0 : g = 0
  · rw [h0, map_zero]; exact zero_mem _
  have hdeg : g.intDegree ≤ 0 := (mem_Oinf_iff' K h0).mp hg
  have e := RatFunc.num_div_denom g
  rw [← e, ratFr_div]
  apply mem_Oinf_div ((Polynomial.map_ne_zero_iff ρ.injective).mpr (RatFunc.denom_ne_zero g))
  rw [natDegree_map, natDegree_map]
  unfold RatFunc.intDegree at hdeg
  omega

/-- `ρ` acting on `O_∞(K)`. -/
noncomputable def oinfMap (ρ : K →+* K) : Oinf K →+* Oinf K :=
  (ratFr ρ).restrict (Oinf K) (Oinf K) fun _ hz => ratFr_mem_Oinf ρ hz

/-- A ring automorphism preserving a subring (both ways) restricts to it. -/
def restrEquiv {L S : Type*} [Ring L] [SetLike S L] [SubringClass S L] (s : S) (τ : L ≃+* L)
    (h1 : ∀ z ∈ s, τ z ∈ s) (h2 : ∀ z ∈ s, τ.symm z ∈ s) : s ≃+* s where
  toFun z := ⟨τ z, h1 z z.2⟩
  invFun z := ⟨τ.symm z, h2 z z.2⟩
  left_inv _ := Subtype.ext (τ.symm_apply_apply _)
  right_inv _ := Subtype.ext (τ.apply_symm_apply _)
  map_mul' _ _ := Subtype.ext (map_mul τ _ _)
  map_add' _ _ := Subtype.ext (map_add τ _ _)

/-- `w ↦ σ⁻¹ w` as a bijection of `HeightOneSpectrum B`. -/
noncomputable def hosEquiv {B : Type*} [CommRing B] [IsDedekindDomain B] (σ : B ≃+* B) :
    HeightOneSpectrum B ≃ HeightOneSpectrum B where
  toFun := pullH σ
  invFun := pullH σ.symm
  left_inv w := by
    apply HeightOneSpectrum.ext
    ext b
    show σ (σ.symm b) ∈ w.asIdeal ↔ b ∈ w.asIdeal
    rw [RingEquiv.apply_symm_apply]
  right_inv w := by
    apply HeightOneSpectrum.ext
    ext b
    show σ.symm (σ b) ∈ w.asIdeal ↔ b ∈ w.asIdeal
    rw [RingEquiv.symm_apply_apply]

theorem ord_hosEquiv {B L : Type*} [CommRing B] [IsDedekindDomain B] [Field L] [Algebra B L]
    [IsFractionRing B L] (σ : B ≃+* B) (σL : L ≃+* L)
    (hσ : ∀ b, algebraMap B L (σ b) = σL (algebraMap B L b)) (w : HeightOneSpectrum B) (x : L) :
    Places.ord (hosEquiv σ w) x = Places.ord w (σL x) := by
  unfold Places.ord
  rw [show hosEquiv σ w = pullH σ w from rfl, valuation_pullH σ σL hσ w x]

end Generic

section Frob

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω]

/-- The `q`-power Frobenius of `k-bar` (bijective: `k-bar` is algebraic over `Fq`). -/
noncomputable def frK : kbar Fq Ω ≃+* kbar Fq Ω :=
  (FiniteField.frobeniusAlgEquivOfAlgebraic Fq (kbar Fq Ω)).toRingEquiv

theorem frK_apply (c : kbar Fq Ω) : frK Fq Ω c = c ^ Fintype.card Fq := rfl

end Frob

section Transport

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

variable {Fq F Ω}

theorem comp_poly_of (τ : Fbar Fq F Ω →+* Fbar Fq F Ω) (ρ : kbar Fq Ω →+* kbar Fq Ω)
    (hc : ∀ c, τ (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) = algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (ρ c))
    (hx : τ (xbar Fq F Ω) = xbar Fq F Ω) :
    (algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω)).comp (mapRingHom ρ) =
      τ.comp (algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω)) := by
  have e : ∀ c : kbar Fq Ω,
      algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω) (C c) = algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c :=
    fun c => (IsScalarTower.algebraMap_apply (kbar Fq Ω) (kbar Fq Ω)[X] (Fbar Fq F Ω) c).symm
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C, e, hc]
  · simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X]
    rw [algebraMap_polyK, aeval_X, hx]

theorem comp_rat_of (τ : Fbar Fq F Ω →+* Fbar Fq F Ω) (ρ : kbar Fq Ω →+* kbar Fq Ω)
    (hc : ∀ c, τ (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) = algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (ρ c))
    (hx : τ (xbar Fq F Ω) = xbar Fq F Ω) :
    (algebraMap (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω)).comp (ratFr ρ) =
      τ.comp (algebraMap (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω)) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (kbar Fq Ω)[X]) (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply]
  rw [ratFr_algebraMap,
    ← IsScalarTower.algebraMap_apply (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω),
    ← IsScalarTower.algebraMap_apply (kbar Fq Ω)[X] (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω)]
  exact RingHom.congr_fun (comp_poly_of τ ρ hc hx) p

theorem comp_oinf_of (τ : Fbar Fq F Ω →+* Fbar Fq F Ω) (ρ : kbar Fq Ω →+* kbar Fq Ω)
    (hc : ∀ c, τ (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) = algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (ρ c))
    (hx : τ (xbar Fq F Ω) = xbar Fq F Ω) :
    (algebraMap (Oinf (kbar Fq Ω)) (Fbar Fq F Ω)).comp (oinfMap ρ) =
      τ.comp (algebraMap (Oinf (kbar Fq Ω)) (Fbar Fq F Ω)) := by
  refine RingHom.ext fun z => ?_
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply (Oinf (kbar Fq Ω)) (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω),
    IsScalarTower.algebraMap_apply (Oinf (kbar Fq Ω)) (RatFunc (kbar Fq Ω)) (Fbar Fq F Ω) z]
  exact RingHom.congr_fun (comp_rat_of τ ρ hc hx) (z : RatFunc (kbar Fq Ω))

theorem mem_Rfin_of (τ : Fbar Fq F Ω →+* Fbar Fq F Ω) (ρ : kbar Fq Ω →+* kbar Fq Ω)
    (hc : ∀ c, τ (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) = algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (ρ c))
    (hx : τ (xbar Fq F Ω) = xbar Fq F Ω) {z : Fbar Fq F Ω}
    (hz : z ∈ FunctionField.ringOfIntegers (kbar Fq Ω) (Fbar Fq F Ω)) :
    τ z ∈ FunctionField.ringOfIntegers (kbar Fq Ω) (Fbar Fq F Ω) :=
  IsIntegral.map_of_comp_eq (mapRingHom ρ) τ (comp_poly_of τ ρ hc hx) hz

theorem mem_Rinf_of (τ : Fbar Fq F Ω →+* Fbar Fq F Ω) (ρ : kbar Fq Ω →+* kbar Fq Ω)
    (hc : ∀ c, τ (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) = algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (ρ c))
    (hx : τ (xbar Fq F Ω) = xbar Fq F Ω) {z : Fbar Fq F Ω}
    (hz : z ∈ integralClosure (Oinf (kbar Fq Ω)) (Fbar Fq F Ω)) :
    τ z ∈ integralClosure (Oinf (kbar Fq Ω)) (Fbar Fq F Ω) :=
  IsIntegral.map_of_comp_eq (oinfMap ρ) τ (comp_oinf_of τ ρ hc hx) hz

end Transport

section SigPl

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]
variable [IsAlgClosed Ω] (hk : constField Fq F = ⊥)

theorem sig_kbar (c : kbar Fq Ω) :
    sig Fq F Ω hk (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) =
      algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (frK Fq Ω c) := by
  rw [sig_algebraMap_kbar, frK_apply, map_pow]

theorem sigsymm_kbar (c : kbar Fq Ω) :
    (sig Fq F Ω hk).symm (algebraMap (kbar Fq Ω) (Fbar Fq F Ω) c) =
      algebraMap (kbar Fq Ω) (Fbar Fq F Ω) ((frK Fq Ω).symm c) := by
  rw [AlgEquiv.symm_apply_eq, sig_kbar, RingEquiv.apply_symm_apply]

theorem sig_xbar : sig Fq F Ω hk (xbar Fq F Ω) = xbar Fq F Ω := AlgEquiv.commutes _ _

theorem sigsymm_xbar : (sig Fq F Ω hk).symm (xbar Fq F Ω) = xbar Fq F Ω := AlgEquiv.commutes _ _

/-- `σ` on the finite ring `Rfin = k-bar[x]`-integral closure. -/
noncomputable def sigRfin : Rfin (kbar Fq Ω) (Fbar Fq F Ω) ≃+* Rfin (kbar Fq Ω) (Fbar Fq F Ω) :=
  restrEquiv (FunctionField.ringOfIntegers (kbar Fq Ω) (Fbar Fq F Ω)) (sig Fq F Ω hk).toRingEquiv
    (fun _ hz => mem_Rfin_of (sig Fq F Ω hk : Fbar Fq F Ω →+* Fbar Fq F Ω) (frK Fq Ω : kbar Fq Ω →+* kbar Fq Ω)
      (sig_kbar Fq F Ω hk) (sig_xbar Fq F Ω hk) hz)
    (fun _ hz => mem_Rfin_of ((sig Fq F Ω hk).symm : Fbar Fq F Ω →+* Fbar Fq F Ω)
      ((frK Fq Ω).symm : kbar Fq Ω →+* kbar Fq Ω) (sigsymm_kbar Fq F Ω hk) (sigsymm_xbar Fq F Ω hk) hz)

/-- `σ` on the ring `Rinf` of the places over `x = ∞`. -/
noncomputable def sigRinf : Rinf (kbar Fq Ω) (Fbar Fq F Ω) ≃+* Rinf (kbar Fq Ω) (Fbar Fq F Ω) :=
  restrEquiv (integralClosure (Oinf (kbar Fq Ω)) (Fbar Fq F Ω)) (sig Fq F Ω hk).toRingEquiv
    (fun _ hz => mem_Rinf_of (sig Fq F Ω hk : Fbar Fq F Ω →+* Fbar Fq F Ω) (frK Fq Ω : kbar Fq Ω →+* kbar Fq Ω)
      (sig_kbar Fq F Ω hk) (sig_xbar Fq F Ω hk) hz)
    (fun _ hz => mem_Rinf_of ((sig Fq F Ω hk).symm : Fbar Fq F Ω →+* Fbar Fq F Ω)
      ((frK Fq Ω).symm : kbar Fq Ω →+* kbar Fq Ω) (sigsymm_kbar Fq F Ω hk) (sigsymm_xbar Fq F Ω hk) hz)

/-- **`σ_*` on places**: `ord_{σ_* P} f = ord_P (σ⁻¹ f)`. -/
noncomputable def sigPl : Places.Place (kbar Fq Ω) (Fbar Fq F Ω) ≃ Places.Place (kbar Fq Ω) (Fbar Fq F Ω) :=
  Equiv.sumCongr (hosEquiv (sigRfin Fq F Ω hk).symm) (hosEquiv (sigRinf Fq F Ω hk).symm)

theorem ord_sigPl (P : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) (f : Fbar Fq F Ω) :
    (sigPl Fq F Ω hk P).ord f = P.ord ((sig Fq F Ω hk).symm f) := by
  rcases P with w | w
  · exact ord_hosEquiv (sigRfin Fq F Ω hk).symm (sig Fq F Ω hk).symm.toRingEquiv (fun _ => rfl) w f
  · exact ord_hosEquiv (sigRinf Fq F Ω hk).symm (sig Fq F Ω hk).symm.toRingEquiv (fun _ => rfl) w f

/-- `σ_*` on divisors. -/
noncomputable def sigD : Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω) ≃+ Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω) :=
  Finsupp.domCongr (sigPl Fq F Ω hk)

theorem sigD_apply (D : Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω)) (Q : Places.Place (kbar Fq Ω) (Fbar Fq F Ω)) :
    sigD Fq F Ω hk D Q = D ((sigPl Fq F Ω hk).symm Q) := rfl

/-- **`div (σ f) = σ_* (div f)`**. -/
theorem div_sig (f : Fbar Fq F Ω) :
    (PlacesK.div (sig Fq F Ω hk f) : Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω)) =
      sigD Fq F Ω hk (PlacesK.div f) := by
  ext Q
  obtain ⟨P, rfl⟩ := (sigPl Fq F Ω hk).surjective Q
  rw [sigD_apply, PlacesK.div_apply, PlacesK.div_apply, Equiv.symm_apply_apply, ord_sigPl,
    AlgEquiv.symm_apply_apply]

theorem deg_sigD (D : Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω)) :
    Places.Divisor.deg (sigD Fq F Ω hk D) = D.deg := by
  unfold Places.Divisor.deg
  rw [show sigD Fq F Ω hk D = Finsupp.mapDomain (sigPl Fq F Ω hk) D from
      Finsupp.equivMapDomain_eq_mapDomain _ _,
    Finsupp.sum_mapDomain_index (fun _ => by ring) (fun _ _ _ => by ring)]
  simp only [placeDeg_one]

theorem map_sigD_PrincK :
    (PrincK (kbar Fq Ω) (Fbar Fq F Ω)).map
        (sigD Fq F Ω hk : Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω) →+ Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω)) =
      PrincK (kbar Fq Ω) (Fbar Fq F Ω) := by
  ext D
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨E, hE, rfl⟩
    obtain ⟨f, hf, rfl⟩ := (mem_PrincK _ _).mp hE
    exact ⟨sig Fq F Ω hk f, (_root_.map_ne_zero _).mpr hf, div_sig Fq F Ω hk f⟩
  · intro hD
    obtain ⟨f, hf, rfl⟩ := (mem_PrincK _ _).mp hD
    refine ⟨PlacesK.div ((sig Fq F Ω hk).symm f),
      div_mem_PrincK _ _ ((_root_.map_ne_zero _).mpr hf), ?_⟩
    show sigD Fq F Ω hk (PlacesK.div ((sig Fq F Ω hk).symm f)) = PlacesK.div f
    rw [← div_sig, AlgEquiv.apply_symm_apply]

/-- **`σ_*` on the divisor class group** of `F-bar / k-bar`. -/
noncomputable def sigPic : PicK (kbar Fq Ω) (Fbar Fq F Ω) ≃+ PicK (kbar Fq Ω) (Fbar Fq F Ω) :=
  QuotientAddGroup.congr _ _ (sigD Fq F Ω hk) (map_sigD_PrincK Fq F Ω hk)

theorem sigPic_mk (D : Places.Divisor (kbar Fq Ω) (Fbar Fq F Ω)) :
    sigPic Fq F Ω hk (clsK _ _ D) = clsK _ _ (sigD Fq F Ω hk D) := rfl

theorem degPicK_sigPic (x : PicK (kbar Fq Ω) (Fbar Fq F Ω)) :
    degPicK _ _ (sigPic Fq F Ω hk x) = degPicK _ _ x := by
  obtain ⟨D, rfl⟩ := QuotientAddGroup.mk_surjective x
  show degPicK _ _ (clsK _ _ (sigD Fq F Ω hk D)) = degPicK _ _ (clsK _ _ D)
  rw [degPicK_clsK, degPicK_clsK, deg_sigD]

theorem sigPic_mem_Pic0K {x : PicK (kbar Fq Ω) (Fbar Fq F Ω)} (hx : x ∈ Pic0K _ _) :
    sigPic Fq F Ω hk x ∈ Pic0K (kbar Fq Ω) (Fbar Fq F Ω) := by
  rw [mem_Pic0K] at hx ⊢
  rwa [degPicK_sigPic]

end SigPl

end RamanujanPetersson.JacFrob

end

-- ===== S4.Def_RP_JacFrob_BrR =====
section

/-!
# S4-JacFrob, part BrR (bridge 1): the rings of the levels `F_N` inside those of `F-bar`

* generic: `ratHom ρ : K(x) →+* K'(x)`, `oinfHom ρ`, `gen_comp_poly/rat/oinf`, `gen_int_fin/inf`
  (a map of function fields compatible with `ρ` on constants and fixing `x` preserves integrality);
* `incL j : Lc (lev j) →+* k-bar`, `incF j : Fc (lev j) →+* F-bar`;
* `finR j : Rfin (Fc (lev j)) →+* Rfin (F-bar)`, `infR j` likewise (injective);
* **`exists_finR`, `exists_infR`**: every element of `Rfin (F-bar)` (`Rinf (F-bar)`) comes from a level.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.JacFrob

open Polynomial IsDedekindDomain RamanujanPetersson.PicDescent Places

section Gen

variable {K K' : Type*} [Field K] [Field K'] [DecidableEq (RatFunc K)] [DecidableEq (RatFunc K')]
variable {L L' : Type*} [Field L] [Field L'] [Algebra K L] [Algebra K[X] L] [Algebra (RatFunc K) L]
  [IsScalarTower K[X] (RatFunc K) L] [IsScalarTower K K[X] L]
  [Algebra K' L'] [Algebra K'[X] L'] [Algebra (RatFunc K') L']
  [IsScalarTower K'[X] (RatFunc K') L'] [IsScalarTower K' K'[X] L']

/-- A field map `ρ : K → K'` acting on the coefficients of rational functions. -/
noncomputable def ratHom (ρ : K →+* K') : RatFunc K →+* RatFunc K' :=
  RatFunc.mapRingHom (Polynomial.mapRingHom ρ)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (Polynomial.map_injective _ ρ.injective))

theorem ratHom_div (ρ : K →+* K') (p d : K[X]) :
    ratHom ρ (algebraMap K[X] (RatFunc K) p / algebraMap K[X] (RatFunc K) d) =
      algebraMap K'[X] (RatFunc K') (p.map ρ) / algebraMap K'[X] (RatFunc K') (d.map ρ) :=
  RatFunc.map_apply_div _ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (Polynomial.map_injective _ ρ.injective)) p d

theorem ratHom_algebraMap (ρ : K →+* K') (p : K[X]) :
    ratHom ρ (algebraMap K[X] (RatFunc K) p) = algebraMap K'[X] (RatFunc K') (p.map ρ) := by
  have h := ratHom_div ρ p 1
  rwa [map_one, div_one, Polynomial.map_one, map_one, div_one] at h

theorem ratHom_mem_Oinf (ρ : K →+* K') {g : RatFunc K} (hg : g ∈ Oinf K) : ratHom ρ g ∈ Oinf K' := by
  by_cases h0 : g = 0
  · rw [h0, map_zero]; exact zero_mem _
  have hdeg : g.intDegree ≤ 0 := (mem_Oinf_iff' K h0).mp hg
  have e := RatFunc.num_div_denom g
  rw [← e, ratHom_div]
  apply mem_Oinf_div ((Polynomial.map_ne_zero_iff ρ.injective).mpr (RatFunc.denom_ne_zero g))
  rw [natDegree_map, natDegree_map]
  unfold RatFunc.intDegree at hdeg
  omega

/-- `ρ` acting on `O_∞`. -/
noncomputable def oinfHom (ρ : K →+* K') : Oinf K →+* Oinf K' :=
  (ratHom ρ).restrict (Oinf K) (Oinf K') fun _ hz => ratHom_mem_Oinf ρ hz

theorem coe_oinfHom (ρ : K →+* K') (z : Oinf K) : ((oinfHom ρ z : Oinf K') : RatFunc K') = ratHom ρ z :=
  RingHom.coe_restrict_apply _ _ _ _ _

variable (ψ : L →+* L') (ρ : K →+* K') (hc : ∀ c, ψ (algebraMap K L c) = algebraMap K' L' (ρ c))
  (hx : ψ (algebraMap K[X] L X) = algebraMap K'[X] L' X)

include hc hx

theorem gen_comp_poly : (algebraMap K'[X] L').comp (mapRingHom ρ) = ψ.comp (algebraMap K[X] L) := by
  have e1 : ∀ c : K, algebraMap K[X] L (C c) = algebraMap K L c :=
    fun c => (IsScalarTower.algebraMap_apply K K[X] L c).symm
  have e2 : ∀ c : K', algebraMap K'[X] L' (C c) = algebraMap K' L' c :=
    fun c => (IsScalarTower.algebraMap_apply K' K'[X] L' c).symm
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_C, e1, e2, hc]
  · simp only [RingHom.comp_apply, coe_mapRingHom, Polynomial.map_X]
    exact hx.symm

theorem gen_comp_rat : (algebraMap (RatFunc K') L').comp (ratHom ρ) = ψ.comp (algebraMap (RatFunc K) L) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors K[X]) (RingHom.ext fun p => ?_)
  simp only [RingHom.comp_apply]
  rw [ratHom_algebraMap, ← IsScalarTower.algebraMap_apply K'[X] (RatFunc K') L',
    ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) L]
  exact RingHom.congr_fun (gen_comp_poly ψ ρ hc hx) p

theorem gen_comp_oinf : (algebraMap (Oinf K') L').comp (oinfHom ρ) = ψ.comp (algebraMap (Oinf K) L) := by
  refine RingHom.ext fun z => ?_
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply (Oinf K') (RatFunc K') L',
    IsScalarTower.algebraMap_apply (Oinf K) (RatFunc K) L z]
  exact RingHom.congr_fun (gen_comp_rat ψ ρ hc hx) (z : RatFunc K)

theorem gen_int_fin {z : L} (hz : IsIntegral K[X] z) : IsIntegral K'[X] (ψ z) :=
  IsIntegral.map_of_comp_eq (mapRingHom ρ) ψ (gen_comp_poly ψ ρ hc hx) hz

theorem gen_int_inf {z : L} (hz : IsIntegral (Oinf K) z) : IsIntegral (Oinf K') (ψ z) :=
  IsIntegral.map_of_comp_eq (oinfHom ρ) ψ (gen_comp_oinf ψ ρ hc hx) hz

end Gen

/-- Coefficients of a polynomial over a directed union lie in one member. -/
theorem exists_coeff_mem {R : Type*} [Semiring R] (A : ℕ → Set R) (hA : Monotone A)
    (h0 : ∀ j, (0 : R) ∈ A j) (hcov : ∀ r, ∃ j, r ∈ A j) (p : R[X]) : ∃ j, ∀ n, p.coeff n ∈ A j := by
  choose f hf using hcov
  refine ⟨p.support.sup fun n => f (p.coeff n), fun n => ?_⟩
  by_cases hn : n ∈ p.support
  · exact hA (Finset.le_sup (f := fun n => f (p.coeff n)) hn) (hf _)
  · rw [Polynomial.notMem_support_iff.mp hn]; exact h0 _

section Lev

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]
variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- `Lc (lev j) → k-bar`. -/
noncomputable def incL (j : ℕ) : Lc Fq Ω (lev j) →+* kbar Fq Ω :=
  (IntermediateField.inclusion (Lc_le_kbar Fq Ω (lev j))).toRingHom

/-- `Fc (lev j) → F-bar`. -/
noncomputable def incF (j : ℕ) : Fc Fq F Ω (lev j) →+* Fbar Fq F Ω :=
  (IntermediateField.inclusion (Fc_le_Fbar Fq F Ω (lev j))).toRingHom

theorem hc_lev (j : ℕ) (c : Lc Fq Ω (lev j)) :
    incF Fq F Ω j (algebraMap (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) c) =
      algebraMap (kbar Fq Ω) (Fbar Fq F Ω) (incL Fq Ω j c) := Subtype.ext rfl

theorem hx_lev (j : ℕ) :
    incF Fq F Ω j (algebraMap (Lc Fq Ω (lev j))[X] (Fc Fq F Ω (lev j)) X) =
      algebraMap (kbar Fq Ω)[X] (Fbar Fq F Ω) X := by
  rw [algebraMap_polyF, algebraMap_polyK, aeval_X, aeval_X]
  exact Subtype.ext rfl

/-- The finite ring of level `lev j` inside that of `F-bar`. -/
noncomputable def finR (j : ℕ) :
    Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) →+* Rfin (kbar Fq Ω) (Fbar Fq F Ω) :=
  (incF Fq F Ω j).restrict (FunctionField.ringOfIntegers (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)))
    (FunctionField.ringOfIntegers (kbar Fq Ω) (Fbar Fq F Ω))
    fun _ hz => gen_int_fin (incF Fq F Ω j) (incL Fq Ω j) (hc_lev Fq F Ω j) (hx_lev Fq F Ω j) hz

/-- The infinite ring of level `lev j` inside that of `F-bar`. -/
noncomputable def infR (j : ℕ) :
    Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)) →+* Rinf (kbar Fq Ω) (Fbar Fq F Ω) :=
  (incF Fq F Ω j).restrict (integralClosure (Oinf (Lc Fq Ω (lev j))) (Fc Fq F Ω (lev j)))
    (integralClosure (Oinf (kbar Fq Ω)) (Fbar Fq F Ω))
    fun _ hz => gen_int_inf (incF Fq F Ω j) (incL Fq Ω j) (hc_lev Fq F Ω j) (hx_lev Fq F Ω j) hz

theorem coe_finR (j : ℕ) (y : Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    (finR Fq F Ω j y : Fbar Fq F Ω) = incF Fq F Ω j y := RingHom.coe_restrict_apply _ _ _ _ _

theorem coe_infR (j : ℕ) (y : Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j))) :
    (infR Fq F Ω j y : Fbar Fq F Ω) = incF Fq F Ω j y := RingHom.coe_restrict_apply _ _ _ _ _

theorem finR_injective (j : ℕ) : Function.Injective (finR Fq F Ω j) := fun a b h =>
  Subtype.ext ((incF Fq F Ω j).injective (by rw [← coe_finR, ← coe_finR, h]))

theorem infR_injective (j : ℕ) : Function.Injective (infR Fq F Ω j) := fun a b h =>
  Subtype.ext ((incF Fq F Ω j).injective (by rw [← coe_infR, ← coe_infR, h]))

theorem range_incL_mono {i j : ℕ} (h : i ≤ j) : Set.range (incL Fq Ω i) ⊆ Set.range (incL Fq Ω j) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨(a : Ω), Lc_le (lev_dvd_lev h) a.2⟩, Subtype.ext rfl⟩

theorem lifts_incL_mono {i j : ℕ} (h : i ≤ j) (r : (kbar Fq Ω)[X]) (hr : r ∈ lifts (incL Fq Ω i)) :
    r ∈ lifts (incL Fq Ω j) :=
  (lifts_iff_coeff_lifts r).mpr fun n => range_incL_mono Fq Ω h ((lifts_iff_coeff_lifts r).mp hr n)

theorem exists_lifts_incL (r : (kbar Fq Ω)[X]) : ∃ j, r ∈ lifts (incL Fq Ω j) := by
  obtain ⟨j, hj⟩ := exists_coeff_mem (fun j => Set.range (incL Fq Ω j)) (fun _ _ h => range_incL_mono Fq Ω h)
    (fun j => ⟨0, map_zero _⟩) (fun c => by
      obtain ⟨j, hj⟩ := exists_lev_of_mem_kbar c.2
      exact ⟨j, ⟨⟨c, hj⟩, rfl⟩⟩) r
  exact ⟨j, (lifts_iff_coeff_lifts r).mpr hj⟩

/-- **Every finite regular function on `F-bar` comes from a level.** -/
theorem exists_finR (z : Rfin (kbar Fq Ω) (Fbar Fq F Ω)) :
    ∃ j, ∃ y : Rfin (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)), finR Fq F Ω j y = z := by
  obtain ⟨j0, hj0⟩ := exists_lev_of_mem_Fbar (z : Fbar Fq F Ω).2
  have hz : IsIntegral (kbar Fq Ω)[X] (z : Fbar Fq F Ω) := z.2
  obtain ⟨p, hpm, hpz⟩ := hz
  obtain ⟨j1, hj1⟩ := exists_coeff_mem (fun j => {r | r ∈ lifts (incL Fq Ω j)})
    (fun _ _ h => lifts_incL_mono Fq Ω h)
    (fun _ => show (0 : (kbar Fq Ω)[X]) ∈ lifts (incL Fq Ω _) from zero_mem _) (exists_lifts_incL Fq Ω) p
  set j := max j0 j1
  have hl : p ∈ lifts (mapRingHom (incL Fq Ω j)) := (lifts_iff_coeff_lifts p).mpr fun n =>
    (lifts_iff_set_range _).mp (lifts_incL_mono Fq Ω (le_max_right j0 j1) _ (hj1 n))
  obtain ⟨p', hp'map, -, hp'm⟩ := lifts_and_natDegree_eq_and_monic hl hpm
  let y0 : Fc Fq F Ω (lev j) := ⟨((z : Fbar Fq F Ω) : Ω), Fc_le (lev_dvd_lev (le_max_left j0 j1)) hj0⟩
  have hy0 : incF Fq F Ω j y0 = (z : Fbar Fq F Ω) := Subtype.ext rfl
  have key : incF Fq F Ω j (eval₂ (algebraMap _ (Fc Fq F Ω (lev j))) y0 p') = 0 := by
    rw [hom_eval₂, ← gen_comp_poly (incF Fq F Ω j) (incL Fq Ω j) (hc_lev Fq F Ω j) (hx_lev Fq F Ω j), hy0,
      ← eval₂_map, hp'map]
    exact hpz
  have h0 : eval₂ (algebraMap _ (Fc Fq F Ω (lev j))) y0 p' = 0 :=
    (incF Fq F Ω j).injective (key.trans (map_zero _).symm)
  exact ⟨j, ⟨y0, (show IsIntegral _ y0 from ⟨p', hp'm, h0⟩)⟩, Subtype.ext ((coe_finR Fq F Ω j _).trans hy0)⟩

theorem exists_oinfHom (a : Oinf (kbar Fq Ω)) (j : ℕ) (h1 : (a : RatFunc (kbar Fq Ω)).num ∈ lifts (incL Fq Ω j))
    (h2 : (a : RatFunc (kbar Fq Ω)).denom ∈ lifts (incL Fq Ω j)) :
    a ∈ Set.range (oinfHom (incL Fq Ω j)) := by
  by_cases ha : (a : RatFunc (kbar Fq Ω)) = 0
  · exact ⟨0, Subtype.ext (by rw [map_zero, ha]; rfl)⟩
  obtain ⟨r1, hr1⟩ := (lifts_iff_set_range _).mp h1
  obtain ⟨r2, hr2⟩ := (lifts_iff_set_range _).mp h2
  have hr20 : r2 ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hr2
    exact RatFunc.denom_ne_zero _ hr2.symm
  have hdeg : (a : RatFunc (kbar Fq Ω)).intDegree ≤ 0 := (mem_Oinf_iff' _ ha).mp a.2
  have hle : r1.natDegree ≤ r2.natDegree := by
    unfold RatFunc.intDegree at hdeg
    rw [← natDegree_map (p := r1) (incL Fq Ω j), ← natDegree_map (p := r2) (incL Fq Ω j), hr1, hr2]
    omega
  refine ⟨⟨_, mem_Oinf_div hr20 hle⟩, Subtype.ext ?_⟩
  rw [coe_oinfHom]
  show ratHom (incL Fq Ω j) (algebraMap _ (RatFunc (Lc Fq Ω (lev j))) r1 /
    algebraMap _ (RatFunc (Lc Fq Ω (lev j))) r2) = (a : RatFunc (kbar Fq Ω))
  rw [ratHom_div, hr1, hr2, RatFunc.num_div_denom]

/-- **Every function on `F-bar` regular at the places over `∞` comes from a level.** -/
theorem exists_infR (z : Rinf (kbar Fq Ω) (Fbar Fq F Ω)) :
    ∃ j, ∃ y : Rinf (Lc Fq Ω (lev j)) (Fc Fq F Ω (lev j)), infR Fq F Ω j y = z := by
  obtain ⟨j0, hj0⟩ := exists_lev_of_mem_Fbar (z : Fbar Fq F Ω).2
  have hz : IsIntegral (Oinf (kbar Fq Ω)) (z : Fbar Fq F Ω) := z.2
  obtain ⟨p, hpm, hpz⟩ := hz
  obtain ⟨j1, hj1⟩ := exists_coeff_mem
    (fun j => {a : Oinf (kbar Fq Ω) | (a : RatFunc (kbar Fq Ω)).num ∈ lifts (incL Fq Ω j) ∧
      (a : RatFunc (kbar Fq Ω)).denom ∈ lifts (incL Fq Ω j)})
    (fun _ _ h _ ha => ⟨lifts_incL_mono Fq Ω h _ ha.1, lifts_incL_mono Fq Ω h _ ha.2⟩)
    (fun _ => by
      show (0 : RatFunc (kbar Fq Ω)).num ∈ _ ∧ (0 : RatFunc (kbar Fq Ω)).denom ∈ _
      rw [RatFunc.num_zero, RatFunc.denom_zero]
      exact ⟨zero_mem _, one_mem _⟩)
    (fun a => by
      obtain ⟨i1, h1⟩ := exists_lifts_incL Fq Ω (a : RatFunc (kbar Fq Ω)).num
      obtain ⟨i2, h2⟩ := exists_lifts_incL Fq Ω (a : RatFunc (kbar Fq Ω)).denom
      exact ⟨max i1 i2, lifts_incL_mono Fq Ω (le_max_left _ _) _ h1,
        lifts_incL_mono Fq Ω (le_max_right _ _) _ h2⟩) p
  set j := max j0 j1
  have hl : p ∈ lifts (oinfHom (incL Fq Ω j)) := (lifts_iff_coeff_lifts p).mpr fun n =>
    exists_oinfHom Fq Ω _ j (lifts_incL_mono Fq Ω (le_max_right j0 j1) _ (hj1 n).1)
      (lifts_incL_mono Fq Ω (le_max_right j0 j1) _ (hj1 n).2)
  obtain ⟨p', hp'map, -, hp'm⟩ := lifts_and_natDegree_eq_and_monic hl hpm
  let y0 : Fc Fq F Ω (lev j) := ⟨((z : Fbar Fq F Ω) : Ω), Fc_le (lev_dvd_lev (le_max_left j0 j1)) hj0⟩
  have hy0 : incF Fq F Ω j y0 = (z : Fbar Fq F Ω) := Subtype.ext rfl
  have key : incF Fq F Ω j (eval₂ (algebraMap _ (Fc Fq F Ω (lev j))) y0 p') = 0 := by
    rw [hom_eval₂, ← gen_comp_oinf (incF Fq F Ω j) (incL Fq Ω j) (hc_lev Fq F Ω j) (hx_lev Fq F Ω j), hy0,
      ← eval₂_map, hp'map]
    exact hpz
  have h0 : eval₂ (algebraMap _ (Fc Fq F Ω (lev j))) y0 p' = 0 :=
    (incF Fq F Ω j).injective (key.trans (map_zero _).symm)
  exact ⟨j, ⟨y0, (show IsIntegral _ y0 from ⟨p', hp'm, h0⟩)⟩, Subtype.ext ((coe_infR Fq F Ω j _).trans hy0)⟩

end Lev

end RamanujanPetersson.JacFrob

end


