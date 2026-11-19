-- Prove2me | Definitions.Def_RPLib_S4_CDPack28
-- name    : RPLib_S4_CDPack28
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T07:29:00.627233+00:00
-- url     : https://prove2.me/theorems/1a3f15cb-9c36-469e-9218-b80053e8bbcb
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 28 of 71
-- statement:
--   Part 28 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_JacLaw_Good`: S4-JacLaw, file O6d-1: choice data for `ν` and the good open `D(good)` of `Sym^d`
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack27
import Definitions.Def_RPLib_S4_CDPack24
import Definitions.Def_RPLib_S4_CDPack26

/-!
# Curve-duality library package, part 28 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_JacLaw_Good`: S4-JacLaw, file O6d-1: choice data for `ν` and the good open `D(good)` of `Sym^d`
-/

set_option autoImplicit false

-- ===== S4.Def_RP_JacLaw_Good =====
section

/-!
# S4-JacLaw, file O6d-1: choice data for `ν` and the good open `D(good)` of `Sym^d`

`NuData K F d` fixes, for `N = d + g`: an effective divisor `Hn` at infinity of degree `N`, a basis `h` of
`V_N = L(Hn) ∩ B`, test elements `χ`, an index `l0`, functionals `lam P'` killing `L(Hn - P')`, a divisor `H` at infinity
with elements `e_1..e_N ∈ L(H)`, and `w0 ∈ B`. The element `good ∈ Sym^d(B)` is the product of the
kernel coordinate `l0`, the `lam` values, `Δ_1` and the resultant of `Δ_{X - w0}` with its derivative.
At a point `y` of `Sym^d` with `y good ≠ 0`, the section `s = sec y` (the kernel line of `L(Hn - A)`)
has exact pole divisor `Hn` and `N` simple zeros, among them the `d` distinct points of `A`
(`zero_spec`, `map_det`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.JacLaw

open RamanujanPetersson.JacSym RamanujanPetersson.RR

theorem finiteType_away {k : Type*} [Field k] {S : Type*} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (r : S) : Algebra.FiniteType k (Localization.Away r) := by
  have : Algebra.FinitePresentation S (Localization.Away r) := IsLocalization.Away.finitePresentation r
  exact Algebra.FiniteType.trans (S := S) inferInstance Algebra.FiniteType.of_finitePresentation

/-- The zero set of `s` as a finset (empty if it is infinite). -/
noncomputable def zeroFin {k B : Type*} [Field k] [CommRing B] [Algebra k B] (s : B) : Finset (B →ₐ[k] k) := by
  classical
  exact if hf : {φ : B →ₐ[k] k | φ s = 0}.Finite then hf.toFinset else ∅

theorem zeroFin_eq {k B : Type*} [Field k] [CommRing B] [Algebra k B] {s : B} {Z : Finset (B →ₐ[k] k)}
    (hZ : ∀ φ, φ ∈ Z ↔ φ s = 0) : zeroFin (k := k) s = Z := by
  have hf : {φ : B →ₐ[k] k | φ s = 0}.Finite := Z.finite_toSet.subset fun φ hφ => (hZ φ).2 hφ
  rw [zeroFin, dif_pos hf]
  ext φ
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hZ]

section Abs

/-! Abstract wrappers: over an abstract `B` the `Module.Free` instances on subspaces and quotients are found at once
(over `Places.Rfin K F` instance search fails or times out), so finiteness enters as an explicit argument. -/

variable {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]

/-- A basis of a finite-dimensional subspace indexed by `Fin n`, `n = finrank`. -/
noncomputable def finBasisSub (L : Submodule k B) (hL : FiniteDimensional k L) {n : ℕ} (hn : finrank k L = n) :
    Basis (Fin n) k L :=
  Module.finBasisOfFinrankEq k L hn

/-- **Zero set from a resultant.** If `P w = u w * charpoly(w on B/(s))` for all `w` and `P w0` is coprime to its
derivative (resultant `≠ 0`), then `s` has exactly `N = dim B/(s)` zeros and they diagonalise every `w`. -/
theorem exists_zeroSet_of_res [IsAlgClosed k] (s : B) (hfin : Module.Finite k (B ⧸ Ideal.span {s})) {N : ℕ}
    (hN : finrank k (B ⧸ Ideal.span {s}) = N) (P : B → k[X]) (u : B → k)
    (hP : ∀ w, P w = C (u w) * LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {s})
      (Ideal.Quotient.mkₐ k (Ideal.span {s}) w)))
    (w0 : B) (hres : resultant (P w0) (derivative (P w0)) N N ≠ 0) :
    ∃ Z : Finset (B →ₐ[k] k), (∀ φ, φ ∈ Z ↔ φ s = 0) ∧ Z.card = N ∧
      ∀ w, P w = C (u w) * ∏ φ ∈ Z, (X - C (φ w)) := by
  set χ0 := LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {s}) (Ideal.Quotient.mkₐ k (Ideal.span {s}) w0))
    with hχ0
  have hsep : χ0.Separable := by
    have hdeg : χ0.natDegree = N := by rw [hχ0, LinearMap.charpoly_natDegree, hN]
    have hmon : χ0.Monic := LinearMap.charpoly_monic _
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [eq_one_of_monic_natDegree_zero hmon (hdeg.trans h0)]; exact separable_one
    have hp : P w0 = C (u w0) * χ0 := hP w0
    have hpdeg : (P w0).natDegree ≤ N := by rw [hp]; exact (natDegree_C_mul_le _ _).trans hdeg.le
    obtain ⟨Q1, Q2, -, -, hPQ⟩ := exists_mul_add_mul_eq_C_resultant (m := N) (n := N) (P w0) (derivative (P w0))
      hpdeg ((natDegree_derivative_le (P w0)).trans (by omega)) (Or.inl hpos.ne')
    set r := resultant (P w0) (derivative (P w0)) N N
    have hcop : IsCoprime (P w0) (derivative (P w0)) := by
      refine ⟨C r⁻¹ * Q1, C r⁻¹ * Q2, ?_⟩
      calc C r⁻¹ * Q1 * P w0 + C r⁻¹ * Q2 * derivative (P w0) =
            C r⁻¹ * (P w0 * Q1 + derivative (P w0) * Q2) := by ring
        _ = 1 := by rw [hPQ, ← C_mul, inv_mul_cancel₀ hres, C_1]
    have hs : (P w0).Separable := hcop
    rw [hp] at hs
    exact hs.of_mul_right
  obtain ⟨Z, hZ, hcard, hchar⟩ := exists_zeroSet s w0 hsep
  exact ⟨Z, hZ, hcard.trans hN, fun w => by rw [hP w, hchar w]⟩

variable {S : Type*} [CommRing S] [Algebra k S]
variable {n : ℕ} (c : Fin n → S) (h : Fin n → B)
variable {L L' : Submodule k B} (hhL : ∀ l, ∀ y ∈ L', h l * y ∈ L)
variable {a N : ℕ} (α : Basis (Fin a) k L') (β : Basis (Fin a ⊕ Fin N) k L)
variable {e : Fin N → B} (he : ∀ i, e i ∈ L) (w : B) (hw : ∀ i, w * e i ∈ L)

/-- `map_famDet_eq` with the basis of the quotient built from linear independence. -/
theorem map_famDet_eq_li (x : S →ₐ[k] k) (hfin : Module.Finite k (B ⧸ Ideal.span {secAt c h x}))
    (hP : x (famPres c h hhL α β he) ≠ 0)
    (hli : LinearIndependent k fun i => Ideal.Quotient.mkₐ k (Ideal.span {secAt c h x}) (e i))
    (hcard : finrank k (B ⧸ Ideal.span {secAt c h x}) = N) :
    (famDet c h hhL α β he w hw).map x.toRingHom =
      C (x (famPres c h hhL α β he)) * LinearMap.charpoly (Algebra.lmul k (B ⧸ Ideal.span {secAt c h x})
        (Ideal.Quotient.mkₐ k (Ideal.span {secAt c h x}) w)) := by
  rw [map_famPres] at hP
  exact map_famDet_eq c h hhL α β he w hw x hP
    (basisOfLinearIndependentOfCardEqFinrank' _ hli (by rw [Fintype.card_fin, hcard]))
    fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank']

end Abs

section Good

variable {K : Type*} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type*} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F]

instance finiteType_Rfin : Algebra.FiniteType K (Places.Rfin K F) :=
  Algebra.FiniteType.trans (S := K[X]) inferInstance inferInstance

instance finiteDimensional_Linf (H : Places.Divisor K F) : FiniteDimensional K (Linf K F H) := by
  have := finiteDimensional_LFK (K := K) (F := F) H
  exact Module.Finite.of_injective (((incB K F).toLinearMap.domRestrict (Linf K F H)).codRestrict (LFK K F H)
    fun b => b.2) fun a b hab => by
      have h' := congrArg Subtype.val hab
      exact Subtype.ext (incB_injective h')

variable (K F) in
/-- The (finitely many) infinite places. -/
noncomputable def infPl : Finset (HeightOneSpectrum (Places.Rinf K F)) := Set.finite_univ.toFinset

theorem mem_infPl (P : HeightOneSpectrum (Places.Rinf K F)) : P ∈ infPl K F := by
  simp [infPl]

variable [IsAlgClosed K]

theorem deg_nsmul_ptInf (P : HeightOneSpectrum (Places.Rinf K F)) (n : ℕ) :
    Places.Divisor.deg (n • ptInf P) = n := by
  rw [ptInf, Finsupp.smul_single, PlacesK.Divisor.deg_single, nsmul_eq_mul, mul_one]
  have := deg_eq_one (K := K) P
  simp [Places.Place.deg, this]

variable (K F) in
/-- Choice data for the negation map `ν : Sym^d ⇢ Sym^g` (`N = d + g`). -/
structure NuData (d : ℕ) where
  Hn : Places.Divisor K F
  Hn_inf : IsInf Hn
  Hn_deg : Places.Divisor.deg Hn = ((d + genusFK K F : ℕ) : ℤ)
  h : Fin (d + 1) → Places.Rfin K F
  h_mem : ∀ l, h l ∈ Linf K F Hn
  h_li : LinearIndependent K h
  χ : Fin d → Places.Rfin K F
  l0 : Fin (d + 1)
  lam : HeightOneSpectrum (Places.Rinf K F) → (Fin (d + 1) → K) →ₗ[K] K
  lam_spec : ∀ P' (y : Fin (d + 1) → K),
    ∑ l, y l • h l ∈ Linf K F (Hn - ptInf P') → lam P' y = 0
  H : Places.Divisor K F
  H_inf : IsInf H
  H_deg : 2 * (genusFK K F : ℤ) - 1 ≤ Places.Divisor.deg (H - Hn)
  e : Fin (d + genusFK K F) → Places.Rfin K F
  e_mem : ∀ i, e i ∈ Linf K F H
  w0 : Places.Rfin K F

namespace NuData

variable {d : ℕ} (D : NuData K F d)

/-- `H_w = H + (w)_∞`. -/
noncomputable def Hw (w : Places.Rfin K F) : Places.Divisor K F := D.H + poleDiv (K := K) (incB K F w)

/-- `L_w = L(H_w) ∩ B`. -/
noncomputable abbrev Lw (w : Places.Rfin K F) : Submodule K (Places.Rfin K F) := Linf K F (D.Hw w)

/-- `L'_w = L(H_w - Hn) ∩ B`. -/
noncomputable abbrev Lp (w : Places.Rfin K F) : Submodule K (Places.Rfin K F) :=
  Linf K F (D.Hw w - D.Hn)

theorem isInf_Hw (w : Places.Rfin K F) : IsInf (D.Hw w) := D.H_inf.add (isInf_poleDiv w)

theorem isInf_Hw' (w : Places.Rfin K F) : IsInf (D.Hw w - D.Hn) :=
  (D.isInf_Hw w).sub D.Hn_inf

theorem deg_Hw' (w : Places.Rfin K F) :
    2 * (genusFK K F : ℤ) - 1 ≤ Places.Divisor.deg (D.Hw w - D.Hn) := by
  have h1 : D.Hw w - D.Hn =
      (D.H - D.Hn) + poleDiv (K := K) (incB K F w) := by
    rw [Hw]; abel
  rw [h1, PlacesK.Divisor.deg_add]
  linarith [D.H_deg, deg_poleDiv_nonneg (K := K) (incB K F w)]

theorem finrank_Lw (w : Places.Rfin K F) : finrank K (D.Lw w) = finrank K (D.Lp w) + (d + genusFK K F) := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have h1 := finrank_Linf_eq hk (D.isInf_Hw' w) (D.deg_Hw' w)
  have hdeg : Places.Divisor.deg (D.Hw w) =
      Places.Divisor.deg (D.Hw w - D.Hn) + ((d + genusFK K F : ℕ) : ℤ) := by
    rw [PlacesK.Divisor.deg_sub, D.Hn_deg]; ring
  have h2 := finrank_Linf_eq hk (D.isInf_Hw w) (by rw [hdeg]; linarith [D.deg_Hw' w])
  rw [hdeg] at h2
  zify
  push_cast at h1 h2 ⊢
  linarith

/-- A basis of `L'_w`. -/
noncomputable def α (w : Places.Rfin K F) : Basis (Fin (finrank K (D.Lp w))) K (D.Lp w) :=
  finBasisSub (D.Lp w) (finiteDimensional_Linf _) rfl

/-- A basis of `L_w` indexed by `Fin a ⊕ Fin N`. -/
noncomputable def β (w : Places.Rfin K F) : Basis (Fin (finrank K (D.Lp w)) ⊕ Fin (d + genusFK K F)) K (D.Lw w) :=
  (finBasisSub (D.Lw w) (finiteDimensional_Linf _) (D.finrank_Lw w)).reindex finSumFinEquiv.symm

theorem hhL (w : Places.Rfin K F) : ∀ l, ∀ y ∈ D.Lp w, D.h l * y ∈ D.Lw w := fun l y hy => by
  have := mul_mem_Linf (D.h_mem l) hy
  have e : D.Hn + (D.Hw w - D.Hn) = D.Hw w := by abel
  rwa [e] at this

theorem he (w : Places.Rfin K F) : ∀ i, D.e i ∈ D.Lw w := fun i =>
  Linf_mono (le_add_of_nonneg_right le_sup_right) (D.e_mem i)

theorem hw (w : Places.Rfin K F) : ∀ i, w * D.e i ∈ D.Lw w := fun i => by
  have := mul_mem_Linf (mem_Linf_poleDiv w) (D.e_mem i)
  rwa [add_comm] at this

/-- `Δ_1` for `L_w`, an element of `Sym^d(B)`. -/
noncomputable def pres (w : Places.Rfin K F) : SymRing K (Places.Rfin K F) d :=
  famPres (kerVec K D.χ D.h) D.h (D.hhL w) (D.α w) (D.β w) (D.he w)

/-- `Δ_{X - w}`, a polynomial over `Sym^d(B)`. -/
noncomputable def det (w : Places.Rfin K F) : (SymRing K (Places.Rfin K F) d)[X] :=
  famDet (kerVec K D.χ D.h) D.h (D.hhL w) (D.α w) (D.β w) (D.he w) w (D.hw w)

/-- The functional `lam P'` applied to the kernel vector. -/
noncomputable def lamS (P' : HeightOneSpectrum (Places.Rinf K F)) : SymRing K (Places.Rfin K F) d :=
  ∑ l, D.lam P' (fun j => if l = j then 1 else 0) • kerVec K D.χ D.h l

/-- The good element: `D(good)` is the domain of `ν` for this choice. -/
noncomputable def good : SymRing K (Places.Rfin K F) d :=
  kerVec K D.χ D.h D.l0 * (∏ P' ∈ infPl K F, D.lamS P') * D.pres D.w0 *
    resultant (D.det D.w0) (derivative (D.det D.w0)) (d + genusFK K F) (d + genusFK K F)

/-- The section `s = Σ_l y(c_l) h_l` at the point `y`. -/
noncomputable def sec (y : SymRing K (Places.Rfin K F) d →ₐ[K] K) : Places.Rfin K F :=
  secAt (kerVec K D.χ D.h) D.h y

theorem sec_symPt (a : Fin d → (Places.Rfin K F →ₐ[K] K)) : D.sec (symPt a) = sPt a D.χ D.h := rfl

theorem sec_eq (y : SymRing K (Places.Rfin K F) d →ₐ[K] K) : D.sec y = sPt (liftTuple y) D.χ D.h := by
  have := D.sec_symPt (liftTuple y)
  rwa [symPt_liftTuple] at this

theorem sec_mem (y : SymRing K (Places.Rfin K F) d →ₐ[K] K) :
    D.sec y ∈ Linf K F (D.Hn) :=
  Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (D.h_mem l)

theorem lamS_apply (y : SymRing K (Places.Rfin K F) d →ₐ[K] K) (P' : HeightOneSpectrum (Places.Rinf K F)) :
    y (D.lamS P') = D.lam P' (fun l => y (kerVec K D.χ D.h l)) := by
  rw [lamS, LinearMap.pi_apply_eq_sum_univ (D.lam P')]
  simp only [map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem apply_sec (y : SymRing K (Places.Rfin K F) d →ₐ[K] K) (i : Fin d) : liftTuple y i (D.sec y) = 0 := by
  rw [sec_eq]; exact apply_sPt _ _ _ i

variable {D} {y : SymRing K (Places.Rfin K F) d →ₐ[K] K}

theorem good_factors (hy : y D.good ≠ 0) : y (kerVec K D.χ D.h D.l0) ≠ 0 ∧ (∀ P', y (D.lamS P') ≠ 0) ∧
    y (D.pres D.w0) ≠ 0 ∧
    y (resultant (D.det D.w0) (derivative (D.det D.w0)) (d + genusFK K F) (d + genusFK K F)) ≠ 0 := by
  simp only [good, map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff] at hy
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hy
  exact ⟨h1, fun P' => h2 P' (mem_infPl P'), h3, h4⟩

theorem kerVec_ne (hy : y D.good ≠ 0) : symPt (liftTuple y) (kerVec K D.χ D.h D.l0) ≠ 0 := by
  rw [symPt_liftTuple]; exact (good_factors hy).1

theorem sec_ne_zero (hy : y D.good ≠ 0) : D.sec y ≠ 0 := by
  rw [sec_eq]; exact sPt_ne_zero D.h_li (kerVec_ne hy)

theorem injective_lift (hy : y D.good ≠ 0) : Function.Injective (liftTuple y) := injective_of_kerVec (kerVec_ne hy)

theorem sec_not_mem (hy : y D.good ≠ 0) (P' : HeightOneSpectrum (Places.Rinf K F)) :
    D.sec y ∉ Linf K F (D.Hn - ptInf P') := fun hm =>
  (good_factors hy).2.1 P' (by rw [lamS_apply]; exact D.lam_spec P' _ hm)

theorem exactPole (hy : y D.good ≠ 0) : ExactPoleH (D.sec y) D.Hn :=
  exactPoleH_of_not_mem (sec_ne_zero hy) (D.sec_mem y) (sec_not_mem hy)

theorem finrank_quot (hy : y D.good ≠ 0) :
    finrank K (Places.Rfin K F ⧸ Ideal.span {D.sec y}) = d + genusFK K F := by
  have h := finrank_quot_of_exactPoleH (sec_ne_zero hy) D.Hn_inf (exactPole hy)
  rw [D.Hn_deg] at h
  exact_mod_cast h

theorem finite_quot (hy : y D.good ≠ 0) : Module.Finite K (Places.Rfin K F ⧸ Ideal.span {D.sec y}) :=
  PlacesK.FDQ.finite _ (sec_ne_zero hy)

theorem hP (hy : y D.good ≠ 0) (w : Places.Rfin K F) :
    ∀ z ∈ D.Lw w, z ∈ Ideal.span {D.sec y} → ∃ y' ∈ D.Lp w, z = D.sec y * y' := by
  intro z hz hzs
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hzs
  refine ⟨t, mem_Linf_sub_of_mulH (sec_ne_zero hy) (exactPole hy) D.Hn_inf (D.isInf_Hw w) ?_, mul_comm _ _⟩
  rwa [mul_comm] at hz

theorem linIndep (hy : y D.good ≠ 0) :
    LinearIndependent K (fun i => Ideal.Quotient.mkₐ K (Ideal.span {D.sec y}) (D.e i)) := by
  have h3 := (good_factors hy).2.2.1
  rw [pres, map_famPres] at h3
  exact linIndep_mk_of_presDet (D.sec y) (secAt_mul_mem _ _ (D.hhL D.w0) y) (D.α D.w0) (D.β D.w0) (D.he D.w0)
    (hP hy D.w0) h3

theorem pres_ne_zero (hy : y D.good ≠ 0) (w : Places.Rfin K F) : y (D.pres w) ≠ 0 := by
  rw [pres, map_famPres]
  exact presDet_ne_zero_of_linIndep (D.sec y) _ (D.α w) (D.β w) (D.he w) (sec_ne_zero hy) (linIndep hy)

theorem res_ne (hy : y D.good ≠ 0) :
    resultant ((D.det D.w0).map y.toRingHom) (derivative ((D.det D.w0).map y.toRingHom)) (d + genusFK K F)
      (d + genusFK K F) ≠ 0 := by
  rw [derivative_map, resultant_map_map]
  exact (good_factors hy).2.2.2

/-- **The zero set at a good point**: `N` simple zeros of `s`, and `Δ_{X - w} = Δ_1 · ∏_{P ∈ Z(s)} (X - w(P))`. -/
theorem zero_spec (hy : y D.good ≠ 0) :
    (∀ φ : Places.Rfin K F →ₐ[K] K, φ ∈ zeroFin (D.sec y) ↔ φ (D.sec y) = 0) ∧
      (zeroFin (k := K) (D.sec y)).card = d + genusFK K F ∧
      ∀ w, (D.det w).map y.toRingHom = C (y (D.pres w)) * ∏ φ ∈ zeroFin (k := K) (D.sec y), (X - C (φ w)) := by
  obtain ⟨Z, hZ, hcard, hdet⟩ := exists_zeroSet_of_res (D.sec y) (finite_quot hy) (finrank_quot hy)
    (fun w => (D.det w).map y.toRingHom) (fun w => y (D.pres w))
    (fun w => map_famDet_eq_li (kerVec K D.χ D.h) D.h (D.hhL w) (D.α w) (D.β w) (D.he w) w (D.hw w) y
      (finite_quot hy) (pres_ne_zero hy w) (linIndep hy) (finrank_quot hy)) D.w0 (res_ne hy)
  rw [zeroFin_eq hZ]
  exact ⟨hZ, hcard, hdet⟩

theorem map_det (hy : y D.good ≠ 0) (w : Places.Rfin K F) :
    (D.det w).map y.toRingHom = C (y (D.pres w)) * ∏ φ ∈ zeroFin (k := K) (D.sec y), (X - C (φ w)) :=
  (zero_spec hy).2.2 w

theorem lift_mem_zeroFin (hy : y D.good ≠ 0) (i : Fin d) : liftTuple y i ∈ zeroFin (D.sec y) :=
  ((zero_spec hy).1 _).2 (D.apply_sec y i)

end NuData

end Good

end RamanujanPetersson.JacLaw

end


