-- Prove2me | Definitions.Def_RPLib_S2_IsogenyDegC
-- name    : RPLib_S2_IsogenyDegC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:16:10.522247+00:00
-- url     : https://prove2.me/theorems/d9b9453c-7385-4da7-9400-0e2e6c618539
-- title:
--   Degrees of $r + s\pi$, part C: kernel, surjectivity, determinant
-- statement:
--   An endomorphism with a pullback of ramification index $e$ is surjective with finite kernel, scales the Weil pairing by $e \cdot \#\ker$, and has determinant $e \cdot \#\ker$ on $E[n]$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Proposition III.8.2

import Mathlib
import Definitions.Def_RPLib_S2_IsogenyDegB

/-!
# S2-IsogenyDeg part C: kernel, surjectivity, pairing compatibility, determinant

* `IsPull ψ e φ` : `ψ` is a pullback for `φ` with ramification index `e`.
* `IsPull.surjective`, `IsPull.finite_ker`, `nsmul_surjective` (`E(L)` is `n`-divisible).
* `IsPull.ePair_map` : `e_n(φ S, φ T) = e_n(S, T) ^ (e * #ker φ)`.
* `IsPull.det_eq` : `det (φ | E[n]) = e * #ker φ` in `ℤ/n`.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

namespace RPLib.Isog

open RPLib.Weil

section Kernel

variable {k : Type*} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- `ψ` is a pullback for `φ` with ramification index `e`. -/
structure IsPull (ψ : FF W L →ₐ[L] FF W L) (e : ℕ) (φ : Pt W L →+ Pt W L) : Prop where
  one_le : 1 ≤ e
  inj : Function.Injective ψ
  hord : ∀ f, f ≠ 0 → ∀ P, ord W L (ψ f) P = e * ord W L f (φ P)
  htau : ∀ S f, tau W L S (ψ f) = ψ (tau W L (φ S) f)

theorem exists_isPull (Φ : (W.baseChange (FF W L)).toAffine.Point) (h : ∀ C, Φ ≠ ιP W L C)
    (φ : Pt W L →+ Pt W L)
    (hE : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) Φ =
      Φ + ιP W L (φ S)) :
    ∃ (ψ : FF W L →ₐ[L] FF W L) (e : ℕ), IsPull ψ e φ := by
  obtain ⟨ψ, e, h1, h2, h3, h4⟩ := exists_pull' Φ h φ hE
  exact ⟨ψ, e, h1, h2, h3, h4⟩

lemma gx_ne_zero' : gx W L ≠ 0 := by have := gx_ne W L 0; rwa [map_zero] at this

lemma eq_zero_of_ord_gx_neg {R : Pt W L} (h : ord W L (gx W L) R < 0) : R = 0 := by
  by_contra hR
  exact absurd h (not_lt.mpr (ord_nonneg_of_nu_le hR gx_ne_zero' (HV_gx W L _ hR).nu_le))

lemma ord_gx_zero_neg : ord W L (gx W L) 0 < 0 := by
  obtain ⟨P, hP⟩ := exists_pole (gx_ne_zero' (W := W) (L := L)) (gx_ne W L)
  have := eq_zero_of_ord_gx_neg hP
  subst this
  exact hP

lemma infinite_pt : Infinite (Pt W L) := by
  let g : L → Pt W L := fun a => Point.some _ _
    (equation_iff_nonsingular.mp (exists_y_alg (W.baseChange L) a).choose_spec)
  exact Infinite.of_injective g (fun a b hab => (Point.some.inj hab).1)

variable {ψ : FF W L →ₐ[L] FF W L} {e : ℕ} {φ : Pt W L →+ Pt W L}

lemma IsPull.ne_alg (hP : IsPull ψ e φ) {f : FF W L} (hf : ∀ c : L, f ≠ algebraMap L (FF W L) c)
    (c : L) : ψ f ≠ algebraMap L (FF W L) c := by
  intro h; rw [← ψ.commutes c] at h; exact hf c (hP.inj h)

/-- A nonconstant isogeny is surjective. -/
theorem IsPull.surjective (hP : IsPull ψ e φ) : Function.Surjective φ := by
  intro Q
  have hf0 : tau W L (-Q) (gx W L) ≠ 0 := tau_ne_zero _ gx_ne_zero'
  have hnc : ∀ c : L, tau W L (-Q) (gx W L) ≠ algebraMap L (FF W L) c := by
    intro c hc
    apply gx_ne W L c
    have := congrArg (tau W L Q) hc
    rwa [← tau_add_apply, add_neg_cancel, tau_zero_apply, AlgEquiv.commutes] at this
  obtain ⟨P, hP'⟩ := exists_pole ((_root_.map_ne_zero ψ).mpr hf0) (hP.ne_alg hnc)
  rw [hP.hord _ hf0, ord_tau] at hP'
  have h2 : ord W L (gx W L) (φ P + -Q) < 0 := by
    by_contra h3
    push_neg at h3
    exact absurd hP' (not_lt.mpr (mul_nonneg (by positivity) h3))
  refine ⟨P, ?_⟩
  have := eq_zero_of_ord_gx_neg h2
  rwa [← sub_eq_add_neg, sub_eq_zero] at this

/-- The kernel of a nonconstant isogeny is finite. -/
theorem IsPull.finite_ker (hP : IsPull ψ e φ) : {P : Pt W L | φ P = 0}.Finite := by
  refine (ord_finite ((_root_.map_ne_zero ψ).mpr (gx_ne_zero' (W := W) (L := L)))).subset ?_
  intro P hPk
  simp only [Set.mem_setOf_eq] at hPk
  rw [Function.mem_support, hP.hord _ gx_ne_zero', hPk]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (by have := hP.one_le; omega)) ord_gx_zero_neg.ne

/-- Multiplication by `n`. -/
noncomputable def nsmulHom (n : ℕ) : Pt W L →+ Pt W L where
  toFun P := n • P
  map_zero' := smul_zero n
  map_add' P Q := smul_add n P Q

lemma map_tau_nsmulG (n : ℕ) (S : Pt W L) :
    Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) (n • G W L) =
      n • G W L + ιP W L (nsmulHom n S) := by
  rw [map_nsmul, map_tau_G, pS, nsmul_add, ← map_nsmul]
  rfl

lemma nsmulG_ne_ιP {n : ℕ} (hn : (n : L) ≠ 0) (C : Pt W L) : n • G W L ≠ ιP W L C := by
  intro hC
  have hinj : Function.Injective (ιP W L) := Point.map_injective (W' := W.toAffine) (f := ιF W L)
  have hall : ∀ S : Pt W L, n • S = 0 := by
    intro S
    have h1 := congrArg (Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k)) hC
    rw [map_tau_nsmulG, map_tau_ιP, hC] at h1
    have h2 : ιP W L (nsmulHom n S) = 0 := by simpa using h1
    exact hinj (h2.trans (map_zero _).symm)
  haveI := infinite_pt (W := W) (L := L)
  exact Set.infinite_univ ((finite_En (W := W) n hn).subset (fun S _ => hall S))

/-- **`E(L)` is `n`-divisible** for `n ≠ 0` in `L`. -/
theorem nsmul_surjective {n : ℕ} (hn : (n : L) ≠ 0) :
    Function.Surjective (fun P : Pt W L => n • P) := by
  obtain ⟨ψ, e, hP⟩ := exists_isPull (n • G W L) (nsmulG_ne_ιP hn) (nsmulHom n) (map_tau_nsmulG n)
  exact hP.surjective

/-- **Pairing compatibility**: `e_n(φ S, φ T) = e_n(S, T) ^ (e * #ker φ)`. -/
theorem IsPull.ePair_map (hP : IsPull ψ e φ) {n : ℕ} (hn : (n : L) ≠ 0) {S T : Pt W L}
    (hS : n • S = 0) (hT : n • T = 0) :
    ePair W L n (φ S) (φ T) = ePair W L n S T ^ (e * hP.finite_ker.toFinset.card) := by
  set K := hP.finite_ker.toFinset with hK
  have hmemK : ∀ x, x ∈ K ↔ φ x = 0 := fun x => by rw [hK, Set.Finite.mem_toFinset]; rfl
  have hφS : n • φ S = 0 := by rw [← map_nsmul, hS, map_zero]
  have hφT : n • φ T = 0 := by rw [← map_nsmul, hT, map_zero]
  let pre : Pt W L → Pt W L := fun x => (nsmul_surjective hn x).choose
  have hpre : ∀ x, n • pre x = x := fun x => (nsmul_surjective hn x).choose_spec
  set V : FF W L := ∏ x ∈ K, tau W L (-pre x) (gT W L n T) with hV
  have hV0 : V ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun x _ => tau_ne_zero _ (gT_ne_zero n T))
  set u : FF W L := ψ (gT W L n (φ T)) with hu
  have hu0 : u ≠ 0 := (_root_.map_ne_zero ψ).mpr (gT_ne_zero n (φ T))
  have hordV : ∀ P, ord W L V P = dT W L n (φ T) (φ P) := by
    intro P
    rw [hV, ord_prod _ _ (fun x _ => tau_ne_zero _ (gT_ne_zero n T))]
    have c1 : ∀ x, ord W L (tau W L (-pre x) (gT W L n T)) P =
        (if n • P - T = x then 1 else 0) - (if n • P = x then 1 else 0) := by
      intro x
      rw [ord_tau, ord_gT hn hT, dT, nsmul_add, smul_neg, hpre, ← sub_eq_add_neg]
      congr 1
      · exact if_congr ⟨fun h => by rw [← h]; abel, fun h => by rw [← h]; abel⟩ rfl rfl
      · exact if_congr sub_eq_zero rfl rfl
    rw [Finset.sum_congr rfl (fun x _ => c1 x), Finset.sum_sub_distrib, Finset.sum_ite_eq,
      Finset.sum_ite_eq]
    simp only [hmemK, dT, map_sub, map_nsmul, sub_eq_zero]
  have hord_u : ∀ P, P ≠ 0 → ord W L u P = ord W L (V ^ e) P := by
    intro P _
    rw [hu, hP.hord _ (gT_ne_zero n (φ T)), ord_gT hn hφT, ord_pow, hordV]
  obtain ⟨c, -, huc⟩ := exists_const_of_ord_eq hu0 (pow_ne_zero e hV0) hord_u
  have htV : tau W L S V = algebraMap L (FF W L) (ePair W L n S T ^ K.card) * V := by
    rw [hV, map_prod, map_pow, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun x _ => ?_)
    rw [← tau_add_apply, add_comm, tau_add_apply, tau_gT hn hS hT, map_mul, AlgEquiv.commutes]
  have htu1 : tau W L S u = algebraMap L (FF W L) (ePair W L n (φ S) (φ T)) * u := by
    rw [hu, hP.htau, tau_gT hn hφS hφT, map_mul, AlgHom.commutes]
  have htu2 : tau W L S u = algebraMap L (FF W L) (ePair W L n S T ^ (e * K.card)) * u := by
    rw [huc, map_mul, AlgEquiv.commutes, map_pow, htV, mul_pow, ← map_pow, ← pow_mul,
      mul_comm K.card e]
    ring
  exact alg_cancel hu0 (htu1.symm.trans htu2)

end Kernel

section Det

variable {k : Type*} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF torsModule

/-- An endomorphism restricted to `E[n]`. -/
noncomputable def torsHom (φ : Pt W L →+ Pt W L) (n : ℕ) :
    RPLib.Torsion.tors (W.baseChange L) n →+ RPLib.Torsion.tors (W.baseChange L) n where
  toFun P := ⟨φ P, by
    rw [RPLib.Torsion.mem_tors, ← map_nsmul, RPLib.Torsion.mem_tors.mp P.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ (P : Pt W L) Q)

/-- An endomorphism restricted to `E[n]`, as a `ℤ/n`-linear map. -/
noncomputable def torsLin (φ : Pt W L →+ Pt W L) (n : ℕ) [NeZero n] :
    RPLib.Torsion.tors (W.baseChange L) n →ₗ[ZMod n] RPLib.Torsion.tors (W.baseChange L) n :=
  (torsHom φ n).toZModLinearMap n

lemma torsLin_apply (φ : Pt W L →+ Pt W L) (n : ℕ) [NeZero n]
    (P : RPLib.Torsion.tors (W.baseChange L) n) :
    ((torsLin φ n P : RPLib.Torsion.tors (W.baseChange L) n) : Pt W L) = φ P := rfl

/-- **`det (φ | E[n]) = e * #ker φ`** in `ℤ/n`. -/
theorem IsPull.det_eq {ψ : FF W L →ₐ[L] FF W L} {e : ℕ} {φ : Pt W L →+ Pt W L}
    (hP : IsPull ψ e φ) (n : ℕ) [NeZero n] (hn : (n : L) ≠ 0) :
    LinearMap.det (torsLin φ n) = ((e * hP.finite_ker.toFinset.card : ℕ) : ZMod n) := by
  obtain ⟨eqv⟩ := RPLib.Torsion.tors_equiv (W := W.baseChange L) n hn
  let eL := eqv.toLinearEquiv (ZMod.map_smul (n := n) eqv)
  let b := (Module.Basis.finTwoProd (ZMod n)).map eL.symm
  have mem : ∀ P : RPLib.Torsion.tors (W.baseChange L) n, n • (P : Pt W L) = 0 :=
    fun P => RPLib.Torsion.mem_tors.mp P.2
  refine det_eq_of_pairing
    (fun P Q : RPLib.Torsion.tors (W.baseChange L) n =>
      Units.mk0 (ePair W L n P Q) (ePair_ne_zero hn (mem P) (mem Q))) ?_ ?_ ?_ ?_ b _ _ ?_
  · intro P P' Q
    ext
    simp only [Units.val_mk0, Units.val_mul, AddSubgroup.coe_add]
    exact ePair_add_left hn (mem P) (mem P') (mem Q)
  · intro P Q Q'
    ext
    simp only [Units.val_mk0, Units.val_mul, AddSubgroup.coe_add]
    exact ePair_add_right hn (mem P) (mem Q) (mem Q')
  · intro P
    ext
    simp only [Units.val_mk0, Units.val_one]
    exact ePair_self hn (mem P)
  · intro Q hQ
    apply Subtype.ext
    apply ePair_nondeg_right hn (mem Q)
    intro S hS
    have h := congrArg Units.val (hQ ⟨S, RPLib.Torsion.mem_tors.mpr hS⟩)
    simpa only [Units.val_mk0, Units.val_one] using h
  · intro P Q
    ext
    simp only [Units.val_mk0, Units.val_pow_eq_pow_val]
    exact hP.ePair_map hn (mem P) (mem Q)

end Det

end RPLib.Isog


