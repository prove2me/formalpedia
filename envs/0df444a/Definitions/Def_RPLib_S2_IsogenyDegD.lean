-- Prove2me | Definitions.Def_RPLib_S2_IsogenyDegD
-- name    : RPLib_S2_IsogenyDegD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:19:15.501958+00:00
-- url     : https://prove2.me/theorems/91a5c49e-ede7-42a0-ad1e-4a73b508fb54
-- title:
--   Degrees of $r + s\pi$, part D: $\deg \pi = q$
-- statement:
--   The endomorphisms $r + s\pi$ of $E(\bar{\mathbb{F}}_q)$ with $\pi$ the $q$-power Frobenius, their degree $e \cdot \#\ker$, $\deg \pi = q$, and $\#\ker(1 - \pi) = \#E(\mathbb{F}_q)$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Proposition II.2.11 and Section V.1

import Mathlib
import Definitions.Def_RPLib_S2_IsogenyDegC

/-!
# S2-IsogenyDeg part D: the endomorphisms `r + s π`, degree, `deg π = q`

* `ne_ιP_of_hE`, `exists_isPull_of_hE` : a point `Φ ∈ W(F)` with the translation rule for a nonzero `φ`
  is nonconstant, so `φ` has a pullback (`IsPull`).
* `deg φ` (via `IsPull`; `0` if there is none), `IsPull.deg_eq`, `IsPull.det_eq_deg`, `IsPull.ePair_deg`.
* `frobFF`, `piG = (gx^q, gy^q)`, `rsHom r s = r + s π`, `PhiRS r s = r G + s πG`, `hE_rs`,
  `exists_isPull_rs`.
* `deg_frob : deg π = q`; `card_ker_one_sub_frob : #ker (1 - π) = N`.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

namespace RPLib.Isog

open RPLib.Weil

section General

variable {k : Type*} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma ne_ιP_of_hE (Φ : (W.baseChange (FF W L)).toAffine.Point) (φ : Pt W L →+ Pt W L)
    (hE : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) Φ =
      Φ + ιP W L (φ S))
    (hφ : φ ≠ 0) (C : Pt W L) : Φ ≠ ιP W L C := by
  intro hC
  apply hφ
  have hinj : Function.Injective (ιP W L) := Point.map_injective (W' := W.toAffine) (f := ιF W L)
  ext S
  have h1 := hE S
  rw [hC, map_tau_ιP] at h1
  have h2 : ιP W L (φ S) = 0 := (add_eq_left.mp h1.symm)
  exact hinj (h2.trans (map_zero _).symm)

theorem exists_isPull_of_hE (Φ : (W.baseChange (FF W L)).toAffine.Point) (φ : Pt W L →+ Pt W L)
    (hE : ∀ S, Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) Φ =
      Φ + ιP W L (φ S))
    (hφ : φ ≠ 0) : ∃ (ψ : FF W L →ₐ[L] FF W L) (e : ℕ), IsPull ψ e φ :=
  exists_isPull Φ (ne_ιP_of_hE Φ φ hE hφ) φ hE

variable (L) in
/-- Two naturals congruent modulo every `n` that is nonzero in `L` are equal. -/
lemma nat_eq_of_zmod {a b : ℕ}
    (h : ∀ (n : ℕ) [NeZero n], (n : L) ≠ 0 → (a : ZMod n) = (b : ZMod n)) : a = b := by
  obtain ⟨n, hn1, hn⟩ := Nat.exists_infinite_primes (a + b + ringChar L + 1)
  haveI : NeZero n := ⟨hn.ne_zero⟩
  have hL : (n : L) ≠ 0 := by
    intro h0
    have hd := (ringChar.spec L n).mp h0
    rcases (Nat.dvd_prime hn).mp hd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · omega
  have := h n hL
  rw [ZMod.natCast_eq_natCast_iff'] at this
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

attribute [local instance] torsModule

lemma IsPull.deg_unique {ψ₁ ψ₂ : FF W L →ₐ[L] FF W L} {e₁ e₂ : ℕ} {φ : Pt W L →+ Pt W L}
    (h₁ : IsPull ψ₁ e₁ φ) (h₂ : IsPull ψ₂ e₂ φ) :
    e₁ * h₁.finite_ker.toFinset.card = e₂ * h₂.finite_ker.toFinset.card :=
  nat_eq_of_zmod L fun n _ hn => by rw [← h₁.det_eq n hn, ← h₂.det_eq n hn]

/-- The degree of an endomorphism of `E(L)` that has a pullback: `e * #ker`; `0` if there is none. -/
noncomputable def deg (φ : Pt W L →+ Pt W L) : ℕ :=
  sInf {d | ∃ (ψ : FF W L →ₐ[L] FF W L) (e : ℕ) (hP : IsPull ψ e φ),
    d = e * hP.finite_ker.toFinset.card}

theorem IsPull.deg_eq {ψ : FF W L →ₐ[L] FF W L} {e : ℕ} {φ : Pt W L →+ Pt W L}
    (hP : IsPull ψ e φ) : deg φ = e * hP.finite_ker.toFinset.card := by
  have hs : {d | ∃ (ψ : FF W L →ₐ[L] FF W L) (e : ℕ) (hP : IsPull ψ e φ),
      d = e * hP.finite_ker.toFinset.card} = {e * hP.finite_ker.toFinset.card} := by
    ext d
    constructor
    · rintro ⟨ψ', e', hP', rfl⟩
      exact hP'.deg_unique hP
    · intro hd
      exact ⟨ψ, e, hP, hd⟩
  rw [deg, hs, csInf_singleton]

/-- **`det (φ | E[n]) = deg φ`** in `ℤ/n`. -/
theorem IsPull.det_eq_deg {ψ : FF W L →ₐ[L] FF W L} {e : ℕ} {φ : Pt W L →+ Pt W L}
    (hP : IsPull ψ e φ) (n : ℕ) [NeZero n] (hn : (n : L) ≠ 0) :
    LinearMap.det (torsLin φ n) = (deg φ : ZMod n) := by
  rw [hP.deg_eq]; exact hP.det_eq n hn

/-- **`e_n(φ S, φ T) = e_n(S, T) ^ deg φ`**. -/
theorem IsPull.ePair_deg {ψ : FF W L →ₐ[L] FF W L} {e : ℕ} {φ : Pt W L →+ Pt W L}
    (hP : IsPull ψ e φ) {n : ℕ} (hn : (n : L) ≠ 0) {S T : Pt W L} (hS : n • S = 0)
    (hT : n • T = 0) : ePair W L n (φ S) (φ T) = ePair W L n S T ^ deg φ := by
  rw [hP.deg_eq]; exact hP.ePair_map hn hS hT

end General

section Frob

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable (W L) in
/-- The `q`-power Frobenius of the function field. -/
noncomputable abbrev frobFF : FF W L →ₐ[F] FF W L := FiniteField.frobeniusAlgHom F (FF W L)

lemma frobFF_apply (f : FF W L) : frobFF W L f = f ^ Fintype.card F := rfl

variable (W L) in
/-- The Frobenius point `πG = (gx^q, gy^q)` of `W(F)`. -/
noncomputable def piG : (W.baseChange (FF W L)).toAffine.Point :=
  Point.map (W' := W.toAffine) (frobFF W L) (G W L)

lemma map_frobFF_ιP (S : Pt W L) :
    Point.map (W' := W.toAffine) (frobFF W L) (ιP W L S) = ιP W L (RPLib.EllFq.frob W L S) := by
  have hc : (frobFF W L).comp (ιF W L) = (ιF W L).comp (frobAut (F := F) L).toAlgHom := by
    ext c
    change (ιF W L c) ^ Fintype.card F = ιF W L (c ^ Fintype.card F)
    rw [map_pow]
  rw [frob_eq_ptMap, ptMap]
  change Point.map (W' := W.toAffine) (frobFF W L) (Point.map (W' := W.toAffine) (ιF W L) S) =
    Point.map (W' := W.toAffine) (ιF W L)
      (Point.map (W' := W.toAffine) (frobAut (F := F) L).toAlgHom S)
  rw [Point.map_map, Point.map_map, hc]

lemma map_tau_piG (S : Pt W L) :
    Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars F) (piG W L) =
      piG W L + ιP W L (RPLib.EllFq.frob W L S) := by
  have hc : ((tauHom W L S).restrictScalars F).comp (frobFF W L) =
      (frobFF W L).comp ((tauHom W L S).restrictScalars F) := by
    refine AlgHom.ext fun f => ?_
    change tauHom W L S (f ^ Fintype.card F) = (tauHom W L S f) ^ Fintype.card F
    rw [map_pow]
  rw [piG, Point.map_map, hc, ← Point.map_map, map_tau_G, pS, map_add, map_frobFF_ιP]

variable (W L) in
/-- The endomorphism `r + s π` of `E(L)`. -/
noncomputable def rsHom (r s : ℤ) : Pt W L →+ Pt W L :=
  r • AddMonoidHom.id (Pt W L) + s • RPLib.EllFq.frob W L

lemma rsHom_apply (r s : ℤ) (P : Pt W L) :
    rsHom W L r s P = r • P + s • RPLib.EllFq.frob W L P := rfl

variable (W L) in
/-- The point `r G + s πG` of `W(F)` representing `r + s π`. -/
noncomputable def PhiRS (r s : ℤ) : (W.baseChange (FF W L)).toAffine.Point :=
  r • G W L + s • piG W L

lemma hE_rs (r s : ℤ) (S : Pt W L) :
    Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars F) (PhiRS W L r s) =
      PhiRS W L r s + ιP W L (rsHom W L r s S) := by
  rw [PhiRS, map_add, map_zsmul, map_zsmul, map_tau_G, map_tau_piG, pS, rsHom_apply, map_add,
    map_zsmul, map_zsmul, smul_add, smul_add]
  abel

/-- **`r + s π ≠ 0` has a pullback.** -/
theorem exists_isPull_rs (r s : ℤ) (h : rsHom W L r s ≠ 0) :
    ∃ (ψ : FF W L →ₐ[L] FF W L) (e : ℕ), IsPull ψ e (rsHom W L r s) :=
  exists_isPull_of_hE (PhiRS W L r s) (rsHom W L r s) (hE_rs r s) h

variable (W) in
/-- An affine point with a prescribed `x`-coordinate. -/
lemma exists_pt_x (u : L) : ∃ (v : L) (h : (W.baseChange L).toAffine.Nonsingular u v), True :=
  ⟨_, equation_iff_nonsingular.mp (exists_y_alg (W.baseChange L) u).choose_spec, trivial⟩

lemma frob_ne_zero : RPLib.EllFq.frob W L ≠ 0 := by
  intro h0
  obtain ⟨v, hv, -⟩ := exists_pt_x W (0 : L)
  have h1 : RPLib.EllFq.frob W L (Point.some _ _ hv) = RPLib.EllFq.frob W L 0 := by
    rw [h0]; rfl
  exact Point.some_ne_zero hv (RPLib.EllFq.frob_injective W L h1)

lemma rsHom_zero_one : rsHom W L 0 1 = RPLib.EllFq.frob W L := by
  ext P; rw [rsHom_apply, zero_smul, one_smul, zero_add]

attribute [local instance] torsModule

lemma torsLin_frob (n : ℕ) [NeZero n] : torsLin (RPLib.EllFq.frob W L) n = frobTors W L n :=
  LinearMap.ext fun P => Subtype.ext (by rw [torsLin_apply, frobTors_apply])

/-- **`deg π = q`.** -/
theorem deg_frob : deg (RPLib.EllFq.frob W L) = Fintype.card F := by
  obtain ⟨ψ, e, hP⟩ := exists_isPull_rs (W := W) (L := L) 0 1
    (by rw [rsHom_zero_one]; exact frob_ne_zero)
  rw [rsHom_zero_one] at hP
  refine nat_eq_of_zmod L fun n _ hn => ?_
  rw [← hP.det_eq_deg n hn, torsLin_frob, det_frobTors W L n hn]

/-- **`#ker (1 - π) = N`**, the number of points of `W` over `F`. -/
theorem card_ker_one_sub_frob {ψ : FF W L →ₐ[L] FF W L} {e : ℕ}
    (hP : IsPull ψ e (rsHom W L 1 (-1))) :
    hP.finite_ker.toFinset.card = RPLib.EllFq.numPoints W := by
  classical
  rw [RPLib.EllFq.numPoints_eq_card_fixed W L, ← Nat.card_eq_card_finite_toFinset hP.finite_ker]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun P => ?_)
  rw [Set.mem_setOf_eq, rsHom_apply, one_smul, neg_one_smul, add_neg_eq_zero, eq_comm]

end Frob

end RPLib.Isog


