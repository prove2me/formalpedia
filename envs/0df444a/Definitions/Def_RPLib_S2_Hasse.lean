-- Prove2me | Definitions.Def_RPLib_S2_Hasse
-- name    : RPLib_S2_Hasse
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:43.489356+00:00
-- url     : https://prove2.me/theorems/0a6f91bd-a359-4dc6-ae4d-b3a1385b6af7
-- title:
--   Point counts of $E$ over $\mathbb{F}_{q^m}$ and Frobenius eigenvalues
-- statement:
--   With $\alpha, \beta$ the roots of $X^2 - aX + q$: $\#E(\mathbb{F}_{q^m}) = q^m + 1 - (\alpha^m + \beta^m)$ for all $m \ge 1$, the trace of $\pi^m$ on $E[n]$, and $|\alpha^m| = q^{m/2}$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Theorem V.2.3.1

import Mathlib
import Definitions.Def_RPLib_S2_HasseA

/-!
# S2-Hasse: Frobenius characteristic polynomial on `E[n]` and the Hasse bound (goal file)

Part A (`scratch.rp.lib.S2.HasseA`), for an elliptic curve `W` over a finite field `F`, `q = #F`,
`N = #W(F)`, `a = q + 1 - N` (`RPLib.EllFq.trace W`) and an algebraically closed `L ⊇ F`:

* (1) `trace_frobTors` (`tr (π | E[n]) = a`), `RPLib.Weil.det_frobTors` (`det (π | E[n]) = q`),
  `frobTors_sq_sub` (`π² - a π + q = 0` on `E[n]`), for every `n` with `(n : L) ≠ 0`.
* (2) `deg_rsHom` (`deg (r + s π) = r² + a r s + q s²`), `trace_sq_le` (`a² ≤ 4 q`), and in Mathlib
  language `trace_sq_le_four_mul` and **`hasse_bound`** (`|q + 1 - #W(F)| ≤ 2 √q`).
* (3) **`norm_root_eq_sqrt`**: every complex root of `X² - a X + q` has norm `√q`.

This file: the same over `F_{q^m}`. For `K / F` finite with `#K = q ^ m`:

* `castPt`, `torsCast`: transport of points and of `E[n]` along `(W_K)_L = W_L`;
  `castPt_frob`: the `#K`-power Frobenius of `W_K` is `π ^ m`; `conj_frobTors`.
* `trace_baseChange : a(W/K) = tseq a q m` (`tseq a q`: `2, a, a t₁ - q t₀, …`).
* **`card_baseChange_eq`** (Mathlib language): `#W(K) = q^m + 1 - (α^m + β^m)` when `α + β = a`,
  `α β = q`; `norm_eq_sqrt_of_sum_prod` : `‖α‖ = √q`; `norm_pow_eq` : `‖α ^ m‖ = √q ^ m`.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.Hasse

/-! ### Transport along an equality of curves -/

section Cast

variable {L : Type*} [Field L] [DecidableEq L]

/-- Points along an equality of Weierstrass curves. -/
noncomputable def castPt {C₁ C₂ : WeierstrassCurve L} (h : C₁ = C₂) :
    C₁.toAffine.Point ≃+ C₂.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

lemma castPt_some {C₁ C₂ : WeierstrassCurve L} (h : C₁ = C₂) {x y : L}
    (hxy : C₁.toAffine.Nonsingular x y) :
    ∃ h' : C₂.toAffine.Nonsingular x y, castPt h (Point.some x y hxy) = Point.some x y h' := by
  subst h
  exact ⟨hxy, rfl⟩

/-- `E[n]` along an equality of Weierstrass curves. -/
noncomputable def torsCast {C₁ C₂ : WeierstrassCurve L} (h : C₁ = C₂) (n : ℕ) :
    RPLib.Torsion.tors C₁ n ≃+ RPLib.Torsion.tors C₂ n where
  toFun P := ⟨castPt h P, RPLib.Torsion.mem_tors.mpr (by
    rw [← map_nsmul, RPLib.Torsion.mem_tors.mp P.2, map_zero])⟩
  invFun P := ⟨(castPt h).symm P, RPLib.Torsion.mem_tors.mpr (by
    rw [← map_nsmul, RPLib.Torsion.mem_tors.mp P.2, map_zero])⟩
  left_inv P := Subtype.ext ((castPt h).symm_apply_apply _)
  right_inv P := Subtype.ext ((castPt h).apply_symm_apply _)
  map_add' P Q := Subtype.ext (map_add (castPt h) _ _)

end Cast

/-! ### The Frobenius of `W / F_{q^m}` is `π ^ m` -/

section Ext

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {K : Type*} [Field K] [Fintype K] [Algebra F K]
  {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L] [IsAlgClosed L]
  [DecidableEq L]

open RPLib.Weil

variable (W K L) in
lemma baseChange_baseChange : (W.baseChange K).baseChange L = W.baseChange L := by
  show W.map ((algebraMap K L).comp (algebraMap F K)) = W.map (algebraMap F L)
  rw [← IsScalarTower.algebraMap_eq]

lemma castPt_frob (m : ℕ) (hK : Fintype.card K = Fintype.card F ^ m)
    (P : ((W.baseChange K).baseChange L).toAffine.Point) :
    castPt (baseChange_baseChange W K L) (RPLib.EllFq.frob (W.baseChange K) L P) =
      (RPLib.EllFq.frob W L)^[m] (castPt (baseChange_baseChange W K L) P) := by
  rw [RPLib.EllFq.frob_iterate]
  rcases P with _ | ⟨x, y, hxy⟩
  · have h0 : (Point.zero : ((W.baseChange K).baseChange L).toAffine.Point) = 0 := rfl
    simp only [h0, map_zero]
  · obtain ⟨h1, e1⟩ := RPLib.EllFq.frob_some (W.baseChange K) L hxy
    obtain ⟨h2, e2⟩ := castPt_some (baseChange_baseChange W K L) hxy
    obtain ⟨h3, e3⟩ := castPt_some (baseChange_baseChange W K L) h1
    rw [e1, e3, e2, RPLib.EllFq.mapPt, Point.map_some, Point.some.injEq,
      RPLib.EllFq.frobeniusAlgHom_pow_apply, RPLib.EllFq.frobeniusAlgHom_pow_apply, hK]
    exact ⟨rfl, rfl⟩

attribute [local instance] torsModule

lemma coe_frobTors_pow (n : ℕ) [NeZero n] (m : ℕ) (P : RPLib.Torsion.tors (W.baseChange L) n) :
    (((frobTors W L n ^ m) P : RPLib.Torsion.tors (W.baseChange L) n) :
        (W.baseChange L).toAffine.Point) =
      (RPLib.EllFq.frob W L)^[m] (P : (W.baseChange L).toAffine.Point) := by
  induction m with
  | zero => rw [pow_zero, Module.End.one_apply, Function.iterate_zero_apply]
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, Function.iterate_succ_apply', frobTors_apply, ih]

variable (W K L) in
/-- `E[n]` of `W_K` over `L` is `E[n]` of `W` over `L`, as `ℤ/n`-modules. -/
noncomputable def torsLinEquiv (n : ℕ) [NeZero n] :
    RPLib.Torsion.tors ((W.baseChange K).baseChange L) n ≃ₗ[ZMod n]
      RPLib.Torsion.tors (W.baseChange L) n :=
  (torsCast (baseChange_baseChange W K L) n).toLinearEquiv (ZMod.map_smul (n := n) _)

lemma conj_frobTors (m : ℕ) (hK : Fintype.card K = Fintype.card F ^ m) (n : ℕ) [NeZero n] :
    (torsLinEquiv W K L n).conj (frobTors (W.baseChange K) L n) = frobTors W L n ^ m := by
  refine LinearMap.ext fun P => Subtype.ext ?_
  rw [LinearEquiv.conj_apply_apply, coe_frobTors_pow]
  change castPt (baseChange_baseChange W K L) (RPLib.EllFq.frob (W.baseChange K) L
    ((castPt (baseChange_baseChange W K L)).symm (P : (W.baseChange L).toAffine.Point))) = _
  rw [castPt_frob m hK, AddEquiv.apply_symm_apply]

include L in
/-- **`a(W / F_{q^m}) = tseq a q m`** (`= α ^ m + β ^ m`). -/
theorem trace_baseChange (m : ℕ) (hK : Fintype.card K = Fintype.card F ^ m) :
    RPLib.EllFq.trace (W.baseChange K) =
      tseq (RPLib.EllFq.trace W) (Fintype.card F : ℤ) m := by
  refine int_eq_of_zmod F L fun n _ hn => ?_
  rw [← trace_frobTors (W := W.baseChange K) (L := L) n hn,
    ← LinearMap.trace_conj' (frobTors (W.baseChange K) L n) (torsLinEquiv W K L n),
    conj_frobTors m hK, trace_frobTors_pow n hn]

end Ext

/-! ### Mathlib-language statements over `F_{q^m}` -/

section MathlibExt

/-- **`#W(F_{q^m}) = q^m + 1 - (α^m + β^m)`** where `X² - a X + q = (X - α)(X - β)`,
`a = q + 1 - #W(F)`. -/
theorem card_baseChange_eq {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F)
    [W.IsElliptic] {K : Type*} [Field K] [Fintype K] [Algebra F K] (m : ℕ)
    (hK : Fintype.card K = Fintype.card F ^ m) (α β : ℂ)
    (hsum : α + β = (Fintype.card F : ℂ) + 1 - Nat.card W.toAffine.Point)
    (hprod : α * β = Fintype.card F) :
    (Nat.card (W.baseChange K).toAffine.Point : ℂ) =
      (Fintype.card F : ℂ) ^ m + 1 - (α ^ m + β ^ m) := by
  classical
  have h := trace_baseChange (W := W) (K := K) (L := AlgebraicClosure K) m hK
  have ha : ((RPLib.EllFq.trace W : ℤ) : ℂ) = α + β := by
    rw [hsum, RPLib.EllFq.trace_eq]
    push_cast
    rfl
  have key : ((tseq (RPLib.EllFq.trace W) (Fintype.card F : ℤ) m : ℤ) : ℂ) = α ^ m + β ^ m := by
    have := map_tseq (Int.castRingHom ℂ) (RPLib.EllFq.trace W) (Fintype.card F : ℤ) m
    simp only [eq_intCast, Int.cast_natCast] at this
    rw [this, ha, ← hprod, tseq_add_mul]
  have hN := congrArg (Int.cast : ℤ → ℂ) h
  rw [key, RPLib.EllFq.trace_eq, hK] at hN
  push_cast at hN
  change ((RPLib.EllFq.numPoints (W.baseChange K) : ℕ) : ℂ) = _
  linear_combination -hN

/-- The roots `α, β` of `X² - a X + q` have norm `√q`. -/
theorem norm_eq_sqrt_of_sum_prod {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F)
    [W.IsElliptic] (α β : ℂ)
    (hsum : α + β = (Fintype.card F : ℂ) + 1 - Nat.card W.toAffine.Point)
    (hprod : α * β = Fintype.card F) :
    ‖α‖ = Real.sqrt (Fintype.card F) := by
  refine norm_root_eq_sqrt W ?_
  rw [← hsum, ← hprod]
  ring

/-- `‖α ^ m‖ = √q ^ m`: the eigenvalues of the `q^m`-Frobenius have absolute value `q^{m/2}`. -/
theorem norm_pow_eq {F : Type*} [Field F] [Fintype F] (W : WeierstrassCurve F)
    [W.IsElliptic] (α β : ℂ)
    (hsum : α + β = (Fintype.card F : ℂ) + 1 - Nat.card W.toAffine.Point)
    (hprod : α * β = Fintype.card F) (m : ℕ) :
    ‖α ^ m‖ = Real.sqrt (Fintype.card F) ^ m := by
  rw [norm_pow, norm_eq_sqrt_of_sum_prod W α β hsum hprod]

end MathlibExt

end RPLib.Hasse


