-- Prove2me | Definitions.Def_RPLib_S2_WeilPairingB
-- name    : RPLib_S2_WeilPairingB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T18:51:57.519181+00:00
-- url     : https://prove2.me/theorems/571f7bfc-0cf5-4293-aec8-6ba0d33db455
-- title:
--   Weil pairing, part B: the generic point and translations
-- statement:
--   The generic point $G = (x, y)$ of $E$ over its function field $L(E)$ and, for each $S \in E(L)$, the translation automorphism $\tau_S$ of $L(E)$ sending $x, y$ to the coordinates of $G + S$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Section III.3

import Mathlib
import Definitions.Def_RPLib_S2_WeilPairingA

/-!
# S2-WeilPairing part B: the generic point and the translation automorphisms

`W` is an elliptic curve over a field `k`, `L` an algebraically closed `k`-algebra, and
`F := (W⁄L)` function field. The generic point `G = (x, y) ∈ W(F)` and, for `S ∈ W(L)`,
`P_S := G + S`. The translation `τ_S : F ≃ₐ[L] F` sends `x, y` to the coordinates of `P_S`.
-/

set_option autoImplicit false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

namespace RPLib.Weil

section Coords

variable {A : Type*} [CommRing A] {V : WeierstrassCurve.Affine A}

/-- The `x`-coordinate of a point (`0` at infinity). -/
def px : V.Point → A
  | .zero => 0
  | .some x _ _ => x

/-- The `y`-coordinate of a point (`0` at infinity). -/
def py : V.Point → A
  | .zero => 0
  | .some _ y _ => y

lemma nonsingular_px_py {P : V.Point} (hP : P ≠ 0) : V.Nonsingular (px P) (py P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact h

lemma eq_some_px_py {P : V.Point} (hP : P ≠ 0) : P = Point.some _ _ (nonsingular_px_py hP) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl

lemma some_eq_some {x y x' y' : A} {h : V.Nonsingular x y} {h' : V.Nonsingular x' y'}
    (hx : x = x') (hy : y = y') : Point.some x y h = Point.some x' y' h' := by
  subst hx hy; rfl

lemma eq_of_px_py {P Q : V.Point} (hP : P ≠ 0) (hQ : Q ≠ 0) (hx : px P = px Q)
    (hy : py P = py Q) : P = Q := by
  rw [eq_some_px_py hP, eq_some_px_py hQ]; exact some_eq_some hx hy

end Coords

section MapCoords

variable {R : Type*} [CommRing R] {W' : WeierstrassCurve.Affine R} {S : Type*} [CommRing S]
  [Algebra R S] {F K : Type*} [Field F] [Field K] [Algebra R F] [Algebra S F] [IsScalarTower R S F]
  [Algebra R K] [Algebra S K] [IsScalarTower R S K] [DecidableEq F] [DecidableEq K] (f : F →ₐ[S] K)

lemma px_map (P : (W'⁄F).Point) : px (Point.map f P) = f (px P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some x y h => rfl

lemma py_map (P : (W'⁄F).Point) : py (Point.map f P) = f (py P) := by
  cases P with
  | zero => exact (map_zero f).symm
  | some x y h => rfl

end MapCoords

lemma mem_range_of_isAlgebraic {K M : Type*} [Field K] [IsAlgClosed K] [Field M] [Algebra K M]
    {z : M} (hz : IsAlgebraic K z) : ∃ a, algebraMap K M a = z := by
  have : Algebra.IsAlgebraic K (IntermediateField.adjoin K {z}) :=
    IntermediateField.isAlgebraic_adjoin_simple hz.isIntegral
  have h := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (IntermediateField.adjoin K {z})
  have hz' : z ∈ IntermediateField.adjoin K {z} := IntermediateField.mem_adjoin_simple_self K z
  rw [h, IntermediateField.mem_bot] at hz'
  exact hz'

section Abbrevs

variable {k : Type*} [Field k] (W : WeierstrassCurve k) (L : Type*) [Field L] [Algebra k L]

/-- The coordinate ring of `W⁄L`. -/
abbrev CR := (W.baseChange L).toAffine.CoordinateRing

/-- The function field of `W⁄L`. -/
abbrev FF := (W.baseChange L).toAffine.FunctionField

/-- Classical decidable equality on the function field (local instance downstream). -/
noncomputable def decEqFF : DecidableEq (FF W L) := Classical.decEq _

end Abbrevs

section BaseChangeCoeffs

variable {k : Type*} [Field k] (W : WeierstrassCurve k)

instance isElliptic_baseChange (A : Type*) [CommRing A] [Algebra k A] [W.IsElliptic] :
    (W.baseChange A).IsElliptic :=
  inferInstanceAs (W.map (algebraMap k A)).IsElliptic

variable (A B : Type*) [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [Algebra A B]
  [IsScalarTower k A B]

lemma bc_a₁ : (W.baseChange B).toAffine.a₁ = algebraMap A B (W.baseChange A).toAffine.a₁ :=
  IsScalarTower.algebraMap_apply k A B W.a₁
lemma bc_a₂ : (W.baseChange B).toAffine.a₂ = algebraMap A B (W.baseChange A).toAffine.a₂ :=
  IsScalarTower.algebraMap_apply k A B W.a₂
lemma bc_a₃ : (W.baseChange B).toAffine.a₃ = algebraMap A B (W.baseChange A).toAffine.a₃ :=
  IsScalarTower.algebraMap_apply k A B W.a₃
lemma bc_a₄ : (W.baseChange B).toAffine.a₄ = algebraMap A B (W.baseChange A).toAffine.a₄ :=
  IsScalarTower.algebraMap_apply k A B W.a₄
lemma bc_a₆ : (W.baseChange B).toAffine.a₆ = algebraMap A B (W.baseChange A).toAffine.a₆ :=
  IsScalarTower.algebraMap_apply k A B W.a₆

end BaseChangeCoeffs

section Generic

variable {k : Type*} [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
  (L : Type*) [Field L] [Algebra k L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- The generic `x`. -/
noncomputable def gx : (FF W L) := algebraMap (CR W L) (FF W L) (mk (W.baseChange L).toAffine (C X))

/-- The generic `y`. -/
noncomputable def gy : (FF W L) := algebraMap (CR W L) (FF W L) (mk (W.baseChange L).toAffine Y)

/-- `L → F` as a `k`-algebra map. -/
noncomputable def ιF : L →ₐ[k] (FF W L) := IsScalarTower.toAlgHom k L (FF W L)

lemma ιF_apply (a : L) : ιF W L a = algebraMap L (FF W L) a := rfl

lemma algebraMap_Rg (a : L) : algebraMap L (CR W L) a = mk (W.baseChange L).toAffine (C (C a)) := rfl

lemma alg_mk_CC (a : L) :
    algebraMap (CR W L) (FF W L) (mk (W.baseChange L).toAffine (C (C a))) = algebraMap L (FF W L) a := by
  rw [← algebraMap_Rg, ← IsScalarTower.algebraMap_apply]

lemma gen_equation : (W.baseChange (FF W L)).toAffine.Equation (gx W L) (gy W L) := by
  have h0 : mk (W.baseChange L).toAffine (W.baseChange L).toAffine.polynomial = 0 :=
    AdjoinRoot.mk_self
  have h1 := congrArg (algebraMap (CR W L) (FF W L)) h0
  rw [map_zero] at h1
  simp only [WeierstrassCurve.Affine.polynomial, map_add, map_sub, map_mul, map_pow,
    alg_mk_CC] at h1
  rw [equation_iff, bc_a₁ W L (FF W L), bc_a₂ W L (FF W L), bc_a₃ W L (FF W L), bc_a₄ W L (FF W L), bc_a₆ W L (FF W L)]
  have hx : algebraMap (CR W L) (FF W L) (mk (W.baseChange L).toAffine (C X)) = gx W L := rfl
  have hy : algebraMap (CR W L) (FF W L) (mk (W.baseChange L).toAffine Y) = gy W L := rfl
  rw [hx, hy] at h1
  linear_combination h1

lemma gen_nonsingular : (W.baseChange (FF W L)).toAffine.Nonsingular (gx W L) (gy W L) :=
  equation_iff_nonsingular.mp (gen_equation W L)

/-- The generic point. -/
noncomputable def G : (W.baseChange (FF W L)).toAffine.Point := .some _ _ (gen_nonsingular W L)

/-- `W(L) → W(F)`. -/
noncomputable def ιP : (W.baseChange L).toAffine.Point →+ (W.baseChange (FF W L)).toAffine.Point :=
  Point.map (W' := W.toAffine) (ιF W L)

lemma gx_ne (a : L) : gx W L ≠ algebraMap L (FF W L) a := by
  intro h
  have h1 : mk (W.baseChange L).toAffine (C X) = algebraMap L (CR W L) a := by
    apply IsFractionRing.injective (CR W L) (FF W L)
    rw [← IsScalarTower.algebraMap_apply]; exact h
  apply XClass_ne_zero (W' := (W.baseChange L).toAffine) a
  rw [XClass, map_sub, map_sub, h1, algebraMap_Rg, sub_self]

lemma G_ne_ιP (T : (W.baseChange L).toAffine.Point) : G W L ≠ ιP W L T := by
  cases T with
  | zero => exact Point.some_ne_zero _
  | some a b h =>
    intro hG
    have := congrArg px hG
    exact gx_ne W L a this

/-- `P_S = G + S`. -/
noncomputable def pS (S : (W.baseChange L).toAffine.Point) : (W.baseChange (FF W L)).toAffine.Point :=
  G W L + ιP W L S

lemma pS_ne_zero (S : (W.baseChange L).toAffine.Point) : pS W L S ≠ 0 := by
  intro h
  apply G_ne_ιP W L (-S)
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left h

lemma pS_transcendental (S : (W.baseChange L).toAffine.Point) :
    Transcendental L (px (pS W L S)) := by
  intro halg
  obtain ⟨a, ha⟩ := mem_range_of_isAlgebraic halg
  obtain ⟨b, hb⟩ := exists_y_alg (W.baseChange L) a
  have hnsb : (W.baseChange L).toAffine.Nonsingular a b := equation_iff_nonsingular.mp hb
  have hnsb' : (W.baseChange L).toAffine.Nonsingular a ((W.baseChange L).toAffine.negY a b) :=
    (nonsingular_neg ..).mpr hnsb
  have hns := nonsingular_px_py (pS_ne_zero W L S)
  have e1 := hns.1
  rw [← ha] at e1
  have e2 : (W.baseChange (FF W L)).toAffine.Equation (ιF W L a) (ιF W L b) :=
    Equation.baseChange (W := W.toAffine) (ιF W L) hb
  rw [ιF_apply, ιF_apply] at e2
  rw [equation_iff] at e1 e2
  rw [bc_a₁ W L (FF W L), bc_a₂ W L (FF W L), bc_a₃ W L (FF W L), bc_a₄ W L (FF W L), bc_a₆ W L (FF W L)] at e1 e2
  have hfac : (py (pS W L S) - algebraMap L (FF W L) b) *
      (py (pS W L S) - algebraMap L (FF W L) ((W.baseChange L).toAffine.negY a b)) = 0 := by
    simp only [WeierstrassCurve.Affine.negY, map_sub, map_neg, map_mul]
    linear_combination e1 - e2
  have key : ∀ (y : L) (hy : (W.baseChange L).toAffine.Nonsingular a y),
      py (pS W L S) = algebraMap L (FF W L) y → False := by
    intro y hy hpy
    apply G_ne_ιP W L (Point.some a y hy - S)
    have hP : pS W L S = ιP W L (Point.some a y hy) :=
      (eq_some_px_py (pS_ne_zero W L S)).trans (some_eq_some ha.symm hpy)
    rw [map_sub, ← hP, pS, add_sub_cancel_right]
  rcases mul_eq_zero.mp hfac with h | h
  · exact key b hnsb (sub_eq_zero.mp h)
  · exact key _ hnsb' (sub_eq_zero.mp h)

lemma eval₂_polynomial (x y : (FF W L)) (h : (W.baseChange (FF W L)).toAffine.Equation x y) :
    (W.baseChange L).toAffine.polynomial.eval₂
      ((aeval x : L[X] →ₐ[L] (FF W L)) : L[X] →+* (FF W L)) y = 0 := by
  rw [equation_iff] at h
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_C, eval₂_X, RingHom.coe_coe, map_add, map_mul, map_pow, aeval_C, aeval_X]
  rw [bc_a₁ W L (FF W L), bc_a₂ W L (FF W L), bc_a₃ W L (FF W L), bc_a₄ W L (FF W L), bc_a₆ W L (FF W L)] at h
  linear_combination h

/-- The ring map `R → F`, `x ↦ x(P_S)`, `y ↦ y(P_S)`. -/
noncomputable def phi (S : (W.baseChange L).toAffine.Point) : (CR W L) →ₐ[L] (FF W L) :=
  AdjoinRoot.liftAlgHom (W.baseChange L).toAffine.polynomial (aeval (px (pS W L S)))
    (py (pS W L S)) (eval₂_polynomial W L _ _ (nonsingular_px_py (pS_ne_zero W L S)).1)

lemma phi_of (S : (W.baseChange L).toAffine.Point) (p : L[X]) :
    phi W L S (algebraMap L[X] (CR W L) p) = aeval (px (pS W L S)) p := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.liftAlgHom_of _ _ _ _ p

lemma phi_injective (S : (W.baseChange L).toAffine.Point) : Function.Injective (phi W L S) := by
  haveI : Algebra.IsIntegral L[X] (CR W L) := Algebra.IsIntegral.of_finite _ _
  have hker : RingHom.ker (phi W L S) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := L[X])
    rw [eq_bot_iff]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker] at hp
    rw [Ideal.mem_bot]
    by_contra hp0
    exact pS_transcendental W L S ⟨p, hp0, by rw [← phi_of]; exact hp⟩
  intro a b hab
  have : a - b ∈ RingHom.ker (phi W L S) := by
    rw [RingHom.mem_ker, map_sub, hab, sub_self]
  rw [hker, Ideal.mem_bot] at this
  exact sub_eq_zero.mp this

/-- The translation, as an algebra map. -/
noncomputable def tauHom (S : (W.baseChange L).toAffine.Point) : (FF W L) →ₐ[L] (FF W L) :=
  IsFractionRing.liftAlgHom (phi_injective W L S)

lemma tauHom_algebraMap (S : (W.baseChange L).toAffine.Point) (r : (CR W L)) :
    tauHom W L S (algebraMap (CR W L) (FF W L) r) = phi W L S r := by
  rw [tauHom, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

lemma tauHom_gx (S : (W.baseChange L).toAffine.Point) :
    tauHom W L S (gx W L) = px (pS W L S) := by
  rw [gx, tauHom_algebraMap]
  show phi W L S (AdjoinRoot.mk _ (C X)) = _
  rw [AdjoinRoot.mk_C, phi, AdjoinRoot.liftAlgHom_of, aeval_X]

lemma tauHom_gy (S : (W.baseChange L).toAffine.Point) :
    tauHom W L S (gy W L) = py (pS W L S) := by
  rw [gy, tauHom_algebraMap]
  show phi W L S (AdjoinRoot.mk _ X) = _
  rw [AdjoinRoot.mk_X, phi, AdjoinRoot.liftAlgHom_root]

/-- Two `L`-algebra maps out of the function field agreeing on `x` and `y` are equal. -/
lemma algHom_ext_gen {M : Type*} [Field M] [Algebra L M] {f g : (FF W L) →ₐ[L] M}
    (hx : f (gx W L) = g (gx W L)) (hy : f (gy W L) = g (gy W L)) : f = g := by
  have hR : f.comp (IsScalarTower.toAlgHom L (CR W L) (FF W L)) = g.comp (IsScalarTower.toAlgHom L (CR W L) (FF W L)) := by
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      simpa [gx, AdjoinRoot.mk_C] using hx
    · simpa [gy, AdjoinRoot.mk_X] using hy
  apply AlgHom.coe_ringHom_injective
  apply IsFractionRing.ringHom_ext (A := (CR W L))
  intro r
  exact AlgHom.congr_fun hR r

lemma map_tau_G (S : (W.baseChange L).toAffine.Point) :
    Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) (G W L) = pS W L S := by
  rw [G, Point.map_some]
  conv_rhs => rw [eq_some_px_py (pS_ne_zero W L S)]
  exact some_eq_some (tauHom_gx W L S) (tauHom_gy W L S)

lemma map_tau_ιP (S T : (W.baseChange L).toAffine.Point) :
    Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) (ιP W L T) = ιP W L T := by
  have hcomp : ((tauHom W L S).restrictScalars k).comp (ιF W L) = ιF W L := by
    apply AlgHom.ext
    intro a
    exact (tauHom W L S).commutes a
  rw [ιP, Point.map_map, hcomp]

lemma map_tau_pS (S T : (W.baseChange L).toAffine.Point) :
    Point.map (W' := W.toAffine) ((tauHom W L S).restrictScalars k) (pS W L T) =
      pS W L (S + T) := by
  rw [pS, map_add, map_tau_G, map_tau_ιP, pS, pS, map_add, add_assoc]

lemma tauHom_comp (S T : (W.baseChange L).toAffine.Point) :
    (tauHom W L S).comp (tauHom W L T) = tauHom W L (S + T) := by
  apply algHom_ext_gen W L
  · rw [AlgHom.comp_apply, tauHom_gx, tauHom_gx, ← map_tau_pS W L S T, px_map]
    rfl
  · rw [AlgHom.comp_apply, tauHom_gy, tauHom_gy, ← map_tau_pS W L S T, py_map]
    rfl

lemma pS_zero : pS W L 0 = G W L := by rw [pS, map_zero, add_zero]

lemma tauHom_zero : tauHom W L 0 = AlgHom.id L (FF W L) := by
  apply algHom_ext_gen W L
  · rw [tauHom_gx, pS_zero]; rfl
  · rw [tauHom_gy, pS_zero]; rfl

/-- The translation automorphism `τ_S` of the function field. -/
noncomputable def tau (S : (W.baseChange L).toAffine.Point) : (FF W L) ≃ₐ[L] (FF W L) :=
  AlgEquiv.ofAlgHom (tauHom W L S) (tauHom W L (-S))
    (by rw [tauHom_comp, add_neg_cancel, tauHom_zero])
    (by rw [tauHom_comp, neg_add_cancel, tauHom_zero])

lemma tau_apply (S : (W.baseChange L).toAffine.Point) (f : (FF W L)) : tau W L S f = tauHom W L S f :=
  rfl

lemma tau_add_apply (S T : (W.baseChange L).toAffine.Point) (f : (FF W L)) :
    tau W L (S + T) f = tau W L S (tau W L T f) := by
  rw [tau_apply, tau_apply, tau_apply, ← tauHom_comp]; rfl

lemma tau_zero_apply (f : (FF W L)) : tau W L 0 f = f := by
  rw [tau_apply, tauHom_zero]; rfl

lemma tau_gx (S : (W.baseChange L).toAffine.Point) : tau W L S (gx W L) = px (pS W L S) :=
  tauHom_gx W L S

lemma tau_gy (S : (W.baseChange L).toAffine.Point) : tau W L S (gy W L) = py (pS W L S) :=
  tauHom_gy W L S

lemma tau_injective : Function.Injective (tau W L) := by
  intro S T h
  have hx := congrArg (fun e : (FF W L) ≃ₐ[L] (FF W L) => e (gx W L)) h
  have hy := congrArg (fun e : (FF W L) ≃ₐ[L] (FF W L) => e (gy W L)) h
  simp only [tau_gx, tau_gy] at hx hy
  have hP := eq_of_px_py (pS_ne_zero W L S) (pS_ne_zero W L T) hx hy
  rw [pS, pS] at hP
  exact Point.map_injective (ιF W L) (add_left_cancel hP)

end Generic

end RPLib.Weil


