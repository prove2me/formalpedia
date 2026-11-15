-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogD
-- name    : RPLib_S3_DWSIsogD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:30:41.968291+00:00
-- url     : https://prove2.me/theorems/d097f927-a2e2-406f-8dc1-8a401665ff6c
-- title:
--   Weight-two Ramanujan-Petersson library: pullback along an isogeny, composition of isogenies
-- statement:
--   Pullback along an isogeny, composition of isogenies.
--
--   For a nonconstant point `Φ ∈ W'(L(E))` the `L`-algebra map `pull2 Φ : L(E') → L(E)` sends `x', y'` to the
--   coordinates of `Φ` (the S2 `pull` with the target curve `W'`). If `Φ` represents `φ : E(L) → E'(L)`, then
--   `τ_S ∘ pull2 Φ = pull2 Φ ∘ τ'_{φ S}`. Hence:
--
--   * `HasGenI.comp` : the composite of two isogenies `E → E' → E''` is an isogeny.
--   * `IsIsogenous W W' L` : a nonzero isogeny `E → E'` commuting with the `q`-Frobenius; it forces equal traces
--     (`IsIsogenous.trace_eq`) and is transitive (`IsIsogenous.trans`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogC

/-!
# S3-DWS-Isog, part D: pullback along an isogeny, composition of isogenies

For a nonconstant point `Φ ∈ W'(L(E))` the `L`-algebra map `pull2 Φ : L(E') → L(E)` sends `x', y'` to the
coordinates of `Φ` (the S2 `pull` with the target curve `W'`). If `Φ` represents `φ : E(L) → E'(L)`, then
`τ_S ∘ pull2 Φ = pull2 Φ ∘ τ'_{φ S}`. Hence:

* `HasGenI.comp` : the composite of two isogenies `E → E' → E''` is an isogeny.
* `IsIsogenous W W' L` : a nonzero isogeny `E → E'` commuting with the `q`-Frobenius; it forces equal traces
  (`IsIsogenous.trace_eq`) and is transitive (`IsIsogenous.trans`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Pull2

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma ne_zero_of_ne_ιQ {Φ : (W'.baseChange (FF W L)).toAffine.Point}
    (h : ∀ C, Φ ≠ ιQ W W' L C) : Φ ≠ 0 := by
  intro h0
  exact h 0 (by rw [h0, map_zero])

lemma transcendental_of_ne_ιQ {Φ : (W'.baseChange (FF W L)).toAffine.Point}
    (h : ∀ C, Φ ≠ ιQ W W' L C) : Transcendental L (px Φ) := by
  have hΦ := ne_zero_of_ne_ιQ h
  intro halg
  obtain ⟨a, ha⟩ := mem_range_of_isAlgebraic halg
  obtain ⟨b, hb⟩ := exists_y_alg (W'.baseChange L) a
  have hnsb : (W'.baseChange L).toAffine.Nonsingular a b := equation_iff_nonsingular.mp hb
  have hnsb' : (W'.baseChange L).toAffine.Nonsingular a ((W'.baseChange L).toAffine.negY a b) :=
    (nonsingular_neg ..).mpr hnsb
  have hns := nonsingular_px_py hΦ
  have e1 := hns.1
  rw [← ha] at e1
  have e2 : (W'.baseChange (FF W L)).toAffine.Equation (ιF W L a) (ιF W L b) :=
    Equation.baseChange (W := W'.toAffine) (ιF W L) hb
  rw [ιF_apply, ιF_apply] at e2
  rw [equation_iff] at e1 e2
  rw [bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), bc_a₃ W' L (FF W L), bc_a₄ W' L (FF W L),
    bc_a₆ W' L (FF W L)] at e1 e2
  have hfac : (py Φ - algebraMap L (FF W L) b) *
      (py Φ - algebraMap L (FF W L) ((W'.baseChange L).toAffine.negY a b)) = 0 := by
    simp only [WeierstrassCurve.Affine.negY, map_sub, map_neg, map_mul]
    linear_combination e1 - e2
  have key : ∀ (y : L) (hy : (W'.baseChange L).toAffine.Nonsingular a y),
      py Φ = algebraMap L (FF W L) y → False := by
    intro y hy hpy
    apply h (Point.some a y hy)
    exact (eq_some_px_py hΦ).trans (some_eq_some ha.symm hpy)
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact key b hnsb (sub_eq_zero.mp h')
  · exact key _ hnsb' (sub_eq_zero.mp h')

lemma eval₂_polynomial2 (x y : FF W L) (h : (W'.baseChange (FF W L)).toAffine.Equation x y) :
    (W'.baseChange L).toAffine.polynomial.eval₂
      ((aeval x : L[X] →ₐ[L] (FF W L)) : L[X] →+* (FF W L)) y = 0 := by
  rw [equation_iff] at h
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_C, eval₂_X, RingHom.coe_coe, map_add, map_mul, map_pow, aeval_C, aeval_X]
  rw [bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), bc_a₃ W' L (FF W L), bc_a₄ W' L (FF W L),
    bc_a₆ W' L (FF W L)] at h
  linear_combination h

variable (Φ : (W'.baseChange (FF W L)).toAffine.Point) (h : ∀ C, Φ ≠ ιQ W W' L C)

/-- The ring map `R' → L(E)`, `x' ↦ x(Φ)`, `y' ↦ y(Φ)`. -/
noncomputable def pullR2 : (CR W' L) →ₐ[L] (FF W L) :=
  AdjoinRoot.liftAlgHom (W'.baseChange L).toAffine.polynomial (aeval (px Φ))
    (py Φ) (eval₂_polynomial2 _ _ (nonsingular_px_py (ne_zero_of_ne_ιQ h)).1)

lemma pullR2_of (p : L[X]) :
    pullR2 Φ h (algebraMap L[X] (CR W' L) p) = aeval (px Φ) p := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.liftAlgHom_of _ _ _ _ p

lemma pullR2_injective : Function.Injective (pullR2 Φ h) := by
  haveI : Algebra.IsIntegral L[X] (CR W' L) := Algebra.IsIntegral.of_finite _ _
  have hker : RingHom.ker (pullR2 Φ h) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := L[X])
    rw [eq_bot_iff]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker] at hp
    rw [Ideal.mem_bot]
    by_contra hp0
    exact transcendental_of_ne_ιQ h ⟨p, hp0, by rw [← pullR2_of Φ h]; exact hp⟩
  intro a b hab
  have : a - b ∈ RingHom.ker (pullR2 Φ h) := by
    rw [RingHom.mem_ker, map_sub, hab, sub_self]
  rw [hker, Ideal.mem_bot] at this
  exact sub_eq_zero.mp this

/-- The pullback `f ↦ f ∘ Φ : L(E') → L(E)`. -/
noncomputable def pull2 : (FF W' L) →ₐ[L] (FF W L) :=
  IsFractionRing.liftAlgHom (pullR2_injective Φ h)

lemma pull2_algebraMap (r : (CR W' L)) :
    pull2 Φ h (algebraMap (CR W' L) (FF W' L) r) = pullR2 Φ h r := by
  rw [pull2, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

lemma pull2_gx : pull2 Φ h (gx W' L) = px Φ := by
  rw [gx, pull2_algebraMap]
  show pullR2 Φ h (AdjoinRoot.mk _ (C X)) = _
  rw [AdjoinRoot.mk_C, pullR2, AdjoinRoot.liftAlgHom_of, aeval_X]

lemma pull2_gy : pull2 Φ h (gy W' L) = py Φ := by
  rw [gy, pull2_algebraMap]
  show pullR2 Φ h (AdjoinRoot.mk _ X) = _
  rw [AdjoinRoot.mk_X, pullR2, AdjoinRoot.liftAlgHom_root]

lemma pull2_injective : Function.Injective (pull2 Φ h) := (pull2 Φ h).toRingHom.injective

/-- Pulling back a constant point of `W''(L(E'))` along `Φ` gives the same constant point. -/
lemma map_pull2_ιQ {W'' : WeierstrassCurve F} [W''.IsElliptic] (C : Pt W'' L) :
    Point.map (W' := W''.toAffine) ((pull2 Φ h).restrictScalars F) (ιQ W' W'' L C) = ιQ W W'' L C := by
  have hcomp : ((pull2 Φ h).restrictScalars F).comp (ιF W' L) = ιF W L := by
    apply AlgHom.ext
    intro a
    exact (pull2 Φ h).commutes a
  rw [ιQ, ιQ, Point.map_map, hcomp]

lemma map_pull2_ιP (C : Pt W' L) :
    Point.map (W' := W'.toAffine) ((pull2 Φ h).restrictScalars F) (ιP W' L C) = ιQ W W' L C :=
  map_pull2_ιQ (W'' := W') Φ h C

lemma map_pull2_G :
    Point.map (W' := W'.toAffine) ((pull2 Φ h).restrictScalars F) (G W' L) = Φ := by
  rw [G, Point.map_some]
  conv_rhs => rw [eq_some_px_py (ne_zero_of_ne_ιQ h)]
  exact some_eq_some (pull2_gx Φ h) (pull2_gy Φ h)

lemma map_pull2_pS (S : Pt W' L) :
    Point.map (W' := W'.toAffine) ((pull2 Φ h).restrictScalars F) (pS W' L S) = Φ + ιQ W W' L S := by
  rw [pS, map_add, map_pull2_G, map_pull2_ιP]

/-- Translation rule: `τ_S ∘ pull2 Φ = pull2 Φ ∘ τ'_{φ S}`. -/
theorem tau_comp_pull2 {φ : Pt W L →+ Pt W' L} (hE : HasGenI φ Φ) (S : Pt W L) :
    (tauHom W L S).comp (pull2 Φ h) = (pull2 Φ h).comp (tauHom W' L (φ S)) := by
  apply algHom_ext_gen W' L
  · have h1 := px_map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) Φ
    have h2 := px_map (W' := W'.toAffine) ((pull2 Φ h).restrictScalars F) (pS W' L (φ S))
    rw [hE] at h1
    rw [map_pull2_pS] at h2
    rw [AlgHom.comp_apply, AlgHom.comp_apply, pull2_gx, tauHom_gx]
    exact h1.symm.trans h2
  · have h1 := py_map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) Φ
    have h2 := py_map (W' := W'.toAffine) ((pull2 Φ h).restrictScalars F) (pS W' L (φ S))
    rw [hE] at h1
    rw [map_pull2_pS] at h2
    rw [AlgHom.comp_apply, AlgHom.comp_apply, pull2_gy, tauHom_gy]
    exact h1.symm.trans h2

end Pull2

section Comp

variable {F : Type*} [Field F] [Fintype F] {W W' W'' : WeierstrassCurve F} [W.IsElliptic]
  [W'.IsElliptic] [W''.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

/-- **The composite of two isogenies is an isogeny.** -/
theorem HasGenI.comp {φ : Pt W L →+ Pt W' L} {ψ : Pt W' L →+ Pt W'' L}
    {Φ : (W'.baseChange (FF W L)).toAffine.Point} {Ψ : (W''.baseChange (FF W' L)).toAffine.Point}
    (hψ : HasGenI ψ Ψ) (hφ : HasGenI φ Φ) : IsIsog (ψ.comp φ) := by
  by_cases hc : ∃ C, Φ = ιQ W W' L C
  · obtain ⟨C, hC⟩ := hc
    refine ⟨0, ?_⟩
    have h0 : ψ.comp φ = 0 := by rw [hφ.eq_zero_of_const C hC, AddMonoidHom.comp_zero]
    rw [h0]
    exact hasGenI_zero
  · push_neg at hc
    refine ⟨Point.map (W' := W''.toAffine) ((pull2 Φ hc).restrictScalars F) Ψ, fun S => ?_⟩
    have hcomp : ((tauHom W L S).restrictScalars F).comp ((pull2 Φ hc).restrictScalars F) =
        ((pull2 Φ hc).restrictScalars F).comp ((tauHom W' L (φ S)).restrictScalars F) := by
      apply AlgHom.ext
      intro f
      exact AlgHom.congr_fun (tau_comp_pull2 Φ hc hφ S) f
    rw [Point.map_map, hcomp, ← Point.map_map, hψ (φ S), map_add, map_pull2_ιQ]
    rfl

lemma IsIsog.comp {φ : Pt W L →+ Pt W' L} {ψ : Pt W' L →+ Pt W'' L} (hψ : IsIsog ψ) (hφ : IsIsog φ) :
    IsIsog (ψ.comp φ) := by
  obtain ⟨Ψ, hΨ⟩ := hψ
  obtain ⟨Φ, hΦ⟩ := hφ
  exact hΨ.comp hΦ

variable (W W' L) in
/-- `W` and `W'` are `F_q`-isogenous: a nonzero isogeny `E → E'` commuting with the `q`-Frobenius. -/
def IsIsogenous : Prop :=
  ∃ φ : Pt W L →+ Pt W' L, IsIsog φ ∧ φ ≠ 0 ∧
    ∀ P, φ (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W' L (φ P)

/-- **`F_q`-isogenous curves have the same number of points and the same trace.** -/
theorem IsIsogenous.trace_eq (h : IsIsogenous W W' L) : RPLib.EllFq.trace W = RPLib.EllFq.trace W' := by
  obtain ⟨φ, hi, h0, hc⟩ := h
  exact trace_eq_of_isog hi h0 hc

theorem IsIsogenous.numPoints_eq (h : IsIsogenous W W' L) :
    RPLib.EllFq.numPoints W = RPLib.EllFq.numPoints W' := by
  obtain ⟨φ, hi, h0, hc⟩ := h
  exact numPoints_eq_of_frob_comm φ (hi.finite_ker h0) hc

/-- The composite of two additive maps with finite kernels is nonzero. -/
lemma comp_ne_zero_of_finite {φ : Pt W L →+ Pt W' L} {ψ : Pt W' L →+ Pt W'' L}
    (hφ : {P | φ P = 0}.Finite) (hψ : {P | ψ P = 0}.Finite) : ψ.comp φ ≠ 0 := by
  intro h0
  haveI : Infinite (Pt W L) := infinite_pt
  have hfin : (Set.univ : Set (Pt W L)).Finite := by
    have hsub : (Set.univ : Set (Pt W L)) ⊆ ⋃ Q ∈ {Q | ψ Q = 0} ∩ Set.range φ, {P | φ P = Q} := by
      intro P _
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range]
      refine ⟨φ P, ⟨?_, P, rfl⟩, rfl⟩
      exact congrArg (fun χ : Pt W L →+ Pt W'' L => χ P) h0
    refine Set.Finite.subset (Set.Finite.biUnion (hψ.subset Set.inter_subset_left) fun Q hQ => ?_) hsub
    obtain ⟨P₀, hP₀⟩ := hQ.2
    refine (hφ.image (fun T => T + P₀)).subset ?_
    intro P hP
    have hP' : φ P = Q := hP
    refine ⟨P - P₀, ?_, sub_add_cancel P P₀⟩
    show φ (P - P₀) = 0
    rw [map_sub, hP', hP₀, sub_self]
  exact Set.infinite_univ hfin

/-- `F_q`-isogeny is transitive. -/
theorem IsIsogenous.trans (h₁ : IsIsogenous W W' L) (h₂ : IsIsogenous W' W'' L) :
    IsIsogenous W W'' L := by
  obtain ⟨φ, hi, h0, hc⟩ := h₁
  obtain ⟨ψ, hi', h0', hc'⟩ := h₂
  refine ⟨ψ.comp φ, hi'.comp hi, comp_ne_zero_of_finite (hi.finite_ker h0) (hi'.finite_ker h0'),
    fun P => ?_⟩
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hc, hc']

end Comp

end RPLib.DWS


