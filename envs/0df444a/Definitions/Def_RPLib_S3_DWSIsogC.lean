-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogC
-- name    : RPLib_S3_DWSIsogC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:29:08.023428+00:00
-- url     : https://prove2.me/theorems/f670c1f8-fc0a-4f11-a47a-699c4002fad9
-- title:
--   Weight-two Ramanujan-Petersson library: isogenies between two curves, and isogenous curves share the trace
-- statement:
--   Isogenies between two curves, and isogenous curves share the trace.
--
--   `W, W'` are elliptic curves over a finite field `F`, `L ⊇ F` algebraically closed, `E = W⁄L`, `E' = W'⁄L`.
--
--   * `ιQ W W' L : E'(L) → W'(L(E))` (constant points), `HasGenI φ Φ` : `Φ ∈ W'(L(E))` represents the additive
--     map `φ : E(L) → E'(L)` (`τ_S Φ = Φ + φ S`), `IsIsog φ` : `φ` has such a representative (an isogeny).
--   * `HasGenI.comp_endo` : `φ ∘ α` is an isogeny for every `α ∈ End(E)`.
--   * `HasGenI.finite_ker` : a nonzero isogeny has finite kernel.
--   * **`numPoints_eq_of_frob_comm`** : an additive map `E(L) → E'(L)` with finite kernel commuting with the
--     `q`-Frobenius forces `#W(F) = #W'(F)`; **`trace_eq_of_isog`** : `F_q`-isogenous curves have the same trace.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogB

/-!
# S3-DWS-Isog, part C: isogenies between two curves, and isogenous curves share the trace

`W, W'` are elliptic curves over a finite field `F`, `L ⊇ F` algebraically closed, `E = W⁄L`, `E' = W'⁄L`.

* `ιQ W W' L : E'(L) → W'(L(E))` (constant points), `HasGenI φ Φ` : `Φ ∈ W'(L(E))` represents the additive
  map `φ : E(L) → E'(L)` (`τ_S Φ = Φ + φ S`), `IsIsog φ` : `φ` has such a representative (an isogeny).
* `HasGenI.comp_endo` : `φ ∘ α` is an isogeny for every `α ∈ End(E)`.
* `HasGenI.finite_ker` : a nonzero isogeny has finite kernel.
* **`numPoints_eq_of_frob_comm`** : an additive map `E(L) → E'(L)` with finite kernel commuting with the
  `q`-Frobenius forces `#W(F) = #W'(F)`; **`trace_eq_of_isog`** : `F_q`-isogenous curves have the same trace.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Two

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF torsModule

variable (W W' L) in
/-- Constant points: `E'(L) → W'(L(E))`. -/
noncomputable def ιQ : Pt W' L →+ (W'.baseChange (FF W L)).toAffine.Point :=
  Point.map (W' := W'.toAffine) (ιF W L)

lemma ιQ_injective : Function.Injective (ιQ W W' L) := by
  unfold ιQ
  exact Point.map_injective _

/-- `Φ ∈ W'(L(E))` represents the additive map `φ : E(L) → E'(L)`. -/
def HasGenI (φ : Pt W L →+ Pt W' L) (Φ : (W'.baseChange (FF W L)).toAffine.Point) : Prop :=
  ∀ S, Point.map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) Φ = Φ + ιQ W W' L (φ S)

/-- `φ : E(L) → E'(L)` is an isogeny: it has a generic-point representative. -/
def IsIsog (φ : Pt W L →+ Pt W' L) : Prop :=
  ∃ Φ : (W'.baseChange (FF W L)).toAffine.Point, HasGenI φ Φ

lemma hasGenI_zero : HasGenI (0 : Pt W L →+ Pt W' L) 0 := fun S => by
  rw [map_zero, AddMonoidHom.zero_apply, map_zero, add_zero]

lemma HasGenI.add {φ ψ : Pt W L →+ Pt W' L} {Φ Ψ : (W'.baseChange (FF W L)).toAffine.Point}
    (h₁ : HasGenI φ Φ) (h₂ : HasGenI ψ Ψ) : HasGenI (φ + ψ) (Φ + Ψ) := fun S => by
  rw [map_add, h₁ S, h₂ S, AddMonoidHom.add_apply, map_add]
  abel

lemma HasGenI.neg {φ : Pt W L →+ Pt W' L} {Φ : (W'.baseChange (FF W L)).toAffine.Point}
    (h : HasGenI φ Φ) : HasGenI (-φ) (-Φ) := fun S => by
  rw [map_neg, h S, AddMonoidHom.neg_apply, map_neg, neg_add]

lemma map_ιQ_of_algHom (ρ : FF W L →ₐ[L] FF W L) (C : Pt W' L) :
    Point.map (W' := W'.toAffine) (ρ.restrictScalars F) (ιQ W W' L C) = ιQ W W' L C := by
  have hcomp : (ρ.restrictScalars F).comp (ιF W L) = ιF W L := by
    apply AlgHom.ext
    intro a
    exact ρ.commutes a
  rw [ιQ, Point.map_map, hcomp]

/-- `φ ∘ α` is an isogeny for every endomorphism `α` of `E`. -/
lemma HasGenI.comp_endo {φ : Pt W L →+ Pt W' L} {ψ : Pt W L →+ Pt W L}
    {Φ : (W'.baseChange (FF W L)).toAffine.Point} {Ψ : (W.baseChange (FF W L)).toAffine.Point}
    (h₁ : HasGenI φ Φ) (h₂ : HasGen ψ Ψ) : IsIsog (φ.comp ψ) := by
  by_cases hψ : ψ = 0
  · refine ⟨0, ?_⟩
    have h0 : φ.comp ψ = 0 := by rw [hψ, AddMonoidHom.comp_zero]
    rw [h0]
    exact hasGenI_zero
  · obtain ⟨ρ, e, hP⟩ := exists_isPull_of_hE Ψ ψ h₂ hψ
    refine ⟨Point.map (W' := W'.toAffine) (ρ.restrictScalars F) Φ, fun S => ?_⟩
    have hc : ((tauHom W L S).restrictScalars F).comp (ρ.restrictScalars F) =
        (ρ.restrictScalars F).comp ((tauHom W L (ψ S)).restrictScalars F) := by
      apply AlgHom.ext
      intro f
      have h := hP.htau S f
      rw [tau_apply, tau_apply] at h
      exact h
    rw [Point.map_map, hc, ← Point.map_map, h₁ (ψ S), map_add, map_ιQ_of_algHom]
    rfl

/-- A constant representative gives the zero map. -/
lemma HasGenI.eq_zero_of_const {φ : Pt W L →+ Pt W' L} {Φ : (W'.baseChange (FF W L)).toAffine.Point}
    (h : HasGenI φ Φ) (C : Pt W' L) (hΦ : Φ = ιQ W W' L C) : φ = 0 := by
  ext S
  have h1 := h S
  rw [hΦ, map_ιQ_of_algHom] at h1
  have h2 : ιQ W W' L (φ S) = ιQ W W' L 0 := by
    rw [map_zero]
    exact add_left_cancel (h1.symm.trans (add_zero _).symm)
  exact ιQ_injective h2

/-- A point of `W'(L(E))` with constant coordinates is a constant point. -/
lemma eq_ιQ_of_const {Φ : (W'.baseChange (FF W L)).toAffine.Point} (hΦ : Φ ≠ 0) {a b : L}
    (ha : px Φ = algebraMap L (FF W L) a) (hb : py Φ = algebraMap L (FF W L) b) :
    ∃ C : Pt W' L, Φ = ιQ W W' L C := by
  have e1 := (nonsingular_px_py hΦ).1
  rw [ha, hb, equation_iff] at e1
  rw [bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), bc_a₃ W' L (FF W L), bc_a₄ W' L (FF W L),
    bc_a₆ W' L (FF W L)] at e1
  have hL : (W'.baseChange L).toAffine.Equation a b := by
    rw [equation_iff]
    apply (algebraMap L (FF W L)).injective
    simp only [map_add, map_mul, map_pow]
    linear_combination e1
  refine ⟨Point.some a b (equation_iff_nonsingular.mp hL), ?_⟩
  rw [ιQ, Point.map_some]
  conv_lhs => rw [eq_some_px_py hΦ]
  exact some_eq_some (by rw [ha]; rfl) (by rw [hb]; rfl)

/-- A nonconstant function is fixed by only finitely many translations. -/
lemma finite_fixed {f : FF W L} (hf : ∀ c : L, f ≠ algebraMap L (FF W L) c) :
    {S : Pt W L | tau W L S f = f}.Finite := by
  have hf0 : f ≠ 0 := by have := hf 0; rwa [map_zero] at this
  obtain ⟨P₀, hP₀⟩ := exists_pole hf0 hf
  refine ((ord_finite hf0).image (fun T => P₀ - T)).subset ?_
  intro S hS
  simp only [Set.mem_ofPred_eq] at hS
  refine ⟨P₀ - S, ?_, sub_sub_cancel P₀ S⟩
  rw [Function.mem_support]
  have h1 := ord_tau S f (P₀ - S)
  rw [hS, sub_add_cancel] at h1
  rw [h1]
  exact hP₀.ne

lemma ker_sub_fixed_px {φ : Pt W L →+ Pt W' L} {Φ : (W'.baseChange (FF W L)).toAffine.Point}
    (h : HasGenI φ Φ) : {S | φ S = 0} ⊆ {S : Pt W L | tau W L S (px Φ) = px Φ} := by
  intro S hS
  simp only [Set.mem_ofPred_eq] at hS ⊢
  have h1 := px_map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) Φ
  rw [h S, hS, map_zero, add_zero] at h1
  rw [tau_apply]
  exact h1.symm

lemma ker_sub_fixed_py {φ : Pt W L →+ Pt W' L} {Φ : (W'.baseChange (FF W L)).toAffine.Point}
    (h : HasGenI φ Φ) : {S | φ S = 0} ⊆ {S : Pt W L | tau W L S (py Φ) = py Φ} := by
  intro S hS
  simp only [Set.mem_ofPred_eq] at hS ⊢
  have h1 := py_map (W' := W'.toAffine) ((tauHom W L S).restrictScalars F) Φ
  rw [h S, hS, map_zero, add_zero] at h1
  rw [tau_apply]
  exact h1.symm

/-- **A nonzero isogeny has finite kernel.** -/
theorem HasGenI.finite_ker {φ : Pt W L →+ Pt W' L} {Φ : (W'.baseChange (FF W L)).toAffine.Point}
    (h : HasGenI φ Φ) (hφ : φ ≠ 0) : {S | φ S = 0}.Finite := by
  have hΦ : Φ ≠ 0 := by
    intro h0
    exact hφ (h.eq_zero_of_const 0 (by rw [h0, map_zero]))
  by_cases hx : ∀ c : L, px Φ ≠ algebraMap L (FF W L) c
  · exact (finite_fixed hx).subset (ker_sub_fixed_px h)
  by_cases hy : ∀ c : L, py Φ ≠ algebraMap L (FF W L) c
  · exact (finite_fixed hy).subset (ker_sub_fixed_py h)
  push_neg at hx hy
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  obtain ⟨C, hC⟩ := eq_ιQ_of_const hΦ ha hb
  exact absurd (h.eq_zero_of_const C hC) hφ

lemma IsIsog.finite_ker {φ : Pt W L →+ Pt W' L} (h : IsIsog φ) (hφ : φ ≠ 0) :
    {S | φ S = 0}.Finite := by
  obtain ⟨Φ, hΦ⟩ := h
  exact hΦ.finite_ker hφ

end Two

section Trace

variable {F : Type*} [Field F] [Fintype F] {W W' : WeierstrassCurve F} [W.IsElliptic] [W'.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF torsModule

/-- `φ` restricted to `E[n] → E'[n]`. -/
noncomputable def torsMap (φ : Pt W L →+ Pt W' L) (n : ℕ) :
    RPLib.Torsion.tors (W.baseChange L) n →+ RPLib.Torsion.tors (W'.baseChange L) n where
  toFun P := ⟨φ P, by
    rw [RPLib.Torsion.mem_tors, ← map_nsmul, RPLib.Torsion.mem_tors.mp P.2, map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' P Q := Subtype.ext (map_add _ (P : Pt W L) Q)

/-- `n ≠ 0` in `L` for every prime `n > char L`. -/
lemma natCast_ne_zero_of_prime {n : ℕ} (hn : n.Prime) (hlt : ringChar L < n) : (n : L) ≠ 0 := by
  intro h0
  have hd := (ringChar.spec L n).mp h0
  rcases (Nat.dvd_prime hn).mp hd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · omega

/-- **An additive map with finite kernel commuting with Frobenius identifies `#W(F)` and `#W'(F)`.** -/
theorem numPoints_eq_of_frob_comm (φ : Pt W L →+ Pt W' L) (hker : {P | φ P = 0}.Finite)
    (hc : ∀ P, φ (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W' L (φ P)) :
    RPLib.EllFq.numPoints W = RPLib.EllFq.numPoints W' := by
  set K : AddSubgroup (Pt W L) := φ.ker
  have hKfin : (K : Set (Pt W L)).Finite := hker.subset (fun x hx => AddMonoidHom.mem_ker.mp hx)
  haveI : Finite K := hKfin.to_subtype
  have hk : 0 < Nat.card K := Nat.card_pos
  set a := RPLib.EllFq.numPoints W
  set b := RPLib.EllFq.numPoints W'
  obtain ⟨n, hn1, hn⟩ := Nat.exists_infinite_primes (a + b + ringChar L + Nat.card K + 1)
  haveI : Fact n.Prime := ⟨hn⟩
  haveI : NeZero n := ⟨hn.ne_zero⟩
  have hL : (n : L) ≠ 0 := natCast_ne_zero_of_prime hn (by omega)
  -- injective on `E[n]`
  have hinj : Function.Injective (torsMap φ n) := by
    rw [injective_iff_map_eq_zero]
    intro P hP
    by_contra h0
    have hP0 : (P : Pt W L) ≠ 0 := fun h => h0 (Subtype.ext h)
    have hord : addOrderOf (P : Pt W L) = n :=
      addOrderOf_eq_prime (RPLib.Torsion.mem_tors.mp P.2) hP0
    have hmem : (P : Pt W L) ∈ K := AddMonoidHom.mem_ker.mpr (congrArg Subtype.val hP)
    have h3 : addOrderOf (⟨P, hmem⟩ : K) = n := by
      rw [← AddSubgroup.addOrderOf_coe]
      exact hord
    have hdvd : addOrderOf (⟨P, hmem⟩ : K) ∣ Nat.card K := addOrderOf_dvd_natCard _
    rw [h3] at hdvd
    have := Nat.le_of_dvd hk hdvd
    omega
  have hcW := RPLib.Torsion.card_tors (W := W.baseChange L) n hL
  have hcW' := RPLib.Torsion.card_tors (W := W'.baseChange L) n hL
  haveI : Finite (RPLib.Torsion.tors (W'.baseChange L) n) :=
    Nat.finite_of_card_ne_zero (by rw [hcW']; exact pow_ne_zero 2 hn.ne_zero)
  have hbij : Function.Bijective ((torsMap φ n).toZModLinearMap n) :=
    hinj.bijective_of_nat_card_le (by rw [hcW, hcW'])
  let e := LinearEquiv.ofBijective ((torsMap φ n).toZModLinearMap n) hbij
  have hcomm : torsLin (rsHom W' L 1 (-1)) n =
      (e : _ →ₗ[ZMod n] _) ∘ₗ torsLin (rsHom W L 1 (-1)) n ∘ₗ (e.symm : _ →ₗ[ZMod n] _) := by
    refine LinearMap.ext fun Q => ?_
    obtain ⟨P, rfl⟩ := e.surjective Q
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    apply Subtype.ext
    show rsHom W' L 1 (-1) (φ P) = φ (rsHom W L 1 (-1) P)
    rw [rsHom_apply, rsHom_apply, map_add, map_zsmul, map_zsmul, hc]
  have hdet := det_one_sub_frob (W := W') (L := L) n hL
  rw [hcomm, LinearMap.det_conj, det_one_sub_frob (W := W) (L := L) n hL] at hdet
  rw [ZMod.natCast_eq_natCast_iff'] at hdet
  rwa [Nat.mod_eq_of_lt (show a < n by omega), Nat.mod_eq_of_lt (show b < n by omega)] at hdet

/-- **`F_q`-isogenous curves have the same trace** (any nonzero isogeny commuting with Frobenius). -/
theorem trace_eq_of_isog {φ : Pt W L →+ Pt W' L} (h : IsIsog φ) (hφ : φ ≠ 0)
    (hc : ∀ P, φ (RPLib.EllFq.frob W L P) = RPLib.EllFq.frob W' L (φ P)) :
    RPLib.EllFq.trace W = RPLib.EllFq.trace W' := by
  rw [RPLib.EllFq.trace, RPLib.EllFq.trace, numPoints_eq_of_frob_comm φ (h.finite_ker hφ) hc]

end Trace

end RPLib.DWS


