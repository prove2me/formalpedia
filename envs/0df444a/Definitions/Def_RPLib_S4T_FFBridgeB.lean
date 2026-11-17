-- Prove2me | Definitions.Def_RPLib_S4T_FFBridgeB
-- name    : RPLib_S4T_FFBridgeB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:21:22.943602+00:00
-- url     : https://prove2.me/theorems/2352172c-a490-43e8-8803-5b29da58d193
-- title:
--   Tate's isogeny theorem over finite fields (prime-to-$p$ form), library: values of the coordinates of `n • G` (specialisation at a point)
-- statement:
--   Values of the coordinates of `n • G` (specialisation at a point).
--
--   `W` an elliptic curve over a field `F`, `L ⊇ F` algebraically closed, `G ∈ W(L(E))` the generic point. For an affine
--   point `P` the valuation ring of `nu P` gives the reduction map `W(L(E)) → W(k_P)` of the FLT bundle
--   (`reduceHom`, a group homomorphism); it sends `G` to the image of `P` under `L ≅ k_P`. Hence:
--
--   * `red_nsmul_G` / `HV_nsmul_G` : if `n • G = (ξ, η)` and `n • P ≠ 0` then `ξ, η` have values `x(n • P), y(n • P)`
--     at `P`;
--   * `nsmul_G_ne_zero` : `n • G ≠ 0` when `n ≠ 0` in `L`;
--   * `HV_unique`, `infinite_Pt`, `exists_good`.
--
--   **Formalization note.** Library module of a formalization of Tate's isogeny theorem over finite fields in prime-to-$p$ form (ordinary elliptic curves with the same number of points are linked by $F$-isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$, stated through $F$-algebra maps of function fields), via Deuring lifting to characteristic $0$. It is conditional only on fifteen Proved prove2.me theorems of the FLT project, which enter as explicit hypotheses whose types are their exact statements (never as lemmas). Part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7

import Mathlib
import Definitions.Def_RPLib_S4T_FFBridgeA
import Definitions.Def_WeierstrassCurve_ReduceHom

/-!
# S4T-FFBridge, part B: values of the coordinates of `n • G` (specialisation at a point)

`W` an elliptic curve over a field `F`, `L ⊇ F` algebraically closed, `G ∈ W(L(E))` the generic point. For an affine
point `P` the valuation ring of `nu P` gives the reduction map `W(L(E)) → W(k_P)` of the FLT bundle
(`reduceHom`, a group homomorphism); it sends `G` to the image of `P` under `L ≅ k_P`. Hence:

* `red_nsmul_G` / `HV_nsmul_G` : if `n • G = (ξ, η)` and `n • P ≠ 0` then `ξ, η` have values `x(n • P), y(n • P)`
  at `P`;
* `nsmul_G_ne_zero` : `n • G ≠ 0` when `n ≠ 0` in `L`;
* `HV_unique`, `infinite_Pt`, `exists_good`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open scoped Polynomial.Bivariate

namespace RPLib.S4T.FFB

open RPLib.Weil RPLib.DWS

section Red

variable {F : Type*} [Field F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma HV_unique {P : Pt W L} {hP : P ≠ 0} {f : FF W L} {c d : L} (h1 : HV W L P hP f c)
    (h2 : HV W L P hP f d) : c = d := by
  have h3 : HV W L P hP 0 (c - d) := (h1.sub h2).congr (sub_self f) rfl
  by_contra hcd
  exact h3.ne_zero (sub_ne_zero.mpr hcd) rfl

lemma infinite_Pt : Infinite (Pt W L) :=
  Infinite.of_injective (ptX W) (fun a b h => by
    have := congrArg px h
    simpa only [px_ptX] using this)

lemma exists_good {n : ℕ} (hn : (n : L) ≠ 0) {T : Set (Pt W L)} (hT : T.Finite) :
    ∃ P : Pt W L, P ≠ 0 ∧ n • P ≠ 0 ∧ P ∉ T := by
  have := infinite_Pt (W := W) (L := L)
  obtain ⟨P, hP⟩ := ((finite_En (W := W) (L := L) n hn).union
    (hT.union (Set.finite_singleton (0 : Pt W L)))).exists_notMem
  exact ⟨P, fun h => hP (Or.inr (Or.inr h)), fun h => hP (Or.inl h), fun h => hP (Or.inr (Or.inl h))⟩

/-- Specialisation of `n • G` at an affine point `P`. -/
theorem red_nsmul_G (n : ℕ) (P : Pt W L) (hP : P ≠ 0) :
    (n • G W L = 0 → n • P = 0) ∧
    ∀ {ξ η : FF W L} (h : (W.baseChange (FF W L)).toAffine.Nonsingular ξ η),
      n • G W L = Point.some ξ η h → n • P ≠ 0 →
        HV W L P hP ξ (px (n • P)) ∧ HV W L P hP η (py (n • P)) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y hxy =>
  let A : ValuationSubring (FF W L) := (nu W L (Point.some x y hxy) hP).valuationSubring
  have memA : ∀ f, f ∈ A ↔ nu W L (Point.some x y hxy) hP f ≤ 1 := fun f =>
    Valuation.mem_valuationSubring_iff _ f
  have nonA : ∀ f, f ∈ A.nonunits ↔ nu W L (Point.some x y hxy) hP f < 1 := fun f => by
    rw [ValuationSubring.mem_nonunits_iff]
    exact (Valuation.IsEquiv.lt_one_iff_lt_one (Valuation.isEquiv_valuation_valuationSubring _)).symm
  have hL : ∀ c : L, algebraMap L (FF W L) c ∈ A := fun c => (memA _).mpr (nu_alg_le c)
  have hF : ∀ r : F, algebraMap F (FF W L) r ∈ A := fun r => by
    rw [IsScalarTower.algebraMap_apply F L (FF W L)]; exact hL _
  let φA : F →+* A := (algebraMap F (FF W L)).codRestrict A hF
  let ιA : L →+* A := (algebraMap L (FF W L)).codRestrict A hL
  letI : DecidableEq (ResidueField A) := Classical.decEq _
  letI : Algebra F (ResidueField A) := ((residue A).comp φA).toAlgebra
  let WA : WeierstrassCurve A := W.map φA
  have hΔ : (WA.map (residue A)).Δ ≠ 0 := by
    show (W.map ((residue A).comp φA)).Δ ≠ 0
    rw [map_Δ]
    exact (W.isUnit_Δ.map _).ne_zero
  let red : (W.baseChange (FF W L)).toAffine.Point →+ (W.baseChange (ResidueField A)).toAffine.Point :=
    reduceHom (W := WA) hΔ
  let ιR : L →ₐ[F] ResidueField A :=
    { (residue A).comp ιA with
      commutes' := fun r => congrArg (residue A)
        (Subtype.ext (IsScalarTower.algebraMap_apply F L (FF W L) r).symm) }
  have hres : ∀ (f : FF W L) (hf : f ∈ A) (c : L),
      residue A ⟨f, hf⟩ = ιR c ↔ HV W L (Point.some x y hxy) hP f c := by
    intro f hf c
    show residue A ⟨f, hf⟩ = residue A ⟨algebraMap L (FF W L) c, hL c⟩ ↔ _
    rw [ValuationSubring.residue_eq_residue_iff_sub_mem_nonunits, nonA]
    rfl
  have hredS : ∀ {a b : FF W L} (h : (W.baseChange (FF W L)).toAffine.Nonsingular a b) (ha : a ∈ A),
      ∃ (hb : b ∈ A) (h' : (W.baseChange (ResidueField A)).toAffine.Nonsingular (residue A ⟨a, ha⟩)
        (residue A ⟨b, hb⟩)), red (Point.some a b h) = Point.some _ _ h' :=
    fun h ha => ⟨_, _, reducePoint_some_of_mem (W := WA) hΔ h ha⟩
  have hredN : ∀ {a b : FF W L} (h : (W.baseChange (FF W L)).toAffine.Nonsingular a b), a ∉ A →
      red (Point.some a b h) = 0 := fun h ha => reducePoint_some_of_notMem (W := WA) hΔ h ha
  have hgx : gx W L ∈ A := (memA _).mpr (HV_gx W L _ hP).nu_le
  have hG : red (G W L) = Point.map ιR (Point.some x y hxy) := by
    obtain ⟨hb, h', e⟩ := hredS (gen_nonsingular W L) hgx
    rw [G, e, Point.map_some]
    exact some_eq_some ((hres _ _ _).mpr (HV_gx W L _ hP)) ((hres _ _ _).mpr (HV_gy W L _ hP))
  have hmain : red (n • G W L) = Point.map ιR (n • Point.some x y hxy) := by
    rw [map_nsmul, hG, map_nsmul]
  refine ⟨fun h0 => ?_, fun {ξ η} h hn hnP => ?_⟩
  · rw [h0, map_zero] at hmain
    exact Point.map_injective ιR (hmain.symm.trans (map_zero _).symm)
  · rw [hn] at hmain
    by_cases hξ : ξ ∈ A
    · obtain ⟨hb, h', e⟩ := hredS h hξ
      rw [e, eq_some_px_py hnP, Point.map_some, Point.some.injEq] at hmain
      exact ⟨(hres _ _ _).mp hmain.1, (hres _ _ _).mp hmain.2⟩
    · rw [hredN h hξ] at hmain
      exact absurd (Point.map_injective ιR (hmain.symm.trans (map_zero _).symm)) hnP

/-- `n • G ≠ 0` when `n ≠ 0` in `L`. -/
theorem nsmul_G_ne_zero {n : ℕ} (hn : (n : L) ≠ 0) : n • G W L ≠ 0 := by
  intro h0
  obtain ⟨P, hP, hnP, -⟩ := exists_good (W := W) hn Set.finite_empty
  exact hnP ((red_nsmul_G n P hP).1 h0)

/-- The coordinates of `n • G` have values `x(n • P), y(n • P)` at `P` when `n • P ≠ 0`. -/
theorem HV_nsmul_G {n : ℕ} {ξ η : FF W L} {h : (W.baseChange (FF W L)).toAffine.Nonsingular ξ η}
    (hG : n • G W L = Point.some ξ η h) {P : Pt W L} (hP : P ≠ 0) (hnP : n • P ≠ 0) :
    HV W L P hP ξ (px (n • P)) ∧ HV W L P hP η (py (n • P)) :=
  (red_nsmul_G n P hP).2 h hG hnP

end Red

end RPLib.S4T.FFB


