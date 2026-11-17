-- Prove2me | Definitions.Def_RPLib_S4T_FFBridge
-- name    : RPLib_S4T_FFBridge
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-16T07:24:52.421258+00:00
-- url     : https://prove2.me/theorems/32cb1f7c-0376-4164-a347-91833da95ea4
-- title:
--   Tate's isogeny theorem over finite fields (prime-to-$p$ form), library: the L9 function-field bridge
-- statement:
--   The L9 function-field bridge.
--
--   **`l9 : RPLib.S4T.Glue.L9Stmt`**. `F`-rational `u : W → W'`, `w : W' → W` over an algebraically closed `k ⊇ F`
--   with `w ∘ u = [N]`, `N ≠ 0` in `F`: the pullbacks `f = u^*`, `g = w^*` (`exists_pullback`) satisfy
--   `(f ∘ g)(x0, y0) = N • (x0, y0)`. Proof: map to `k(E)` by `jFF`; the coordinates of both sides have the same value
--   `x(N • P)`, `y(N • P)` at all but finitely many points `P` (`HV_rep` twice, `HV_nsmul_G`), so they agree.
--
--   **Formalization note.** Library module of a formalization of Tate's isogeny theorem over finite fields in prime-to-$p$ form (ordinary elliptic curves with the same number of points are linked by $F$-isogenies $u, w$ with $w \circ u = [N]$, $p \nmid N$, stated through $F$-algebra maps of function fields), via Deuring lifting to characteristic $0$. It is conditional only on fifteen Proved prove2.me theorems of the FLT project, which enter as explicit hypotheses whose types are their exact statements (never as lemmas). Part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144, Theorem 1; M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560, Chapter 4; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Sections III.6-III.7

import Mathlib
import Definitions.Def_RPLib_S4T_FFBridgeC
import Definitions.Def_RPLib_S4T_Glue

/-!
# S4T-FFBridge: the L9 function-field bridge

**`l9 : RPLib.S4T.Glue.L9Stmt`**. `F`-rational `u : W → W'`, `w : W' → W` over an algebraically closed `k ⊇ F`
with `w ∘ u = [N]`, `N ≠ 0` in `F`: the pullbacks `f = u^*`, `g = w^*` (`exists_pullback`) satisfy
`(f ∘ g)(x0, y0) = N • (x0, y0)`. Proof: map to `k(E)` by `jFF`; the coordinates of both sides have the same value
`x(N • P)`, `y(N • P)` at all but finitely many points `P` (`HV_rep` twice, `HV_nsmul_G`), so they agree.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace RPLib.S4T.FFB

open RPLib.Weil RPLib.DWS

attribute [local instance] finite_coordinateRing decEqFF

/-- **L9** (function-field bridge). -/
theorem l9 : RPLib.S4T.Glue.L9Stmt := by
  intro F _ _ W W' _ _ k _ _ _ _ u w hu hw N hN hwu
  have hNk : (N : k) ≠ 0 := by
    rw [← map_natCast (algebraMap F k) N]; exact (_root_.map_ne_zero _).mpr hN
  obtain ⟨hu0, hw0⟩ := ne_zero_of_comp hNk hwu
  obtain ⟨nX, dX, nY, dY, B, hB, hrep⟩ :=
    (show u = 0 ∨ IsRationallyRepresented k W W' u from hu).resolve_left hu0
  obtain ⟨mX, eX, mY, eY, B', hB', hrep'⟩ :=
    (show w = 0 ∨ IsRationallyRepresented k W' W w from hw).resolve_left hw0
  have hker : {P : Pt W k | u P = 0}.Finite := ker_finite_of_comp hwu (finite_En N hNk)
  have hbad' : {Q : Pt W' k | Q = 0 ∨ px Q ∈ B'}.Finite :=
    ((Set.finite_singleton 0).union (finite_px hB')).subset (fun Q hQ => by
      by_cases h0 : Q = 0
      · exact Or.inl h0
      · exact Or.inr ⟨h0, hQ.resolve_left h0⟩)
  let T : Set (Pt W k) :=
    {P | P ≠ 0 ∧ px P ∈ B} ∪ (u ⁻¹' {Q | Q = 0 ∨ px Q ∈ B'} ∪ {P | N • P = 0})
  have hT : T.Finite := (finite_px hB).union ((finite_preimage u hker hbad').union (finite_En N hNk))
  have hgood : ∀ P : Pt W k, P ≠ 0 → P ∉ T → px P ∉ B ∧ u P ≠ 0 ∧ px (u P) ∉ B' ∧ N • P ≠ 0 :=
    fun P hP hPT => ⟨fun h => hPT (Or.inl ⟨hP, h⟩), fun h => hPT (Or.inr (Or.inl (Or.inl h))),
      fun h => hPT (Or.inr (Or.inl (Or.inr h))), fun h => hPT (Or.inr (Or.inr h))⟩
  have hInf := infinite_Pt (W := W) (L := k)
  have hinfu : (u '' {P | P ≠ 0 ∧ px P ∉ B}).Infinite := by
    intro hfin
    have h1 := finite_preimage u hker hfin
    exact Set.infinite_univ (((h1.union (Set.finite_singleton 0)).union (finite_px hB)).subset
      (fun P _ => by
        by_cases h0 : P = 0
        · exact Or.inl (Or.inr h0)
        · by_cases hb : px P ∈ B
          · exact Or.inr ⟨h0, hb⟩
          · exact Or.inl (Or.inl (Set.subset_preimage_image u _ ⟨h0, hb⟩))))
  obtain ⟨f, hfx, hfy⟩ := exists_pullback hB hrep hinfu
  have hinfw : (w '' {Q | Q ≠ 0 ∧ px Q ∉ B'}).Infinite := by
    have hsub : (w.comp u) '' {P | P ≠ 0 ∧ P ∉ T} ⊆ w '' {Q | Q ≠ 0 ∧ px Q ∉ B'} := by
      rintro _ ⟨P, ⟨hP, hPT⟩, rfl⟩
      obtain ⟨-, h1, h2, -⟩ := hgood P hP hPT
      exact ⟨u P, ⟨h1, h2⟩, rfl⟩
    refine Set.Infinite.mono hsub ?_
    intro hfin
    have hk : {P : Pt W k | (w.comp u) P = 0}.Finite :=
      (finite_En N hNk).subset (fun P (hP : w (u P) = 0) => by
        show N • P = 0
        rw [← wu_apply hwu P]; exact hP)
    have h1 := finite_preimage (w.comp u) hk hfin
    exact Set.infinite_univ (((h1.union (Set.finite_singleton 0)).union hT).subset (fun P _ => by
      by_cases h0 : P = 0
      · exact Or.inl (Or.inr h0)
      · by_cases hb : P ∈ T
        · exact Or.inr hb
        · exact Or.inl (Or.inl (Set.subset_preimage_image _ _ ⟨h0, hb⟩))))
  obtain ⟨g, hgx, hgy⟩ := exists_pullback hB' hrep' hinfw
  -- the generic multiple `N • G`
  obtain ⟨ξ, η, hξη, hGN⟩ : ∃ (ξ η : FF W k) (h : (W.baseChange (FF W k)).toAffine.Nonsingular ξ η),
      N • G W k = Point.some ξ η h := ⟨_, _, _, eq_some_px_py (nsmul_G_ne_zero (W := W) hNk)⟩
  have hfg : ∀ p : F[X][Y], jFF W k (f (ev W'.toAffine.FunctionField (x0 W') (y0 W') p)) =
      ev (FF W k) (jFF W k (f (x0 W'))) (jFF W k (f (y0 W'))) p := fun p =>
    (congrArg (jFF W k) (evalEvalBC_algHom f p (x0 W') (y0 W'))).trans
      (evalEvalBC_algHom (jFF W k) p _ _)
  have hXu : jFF W k (f (x0 W')) =
      ev (FF W k) (gx W k) (gy W k) nX / ev (FF W k) (gx W k) (gy W k) dX := by
    rw [hfx, map_div₀, jFF_ev, jFF_ev]
  have hYu : jFF W k (f (y0 W')) =
      ev (FF W k) (gx W k) (gy W k) nY / ev (FF W k) (gx W k) (gy W k) dY := by
    rw [hfy, map_div₀, jFF_ev, jFF_ev]
  have hval : ∀ (P : Pt W k) (hP : P ≠ 0), P ∉ T →
      HV W k P hP (jFF W k (f (g (x0 W)))) (px (N • P)) ∧
        HV W k P hP (jFF W k (f (g (y0 W)))) (py (N • P)) := by
    intro P hP hPT
    obtain ⟨hPB, hu0', huB, -⟩ := hgood P hP hPT
    obtain ⟨-, hx, hy⟩ := HV_rep hrep hP hPB (HV_gx W k P hP) (HV_gy W k P hP)
    rw [← hXu] at hx
    rw [← hYu] at hy
    obtain ⟨-, hx', hy'⟩ := HV_rep hrep' hu0' huB hx hy
    rw [wu_apply hwu] at hx' hy'
    simp only [hgx, hgy, map_div₀, hfg]
    exact ⟨hx', hy'⟩
  have hxe : jFF W k (f (g (x0 W))) = ξ := sub_eq_zero.mp (eq_zero_of_HV hT (fun P hP hPT =>
    ((hval P hP hPT).1.sub (HV_nsmul_G hGN hP (hgood P hP hPT).2.2.2).1).congr rfl (sub_self _)))
  have hye : jFF W k (f (g (y0 W))) = η := sub_eq_zero.mp (eq_zero_of_HV hT (fun P hP hPT =>
    ((hval P hP hPT).2.sub (HV_nsmul_G hGN hP (hgood P hP hPT).2.2.2).2).congr rfl (sub_self _)))
  refine ⟨f, g, N, hN, gen0_nonsingular W, ?_⟩
  apply Point.map_injective (W' := W.toAffine) (jFF W k)
  show Point.map (W' := W.toAffine) (jFF W k) (Point.map (W' := W.toAffine) (f.comp g) (P0 W)) =
    Point.map (W' := W.toAffine) (jFF W k) (N • P0 W)
  rw [map_nsmul, map_jFF_P0, hGN, P0, Point.map_some, Point.map_some]
  exact some_eq_some hxe hye

end RPLib.S4T.FFB


