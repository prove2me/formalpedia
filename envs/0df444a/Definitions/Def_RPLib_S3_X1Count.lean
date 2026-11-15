-- Prove2me | Definitions.Def_RPLib_S3_X1Count
-- name    : RPLib_S3_X1Count
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:27:19.815197+00:00
-- url     : https://prove2.me/theorems/e02736b9-e9b7-413d-b179-fd48520f28b7
-- title:
--   Weight-two Ramanujan-Petersson library: Point counts of `Y₁(M)` over `F_{p^m}` versus degree-1 places
-- statement:
--   Point counts of `Y₁(M)` over `F_{p^m}` versus degree-1 places.
--
--   Namespace `RamanujanPetersson.X1Count`. Main result **`card_Y1_sub_numPoints_le`**: for `p` prime, `M ≥ 4`,
--   `p ∤ M`, there are a nonempty finite family of plane-curve components `g i : Comp (ZMod p)` (monic in `Y`,
--   irreducible, `∂g/∂Y ≠ 0`; function fields `(g i).FF` over `ZMod p`) and a constant `C` with
--   `|#Y₁(M)(GaloisField p m) - Σ_i numPoints (ZMod p) (g i).FF m| ≤ C` for all `m ≥ 1`.
--
--   * `_A`: `polyG`, `polyH`, `mem_Y1_iff_poly` (`(b,c) ∈ Y₁(M)(F) ↔ G_M(b,c) = 0 ∧ H_M(b,c) ≠ 0`, `M ≥ 4`),
--     `exists_mem_Y1` (a point over `AlgebraicClosure (ZMod p)`), `polyGp`, `polyHp`, `mem_Y1_iff_polyp`,
--     `polyGp_ne_zero`, `exists_good_point`.
--   * `_B`: `ev`, `Comp k`, `Comp.FF` (a function field over `k`), `card_algHom_le_of_conductor`, `ptEquiv`,
--     **`Comp.card_points_sub_numPoints_le`** (`|#{g = 0}(L) - numPoints k g.FF [L : k]| ≤ C_g`).
--   * `_C`: `card_common_le` (Bezout-lite), `count_good` (assembly), Nagata shear `sig`, `derivative_shS_ne_zero`,
--     `conv`/`ev_conv`.
--
--   The nonempty family replaces the goal's "rational cusp" (NOTES.md D1): the sign argument of S3_DESIGN item 6 then
--   forces one component with full constant field. The constant field of the component is not computed here.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_X1CountA
import Definitions.Def_RPLib_S3_X1CountC

/-!
# Point counts of `Y₁(M)` over `F_{p^m}` versus degree-1 places (unit S3-X1Count, goal file)

Namespace `RamanujanPetersson.X1Count`. Main result **`card_Y1_sub_numPoints_le`**: for `p` prime, `M ≥ 4`,
`p ∤ M`, there are a nonempty finite family of plane-curve components `g i : Comp (ZMod p)` (monic in `Y`,
irreducible, `∂g/∂Y ≠ 0`; function fields `(g i).FF` over `ZMod p`) and a constant `C` with
`|#Y₁(M)(GaloisField p m) - Σ_i numPoints (ZMod p) (g i).FF m| ≤ C` for all `m ≥ 1`.

* `_A`: `polyG`, `polyH`, `mem_Y1_iff_poly` (`(b,c) ∈ Y₁(M)(F) ↔ G_M(b,c) = 0 ∧ H_M(b,c) ≠ 0`, `M ≥ 4`),
  `exists_mem_Y1` (a point over `AlgebraicClosure (ZMod p)`), `polyGp`, `polyHp`, `mem_Y1_iff_polyp`,
  `polyGp_ne_zero`, `exists_good_point`.
* `_B`: `ev`, `Comp k`, `Comp.FF` (a function field over `k`), `card_algHom_le_of_conductor`, `ptEquiv`,
  **`Comp.card_points_sub_numPoints_le`** (`|#{g = 0}(L) - numPoints k g.FF [L : k]| ≤ C_g`).
* `_C`: `card_common_le` (Bezout-lite), `count_good` (assembly), Nagata shear `sig`, `derivative_shS_ne_zero`,
  `conv`/`ev_conv`.

The nonempty family replaces the goal's "rational cusp" (NOTES.md D1): the sign argument of S3_DESIGN item 6 then
forces one component with full constant field. The constant field of the component is not computed here.
-/

set_option autoImplicit false

open Polynomial

namespace RamanujanPetersson.X1Count

open RamanujanPetersson.Places

/-! ### The final count -/

section Final

variable (p : ℕ) [Fact p.Prime]

/-- **Point count of `Y₁(M)` over `F_{p^m}`** (`M ≥ 4`, `p ∤ M`): a nonempty finite family of components
`g_i` (function fields `FF g_i` over `F_p`) with `|#Y₁(M)(F_{p^m}) - Σ_i N_m(FF g_i)| ≤ C` for all `m ≥ 1`. -/
theorem card_Y1_sub_numPoints_le [DecidableEq (RatFunc (ZMod p))] {M : ℕ} (hM : 4 ≤ M) (hpM : ¬ p ∣ M) :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty ι ∧ ∃ (g : ι → Comp (ZMod p)) (C : ℕ), ∀ m : ℕ, 1 ≤ m →
      ∀ [DecidableEq (GaloisField p m)],
        |(Nat.card (RPLib.TateNF.Y1 (GaloisField p m) M) : ℤ) -
          ∑ i, (numPoints (ZMod p) (g i).FF m : ℤ)| ≤ C := by
  classical
  have hp := (Fact.out : p.Prime)
  set G0 : (ZMod p)[X][X] := conv (polyGp p M) with hG0
  set H0 : (ZMod p)[X][X] := conv (polyHp p M) with hH0
  have hG0ne : G0 ≠ 0 := fun h => polyGp_ne_zero p hM (by rw [← convBack_conv (polyGp p M), ← hG0, h, map_zero])
  set N : ℕ := p * (G0.natDegree + 2) + 1 with hNdef
  have hNle : G0.natDegree + 2 ≤ p * (G0.natDegree + 2) := Nat.le_mul_of_pos_left _ hp.pos
  have hNk : ((N : ℕ) : ZMod p) ≠ 0 := by
    rw [hNdef, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add, Nat.cast_one]
    exact one_ne_zero
  set F := sig (k := ZMod p) N G0 with hF
  set E := sig (k := ZMod p) N H0 with hE
  have hFne : F ≠ 0 := by rw [hF]; exact (map_ne_zero_iff _ (sig N).injective).mpr hG0ne
  have hlcF : IsUnit F.leadingCoeff := isUnit_lc_shS N (by omega) G0 hG0ne (by omega)
  have hlc : ∀ g, g ∣ F → IsUnit g.leadingCoeff := by
    rintro g ⟨q, hq⟩
    rw [hq, leadingCoeff_mul] at hlcF
    exact isUnit_of_mul_isUnit_left hlcF
  have hder : ∀ g, Irreducible g → g ∣ F → derivative g ≠ 0 := by
    intro g hg hgF
    have e : g = shS (X ^ N) ((sig N).symm g) := ((sig N).apply_symm_apply g).symm
    have hirr : Irreducible ((sig (k := ZMod p) N).symm g) := (MulEquiv.irreducible_iff (sig N)).mp (by
      rw [RingEquiv.apply_symm_apply]; exact hg)
    have hdvd : (sig (k := ZMod p) N).symm g ∣ G0 := by
      have := map_dvd (sig (k := ZMod p) N).symm hgF
      rwa [hF, RingEquiv.symm_apply_apply] at this
    have hdeg := natDegree_le_of_dvd hdvd hG0ne
    rw [e]
    exact derivative_shS_ne_zero p hNk hirr (by omega)
  obtain ⟨S, hS, hcov, C0, hC0⟩ := count_good F E hFne hlc hder
  -- nonemptiness from a good point over the algebraic closure
  have hne : S.Nonempty := by
    obtain ⟨v, hvG, hvH⟩ := exists_good_point p hM hpM
    have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    set w : AlgebraicClosure (ZMod p) × AlgebraicClosure (ZMod p) := (v 0 - v 1 ^ N, v 1)
    have ew : ∀ P : MvPolynomial (Fin 2) (ZMod p), ev w (sig (k := ZMod p) N (conv P)) = MvPolynomial.aeval v P :=
      fun P => by
      rw [ev_sig, ev_conv]
      simp only [w, sub_add_cancel, hv]
    obtain ⟨g, hg, -⟩ := hcov _ w (by rw [hF, hG0, ew, hvG]) (by rw [hE, hH0, ew]; exact hvH)
    exact ⟨g, hg⟩
  let gC : S → Comp (ZMod p) := fun g => ⟨g.1, (hS g.1 g.2).1, (hS g.1 g.2).2.1, (hS g.1 g.2).2.2.1⟩
  choose Cg hCg using fun i : S => (gC i).card_points_sub_numPoints_le
  refine ⟨S, inferInstance, hne.coe_sort, gC, C0 + ∑ i, Cg i, fun m hm _ => ?_⟩
  have hfin : Module.finrank (ZMod p) (GaloisField p m) = m := GaloisField.finrank p (by omega)
  -- the plane count equals #Y1
  have hY : Nat.card (RPLib.TateNF.Y1 (GaloisField p m) M) = Nat.card {v : GaloisField p m × GaloisField p m // ev v F = 0 ∧ ev v E ≠ 0} := by
    have key : ∀ v : GaloisField p m × GaloisField p m, (ev v F = 0 ∧ ev v E ≠ 0) ↔ (v.1 + v.2 ^ N, v.2) ∈ RPLib.TateNF.Y1 (GaloisField p m) M := by
      intro v
      rw [mem_Y1_iff_polyp p hM, hF, hE, ev_sig, ev_sig, hG0, hH0, ev_conv, ev_conv]
    refine (Nat.card_congr ⟨fun x => ⟨(x.1.1 - x.1.2 ^ N, x.1.2), ?_⟩,
      fun v => ⟨(v.1.1 + v.1.2 ^ N, v.1.2), (key v.1).mp v.2⟩, fun x => ?_, fun v => ?_⟩)
    · rw [key]; simpa using x.2
    · ext <;> simp
    · ext <;> simp
  have hsplit : ∀ i : S, |(Nat.card {v : GaloisField p m × GaloisField p m // ev v (i : (ZMod p)[X][X]) = 0} : ℤ) -
      numPoints (ZMod p) (gC i).FF m| ≤ Cg i := fun i => by
    have := hCg i (GaloisField p m)
    rwa [hfin] at this
  have hsum : ∑ g ∈ S, (Nat.card {v : GaloisField p m × GaloisField p m // ev v g = 0} : ℤ) =
      ∑ i : S, (Nat.card {v : GaloisField p m × GaloisField p m // ev v (i : (ZMod p)[X][X]) = 0} : ℤ) :=
    (Finset.sum_coe_sort S fun g => (Nat.card {v : GaloisField p m × GaloisField p m // ev v g = 0} : ℤ)).symm
  have h0 := hC0 (GaloisField p m)
  rw [hsum] at h0
  rw [show Nat.card (RPLib.TateNF.Y1 (GaloisField p m) M) = _ from hY]
  calc |(Nat.card {v : GaloisField p m × GaloisField p m // ev v F = 0 ∧ ev v E ≠ 0} : ℤ) - ∑ i, (numPoints (ZMod p) (gC i).FF m : ℤ)|
      ≤ |(Nat.card {v : GaloisField p m × GaloisField p m // ev v F = 0 ∧ ev v E ≠ 0} : ℤ) -
          ∑ i : S, (Nat.card {v : GaloisField p m × GaloisField p m // ev v (i : (ZMod p)[X][X]) = 0} : ℤ)| +
        |∑ i : S, (Nat.card {v : GaloisField p m × GaloisField p m // ev v (i : (ZMod p)[X][X]) = 0} : ℤ) -
          ∑ i, (numPoints (ZMod p) (gC i).FF m : ℤ)| := abs_sub_le _ _ _
    _ ≤ C0 + ∑ i, (Cg i : ℤ) := by
        refine add_le_add h0 ?_
        rw [← Finset.sum_sub_distrib]
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hsplit i)
    _ = ((C0 + ∑ i, Cg i : ℕ) : ℤ) := by push_cast; ring

end Final

end RamanujanPetersson.X1Count


