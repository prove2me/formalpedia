-- Prove2me | Definitions.Def_RPLib_S2_IsogenyDeg
-- name    : RPLib_S2_IsogenyDeg
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:24:47.550194+00:00
-- url     : https://prove2.me/theorems/1192ff05-89d6-4c53-8df1-37bf92a7267d
-- title:
--   Degrees of the endomorphisms $r + s\pi$ of an elliptic curve over $\bar{\mathbb{F}}_q$
-- statement:
--   Summary module: for $E/\mathbb{F}_q$ and all integers $r, s$, $\det(r + s\pi \mid E[n]) = \deg(r + s\pi)$ in $\mathbb{Z}/n$ for $n$ prime to $p$, $e_n(\varphi S, \varphi T) = e_n(S,T)^{\deg\varphi}$, $\deg \pi = q$ and $\deg(1 - \pi) = \#E(\mathbb{F}_q)$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (elliptic-curve layer). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, doi:10.1007/978-0-387-09494-6, Sections III.6 and V.1

import Mathlib
import Definitions.Def_RPLib_S2_IsogenyDegF

/-!
# S2-IsogenyDeg: degrees of the endomorphisms `r + s π` of `E(F̄_q)`

For an elliptic curve `W` over a finite field `F` (`q = #F`) and an algebraically closed `L ⊇ F`:

* `rsHom W L r s = r + s π` (`π` = the `q`-power Frobenius `RPLib.EllFq.frob`), represented by the point
  `PhiRS W L r s = r G + s πG` of `W` over the function field; for `r + s π ≠ 0` it has a pullback
  `ψ` on the function field with ramification index `e` (`IsPull`, `exists_isPull_rs`).
* `deg φ = e * #ker φ` (`IsPull.deg_eq`; `deg 0 = 0`).
* `det_rs_eq_deg` : `det (r + s π | E[n]) = deg (r + s π)` in `ℤ/n` for every `n` prime to `p`.
* `ePair_rs` : `e_n((r + s π) S, (r + s π) T) = e_n(S, T) ^ deg (r + s π)`.
* `deg_frob : deg π = q`.
* `exists_isPull_one_sub_frob` (`1 - π` is separable: `e = 1`) and
  **`deg_one_sub_frob : deg (1 - π) = #W(F)`**, hence `det_one_sub_frob : det (1 - π | E[n]) = #W(F)`.
* (part F) for `p ∤ r` (`(r : L) ≠ 0`): `exists_isPull_rs_sep` (`r + s π` is separable, `e = 1`) and
  **`deg_rs_eq_card_ker : deg (r + s π) = #ker (r + s π)`**; also `rsHom_ne_zero`, `torsLin_rs`,
  `det_torsLin_r : det ([r] | E[n]) = r²`, `IsPull.e_eq_one_r`.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace RPLib.Isog

open RPLib.Weil

section Headline

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF torsModule

lemma deg_zero : deg (0 : Pt W L →+ Pt W L) = 0 := by
  have hs : {d | ∃ (ψ : FF W L →ₐ[L] FF W L) (e : ℕ) (hP : IsPull ψ e (0 : Pt W L →+ Pt W L)),
      d = e * hP.finite_ker.toFinset.card} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun d hd => ?_
    obtain ⟨ψ, e, hP, -⟩ := hd
    obtain ⟨v, hv, -⟩ := exists_pt_x W (0 : L)
    obtain ⟨P, hP'⟩ := hP.surjective (Point.some _ _ hv)
    exact Point.some_ne_zero hv (hP'.symm.trans (AddMonoidHom.zero_apply P))
  rw [deg, hs, Nat.sInf_empty]

lemma det_torsLin_zero (n : ℕ) [NeZero n] (hn : (n : L) ≠ 0) :
    LinearMap.det (torsLin (0 : Pt W L →+ Pt W L) n) = 0 := by
  obtain ⟨eqv⟩ := RPLib.Torsion.tors_equiv (W := W.baseChange L) n hn
  let eL := eqv.toLinearEquiv (ZMod.map_smul (n := n) eqv)
  let b := (Module.Basis.finTwoProd (ZMod n)).map eL.symm
  have h0 : torsLin (0 : Pt W L →+ Pt W L) n = 0 :=
    LinearMap.ext fun P => Subtype.ext (by rw [torsLin_apply]; rfl)
  rw [h0, LinearMap.det_zero' b]

/-- **`det (r + s π | E[n]) = deg (r + s π)`** in `ℤ/n`, for every `n` prime to `p`. -/
theorem det_rs_eq_deg (r s : ℤ) (n : ℕ) [NeZero n] (hn : (n : L) ≠ 0) :
    LinearMap.det (torsLin (rsHom W L r s) n) = (deg (rsHom W L r s) : ZMod n) := by
  by_cases h : rsHom W L r s = 0
  · rw [h, deg_zero, det_torsLin_zero n hn, Nat.cast_zero]
  · obtain ⟨ψ, e, hP⟩ := exists_isPull_rs r s h
    exact hP.det_eq_deg n hn

/-- **Pairing compatibility** for `r + s π ≠ 0`. -/
theorem ePair_rs (r s : ℤ) (h : rsHom W L r s ≠ 0) {n : ℕ} (hn : (n : L) ≠ 0) {S T : Pt W L}
    (hS : n • S = 0) (hT : n • T = 0) :
    ePair W L n (rsHom W L r s S) (rsHom W L r s T) = ePair W L n S T ^ deg (rsHom W L r s) := by
  obtain ⟨ψ, e, hP⟩ := exists_isPull_rs r s h
  exact hP.ePair_deg hn hS hT

/-- **`det (1 - π | E[n]) = #W(F)`** in `ℤ/n`, for every `n` prime to `p`. -/
theorem det_one_sub_frob (n : ℕ) [NeZero n] (hn : (n : L) ≠ 0) :
    LinearMap.det (torsLin (rsHom W L 1 (-1)) n) = (RPLib.EllFq.numPoints W : ZMod n) := by
  rw [det_rs_eq_deg 1 (-1) n hn, deg_one_sub_frob]

end Headline

end RPLib.Isog


