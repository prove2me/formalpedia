-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogN
-- name    : RPLib_S3_DWSIsogN
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:59:30.905792+00:00
-- url     : https://prove2.me/theorems/99cb29bc-154b-4471-9699-2d31ec641663
-- title:
--   Weight-two Ramanujan-Petersson library: `G`-invariant functions come from `E/G`
-- statement:
--   `G`-invariant functions come from `E/G`.
--
--   `qR hW'` is the image of the pullback `L(E') → L(E)`, `f ↦ f ∘ Ψ`, along the quotient map.
--   * **`goodQ_mem_qR`** : an invariant function regular off `G` is a polynomial in `X_G, Y_G` (induction on the pole
--     order at `O`, using `GoodQ.lead` with the monomials `X_G^a Y_G^b` and the simple-pole lemma).
--   * **`invG_mem_qR`** : every `G`-invariant function lies in `qR hW'` (clear the poles off `G` with powers of
--     `X_G - X_G(P)`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogM

/-!
# S3-DWS-Isog, part N: `G`-invariant functions come from `E/G`

`qR hW'` is the image of the pullback `L(E') → L(E)`, `f ↦ f ∘ Ψ`, along the quotient map.
* **`goodQ_mem_qR`** : an invariant function regular off `G` is a polynomial in `X_G, Y_G` (induction on the pole
  order at `O`, using `GoodQ.lead` with the monomials `X_G^a Y_G^b` and the simple-pole lemma).
* **`invG_mem_qR`** : every `G`-invariant function lies in `qR hW'` (clear the poles off `G` with powers of
  `X_G - X_G(P)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section Range

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {G : AddSubgroup (Pt W L)} [Fintype G] {W' : WeierstrassCurve F} [W'.IsElliptic]

/-- The image of `L(E')` in `L(E)` under the quotient map. -/
noncomputable abbrev qR (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) :
    Subalgebra L (FF W L) :=
  (pull2 (qPt hW') (qPt_ne_ιQ hW')).range

lemma qx_mem_qR (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) : qx G ∈ qR hW' :=
  (AlgHom.mem_range _).mpr ⟨gx W' L, (pull2_gx _ _).trans (px_qPt hW')⟩

lemma qy_mem_qR (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) : qy G ∈ qR hW' :=
  (AlgHom.mem_range _).mpr ⟨gy W' L, (pull2_gy _ _).trans (py_qPt hW')⟩

lemma inv_mem_qR (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) {f : FF W L}
    (hf : f ∈ qR hW') : f⁻¹ ∈ qR hW' := by
  obtain ⟨u, rfl⟩ := (AlgHom.mem_range _).mp hf
  exact (AlgHom.mem_range _).mpr ⟨u⁻¹, map_inv₀ _ u⟩

/-- **Invariant functions regular off `G` are polynomials in `X_G, Y_G`.** -/
theorem goodQ_mem_qR (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) {f : FF W L} (hf : GoodQ G f) :
    f ∈ qR hW' := by
  have hx := qx_mem_qR hW'
  have hy := qy_mem_qR hW'
  have hconst : ∀ c : L, algebraMap L (FF W L) c ∈ qR hW' := fun c => Subalgebra.algebraMap_mem _ c
  have key : ∀ n : ℕ, ∀ f : FF W L, GoodQ G f → Ge (-(n : ℤ)) f 0 → f ∈ qR hW' := by
    intro n
    induction n with
    | zero =>
      intro f hf h0
      obtain ⟨c, rfl⟩ := hf.eq_const (by simpa using h0)
      exact hconst c
    | succ n ih =>
      intro f hf hfn
      by_cases hf0 : f = 0
      · rw [hf0]; exact zero_mem _
      by_cases hn : n = 0
      · subst hn
        have h1 := hfn.resolve_left hf0
        have h2 := hf.ord_ne_neg_one hG hf0
        push_cast at h1
        obtain ⟨c, rfl⟩ := hf.eq_const (Or.inr (by omega))
        exact hconst c
      obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, 2 * a + 3 * b = n + 1 := by
        rcases Nat.even_or_odd (n + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
        · exact ⟨k, 0, by omega⟩
        · exact ⟨k - 1, 1, by omega⟩
      have hM : GoodQ G (qx G ^ a * qy G ^ b) := (goodQ_qx.pow a).mul (goodQ_qy.pow b)
      have hxa : qx G ^ a ≠ 0 := pow_ne_zero _ (ord_qx_zero (G := G)).1
      have hyb : qy G ^ b ≠ 0 := pow_ne_zero _ (ord_qy_zero (G := G)).1
      have hMn : ord W L (qx G ^ a * qy G ^ b) 0 = -((n + 1 : ℕ) : ℤ) := by
        rw [ord_mul hxa hyb, ord_pow, ord_pow, (ord_qx_zero (G := G)).2, (ord_qy_zero (G := G)).2]
        push_cast; omega
      obtain ⟨c, hc, hcn⟩ := hf.lead hM (mul_ne_zero hxa hyb) hMn hfn
      have h1 := ih _ hc (hcn.mono (by push_cast; omega))
      have h2 : f = (f - algebraMap L (FF W L) c * (qx G ^ a * qy G ^ b)) +
          algebraMap L (FF W L) c * (qx G ^ a * qy G ^ b) := by ring
      rw [h2]
      exact add_mem h1 (mul_mem (hconst c) (mul_mem (pow_mem hx a) (pow_mem hy b)))
  by_cases hf0 : f = 0
  · rw [hf0]; exact zero_mem _
  exact key (-ord W L f 0).toNat f hf (Or.inr (by have := Int.self_le_toNat (-ord W L f 0); omega))

lemma Ge.prod0 {ι : Type*} {s : Finset ι} {g : ι → FF W L} {P : Pt W L} (h : ∀ i ∈ s, Ge 0 (g i) P) :
    Ge 0 (∏ i ∈ s, g i) P :=
  Finset.prod_induction g (fun x => Ge 0 x P) (fun _ _ ha hb => ha.mul0 hb)
    (by rw [← map_one (algebraMap L (FF W L))]; exact Ge.const 1 P) h

lemma ge_one_of_HV0 {P : Pt W L} {hP : P ≠ 0} {f : FF W L} (h : HV W L P hP f 0) : Ge 1 f P := by
  by_cases hf : f = 0
  · exact Or.inl hf
  · exact Or.inr (one_le_ord_of_HV h hf)

variable (G) in
open scoped Classical in
/-- `X_G - X_G(P)` for `P ∉ G` (and `1` on `G`). -/
noncomputable def clr (P : Pt W L) : FF W L :=
  if hP : P ∈ G then 1 else qx G - algebraMap L (FF W L)
    (Classical.choose (exists_HV_of_ge (ne_zero_of_nmem hP) ((goodQ_qx (G := G)).2 P hP)))

lemma clr_mem (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) (P : Pt W L) :
    clr G P ∈ qR hW' := by
  unfold clr
  split_ifs
  · exact one_mem _
  · exact sub_mem (qx_mem_qR hW') (Subalgebra.algebraMap_mem _ _)

lemma clr_inv (P : Pt W L) : InvG G (clr G P) := by
  intro S hS
  unfold clr
  split_ifs
  · exact map_one _
  · rw [map_sub, AlgEquiv.commutes, (goodQ_qx (G := G)).1 S hS]

lemma clr_ne_zero (P : Pt W L) : clr G P ≠ 0 := by
  unfold clr
  split_ifs
  · exact one_ne_zero
  · exact (qx_sub_ord _).1

lemma clr_ge {Q : Pt W L} (hQ : Q ∉ G) (P : Pt W L) : Ge 0 (clr G P) Q := by
  unfold clr
  split_ifs
  · rw [← map_one (algebraMap L (FF W L))]; exact Ge.const 1 Q
  · exact ((goodQ_qx (G := G)).2 Q hQ).sub (Ge.const _ Q)

lemma clr_ge_one {P : Pt W L} (hP : P ∉ G) : Ge 1 (clr G P) P := by
  unfold clr
  rw [dif_neg hP]
  exact ge_one_of_HV0 (HV_sub_self (Classical.choose_spec
    (exists_HV_of_ge (ne_zero_of_nmem hP) ((goodQ_qx (G := G)).2 P hP))))

/-- **Every `G`-invariant function comes from `E/G`.** -/
theorem invG_mem_qR (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) {f : FF W L} (hf : InvG G f) :
    f ∈ qR hW' := by
  by_cases hf0 : f = 0
  · rw [hf0]; exact zero_mem _
  set Z := (ord_finite hf0).toFinset with hZ
  set m : ℕ := ∑ P ∈ Z, (ord W L f P).natAbs with hm
  set h : FF W L := ∏ P ∈ Z, clr G P ^ m with hh
  have hhR : h ∈ qR hW' := prod_mem fun P _ => pow_mem (clr_mem hW' P) m
  have hh0 : h ≠ 0 := Finset.prod_ne_zero_iff.mpr fun P _ => pow_ne_zero _ (clr_ne_zero P)
  have hinv : InvG G (f * h) := by
    intro S hS
    rw [map_mul, hf S hS, hh, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun P _ => by rw [map_pow, clr_inv P S hS]
  have hoff : ∀ Q : Pt W L, Q ∉ G → Ge 0 (f * h) Q := by
    intro Q hQ
    by_cases hQZ : Q ∈ Z
    · rw [hh, ← Finset.mul_prod_erase Z _ hQZ]
      have hle : (ord W L f Q).natAbs ≤ m := by
        rw [hm]
        exact Finset.single_le_sum (f := fun P => (ord W L f P).natAbs) (fun _ _ => Nat.zero_le _) hQZ
      have h1 : Ge (ord W L f Q) f Q := Or.inr le_rfl
      have h2 := (clr_ge_one hQ).pow m
      have h3 : Ge 0 (∏ P ∈ Z.erase Q, clr G P ^ m) Q :=
        Ge.prod0 fun P _ => ((clr_ge hQ P).pow m).mono (by simp)
      exact (h1.mul (h2.mul h3)).mono (by omega)
    · have hz : ord W L f Q = 0 := by
        by_contra hz
        exact hQZ ((Set.Finite.mem_toFinset _).mpr hz)
      exact Ge.mul0 (Or.inr hz.symm.le)
        (Ge.prod0 fun P _ => ((clr_ge hQ P).pow m).mono (by simp))
  have hmem := goodQ_mem_qR hG hW' ⟨hinv, hoff⟩
  have e : f = (f * h) * h⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hh0, mul_one]
  rw [e]
  exact mul_mem hmem (inv_mem_qR hW' hhR)

end Range

end RPLib.DWS


