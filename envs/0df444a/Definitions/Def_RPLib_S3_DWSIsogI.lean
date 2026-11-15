-- Prove2me | Definitions.Def_RPLib_S3_DWSIsogI
-- name    : RPLib_S3_DWSIsogI
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:42:19.656398+00:00
-- url     : https://prove2.me/theorems/bf6fd11f-f846-408d-89e5-78ec6ba4d936
-- title:
--   Weight-two Ramanujan-Petersson library: values of `(X_G, Y_G)`, surjectivity and fibers
-- statement:
--   Values of `(X_G, Y_G)`, surjectivity and fibers.
--
--   Setting: `G` a finite subgroup of `E(L)` with `p ∤ #G`, `W'` elliptic over `F`, `(X_G, Y_G) ∈ W'(L(E))`.
--   * `HV` bridges (`ge_of_HV`, `exists_HV_of_ge`, `HV_unique`, `HV_of_sub_mem`, ...).
--   * `eqn_of_HV` : the values of `(X_G, Y_G)` at `P ∉ G` lie on `W'`.
--   * `key_id` : `(Y - c)(Y - c') = -(X - a) M` for `(a, c) ∈ W'`, `c' = -c - a₁a - a₃`.
--   * `exists_preimage` : every affine non-2-torsion point of `W'` is a value of `(X_G, Y_G)` (via `L2`).
--   * `count_le`, **`fiber`** : two points off `G` with the same value differ by an element of `G`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib
import Definitions.Def_RPLib_S3_DWSIsogH

/-!
# S3-DWS-Isog, part I: values of `(X_G, Y_G)`, surjectivity and fibers

Setting: `G` a finite subgroup of `E(L)` with `p ∤ #G`, `W'` elliptic over `F`, `(X_G, Y_G) ∈ W'(L(E))`.
* `HV` bridges (`ge_of_HV`, `exists_HV_of_ge`, `HV_unique`, `HV_of_sub_mem`, ...).
* `eqn_of_HV` : the values of `(X_G, Y_G)` at `P ∉ G` lie on `W'`.
* `key_id` : `(Y - c)(Y - c') = -(X - a) M` for `(a, c) ∈ W'`, `c' = -c - a₁a - a₃`.
* `exists_preimage` : every affine non-2-torsion point of `W'` is a value of `(X_G, Y_G)` (via `L2`).
* `count_le`, **`fiber`** : two points off `G` with the same value differ by an element of `G`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
open IsDedekindDomain
open scoped nonZeroDivisors

namespace RPLib.DWS

open RPLib.Weil RPLib.Isog RPLib.Hasse

section ValHV

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

lemma ge_of_HV {P : Pt W L} {hP : P ≠ 0} {f : FF W L} {c : L} (h : HV W L P hP f c) : Ge 0 f P := by
  by_cases hf : f = 0
  · exact Or.inl hf
  · exact Or.inr (ord_nonneg_of_nu_le hP hf h.nu_le)

lemma ord_eq_zero_of_HV {P : Pt W L} {hP : P ≠ 0} {f : FF W L} {c : L} (h : HV W L P hP f c)
    (hc : c ≠ 0) : f ≠ 0 ∧ ord W L f P = 0 := by
  refine ⟨h.ne_zero hc, ?_⟩
  rw [ord_eq hP, h.nu_eq_one hc, WithZero.log_one, neg_zero]

lemma one_le_ord_of_HV {P : Pt W L} {hP : P ≠ 0} {f : FF W L} (h : HV W L P hP f 0) (hf : f ≠ 0) :
    1 ≤ ord W L f P := by
  have hlt : nu W L P hP f < 1 := by simpa [HV] using h
  have hne : nu W L P hP f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  rw [ord_eq hP]
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
  omega

lemma nu_le_one_of_ge {P : Pt W L} (hP : P ≠ 0) {f : FF W L} (hf : f ≠ 0) (h : 0 ≤ ord W L f P) :
    nu W L P hP f ≤ 1 := by
  rw [ord_eq hP] at h
  have hne : nu W L P hP f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  rw [← WithZero.exp_log hne, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega

lemma exists_HV_of_ge {P : Pt W L} (hP : P ≠ 0) {f : FF W L} (h : Ge 0 f P) :
    ∃ c, HV W L P hP f c := by
  by_cases hf : f = 0
  · exact ⟨0, (HV_alg (W := W) (P := P) (hP := hP) (0 : L)).congr (by rw [hf, map_zero]) rfl⟩
  · exact exists_HV hP (nu_le_one_of_ge hP hf (h.resolve_left hf))

lemma HV_unique {P : Pt W L} {hP : P ≠ 0} {f : FF W L} {c d : L} (h1 : HV W L P hP f c)
    (h2 : HV W L P hP f d) : c = d :=
  sub_eq_zero.mp (HV_eq_zero ((h1.sub h2).congr (sub_self f) rfl))

lemma HV_sub_self {P : Pt W L} {hP : P ≠ 0} {f : FF W L} {c : L} (h : HV W L P hP f c) :
    HV W L P hP (f - algebraMap L (FF W L) c) 0 :=
  (h.sub (HV_alg c)).congr rfl (sub_self c)

end ValHV

section Quot

variable {F : Type*} [Field F] [Fintype F] {W : WeierstrassCurve F} [W.IsElliptic]
  {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]

attribute [local instance] finite_coordinateRing decEqFF

variable {G : AddSubgroup (Pt W L)} [Fintype G] {W' : WeierstrassCurve F} [W'.IsElliptic]

lemma ne_zero_of_nmem {P : Pt W L} (hP : P ∉ G) : P ≠ 0 := fun h => hP (h ▸ G.zero_mem)

/-- Values of a `G`-invariant function are constant on cosets of `G`. -/
lemma HV_of_sub_mem {f : FF W L} (hf : InvG G f) {P Q : Pt W L} (hPQ : Q - P ∈ G) {hP : P ≠ 0}
    {hQ : Q ≠ 0} {c : L} (h : HV W L P hP f c) : HV W L Q hQ f c := by
  have e : P + (Q - P) = Q := by abel
  have h1 : P + (Q - P) ≠ 0 := by rw [e]; exact hQ
  unfold HV at *
  rw [← nu_congr e h1 hQ, ← nu_tau P (Q - P) hP h1, map_sub, AlgEquiv.commutes, hf _ hPQ]
  exact h

/-- The equation of `W'` satisfied by `(X_G, Y_G)`, with coefficients written over `L`. -/
lemma qeq (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) :
    qy G ^ 2 + algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * qx G * qy G +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₃ * qy G =
    qx G ^ 3 + algebraMap L (FF W L) (W'.baseChange L).toAffine.a₂ * qx G ^ 2 +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₄ * qx G +
      algebraMap L (FF W L) (W'.baseChange L).toAffine.a₆ := by
  have e := (equation_iff _ _).mp hW'
  rwa [bc_a₁ W' L (FF W L), bc_a₂ W' L (FF W L), bc_a₃ W' L (FF W L), bc_a₄ W' L (FF W L),
    bc_a₆ W' L (FF W L)] at e

/-- The values of `(X_G, Y_G)` lie on `W'`. -/
lemma eqn_of_HV (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) {P : Pt W L}
    {hP : P ≠ 0} {a c : L} (ha : HV W L P hP (qx G) a) (hc : HV W L P hP (qy G) c) :
    (W'.baseChange L).toAffine.Equation a c := by
  rw [equation_iff]
  have h1 := ((hc.pow 2).add (((HV_alg (P := P) (hP := hP)
    (W'.baseChange L).toAffine.a₁).mul ha).mul hc)).add
    ((HV_alg (P := P) (hP := hP) (W'.baseChange L).toAffine.a₃).mul hc)
  have h2 := (((ha.pow 3).add ((HV_alg (P := P) (hP := hP) (W'.baseChange L).toAffine.a₂).mul
    (ha.pow 2))).add ((HV_alg (P := P) (hP := hP) (W'.baseChange L).toAffine.a₄).mul ha)).add
    (HV_alg (P := P) (hP := hP) (W'.baseChange L).toAffine.a₆)
  exact HV_unique (h1.congr (qeq hW') rfl) h2

variable (G W') in
/-- The cofactor `M` in `(Y - c)(Y - c') = -(X - a) M`. -/
noncomputable def Mq (a : L) : FF W L :=
  algebraMap L (FF W L) (W'.baseChange L).toAffine.a₁ * qy G -
    (qx G ^ 2 + algebraMap L (FF W L) a * qx G + algebraMap L (FF W L) (a ^ 2)) -
    algebraMap L (FF W L) (W'.baseChange L).toAffine.a₂ * (qx G + algebraMap L (FF W L) a) -
    algebraMap L (FF W L) (W'.baseChange L).toAffine.a₄

lemma key_id (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) {a c : L}
    (hac : (W'.baseChange L).toAffine.Equation a c) :
    (qy G - algebraMap L (FF W L) c) *
      (qy G - algebraMap L (FF W L) ((W'.baseChange L).toAffine.negY a c)) =
      -(qx G - algebraMap L (FF W L) a) * Mq G W' a := by
  have e := qeq hW'
  have e2 := congrArg (algebraMap L (FF W L)) ((equation_iff _ _).mp hac)
  simp only [map_add, map_mul, map_pow] at e2
  simp only [Mq, negY, map_sub, map_neg, map_mul, map_pow]
  linear_combination e - e2

lemma HV_Mq {P : Pt W L} {hP : P ≠ 0} {a av cv : L} (ha : HV W L P hP (qx G) av)
    (hc : HV W L P hP (qy G) cv) :
    HV W L P hP (Mq G W' a) ((W'.baseChange L).toAffine.a₁ * cv - (av ^ 2 + a * av + a ^ 2) -
      (W'.baseChange L).toAffine.a₂ * (av + a) - (W'.baseChange L).toAffine.a₄) :=
  ((((HV_alg _).mul hc).sub (((ha.pow 2).add ((HV_alg a).mul ha)).add (HV_alg _))).sub
    ((HV_alg _).mul (ha.add (HV_alg a)))).sub (HV_alg _)

lemma qx_sub_ord (a : L) :
    qx G - algebraMap L (FF W L) a ≠ 0 ∧ ord W L (qx G - algebraMap L (FF W L) a) 0 = -2 := by
  rw [sub_eq_add_neg]
  exact ge_lead ord_qx_zero.1 ord_qx_zero.2 ((Ge.const a 0).neg.mono (by norm_num))

lemma qy_sub_ord (c : L) :
    qy G - algebraMap L (FF W L) c ≠ 0 ∧ ord W L (qy G - algebraMap L (FF W L) c) 0 = -3 := by
  rw [sub_eq_add_neg]
  exact ge_lead ord_qy_zero.1 ord_qy_zero.2 ((Ge.const c 0).neg.mono (by norm_num))

/-- **Surjectivity.** Every affine point of `W'` that is not 2-torsion is a value of `(X_G, Y_G)`. -/
theorem exists_preimage (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) {a c : L}
    (hac : (W'.baseChange L).toAffine.Equation a c) (h2 : c ≠ (W'.baseChange L).toAffine.negY a c) :
    ∃ P : Pt W L, ∃ hP : P ∉ G, HV W L P (ne_zero_of_nmem hP) (qx G) a ∧
      HV W L P (ne_zero_of_nmem hP) (qy G) c := by
  by_contra hno
  set c' := (W'.baseChange L).toAffine.negY a c with hc'
  obtain ⟨hx0, hxo⟩ := qx_sub_ord (G := G) a
  obtain ⟨hy0, hyo⟩ := qy_sub_ord (G := G) c'
  have hh0 : (qy G - algebraMap L (FF W L) c') / (qx G - algebraMap L (FF W L) a) ≠ 0 :=
    div_ne_zero hy0 hx0
  have hgood : GoodQ G ((qy G - algebraMap L (FF W L) c') / (qx G - algebraMap L (FF W L) a)) := by
    refine ⟨fun S hS => ?_, fun P hP => ?_⟩
    · rw [map_div₀, map_sub, map_sub, AlgEquiv.commutes, AlgEquiv.commutes,
        (goodQ_qx (G := G)).1 S hS, (goodQ_qy (G := G)).1 S hS]
    · have hP0 := ne_zero_of_nmem hP
      obtain ⟨av, hav⟩ := exists_HV_of_ge hP0 ((goodQ_qx (G := G)).2 P hP)
      obtain ⟨cv, hcv⟩ := exists_HV_of_ge hP0 ((goodQ_qy (G := G)).2 P hP)
      by_cases hxa : av = a
      · rw [hxa] at hav
        have hE := eqn_of_HV hW' hav hcv
        rcases Y_eq_of_X_eq hE hac rfl with hcc | hcc
        · exact absurd ⟨P, hP, hav, hcv.congr rfl hcc⟩ hno
        · have hyc := hcv.sub (HV_alg (P := P) (hP := hP0) c)
          have hcv0 : cv - c ≠ 0 := by rw [hcc]; exact sub_ne_zero.mpr (Ne.symm h2)
          obtain ⟨hyc0, hyco⟩ := ord_eq_zero_of_HV hyc hcv0
          have hk := key_id hW' hac
          rw [← hc'] at hk
          have hM0 : Mq G W' a ≠ 0 := by
            intro hM; rw [hM, mul_zero] at hk; exact mul_ne_zero hyc0 hy0 hk
          have hMge : 0 ≤ ord W L (Mq G W' a) P :=
            (ge_of_HV (HV_Mq (a := a) hav hcv)).resolve_left hM0
          have hords := congrArg (fun g => ord W L g P) hk
          rw [ord_mul hyc0 hy0, neg_mul, ord_neg', ord_mul hx0 hM0, hyco] at hords
          right
          rw [ord_div hy0 hx0]; linarith
      · exact ge_of_HV ((hcv.sub (HV_alg c')).div (hav.sub (HV_alg a)) (sub_ne_zero.mpr hxa))
  have hord : ord W L ((qy G - algebraMap L (FF W L) c') / (qx G - algebraMap L (FF W L) a)) 0 = -1 := by
    rw [ord_div hy0 hx0, hyo, hxo]; norm_num
  exact GoodQ.ord_ne_neg_one hG hgood hh0 hord

variable (G) in
/-- The coset `P + G` as a finset. -/
noncomputable def coset (P : Pt W L) : Finset (Pt W L) :=
  (Finset.univ.map (Function.Embedding.subtype (· ∈ G))).map (addLeftEmbedding P)

lemma mem_coset {P Q : Pt W L} : Q ∈ coset G P ↔ Q - P ∈ G := by
  constructor
  · intro h
    obtain ⟨R, hR, rfl⟩ := Finset.mem_map.mp h
    obtain ⟨T, -, rfl⟩ := Finset.mem_map.mp hR
    show P + (T : Pt W L) - P ∈ G
    simp
  · intro h
    exact Finset.mem_map.mpr ⟨Q - P, Finset.mem_map.mpr ⟨⟨Q - P, h⟩, Finset.mem_univ _, rfl⟩,
      show P + (Q - P) = Q by abel⟩

lemma card_coset (P : Pt W L) : (coset G P).card = Fintype.card G := by
  simp [coset]

/-- **Pole count.** A `G`-invariant `f`, regular off `G`, with `ord_O f = -m`, has
`k · #A ≤ m · #G` for any finset `A` off `G` on which `ord f ≥ k`. -/
lemma count_le {f : FF W L} (hf : f ≠ 0) (hinv : InvG G f) (hoff : ∀ P, P ∉ G → Ge 0 f P) {m : ℤ}
    (hm : ord W L f 0 = -m) (A : Finset (Pt W L)) (hA : ∀ P ∈ A, P ∉ G) {k : ℤ}
    (hk : ∀ P ∈ A, k ≤ ord W L f P) : k * A.card ≤ m * Fintype.card G := by
  classical
  set Gs : Finset (Pt W L) := Finset.univ.map ⟨((↑) : G → Pt W L), Subtype.val_injective⟩ with hGs
  have hmemG : ∀ P, P ∈ Gs ↔ P ∈ G := fun P => by
    simp only [hGs, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    exact ⟨fun ⟨T, hT⟩ => hT ▸ T.2, fun h => ⟨⟨P, h⟩, rfl⟩⟩
  set Z : Finset (Pt W L) := (ord_finite hf).toFinset ∪ A ∪ Gs with hZdef
  have hZ := sum_ord_eq_zero hf Z (fun P hP => by
    rw [hZdef, Finset.mem_union, Finset.mem_union, Set.Finite.mem_toFinset, Function.mem_support]
    exact Or.inl (Or.inl hP))
  rw [← Finset.sum_sdiff (Finset.subset_union_right : Gs ⊆ Z)] at hZ
  have hsG : ∑ P ∈ Gs, ord W L f P = -m * Fintype.card G := by
    rw [hGs, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
    rw [Finset.sum_congr rfl (fun T _ => hinv.ord_mem T.2), hm, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  have hAZ : A ⊆ Z \ Gs := fun P hP => Finset.mem_sdiff.mpr
    ⟨Finset.mem_union_left _ (Finset.mem_union_right _ hP), fun h => hA P hP ((hmemG P).mp h)⟩
  have hrest : ∑ P ∈ A, ord W L f P ≤ ∑ P ∈ Z \ Gs, ord W L f P := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hAZ (fun P hP _ => ?_)
    have hPG : P ∉ G := fun h => (Finset.mem_sdiff.mp hP).2 ((hmemG P).mpr h)
    exact (hoff P hPG).resolve_left hf
  have hAk := Finset.card_nsmul_le_sum A (fun P => ord W L f P) k hk
  rw [nsmul_eq_mul] at hAk
  linarith

/-- **Fibers.** Two points off `G` at which `(X_G, Y_G)` takes the same value differ by an element
of `G`. -/
theorem fiber (hG : (Fintype.card G : L) ≠ 0)
    (hW' : (W'.baseChange (FF W L)).toAffine.Equation (qx G) (qy G)) {P₀ P₁ : Pt W L} (h₀ : P₀ ∉ G)
    (h₁ : P₁ ∉ G) {a c : L} (ha₀ : HV W L P₀ (ne_zero_of_nmem h₀) (qx G) a)
    (hc₀ : HV W L P₀ (ne_zero_of_nmem h₀) (qy G) c) (ha₁ : HV W L P₁ (ne_zero_of_nmem h₁) (qx G) a)
    (hc₁ : HV W L P₁ (ne_zero_of_nmem h₁) (qy G) c) : P₁ - P₀ ∈ G := by
  by_contra hn
  obtain ⟨hx0, hxo⟩ := qx_sub_ord (G := G) a
  have hinv : InvG G (qx G - algebraMap L (FF W L) a) := fun S hS => by
    rw [map_sub, AlgEquiv.commutes, (goodQ_qx (G := G)).1 S hS]
  have hoff : ∀ P, P ∉ G → Ge 0 (qx G - algebraMap L (FF W L) a) P := fun P hP =>
    ((goodQ_qx (G := G)).2 P hP).sub (Ge.const a P)
  have hm : ord W L (qx G - algebraMap L (FF W L) a) 0 = -2 := hxo
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  have hcos : ∀ {P : Pt W L} {k : ℤ}, k ≤ ord W L (qx G - algebraMap L (FF W L) a) P →
      ∀ Q ∈ coset G P, k ≤ ord W L (qx G - algebraMap L (FF W L) a) Q := by
    intro P k hk Q hQ
    rw [show Q = P + (Q - P) by abel, hinv.ord_add (mem_coset.mp hQ)]; exact hk
  have hnot : ∀ {P : Pt W L}, P ∉ G → ∀ Q ∈ coset G P, Q ∉ G := by
    intro P hP Q hQ hQG; apply hP
    have := G.sub_mem hQG (mem_coset.mp hQ); simpa using this
  have hdisj : ∀ {P Q : Pt W L}, Q - P ∉ G → Disjoint (coset G P) (coset G Q) := by
    intro P Q hPQ
    rw [Finset.disjoint_left]
    intro R hRP hRQ; apply hPQ
    have := G.sub_mem (mem_coset.mp hRP) (mem_coset.mp hRQ)
    rwa [show R - P - (R - Q) = Q - P by abel] at this
  have hone : ∀ {P : Pt W L} (hP : P ∉ G), HV W L P (ne_zero_of_nmem hP) (qx G) a →
      1 ≤ ord W L (qx G - algebraMap L (FF W L) a) P :=
    fun hP h => one_le_ord_of_HV (HV_sub_self h) hx0
  have hac := eqn_of_HV hW' ha₀ hc₀
  by_cases h2 : c = (W'.baseChange L).toAffine.negY a c
  · -- `(a, c)` is 2-torsion: `X - a` vanishes to order `≥ 2` on the fiber
    have hns := (nonsingular_iff' _ _).mp (equation_iff_nonsingular.mp hac)
    have hMv : (W'.baseChange L).toAffine.a₁ * c - (a ^ 2 + a * a + a ^ 2) -
        (W'.baseChange L).toAffine.a₂ * (a + a) - (W'.baseChange L).toAffine.a₄ ≠ 0 := by
      rcases hns.2 with h | h
      · intro h0; apply h; linear_combination h0
      · exfalso; apply h; rw [negY] at h2; linear_combination h2
    have htwo : ∀ {P : Pt W L} (hP : P ∉ G), HV W L P (ne_zero_of_nmem hP) (qx G) a →
        HV W L P (ne_zero_of_nmem hP) (qy G) c → 2 ≤ ord W L (qx G - algebraMap L (FF W L) a) P := by
      intro P hP ha hc
      obtain ⟨hy0, -⟩ := qy_sub_ord (G := G) c
      have hk := key_id hW' hac
      rw [← h2] at hk
      obtain ⟨hM0, hMo⟩ := ord_eq_zero_of_HV (HV_Mq (a := a) ha hc) hMv
      have h1 := one_le_ord_of_HV (HV_sub_self hc) hy0
      have hords := congrArg (fun g => ord W L g P) hk
      rw [ord_mul hy0 hy0, neg_mul, ord_neg', ord_mul hx0 hM0, hMo] at hords
      linarith
    have hA := count_le hx0 hinv hoff hm (coset G P₀ ∪ coset G P₁)
      (fun Q hQ => (Finset.mem_union.mp hQ).elim (hnot h₀ Q) (hnot h₁ Q)) (k := 2)
      (fun Q hQ => (Finset.mem_union.mp hQ).elim (hcos (htwo h₀ ha₀ hc₀) Q)
        (hcos (htwo h₁ ha₁ hc₁) Q))
    rw [Finset.card_union_of_disjoint (hdisj hn), card_coset, card_coset] at hA
    push_cast at hA
    omega
  · -- otherwise the fiber over `-(a, c)` is a third coset
    obtain ⟨Q, hQ, haQ, hcQ⟩ := exists_preimage hG hW' ((equation_neg _ _).mpr hac)
      (by rw [negY_negY]; exact Ne.symm h2)
    have hQP : ∀ {P : Pt W L} (hP : P ∉ G), HV W L P (ne_zero_of_nmem hP) (qy G) c → Q - P ∉ G := by
      intro P hP hc hm'
      exact h2 (HV_unique (HV_of_sub_mem (goodQ_qy (G := G)).1 hm' hc) hcQ)
    have hA := count_le hx0 hinv hoff hm (coset G P₀ ∪ coset G P₁ ∪ coset G Q)
      (fun R hR => by
        rcases Finset.mem_union.mp hR with hR | hR
        · exact (Finset.mem_union.mp hR).elim (hnot h₀ R) (hnot h₁ R)
        · exact hnot hQ R hR) (k := 1)
      (fun R hR => by
        rcases Finset.mem_union.mp hR with hR | hR
        · exact (Finset.mem_union.mp hR).elim (hcos (hone h₀ ha₀) R) (hcos (hone h₁ ha₁) R)
        · exact hcos (hone hQ haQ) R hR)
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
        ⟨hdisj (hQP h₀ hc₀), hdisj (hQP h₁ hc₁)⟩),
      Finset.card_union_of_disjoint (hdisj hn), card_coset, card_coset, card_coset] at hA
    push_cast at hA
    omega

end Quot

end RPLib.DWS


