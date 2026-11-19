-- Prove2me | Definitions.Def_RPLib_S4_CDPack56
-- name    : RPLib_S4_CDPack56
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-18T18:59:08.874203+00:00
-- url     : https://prove2.me/theorems/50781224-26f4-4829-bba2-938de85f32fe
-- title:
--   Curve-duality library (Poincaré duality on curves over finite fields), part 56 of 71
-- statement:
--   Part 56 of 71 of the curve-duality library: the following library modules, in dependency order.
--
--   * `Def_RP_ThetaSquare_Curve2`: Unit S4-ThetaSquare, file Curve2: the support of `D_e` on `K`-points (T4c, part 2; Riemann-Roch only)
--   * `Def_RP_ThetaSquare_Curve3`: Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)
--
--   **Formalization note.** Library package of a formalization of Poincaré duality for constant coefficients on an affine curve over a finite field (the cup pairing $H^1_c(\bar U,\Lambda)\times H^1(\bar U,\sigma)\to\Lambda$ of the geometric fundamental group is perfect). The modules are copied verbatim (import lines removed), each inside its own `section` ... `end`, in dependency order. They contain definitions together with proved lemmas (no `sorry`; where divisibility facts about Picard groups are used they are explicit hypotheses), so that later solution files can import them.
-- source:
--   J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter V, §2 (Poincaré duality for curves); P. Deligne, Cohomologie étale (SGA 4½), Lecture Notes in Math. 569, Springer (1977), « Dualité »; J. S. Milne, Jacobian varieties, in Arithmetic Geometry (G. Cornell, J. H. Silverman, eds.), Springer (1986), 167-212; H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer (2009)

import Mathlib
import Definitions.Def_RPLib_S4_CDPack55b
import Definitions.Def_RPLib_S4_CDPack54
import Definitions.Def_RPLib_S4_CDPack31

/-!
# Curve-duality library package, part 56 of 71

Library modules of the formalization of Poincaré duality for constant coefficients on an affine curve over a
finite field (`RamanujanPetersson.CupDuality.constDuality_S3_perfect`). Each module below is copied verbatim
(import lines removed) inside its own `section` ... `end`:

* `Def_RP_ThetaSquare_Curve2`: Unit S4-ThetaSquare, file Curve2: the support of `D_e` on `K`-points (T4c, part 2; Riemann-Roch only)
* `Def_RP_ThetaSquare_Curve3`: Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)
-/

set_option autoImplicit false

-- ===== S4.Def_RP_ThetaSquare_Curve2 =====
section

/-!
# Unit S4-ThetaSquare, file Curve2: the support of `D_e` on `K`-points (T4c, part 2; Riemann-Roch only)

Let `G ≥ 0` have degree `g` and `ℓ(G) = 1`, let `W0` be canonical, and let the class of `e ∈ J(K)` be
`[W0 - G] - (g - 2)[P0]`. Then (Milne III.6.7, support part):

* `one_le_ell_iff`: `ℓ(D) ≥ 1` iff the class of `D` contains an effective divisor;
* **`eff_iff_mem_supp`**: `W0 - G + [v]` is equivalent to an effective divisor iff `v ∈ supp G`
  (Riemann-Roch in degree `g - 1` and uniqueness of the effective divisor in the class of `G`);
* `ell_eq_one_of_mem`: for `v ∈ supp G` that effective divisor `E_v` is unique;
* `exists_sum_ajCls_iff`: the Riemann condition of `mem_W_fe` in divisor form;
* **`mem_W_fe_iff`**: `f_e(q) ∈ W` iff `q ∈ supp G`, for every `K`-point `q` of `X1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Curve2

open Classical

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

/-- `ℓ(D) ≥ 1` iff the class of `D` contains an effective divisor. -/
theorem one_le_ell_iff (D : Places.Divisor K F) :
    1 ≤ ellFK K F D ↔ ∃ E : Places.Divisor K F, 0 ≤ E ∧ clsK K F E = clsK K F D := by
  constructor
  · intro h
    have hne : LFK K F D ≠ ⊥ := by
      intro hb
      rw [ellFK_def, hb, finrank_bot] at h
      omega
    obtain ⟨f, hfL, hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    refine ⟨PlacesK.div f + D, (mem_LFK hf).1 hfL, ?_⟩
    rw [clsK_add (K := K) (F := F), show clsK K F (PlacesK.div f) = 0 from
      (QuotientAddGroup.eq_zero_iff _).2 (div_mem_PrincK K F hf), zero_add]
  · rintro ⟨E, hE, hc⟩
    obtain ⟨f, hf, hfd⟩ := (mem_PrincK K F).1 ((clsK_eq_iff K F).1 hc.symm)
    have hfL : f ∈ LFK K F D := by
      rw [mem_LFK hf, hfd, show -D + E + D = E by abel]
      exact hE
    haveI := finiteDimensional_LFK (K := K) (F := F) D
    have hpos : 0 < finrank K (LFK K F D) :=
      Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨f, hfL⟩, fun h => hf (congrArg Subtype.val h)⟩
    rw [ellFK_def]
    omega

/-- **Riemann-Roch support lemma**: for `G ≥ 0` of degree `g` with `ℓ(G) = 1` and a canonical `W0`,
`W0 - G + [v]` is equivalent to an effective divisor iff `v ∈ supp G`. -/
theorem eff_iff_mem_supp {W0 G : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (hG : 0 ≤ G)
    (hd : G.deg = genusFK K F) (h1 : ellFK K F G = 1) (v : Place K F) :
    (∃ E : Places.Divisor K F, 0 ≤ E ∧ clsK K F E = clsK K F (W0 - G + Finsupp.single v 1)) ↔
      1 ≤ G v := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have hrr := riemannRochFK' hk hW (G - Finsupp.single v 1)
  rw [show W0 - (G - Finsupp.single v 1) = W0 - G + Finsupp.single v 1 by abel,
    PlacesK.Divisor.deg_sub, hd, deg_single_one] at hrr
  rw [← one_le_ell_iff (W0 - G + Finsupp.single v 1)]
  constructor
  · intro h
    have h2 : 1 ≤ ellFK K F (G - Finsupp.single v 1) := by omega
    obtain ⟨H, hH, hc⟩ := (one_le_ell_iff _).1 h2
    obtain ⟨f0, -, -, huniq⟩ := exists_eq_of_ell_one h1
    have hc' : clsK K F (H + Finsupp.single v 1) = clsK K F G := by
      rw [clsK_add (K := K) (F := F), hc, ← clsK_add (K := K) (F := F), sub_add_cancel]
    have hHG : H + Finsupp.single v 1 = G :=
      (huniq _ (add_nonneg hH (Finsupp.single_nonneg.2 zero_le_one)) hc').trans (huniq G hG rfl).symm
    rw [← hHG, Finsupp.add_apply, Finsupp.single_eq_same]
    have := Finsupp.le_def.1 hH v
    simp only [Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  · intro hv
    have hGv : 0 ≤ G - Finsupp.single v 1 := by
      rw [Finsupp.le_def]
      intro w
      rw [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h
        simpa using hv
      · simpa using Finsupp.le_def.1 hG w
    have h2 := (one_le_ell_iff (G - Finsupp.single v 1)).2 ⟨_, hGv, rfl⟩
    omega

/-- For `v ∈ supp G`, `ℓ(W0 - G + [v]) = 1`: the effective divisor `E_v ~ W0 - G + [v]` is unique. -/
theorem ell_eq_one_of_mem {W0 G : Places.Divisor K F} (hW : IsCanonicalFK K F W0) (hG : 0 ≤ G)
    (hd : G.deg = genusFK K F) (h1 : ellFK K F G = 1) {v : Place K F} (hv : 1 ≤ G v) :
    ellFK K F (W0 - G + Finsupp.single v 1) = 1 := by
  have hk := constField_eq_bot' (K := K) (F := F)
  have hrr := riemannRochFK' hk hW (G - Finsupp.single v 1)
  rw [show W0 - (G - Finsupp.single v 1) = W0 - G + Finsupp.single v 1 by abel,
    PlacesK.Divisor.deg_sub, hd, deg_single_one] at hrr
  have hle := ellFK_mono (K := K) (F := F)
    (sub_le_self G (Finsupp.single_nonneg.2 (zero_le_one' ℤ)) : G - Finsupp.single v 1 ≤ G)
  have hge := (one_le_ell_iff (W0 - G + Finsupp.single v 1)).2 ((eff_iff_mem_supp hW hG hd h1 v).2 hv)
  omega

/-- The Riemann condition of `mem_W_fe` in divisor form: for `ε = [W0 - G] - (g-2)[P0]`,
`[v] - [P0] + ε` is a sum of `g - 1` points minus `(g-1)[P0]` iff `W0 - G + [v]` is equivalent to an effective divisor. -/
theorem exists_sum_ajCls_iff (hg : 0 < genusFK K F) (P0 : Place K F) {W0 G : Places.Divisor K F}
    (hW : IsCanonicalFK K F W0) (hd : G.deg = genusFK K F) (ε : Pic0K K F)
    (hε : (ε : PicK K F) = clsK K F (W0 - G) - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1))
    (v : Place K F) :
    (∃ t : Fin (n0 K F) → Place K F, ajCls K F P0 v + ε = ∑ i, ajCls K F P0 (t i)) ↔
      ∃ E : Places.Divisor K F, 0 ≤ E ∧ clsK K F E = clsK K F (W0 - G + Finsupp.single v 1) := by
  have hn : ((n0 K F : ℕ) : ℤ) = genusFK K F - 1 := by
    rw [n0]
    omega
  set c := clsK K F (Finsupp.single P0 1) with hcdef
  have hsum : ∀ t : Fin (n0 K F) → Place K F,
      ((∑ i, ajCls K F P0 (t i) : Pic0K K F) : PicK K F) =
        clsK K F (∑ i, Finsupp.single (t i) (1 : ℤ)) - ((genusFK K F : ℤ) - 1) • c := by
    intro t
    rw [AddSubmonoidClass.coe_finsetSum, clsK_sum]
    show ∑ i, (clsK K F (Finsupp.single (t i) 1) - c) = _
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← hn, natCast_zsmul]
  have hc1 : ((genusFK K F : ℤ) - 1) • c = ((genusFK K F : ℤ) - 2) • c + c := by
    rw [show (genusFK K F : ℤ) - 1 = ((genusFK K F : ℤ) - 2) + 1 by ring, add_zsmul, one_zsmul]
  have hlhs : ((ajCls K F P0 v + ε : Pic0K K F) : PicK K F) =
      clsK K F (W0 - G + Finsupp.single v 1) - ((genusFK K F : ℤ) - 1) • c := by
    rw [AddSubgroup.coe_add, coe_ajCls, hε, clsK_add (K := K) (F := F), hc1]
    generalize ((genusFK K F : ℤ) - 2) • c = y
    abel
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨∑ i, Finsupp.single (t i) (1 : ℤ),
      Finset.sum_nonneg fun i _ => Finsupp.single_nonneg.2 zero_le_one, ?_⟩
    have h := congrArg Subtype.val ht
    rw [hlhs, hsum] at h
    exact (sub_left_inj.1 h).symm
  · rintro ⟨E, hE, hc⟩
    have hdeg : E.deg = ((n0 K F : ℕ) : ℤ) := by
      have h := congrArg (degPicK K F) hc
      rw [degPicK_clsK, degPicK_clsK, PlacesK.Divisor.deg_add, PlacesK.Divisor.deg_sub, hd,
        degFK_canonical (constField_eq_bot' (K := K) (F := F)) hW, deg_single_one] at h
      rw [h, hn]
      ring
    obtain ⟨t, ht⟩ := exists_sum_single_of_nonneg (n0 K F) hE hdeg
    refine ⟨t, Subtype.ext ?_⟩
    rw [hlhs, hsum, ← ht, hc]

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Support of `D_e` on `K`-points, set form** (Milne III.6.7): if the class of `e` is `[W0 - G] - (g-2)[P0]`
with `G ≥ 0`, `deg G = g`, `ℓ(G) = 1`, then `f_e(q) ∈ W` iff `q ∈ supp G`. -/
theorem mem_W_fe_iff (hg : 0 < genusFK K F) (P0 : Place K F) {W0 G : Places.Divisor K F}
    (hW : IsCanonicalFK K F W0) (hG : 0 ≤ G) (hd : G.deg = genusFK K F) (h1 : ellFK K F G = 1)
    (e : 𝟙_ (Over (Spec (.of K))) ⟶ Jac K F)
    (he : ((Multiplicative.toAdd (jacPicEquiv K F e) : Pic0K K F) : PicK K F) =
      clsK K F (W0 - G) - ((genusFK K F : ℤ) - 2) • clsK K F (Finsupp.single P0 1))
    (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    feX P0 e (q.left (IsLocalRing.closedPoint K)) ∈ W P0 ↔ 1 ≤ G (kPl q) := by
  rw [mem_W_fe, ← eff_iff_mem_supp hW hG hd h1 (kPl q), ← exists_sum_ajCls_iff hg P0 hW hd _ he (kPl q)]
  refine exists_congr fun t => ?_
  rw [_root_.map_mul, jacPicEquiv_ajO, ← ofAdd_toAdd (jacPicEquiv K F e), ← ofAdd_add]
  exact Multiplicative.ofAdd.injective.eq_iff

end Geom

end Curve2

end RamanujanPetersson.ThetaSquare

end

-- ===== S4.Def_RP_ThetaSquare_Curve3 =====
section

/-!
# Unit S4-ThetaSquare, file Curve3: Abel for one point and the plus chart through a `K`-point (T4c, part 3)

* `div_pow_of_div`, `le_ell_single`: if `div f = [Q'] - [Q]` with `Q ≠ Q'` then `ℓ(n[Q]) ≥ n + 1` for all `n`;
* **`eq_of_clsK_single`** (Abel for one point, `g ≥ 1`): `[Q] ~ [Q'] ⇒ Q = Q'`; `ajK_injective`;
* `kPl_kptO_plusX`: the place of the plus-curve point at `x` is `ptR2 x`; `kPl_chart`: the place of a chart point;
* **`exists_chart0`**: every `K`-point `q` of `X1` lies in a chart `{c0}`, at a point centered at `kPl q`;
  `xcR_ne_of_isCenter`: then `x - c0` does not vanish at that place;
* **`eq_iota2`**: if `ptR2 x` is the place of `q` (chart `{c0}` from `exists_chart0`), then `q = ι2 (kpt x)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxSynthPendingDepth 3

open IsDedekindDomain Polynomial Module

namespace RamanujanPetersson.ThetaSquare

open RamanujanPetersson.Places (Place Rfin Rinf)
open RamanujanPetersson.JacLaw RamanujanPetersson.JacSym RamanujanPetersson.RR RamanujanPetersson.JacComplete

universe u

section Abel

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem div_pow_of_div {f : F} (hf : f ≠ 0) {Q Q' : Place K F}
    (hd : (PlacesK.div f : Places.Divisor K F) = -Finsupp.single Q 1 + Finsupp.single Q' 1) (n : ℕ) :
    (PlacesK.div (f ^ n) : Places.Divisor K F) = Finsupp.single Q' (n : ℤ) - Finsupp.single Q (n : ℤ) := by
  induction n with
  | zero => rw [pow_zero, divK_one, Nat.cast_zero, Finsupp.single_zero, Finsupp.single_zero, sub_self]
  | succ n ih =>
    rw [pow_succ, PlacesK.div_mul (pow_ne_zero n hf) hf, ih, hd]
    push_cast
    rw [Finsupp.single_add, Finsupp.single_add]
    abel

/-- If `[Q] ~ [Q']` with `Q ≠ Q'`, then `ℓ(n[Q]) ≥ n + 1` (powers of `f` have exact pole order `n` at `Q`). -/
theorem le_ell_single {f : F} (hf : f ≠ 0) {Q Q' : Place K F} (hne : Q ≠ Q')
    (hd : (PlacesK.div f : Places.Divisor K F) = -Finsupp.single Q 1 + Finsupp.single Q' 1) (n : ℕ) :
    n + 1 ≤ ellFK K F (Finsupp.single Q (n : ℤ)) := by
  induction n with
  | zero => rw [Nat.cast_zero, Finsupp.single_zero, ellFK_zero']
  | succ n ih =>
    have e : Finsupp.single Q ((n + 1 : ℕ) : ℤ) = Finsupp.single Q (n : ℤ) + Finsupp.single Q 1 := by
      push_cast; exact Finsupp.single_add _ _ _
    have hle : Finsupp.single Q (n : ℤ) ≤ Finsupp.single Q ((n + 1 : ℕ) : ℤ) := by
      rw [e]; exact le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one)
    have hlt : LFK K F (Finsupp.single Q (n : ℤ)) < LFK K F (Finsupp.single Q ((n + 1 : ℕ) : ℤ)) := by
      refine lt_of_le_of_ne ((ffDataK K F).LD_mono hle) fun heq => ?_
      have hmem : f ^ (n + 1) ∈ LFK K F (Finsupp.single Q ((n + 1 : ℕ) : ℤ)) := by
        rw [mem_LFK (pow_ne_zero _ hf), div_pow_of_div hf hd, sub_add_cancel]
        exact Finsupp.single_nonneg.2 (by positivity)
      rw [← heq, mem_LFK (pow_ne_zero _ hf), div_pow_of_div hf hd] at hmem
      have h := Finsupp.le_def.1 hmem Q
      have h2 : (0 : ℤ) ≤ 0 - ((n : ℤ) + 1) + n := by
        simpa [Finsupp.single_apply, hne, hne.symm] using h
      omega
    haveI := finiteDimensional_LFK (K := K) (F := F) (Finsupp.single Q ((n + 1 : ℕ) : ℤ))
    have h3 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [ellFK_def] at ih ⊢
    omega

/-- **Abel for one point**: for `g ≥ 1`, `[Q] ~ [Q']` forces `Q = Q'`. -/
theorem eq_of_clsK_single (hg : 0 < genusFK K F) {Q Q' : Place K F}
    (h : clsK K F (Finsupp.single Q 1) = clsK K F (Finsupp.single Q' 1)) : Q = Q' := by
  by_contra hne
  obtain ⟨f, hf, hd⟩ := (mem_PrincK K F).1 ((clsK_eq_iff K F).1 h)
  have h1 := le_ell_single hf hne hd (2 * genusFK K F)
  have hk := constField_eq_bot' (K := K) (F := F)
  have h2 := ellFK_eq_of_deg hk (D := Finsupp.single Q ((2 * genusFK K F : ℕ) : ℤ))
    (by rw [deg_single']; push_cast; omega)
  rw [deg_single'] at h2
  omega

end Abel

section Geom

open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory CartesianMonoidalCategory MonObj

variable {K : Type u} [Field K] [DecidableEq (RatFunc K)]
variable {F : Type u} [Field F] [Algebra K F] [Algebra K[X] F] [Algebra (RatFunc K) F]
  [IsScalarTower K[X] (RatFunc K) F] [IsScalarTower K K[X] F] [FunctionField K F]
  [Algebra.IsSeparable (RatFunc K) F] [IsAlgClosed K]

theorem ajK_injective (hg : 0 < genusFK K F) (P0 : Place K F) : Function.Injective (ajK K F P0) := by
  intro Q Q' h
  have h1 : ajCls K F P0 Q = ajCls K F P0 Q' :=
    Multiplicative.ofAdd.injective ((jacPicEquiv K F).symm.injective h)
  have h2 : ((ajCls K F P0 Q : Pic0K K F) : PicK K F) = ajCls K F P0 Q' := by rw [h1]
  rw [coe_ajCls, coe_ajCls] at h2
  exact eq_of_clsK_single hg (sub_left_inj.1 h2)

/-- The place of the plus-curve point at `x` is `ptR2 x`. -/
theorem kPl_kptO_plusX (hg : 0 < genusFK K F) (c0 : K) (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K))
    (i0 : Fin (genusFK K F)) (x : R2 c0 a i0 →ₐ[K] K) :
    kPl (kptO x ≫ plusX c0 a i0) = (Sum.inl (ptP (ptR2 c0 a i0 x)) : Place K F) := by
  refine ajK_injective hg (Sum.inl (ptP (ptR2 c0 a i0 x))) ?_
  rw [← kPl_spec, Category.assoc]
  exact kptO_plusX_ajO c0 a i0 _ x

/-- The place of a `K`-point of `X1` given in a chart `A` is the center `plA`. -/
theorem kPl_chart (hg : 0 < genusFK K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) (A : (ChartIdx K)ᵒᵖ)
    (ψ : SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1 →ₐ[K] K)
    (hq : q.left (IsLocalRing.closedPoint K) = colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A
      (kpt (A := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) ψ)) :
    kPl q = plA A.unop (ψ.comp diag1) := by
  refine ajK_injective hg (plA A.unop (ψ.comp diag1)) ?_
  rw [← kPl_spec]
  apply Over.OverMorphism.ext
  refine ext_of_apply_closedPoint_eq (Jac K F).hom (Over.w _) (Over.w _) ?_
  have e : (q ≫ ajO (plA A.unop (ψ.comp diag1))).left (IsLocalRing.closedPoint K) =
      ajX1 (plA A.unop (ψ.comp diag1)) (q.left (IsLocalRing.closedPoint K)) := rfl
  rw [e, hq, ajX1_apply]
  rfl

/-- **Every `K`-point of `X1` lies in a chart `{c0}`**, at a point centered at `kPl q`. -/
theorem exists_chart0 (hg : 0 < genusFK K F) (q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F) :
    ∃ c0 : K, ∃ ψ0 : SymRing K (Bc F c0) 1 →ₐ[K] K, IsCenter (kPl q) (ψ0.comp diag1) ∧
      q.left (IsLocalRing.closedPoint K) = colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (op (idx0 c0))
        (kpt (A := SymRing K (Bc F c0) 1) ψ0) := by
  have hx : IsClosed ({q.left (IsLocalRing.closedPoint K)} : Set (X1 K F)) :=
    JacChunk.isClosed_singleton_apply (𝟙 (Spec (.of K))) (toSpecK K (algebraMap K[X] F X) 1) q.left (Over.w q) _
      (JacChunk.isClosed_specPt _)
  obtain ⟨A, p, hp⟩ := cht_cov (K := K) (F := F) _ hx
  have hpc : IsClosed ({p} : Set (cht K F A)) := by
    haveI := isOpenImmersion_ιX1 (K := K) (F := F) A
    have hinj := (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A).isOpenEmbedding.injective
    have h := hx.preimage (colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A).isOpenEmbedding.continuous
    have e2 : (⇑(colimit.ι (symDiagram K (algebraMap K[X] F X) 1) A)) ⁻¹'
        {q.left (IsLocalRing.closedPoint K)} = {p} := by
      ext w
      simp only [Set.mem_preimage]
      rw [← hp]
      exact hinj.eq_iff
    exact (congrArg IsClosed e2).mp h
  obtain ⟨ψ, rfl⟩ := exists_kpt (K := K) (A := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) p hpc
  have hc0 : A.unop.2.choose ∈ A.unop.1 := A.unop.2.choose_spec
  let f : A ⟶ op (idx0 A.unop.2.choose) :=
    (homOfLE (Subtype.coe_le_coe.1 (Finset.singleton_subset_iff.2 hc0) : idx0 A.unop.2.choose ≤ A.unop)).op
  refine ⟨A.unop.2.choose, ψ.comp (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop)), ?_, ?_⟩
  · have key2 : (ψ.comp (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop))).comp diag1 =
        (ψ.comp diag1).comp (Subalgebra.inclusion (chartRing_mono _ (leOfHom f.unop))) := by
      rw [AlgHom.comp_assoc, chartMap, symMap_diag1, AlgHom.comp_assoc]
    rw [key2, kPl_chart hg q A ψ hp.symm]
    exact isCenter_restrict (leOfHom f.unop) _ (isCenter_plA A.unop (ψ.comp diag1))
  · have key : (symDiagram K (algebraMap K[X] F X) 1).map f
          (kpt (A := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1) ψ) =
        kpt (A := SymRing K (Bc F A.unop.2.choose) 1)
          (ψ.comp (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop))) := by
      rw [symDiagram_map]
      exact SpecMap_kpt (A := SymRing K (Bc F A.unop.2.choose) 1)
        (B := SymRing K (chartRing (algebraMap K[X] F X) A.unop.1) 1)
        (chartMap (algebraMap K[X] F X) 1 (leOfHom f.unop)) ψ
    rw [← hp, ← key, ← colimit.w (symDiagram K (algebraMap K[X] F X) 1) f]
    rfl

/-- In the chart `{c0}` through a place `P`, `x - c0` does not vanish at `P`. -/
theorem xcR_ne_of_isCenter (c0 : K) {φ : Rfin K F →ₐ[K] K} {θ : Bc F c0 →ₐ[K] K}
    (h : IsCenter (Sum.inl (ptP φ) : Place K F) θ) : φ (xcR F c0) ≠ 0 := by
  intro h0
  have h1 := h.1 (uc0 F c0)
  rw [placeVal_inl] at h1
  have h2 : (ptP φ).valuation F (algebraMap (Rfin K F) F (xcR F c0)) < 1 := by
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem (K := F), mem_ptP]
    exact h0
  have e : ((uc0 F c0 : Bc F c0) : F) * algebraMap (Rfin K F) F (xcR F c0) = 1 := by
    change (algebraMap K[X] F X - algebraMap K F c0)⁻¹ * ((xcR F c0 : Rfin K F) : F) = 1
    rw [coe_xcR]
    exact inv_mul_cancel₀ (sub_ne_zero_of_tr (transcendental_xF K F) c0)
  have h3 := congrArg ((ptP φ).valuation F) e
  rw [map_mul, map_one] at h3
  have h4 : (ptP φ).valuation F ((uc0 F c0 : Bc F c0) : F) *
      (ptP φ).valuation F (algebraMap (Rfin K F) F (xcR F c0)) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_left' h1) h2
  rw [h3] at h4
  exact lt_irrefl _ h4

/-- **The plus chart through a `K`-point**: if `ptR2 x` is the place of `q` and `q` sits in the chart `{c0}`
(`exists_chart0`), then `q = ι2 (kpt x)`. -/
theorem eq_iota2 {q : 𝟙_ (Over (Spec (.of K))) ⟶ X1O K F} {c0 : K} {ψ0 : SymRing K (Bc F c0) 1 →ₐ[K] K}
    (hc : IsCenter (kPl q) (ψ0.comp diag1))
    (hq : q.left (IsLocalRing.closedPoint K) = colimit.ι (symDiagram K (algebraMap K[X] F X) 1) (op (idx0 c0))
        (kpt (A := SymRing K (Bc F c0) 1) ψ0))
    (a : Fin (genusFK K F) → (Rfin K F →ₐ[K] K)) (i0 : Fin (genusFK K F)) (x : R2 c0 a i0 →ₐ[K] K)
    (hx : (Sum.inl (ptP (ptR2 c0 a i0 x)) : Place K F) = kPl q) :
    q.left (IsLocalRing.closedPoint K) = ι2 c0 a i0 (kpt x) := by
  have h2 : IsCenter (kPl q) ((x.comp (symToR2 c0 a i0)).comp diag1) := by
    rw [symToR2_diag1, ← hx]
    exact isCenter_R1 c0 (x.comp (awayι (K := K) (plusH c0 a i0)))
  have heq : ψ0.comp diag1 = (x.comp (symToR2 c0 a i0)).comp diag1 :=
    eq_of_zero_imp fun b hb => (h2.2 b).1 ((hc.2 b).2 hb)
  have heq' : ψ0 = x.comp (symToR2 c0 a i0) := by
    refine AlgHom.ext fun s => ?_
    have h5 := congrArg (fun φ => φ (undiag1 s)) heq
    simpa only [AlgHom.comp_apply, diag1_undiag1] using h5
  rw [hq, heq', ← SpecMap_kpt]
  rfl

end Geom

end RamanujanPetersson.ThetaSquare

end


