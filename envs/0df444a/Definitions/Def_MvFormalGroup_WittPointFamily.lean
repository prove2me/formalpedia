-- Prove2me | Definitions.Def_MvFormalGroup_WittPointFamily
-- name    : MvFormalGroup_WittPointFamily
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/6d7c867e-fb8e-5974-91f1-6893caccd32e
-- title:
--   Power-series points of formal groups, Witt points, Cartier evaluation
-- statement:
--   Fix a commutative ring $R$, a formal group law $\Phi$ of dimension $d$ over $R$ and a variable set $\tau$. [`MvFormalGroup.SeriesPoint Φ τ`](../def/MvFormalGroup_WittPointFamily.html#L17) is the structure whose data is a $d$-tuple `val` of power series in the variables $\tau$ together with the proof that each has vanishing constant coefficient; addition is $a+b=\Phi(a,b)$ (coordinatewise substitution of the pair $(a,b)$ into the coordinates of $\Phi$), the zero point is the zero tuple and the opposite is the inverse family `negSeries Φ a` constructed by successive homogeneous approximation. This makes `SeriesPoint Φ τ` an additive group, commutative when `Φ.IsComm` holds, with $a-b=\Phi(a,\iota_\Phi(b))$. A homomorphism $\varphi\colon\Phi\to\Phi'$ of commutative laws induces the additive map `mapPt` sending $a$ to $\varphi(a)$, and a substitutable family $b$ of constant-term-free series in new variables $\tau'$ induces the additive base-change map `substPt`.
--
--   On the Witt side, for a prime $p$, [`MvFormalGroup.WittLaw.seriesPoint p R τ`](../def/MvFormalGroup_WittPointFamily.html#L182) is the additive subgroup of the ring $W(R[[\tau]])$ of $p$-typical Witt vectors over $R[[\tau]]$ cut out by the two conditions that every component has zero constant coefficient and that the family of components is substitutable (`HasSubst`): each monomial in $\tau$ has non-zero coefficient in only finitely many components. Closure under addition and negation rests on the identities expressing $(x+y)_n$ and $(cx)_n$ as substitutions of the component families into the Witt addition and multiplication families `addFam`, `mulFam`. Defined on this subgroup are the additive operators `wittSMulPt w` (multiplication by the image of $w\in W(R)$ under the constants map), its Teichmüller specialisation `teichPt c`, whose $n$-th component is $c^{p^n}$ times the $n$-th component, the Verschiebung `verPt`, the Frobenius `frobPt` when $R$ has characteristic $p$ (acting as $p$-th power on components), and the base-change map `substPt`; the tautological points `tautPt` (components $X_n$, for $\tau=\mathbb{N}$) and `curveTautPt` (components `curveFam R n`, for $\tau$ a point) are exhibited. Finally `CartierModule.evalPt` is the additive-in-both-arguments pairing sending a Cartier-module element $f$ and a Witt point $w$ to the $\Phi$-point whose $j$-th coordinate is obtained by substituting the components of $w$ into $f_j$; it converts `verPt` into `frobenius`, `frobPt` into `verschiebung`, `teichPt c` into `homothety c`, `wittSMulPt w` into the $W(R)$-action, and commutes with `mapPt` and with base change. Evaluation at `tautPt` returns $f$ itself (hence is injective), evaluation at `curveTautPt` returns the curve of $f$, and `presPi`/`presPiHom` assemble a finite family $(f_l)$ into the additive map $(w_l)\mapsto\sum_l \mathrm{evalPt}(f_l,w_l)$.
--
--   **Relation to Mathlib.** Mathlib supplies the $p$-typical Witt vectors with their Frobenius, Verschiebung and Teichmüller maps, multivariable power series and the substitution calculus (`subst`, `HasSubst`), but no multivariable formal group laws or Cartier modules; the point groups, operators and evaluation pairing here are the project's own. The instance `charP_mvPowerSeries` transports `CharP R p` to `MvPowerSeries τ R` along the constants map.
--
--   **Where it is used.** These are the groups of points with power-series coordinates in which Cartier's presentation of a commutative formal group law by its module of $p$-typical curves is formulated: `presPi` is the comparison map from a finite family of Witt points, and the compatibilities of `evalPt` with Frobenius, Verschiebung and homotheties are the module-theoretic translations of the operators on points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_WittPointFamily.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v w

namespace MvFormalGroup

open MvPowerSeries WittLaw

structure SeriesPoint {d : ℕ} {R : Type u} [CommRing R] (Φ : MvFormalGroup d R) (τ : Type v) :
    Type (max u v) where

  val : Fin d → MvPowerSeries τ R

  constantCoeff_eq_zero : ∀ j, (val j).constantCoeff = 0

namespace SeriesPoint

variable {d d' : ℕ} {R : Type u} [CommRing R] {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}
  {τ : Type v} {τ' : Type w}

@[ext] theorem ext {a b : SeriesPoint Φ τ} (h : a.val = b.val) : a = b := by
  cases a; cases b; cases h; rfl

theorem hasSubst_val (a : SeriesPoint Φ τ) : HasSubst a.val :=
  hasSubst_of_constantCoeff_zero a.constantCoeff_eq_zero

protected def zero : SeriesPoint Φ τ := ⟨fun _ => 0, fun _ => map_zero _⟩

instance instZero : Zero (SeriesPoint Φ τ) := ⟨SeriesPoint.zero⟩

@[simp] theorem val_zero : (0 : SeriesPoint Φ τ).val = fun _ => 0 := rfl

protected def add (a b : SeriesPoint Φ τ) : SeriesPoint Φ τ where
  val := fun j => subst (Sum.elim a.val b.val) (Φ.toPowerSeries j)
  constantCoeff_eq_zero := constantCoeff_subst_elim Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero

instance instAdd : Add (SeriesPoint Φ τ) := ⟨SeriesPoint.add⟩

@[simp] theorem val_add (a b : SeriesPoint Φ τ) :
    (a + b).val = fun j => subst (Sum.elim a.val b.val) (Φ.toPowerSeries j) := rfl

protected def neg (a : SeriesPoint Φ τ) : SeriesPoint Φ τ where
  val := negSeries Φ a.val
  constantCoeff_eq_zero := constantCoeff_negSeries Φ a.val

instance instNeg : Neg (SeriesPoint Φ τ) := ⟨SeriesPoint.neg⟩

@[simp] theorem val_neg (a : SeriesPoint Φ τ) : (-a).val = negSeries Φ a.val := rfl

instance instAddGroup : AddGroup (SeriesPoint Φ τ) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := SeriesPoint.ext (funext fun j =>
    subst_elim_assoc Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero c.constantCoeff_eq_zero j)
  zero_add a := SeriesPoint.ext (funext fun j => subst_elim_zero_left Φ a.constantCoeff_eq_zero j)
  add_zero a := SeriesPoint.ext (funext fun j => subst_elim_zero_right Φ a.constantCoeff_eq_zero j)
  neg_add_cancel a := SeriesPoint.ext (funext fun j =>
    subst_elim_negSeries_left Φ a.constantCoeff_eq_zero j)

instance instAddCommGroup [Φ.IsComm] : AddCommGroup (SeriesPoint Φ τ) :=
  { SeriesPoint.instAddGroup with
    add_comm := fun a b => SeriesPoint.ext (funext fun j =>
      subst_elim_comm Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero j) }

theorem val_sub [Φ.IsComm] (a b : SeriesPoint Φ τ) :
    (a - b).val = fun j => subst (Sum.elim a.val (negSeries Φ b.val)) (Φ.toPowerSeries j) := by
  rw [sub_eq_add_neg]; rfl

def mapPt [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') : SeriesPoint Φ τ →+ SeriesPoint Φ' τ where
  toFun a := ⟨fun i => subst a.val (φ.toPowerSeries i), fun i =>
    constantCoeff_subst_eq_zero a.hasSubst_val a.constantCoeff_eq_zero (φ.constantCoeff_eq_zero i)⟩
  map_zero' := SeriesPoint.ext (funext fun i =>
    subst_zero_of_constantCoeff_eq_zero (φ.constantCoeff_eq_zero i))
  map_add' a b := SeriesPoint.ext (funext fun i =>
    φ.subst_subst_elim a.constantCoeff_eq_zero b.constantCoeff_eq_zero i)

@[simp] theorem val_mapPt [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (a : SeriesPoint Φ τ) :
    (mapPt φ a).val = fun i => subst a.val (φ.toPowerSeries i) := rfl

def substPt [Φ.IsComm] {b : τ → MvPowerSeries τ' R} (hb : HasSubst b)
    (hb0 : ∀ t, (b t).constantCoeff = 0) : SeriesPoint Φ τ →+ SeriesPoint Φ τ' where
  toFun a := ⟨fun j => subst b (a.val j), fun j =>
    constantCoeff_subst_eq_zero hb hb0 (a.constantCoeff_eq_zero j)⟩
  map_zero' := SeriesPoint.ext (funext fun j => by
    show subst b (0 : MvPowerSeries τ R) = 0
    rw [← coe_substAlgHom hb, map_zero])
  map_add' a c := SeriesPoint.ext (funext fun j =>
    subst_subst_elim Φ a.constantCoeff_eq_zero c.constantCoeff_eq_zero hb j)

@[simp] theorem val_substPt [Φ.IsComm] {b : τ → MvPowerSeries τ' R} (hb : HasSubst b)
    (hb0 : ∀ t, (b t).constantCoeff = 0) (a : SeriesPoint Φ τ) :
    (substPt hb hb0 a).val = fun j => subst b (a.val j) := rfl

end SeriesPoint

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R] {τ : Type v} {τ' : Type w}

def pairSeries (a b : ℕ → MvPowerSeries τ R) : Fin 2 × ℕ → MvPowerSeries τ R :=
  fun im => Fin.cases (a im.2) (fun _ => b im.2) im.1

variable {p}

omit hp [CommRing R] in
@[simp] theorem pairSeries_zero (a b : ℕ → MvPowerSeries τ R) (m : ℕ) :
    pairSeries a b (0, m) = a m := rfl

omit hp [CommRing R] in
@[simp] theorem pairSeries_one (a b : ℕ → MvPowerSeries τ R) (m : ℕ) :
    pairSeries a b (1, m) = b m := rfl

omit hp [CommRing R] in
theorem pairSeries_eq_vec (a b : ℕ → MvPowerSeries τ R) :
    pairSeries a b = fun im : Fin 2 × ℕ => (![a, b] : Fin 2 → ℕ → MvPowerSeries τ R) im.1 im.2 := by
  funext ⟨i, m⟩
  refine Fin.cases rfl (fun l => ?_) i
  fin_cases l; rfl

omit hp in

theorem subst_map_eq_peval {k : ℕ} (Q : MvPolynomial (Fin k × ℕ) ℤ) (x : Fin k → ℕ → MvPowerSeries τ R) :
    subst (fun im : Fin k × ℕ => x im.1 im.2)
      ((MvPolynomial.map (Int.castRingHom R) Q : MvPolynomial (Fin k × ℕ) R) :
        MvPowerSeries (Fin k × ℕ) R) = WittVector.peval Q x := by
  rw [← WittVector.peval_X R Q, subst_coe, WittVector.map_peval]
  congr 1
  funext i m
  exact MvPolynomial.aeval_X _ _

omit hp in
theorem hasSubst_pairSeries {a b : ℕ → MvPowerSeries τ R} (ha : HasSubst a) (hb : HasSubst b) :
    HasSubst (pairSeries a b) := by
  refine ⟨fun ⟨i, m⟩ => Fin.cases (ha.const_coeff m) (fun _ => hb.const_coeff m) i, fun e => ?_⟩
  refine (((ha.coeff_zero e).image (Prod.mk 0)).union ((hb.coeff_zero e).image (Prod.mk 1))).subset ?_
  rintro ⟨i, m⟩ him
  revert him
  refine Fin.cases (fun him => Or.inl ⟨m, him, rfl⟩) (fun l him => Or.inr ⟨m, him, ?_⟩) i
  fin_cases l; rfl

omit hp in
theorem constantCoeff_pairSeries {a b : ℕ → MvPowerSeries τ R} (ha : ∀ n, (a n).constantCoeff = 0)
    (hb : ∀ n, (b n).constantCoeff = 0) (im : Fin 2 × ℕ) : (pairSeries a b im).constantCoeff = 0 := by
  rcases im with ⟨i, m⟩
  exact Fin.cases (ha m) (fun _ => hb m) i

theorem add_coeff_eq_subst_addFam (x y : WittVector p (MvPowerSeries τ R)) (n : ℕ) :
    (x + y).coeff n = subst (pairSeries x.coeff y.coeff) (addFam p R n) := by
  rw [WittVector.add_coeff, pairSeries_eq_vec, addFam, subst_map_eq_peval]

theorem map_C_mul_coeff_eq_subst_mulFam (w : WittVector p R) (x : WittVector p (MvPowerSeries τ R))
    (n : ℕ) :
    (WittVector.map (C : R →+* MvPowerSeries τ R) w * x).coeff n = subst x.coeff (mulFam p w n) := by
  let ψ : MvPolynomial ℕ R →+* MvPowerSeries τ R := (MvPolynomial.aeval x.coeff).toRingHom
  have hψ : ∀ P : MvPolynomial ℕ R, MvPolynomial.aeval x.coeff P = ψ P := fun _ => rfl
  have h1 : WittVector.map ψ (cVec p w) = WittVector.map (C : R →+* MvPowerSeries τ R) w := by
    refine WittVector.ext fun m => ?_
    rw [WittVector.map_coeff, cVec_coeff, WittVector.map_coeff, ← hψ, MvPolynomial.aeval_C]
    rfl
  have h2 : WittVector.map ψ (WittVector.mk p (MvPolynomial.X : ℕ → MvPolynomial ℕ R)) = x := by
    refine WittVector.ext fun m => ?_
    rw [WittVector.map_coeff, WittVector.coeff_mk, ← hψ, MvPolynomial.aeval_X]
  rw [mulFam_apply, subst_coe, hψ, mulPoly, ← WittVector.map_coeff ψ _ n, map_mul, h1, h2]

theorem teichmuller_C_mul_coeff (c : R) (x : WittVector p (MvPowerSeries τ R)) (n : ℕ) :
    (WittVector.teichmuller p (C c : MvPowerSeries τ R) * x).coeff n = (c ^ p ^ n) • x.coeff n := by
  rw [WittVector.teichmuller_mul_coeff, ← map_pow, smul_eq_C_mul]

variable (p R τ)

def seriesPoint : AddSubgroup (WittVector p (MvPowerSeries τ R)) where
  carrier := {x | (∀ n, (x.coeff n).constantCoeff = 0) ∧ HasSubst (fun n => x.coeff n)}
  zero_mem' := ⟨fun n => by rw [WittVector.zero_coeff, map_zero], by
    simpa only [WittVector.zero_coeff] using (HasSubst.zero : HasSubst fun _ : ℕ => (0 : MvPowerSeries τ R))⟩
  add_mem' := by
    rintro x y ⟨hx0, hx⟩ ⟨hy0, hy⟩
    have hP := hasSubst_pairSeries hx hy
    have hfam : (fun n => (x + y).coeff n) = fun n => subst (pairSeries x.coeff y.coeff) (addFam p R n) :=
      funext (add_coeff_eq_subst_addFam x y)
    refine ⟨fun n => ?_, ?_⟩
    · rw [add_coeff_eq_subst_addFam]
      exact constantCoeff_subst_eq_zero hP (constantCoeff_pairSeries hx0 hy0) (constantCoeff_addFam p R n)
    · rw [hfam]
      simpa only [coe_substAlgHom] using (hasSubst_addFam p R).comp hP
  neg_mem' := by
    rintro x ⟨hx0, hx⟩
    have hneg : -x = WittVector.map (C : R →+* MvPowerSeries τ R) (-1) * x := by
      rw [map_neg, map_one, neg_one_mul]
    have hfam : (fun n => (-x).coeff n) = fun n => subst x.coeff (mulFam p (-1 : WittVector p R) n) := by
      funext n
      rw [hneg, map_C_mul_coeff_eq_subst_mulFam]
    refine ⟨fun n => ?_, ?_⟩
    · rw [hneg, map_C_mul_coeff_eq_subst_mulFam]
      exact constantCoeff_subst_eq_zero hx hx0 (constantCoeff_mulFam _ n)
    · rw [hfam]
      simpa only [coe_substAlgHom] using (hasSubst_mulFam (-1 : WittVector p R)).comp hx

variable {p R τ}

theorem mem_seriesPoint_iff (x : WittVector p (MvPowerSeries τ R)) :
    x ∈ seriesPoint p R τ ↔ (∀ n, (x.coeff n).constantCoeff = 0) ∧ HasSubst (fun n => x.coeff n) :=
  Iff.rfl

theorem constantCoeff_coeff (w : seriesPoint p R τ) (n : ℕ) :
    ((w : WittVector p (MvPowerSeries τ R)).coeff n).constantCoeff = 0 :=
  w.2.1 n

theorem hasSubst_coeff (w : seriesPoint p R τ) :
    HasSubst (fun n => (w : WittVector p (MvPowerSeries τ R)).coeff n) :=
  w.2.2

@[simp] theorem coe_add_coeff (w w' : seriesPoint p R τ) (n : ℕ) :
    ((w + w' : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n =
      subst (pairSeries (fun m => (w : WittVector p (MvPowerSeries τ R)).coeff m)
        fun m => (w' : WittVector p (MvPowerSeries τ R)).coeff m) (addFam p R n) :=
  add_coeff_eq_subst_addFam _ _ n

theorem map_C_mul_mem (w : WittVector p R) {x : WittVector p (MvPowerSeries τ R)}
    (hx : x ∈ seriesPoint p R τ) : WittVector.map (C : R →+* MvPowerSeries τ R) w * x ∈ seriesPoint p R τ := by
  have hfam : (fun n => (WittVector.map (C : R →+* MvPowerSeries τ R) w * x).coeff n) =
      fun n => subst x.coeff (mulFam p w n) := funext (map_C_mul_coeff_eq_subst_mulFam w x)
  refine ⟨fun n => ?_, ?_⟩
  · rw [map_C_mul_coeff_eq_subst_mulFam]
    exact constantCoeff_subst_eq_zero hx.2 hx.1 (constantCoeff_mulFam _ n)
  · rw [hfam]
    simpa only [coe_substAlgHom] using (hasSubst_mulFam w).comp hx.2

def wittSMulPt (w : WittVector p R) : seriesPoint p R τ →+ seriesPoint p R τ where
  toFun x := ⟨WittVector.map (C : R →+* MvPowerSeries τ R) w * x, map_C_mul_mem w x.2⟩
  map_zero' := Subtype.ext (mul_zero _)
  map_add' _ _ := Subtype.ext (mul_add _ _ _)

@[simp] theorem coe_wittSMulPt (w : WittVector p R) (x : seriesPoint p R τ) :
    ((wittSMulPt w x : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)) =
      WittVector.map (C : R →+* MvPowerSeries τ R) w * x := rfl

theorem coeff_wittSMulPt (w : WittVector p R) (x : seriesPoint p R τ) (n : ℕ) :
    ((wittSMulPt w x : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n =
      subst (fun m => (x : WittVector p (MvPowerSeries τ R)).coeff m) (mulFam p w n) :=
  map_C_mul_coeff_eq_subst_mulFam w _ n

theorem wittSMulPt_one (x : seriesPoint p R τ) : wittSMulPt (1 : WittVector p R) x = x :=
  Subtype.ext (by rw [coe_wittSMulPt, map_one, one_mul])

theorem wittSMulPt_mul (w w' : WittVector p R) (x : seriesPoint p R τ) :
    wittSMulPt (w * w') x = wittSMulPt w (wittSMulPt w' x) :=
  Subtype.ext (by rw [coe_wittSMulPt, coe_wittSMulPt, coe_wittSMulPt, map_mul, mul_assoc])

theorem wittSMulPt_add (w w' : WittVector p R) (x : seriesPoint p R τ) :
    wittSMulPt (w + w') x = wittSMulPt w x + wittSMulPt w' x :=
  Subtype.ext (by rw [coe_wittSMulPt, AddSubgroup.coe_add, coe_wittSMulPt, coe_wittSMulPt, map_add,
    add_mul])

def teichPt (c : R) : seriesPoint p R τ →+ seriesPoint p R τ :=
  wittSMulPt (WittVector.teichmuller p c)

theorem coe_teichPt (c : R) (x : seriesPoint p R τ) :
    ((teichPt c x : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)) =
      WittVector.teichmuller p (C c : MvPowerSeries τ R) * x := by
  rw [teichPt, coe_wittSMulPt, WittVector.map_teichmuller]

@[simp] theorem coeff_teichPt (c : R) (x : seriesPoint p R τ) (n : ℕ) :
    ((teichPt c x : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n =
      (c ^ p ^ n) • (x : WittVector p (MvPowerSeries τ R)).coeff n := by
  rw [coe_teichPt, teichmuller_C_mul_coeff]

theorem verschiebung_mem {x : WittVector p (MvPowerSeries τ R)} (hx : x ∈ seriesPoint p R τ) :
    WittVector.verschiebung x ∈ seriesPoint p R τ := by
  refine ⟨fun n => ?_, ⟨fun n => ?_, fun e => ?_⟩⟩
  · cases n with
    | zero => rw [WittVector.verschiebung_coeff_zero, map_zero]
    | succ n => rw [WittVector.verschiebung_coeff_succ]; exact hx.1 n
  · cases n with
    | zero => rw [WittVector.verschiebung_coeff_zero, map_zero]; exact IsNilpotent.zero
    | succ n => rw [WittVector.verschiebung_coeff_succ, hx.1 n]; exact IsNilpotent.zero
  · refine ((hx.2.coeff_zero e).image Nat.succ).subset fun n hn => ?_
    cases n with
    | zero => exact absurd (by rw [WittVector.verschiebung_coeff_zero, map_zero]) hn
    | succ n =>
      refine ⟨n, ?_, rfl⟩
      rwa [Set.mem_setOf_eq, WittVector.verschiebung_coeff_succ] at hn

def verPt : seriesPoint p R τ →+ seriesPoint p R τ where
  toFun x := ⟨WittVector.verschiebung x, verschiebung_mem x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp] theorem coe_verPt (x : seriesPoint p R τ) :
    ((verPt x : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)) = WittVector.verschiebung x := rfl

theorem coeff_verPt_zero (x : seriesPoint p R τ) :
    ((verPt x : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff 0 = 0 :=
  WittVector.verschiebung_coeff_zero _

theorem coeff_verPt_succ (x : seriesPoint p R τ) (n : ℕ) :
    ((verPt x : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff (n + 1) =
      (x : WittVector p (MvPowerSeries τ R)).coeff n :=
  WittVector.verschiebung_coeff_succ _ n

instance charP_mvPowerSeries [CharP R p] : CharP (MvPowerSeries τ R) p :=
  charP_of_injective_ringHom (C_injective (σ := τ) (R := R)) p

theorem frobenius_mem [CharP R p] {x : WittVector p (MvPowerSeries τ R)} (hx : x ∈ seriesPoint p R τ) :
    WittVector.frobenius x ∈ seriesPoint p R τ := by
  have hfam : (fun n => (WittVector.frobenius x).coeff n) = fun n => subst x.coeff (frobFam p R n) := by
    funext n
    rw [WittVector.coeff_frobenius_charP, frobFam_apply, subst_pow hx.2, subst_X hx.2]
  refine ⟨fun n => ?_, ?_⟩
  · rw [WittVector.coeff_frobenius_charP, map_pow, hx.1 n, zero_pow hp.out.ne_zero]
  · rw [hfam]
    simpa only [coe_substAlgHom] using (hasSubst_frobFam (p := p) (R := R)).comp hx.2

def frobPt [CharP R p] : seriesPoint p R τ →+ seriesPoint p R τ where
  toFun x := ⟨WittVector.frobenius x, frobenius_mem x.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

@[simp] theorem coe_frobPt [CharP R p] (x : seriesPoint p R τ) :
    ((frobPt x : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)) = WittVector.frobenius x := rfl

@[simp] theorem coeff_frobPt [CharP R p] (x : seriesPoint p R τ) (n : ℕ) :
    ((frobPt x : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n =
      (x : WittVector p (MvPowerSeries τ R)).coeff n ^ p :=
  WittVector.coeff_frobenius_charP p _ n

theorem coeff_frobPt_iterate [CharP R p] (x : seriesPoint p R τ) (m n : ℕ) :
    (((⇑(frobPt (p := p) (R := R) (τ := τ)))^[m] x : seriesPoint p R τ) :
        WittVector p (MvPowerSeries τ R)).coeff n =
      (x : WittVector p (MvPowerSeries τ R)).coeff n ^ p ^ m := by
  induction m generalizing x with
  | zero => rw [Function.iterate_zero_apply, pow_zero, pow_one]
  | succ m ih => rw [Function.iterate_succ_apply, ih, coeff_frobPt, ← pow_mul, ← pow_succ']

theorem frobPt_teichPt [CharP R p] (c : R) (x : seriesPoint p R τ) :
    frobPt (teichPt c x) = teichPt (c ^ p) (frobPt x) := by
  refine Subtype.ext (WittVector.ext fun n => ?_)
  rw [coeff_frobPt, coeff_teichPt, coeff_teichPt, coeff_frobPt, smul_pow, ← pow_mul, ← pow_mul,
    mul_comm (p ^ n) p]

def tautPt : seriesPoint p R ℕ :=
  ⟨WittVector.mk p fun n => (X n : MvPowerSeries ℕ R), fun n => by
    rw [WittVector.coeff_mk, constantCoeff_X], by simpa only [WittVector.coeff_mk] using HasSubst.X⟩

@[simp] theorem coeff_tautPt (n : ℕ) :
    ((tautPt : seriesPoint p R ℕ) : WittVector p (MvPowerSeries ℕ R)).coeff n = X n := rfl

def curveTautPt : seriesPoint p R Unit :=
  ⟨WittVector.mk p (CartierModule.curveFam R), fun n => by
    rw [WittVector.coeff_mk]; exact CartierModule.constantCoeff_curveFam n, by
    simpa only [WittVector.coeff_mk] using (CartierModule.hasSubst_curveFam (R := R))⟩

@[simp] theorem coeff_curveTautPt (n : ℕ) :
    ((curveTautPt : seriesPoint p R Unit) : WittVector p (PowerSeries R)).coeff n =
      CartierModule.curveFam R n := rfl

theorem map_subst_mem {b : τ → MvPowerSeries τ' R} (hb : HasSubst b)
    (hb0 : ∀ t, (b t).constantCoeff = 0)
    {x : WittVector p (MvPowerSeries τ R)} (hx : x ∈ seriesPoint p R τ) :
    WittVector.mk p (fun n => subst b (x.coeff n)) ∈ seriesPoint p R τ' := by
  refine ⟨fun n => ?_, ?_⟩
  · rw [WittVector.coeff_mk]
    exact constantCoeff_subst_eq_zero hb hb0 (hx.1 n)
  · simpa only [WittVector.coeff_mk, coe_substAlgHom] using hx.2.comp hb

def substPt {b : τ → MvPowerSeries τ' R} (hb : HasSubst b) (hb0 : ∀ t, (b t).constantCoeff = 0) :
    seriesPoint p R τ →+ seriesPoint p R τ' where
  toFun x := ⟨WittVector.mk p fun n => subst b ((x : WittVector p (MvPowerSeries τ R)).coeff n),
    map_subst_mem hb hb0 x.2⟩
  map_zero' := Subtype.ext (WittVector.ext fun n => by
    change subst b (((0 : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n) =
      ((0 : seriesPoint p R τ') : WittVector p (MvPowerSeries τ' R)).coeff n
    rw [AddSubgroup.coe_zero, WittVector.zero_coeff, AddSubgroup.coe_zero, WittVector.zero_coeff,
      ← coe_substAlgHom hb, map_zero])
  map_add' x y := Subtype.ext (WittVector.ext fun n => by
    change subst b (((x + y : seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n) =
      ((⟨_, map_subst_mem hb hb0 x.2⟩ + ⟨_, map_subst_mem hb hb0 y.2⟩ : seriesPoint p R τ') :
        WittVector p (MvPowerSeries τ' R)).coeff n
    rw [coe_add_coeff, coe_add_coeff, subst_comp_subst_apply
      (hasSubst_pairSeries (hasSubst_coeff x) (hasSubst_coeff y)) hb]
    congr 1
    funext ⟨i, m⟩
    refine Fin.cases rfl (fun l => ?_) i
    fin_cases l; rfl)

@[simp] theorem coeff_substPt {b : τ → MvPowerSeries τ' R} (hb : HasSubst b)
    (hb0 : ∀ t, (b t).constantCoeff = 0) (x : seriesPoint p R τ) (n : ℕ) :
    ((substPt hb hb0 x : seriesPoint p R τ') : WittVector p (MvPowerSeries τ' R)).coeff n =
      subst b ((x : WittVector p (MvPowerSeries τ R)).coeff n) := rfl

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {τ : Type v} {τ' : Type w}

def evalPtFun (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ) : SeriesPoint Φ τ where
  val := fun j => subst (fun n => (w : WittVector p (MvPowerSeries τ R)).coeff n) (f.toPowerSeries j)
  constantCoeff_eq_zero := fun j =>
    constantCoeff_subst_eq_zero (WittLaw.hasSubst_coeff w) (WittLaw.constantCoeff_coeff w)
      (f.constantCoeff_eq_zero j)

@[simp] theorem val_evalPtFun (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ) :
    (evalPtFun f w).val =
      fun j => subst (fun n => (w : WittVector p (MvPowerSeries τ R)).coeff n) (f.toPowerSeries j) :=
  rfl

theorem evalPtFun_add [Φ.IsComm] (f : CartierModule p Φ) (w w' : WittLaw.seriesPoint p R τ) :
    evalPtFun f (w + w') = evalPtFun f w + evalPtFun f w' := by
  refine SeriesPoint.ext (funext fun j => ?_)
  have hf := f.constantCoeff_eq_zero
  have hP := WittLaw.hasSubst_pairSeries (WittLaw.hasSubst_coeff w) (WittLaw.hasSubst_coeff w')
  change subst (fun n => ((w + w' : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n)
      (f.toPowerSeries j) =
    subst (Sum.elim (evalPtFun f w).val (evalPtFun f w').val) (Φ.toPowerSeries j)
  have hfam : (fun n => ((w + w' : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n) =
      fun n => subst (WittLaw.pairSeries (fun m => (w : WittVector p (MvPowerSeries τ R)).coeff m)
        fun m => (w' : WittVector p (MvPowerSeries τ R)).coeff m) (WittLaw.addFam p R n) :=
    funext (WittLaw.coe_add_coeff w w')
  rw [hfam, ← subst_comp_subst_apply (hasSubst_addFam p R) hP, f.subst_addFam,
    subst_subst_elim Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) hP]
  congr 1
  funext s
  rcases s with l | l
  · show subst _ (subst (blk 0) (f.toPowerSeries l)) = _
    rw [subst_comp_subst_apply (hasSubst_blk 0) hP]
    congr 1
    funext m
    exact subst_X hP ((0 : Fin 2), m)
  · show subst _ (subst (blk 1) (f.toPowerSeries l)) = _
    rw [subst_comp_subst_apply (hasSubst_blk 1) hP]
    congr 1
    funext m
    exact subst_X hP ((1 : Fin 2), m)

def evalPt [Φ.IsComm] : CartierModule p Φ →+ WittLaw.seriesPoint p R τ →+ SeriesPoint Φ τ where
  toFun f :=
    { toFun := evalPtFun f
      map_zero' := SeriesPoint.ext (funext fun j => by
        show subst (fun n => ((0 : WittLaw.seriesPoint p R τ) : WittVector p (MvPowerSeries τ R)).coeff n)
          (f.toPowerSeries j) = 0
        simp only [AddSubgroup.coe_zero, WittVector.zero_coeff]
        exact subst_zero_of_constantCoeff_eq_zero (f.constantCoeff_eq_zero j))
      map_add' := evalPtFun_add f }
  map_zero' := AddMonoidHom.ext fun w => SeriesPoint.ext (funext fun j => by
    show subst _ (0 : MvPowerSeries ℕ R) = 0
    rw [← coe_substAlgHom (WittLaw.hasSubst_coeff w), map_zero])
  map_add' f g := AddMonoidHom.ext fun w => SeriesPoint.ext (funext fun j =>
    subst_subst_elim Φ f.constantCoeff_eq_zero g.constantCoeff_eq_zero (WittLaw.hasSubst_coeff w) j)

@[simp] theorem val_evalPt [Φ.IsComm] (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ) :
    (evalPt f w).val =
      fun j => subst (fun n => (w : WittVector p (MvPowerSeries τ R)).coeff n) (f.toPowerSeries j) :=
  rfl

theorem evalPt_apply [Φ.IsComm] (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ) :
    evalPt f w = evalPtFun f w := rfl

theorem val_evalPt_precomp [Φ.IsComm] {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u)
    (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ) (j : Fin d) :
    (evalPt (precomp hu f) w).val j =
      subst (fun n => subst (fun m => (w : WittVector p (MvPowerSeries τ R)).coeff m) (u n))
        (f.toPowerSeries j) := by
  rw [val_evalPt, toPowerSeries_precomp]
  exact subst_comp_subst_apply hu.hasSubst (WittLaw.hasSubst_coeff w) _

theorem evalPt_eq_evalPt_precomp [Φ.IsComm] {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u)
    (f : CartierModule p Φ) (w w' : WittLaw.seriesPoint p R τ)
    (h : ∀ n, (w' : WittVector p (MvPowerSeries τ R)).coeff n =
      subst (fun m => (w : WittVector p (MvPowerSeries τ R)).coeff m) (u n)) :
    evalPt f w' = evalPt (precomp hu f) w := by
  refine SeriesPoint.ext (funext fun j => ?_)
  rw [val_evalPt_precomp]
  change subst (fun n => (w' : WittVector p (MvPowerSeries τ R)).coeff n) (f.toPowerSeries j) = _
  have hfam : (fun n => (w' : WittVector p (MvPowerSeries τ R)).coeff n) =
      fun n => subst (fun m => (w : WittVector p (MvPowerSeries τ R)).coeff m) (u n) := funext h
  rw [hfam]

theorem evalPt_verPt [Φ.IsComm] (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ) :
    evalPt f (WittLaw.verPt w) = evalPt (frobenius f) w := by
  refine evalPt_eq_evalPt_precomp WittLaw.isEndo_verFam f w _ fun n => ?_
  cases n with
  | zero =>
    rw [WittLaw.coeff_verPt_zero, WittLaw.verFam_zero, ← coe_substAlgHom (WittLaw.hasSubst_coeff w),
      map_zero]
  | succ n => rw [WittLaw.coeff_verPt_succ, WittLaw.verFam_succ, subst_X (WittLaw.hasSubst_coeff w)]

theorem evalPt_frobPt [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ) :
    evalPt f (WittLaw.frobPt w) = evalPt (verschiebung f) w := by
  refine evalPt_eq_evalPt_precomp WittLaw.isEndo_frobFam f w _ fun n => ?_
  rw [WittLaw.coeff_frobPt, WittLaw.frobFam_apply, subst_pow (WittLaw.hasSubst_coeff w),
    subst_X (WittLaw.hasSubst_coeff w)]

theorem evalPt_frobPt_iterate [Φ.IsComm] [CharP R p] (f : CartierModule p Φ)
    (w : WittLaw.seriesPoint p R τ) (m : ℕ) :
    evalPt f ((⇑(WittLaw.frobPt (p := p) (R := R) (τ := τ)))^[m] w) =
      evalPt ((⇑(verschiebung (p := p) (Φ := Φ)))^[m] f) w := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply, evalPt_frobPt, ih]

theorem evalPt_teichPt [Φ.IsComm] (c : R) (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ) :
    evalPt f (WittLaw.teichPt c w) = evalPt (homothety c f) w := by
  refine evalPt_eq_evalPt_precomp (WittLaw.isEndo_teichFam c) f w _ fun n => ?_
  rw [WittLaw.coeff_teichPt, WittLaw.teichFam_apply, subst_smul (WittLaw.hasSubst_coeff w),
    subst_X (WittLaw.hasSubst_coeff w)]

theorem evalPt_wittSMulPt [Φ.IsComm] (w : WittVector p R) (f : CartierModule p Φ)
    (x : WittLaw.seriesPoint p R τ) :
    evalPt f (WittLaw.wittSMulPt w x) = evalPt (w • f) x := by
  rw [smul_eq_precomp]
  exact evalPt_eq_evalPt_precomp (WittLaw.isEndo_mulFam w) f x _ (WittLaw.coeff_wittSMulPt w x)

theorem mapPt_evalPt [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ)
    (w : WittLaw.seriesPoint p R τ) :
    SeriesPoint.mapPt φ (evalPt f w) = evalPt (map φ f) w := by
  refine SeriesPoint.ext (funext fun i => ?_)
  change subst (evalPt f w).val (φ.toPowerSeries i) =
    subst (fun n => (w : WittVector p (MvPowerSeries τ R)).coeff n) ((map φ f).toPowerSeries i)
  rw [val_evalPt, toPowerSeries_map]
  exact (subst_comp_subst_apply f.hasSubst_toPowerSeries (WittLaw.hasSubst_coeff w) _).symm

theorem substPt_evalPt [Φ.IsComm] {b : τ → MvPowerSeries τ' R} (hb : HasSubst b)
    (hb0 : ∀ t, (b t).constantCoeff = 0) (f : CartierModule p Φ) (w : WittLaw.seriesPoint p R τ) :
    SeriesPoint.substPt hb hb0 (evalPt f w) = evalPt f (WittLaw.substPt hb hb0 w) := by
  refine SeriesPoint.ext (funext fun j => ?_)
  change subst b (subst (fun n => (w : WittVector p (MvPowerSeries τ R)).coeff n) (f.toPowerSeries j)) =
    subst (fun n => ((WittLaw.substPt hb hb0 w : WittLaw.seriesPoint p R τ') :
      WittVector p (MvPowerSeries τ' R)).coeff n) (f.toPowerSeries j)
  exact subst_comp_subst_apply (WittLaw.hasSubst_coeff w) hb _

theorem val_evalPt_tautPt [Φ.IsComm] (f : CartierModule p Φ) :
    (evalPt f (WittLaw.tautPt : WittLaw.seriesPoint p R ℕ)).val = f.toPowerSeries := by
  funext j
  rw [val_evalPt]
  exact congrFun subst_self _

theorem val_evalPt_curveTautPt [Φ.IsComm] (f : CartierModule p Φ) :
    (evalPt f (WittLaw.curveTautPt : WittLaw.seriesPoint p R Unit)).val = curve f := rfl

theorem evalPt_tautPt_injective [Φ.IsComm] :
    Function.Injective fun f : CartierModule p Φ => evalPt f (WittLaw.tautPt : WittLaw.seriesPoint p R ℕ) :=
  fun f g h => CartierModule.ext (by rw [← val_evalPt_tautPt f, ← val_evalPt_tautPt g]; exact congrArg _ h)

def presPi [Φ.IsComm] {ι : Type*} [Fintype ι] (f : ι → CartierModule p Φ)
    (w : ι → WittLaw.seriesPoint p R τ) : SeriesPoint Φ τ :=
  ∑ l, evalPt (f l) (w l)

theorem presPi_def [Φ.IsComm] {ι : Type*} [Fintype ι] (f : ι → CartierModule p Φ)
    (w : ι → WittLaw.seriesPoint p R τ) : presPi f w = ∑ l, evalPt (f l) (w l) := rfl

theorem presPi_add [Φ.IsComm] {ι : Type*} [Fintype ι] (f : ι → CartierModule p Φ)
    (w w' : ι → WittLaw.seriesPoint p R τ) : presPi f (w + w') = presPi f w + presPi f w' := by
  simp only [presPi, Pi.add_apply, map_add, Finset.sum_add_distrib]

theorem presPi_zero [Φ.IsComm] {ι : Type*} [Fintype ι] (f : ι → CartierModule p Φ) :
    presPi f (0 : ι → WittLaw.seriesPoint p R τ) = 0 := by
  simp only [presPi, Pi.zero_apply, map_zero, Finset.sum_const_zero]

theorem presPi_neg [Φ.IsComm] {ι : Type*} [Fintype ι] (f : ι → CartierModule p Φ)
    (w : ι → WittLaw.seriesPoint p R τ) : presPi f (-w) = -presPi f w := by
  simp only [presPi, Pi.neg_apply, map_neg, Finset.sum_neg_distrib]

theorem presPi_sub [Φ.IsComm] {ι : Type*} [Fintype ι] (f : ι → CartierModule p Φ)
    (w w' : ι → WittLaw.seriesPoint p R τ) : presPi f (w - w') = presPi f w - presPi f w' := by
  simp only [presPi, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]

def presPiHom [Φ.IsComm] {ι : Type*} [Fintype ι] (f : ι → CartierModule p Φ) :
    (ι → WittLaw.seriesPoint p R τ) →+ SeriesPoint Φ τ where
  toFun := presPi f
  map_zero' := presPi_zero f
  map_add' := presPi_add f

@[simp] theorem presPiHom_apply [Φ.IsComm] {ι : Type*} [Fintype ι] (f : ι → CartierModule p Φ)
    (w : ι → WittLaw.seriesPoint p R τ) : presPiHom f w = presPi f w := rfl

theorem presPi_add_left [Φ.IsComm] {ι : Type*} [Fintype ι] (f g : ι → CartierModule p Φ)
    (w : ι → WittLaw.seriesPoint p R τ) : presPi (f + g) w = presPi f w + presPi g w := by
  simp only [presPi, Pi.add_apply, map_add, AddMonoidHom.add_apply, Finset.sum_add_distrib]

theorem mapPt_presPi [Φ.IsComm] [Φ'.IsComm] {ι : Type*} [Fintype ι] (φ : Φ.Hom Φ')
    (f : ι → CartierModule p Φ) (w : ι → WittLaw.seriesPoint p R τ) :
    SeriesPoint.mapPt φ (presPi f w) = presPi (fun l => map φ (f l)) w := by
  simp only [presPi, map_sum, mapPt_evalPt]

namespace Examples

theorem val_evalPt_addLinear (v : Fin d → R) (w : WittLaw.seriesPoint p R τ) (i : Fin d) :
    (evalPt (addLinear p v) w).val i = v i • (w : WittVector p (MvPowerSeries τ R)).coeff 0 := by
  change subst _ ((addLinear p v).toPowerSeries i) = _
  rw [toPowerSeries_addLinear, subst_smul (WittLaw.hasSubst_coeff w),
    subst_X (WittLaw.hasSubst_coeff w)]

end Examples

end CartierModule

end MvFormalGroup

end


