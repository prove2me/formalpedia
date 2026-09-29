-- Prove2me | Definitions.Def_MvFormalGroup_CartierModule
-- name    : MvFormalGroup_CartierModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/916015cc-86b4-5cbc-87bf-0048e7ed62c4
-- title:
--   Cartier modules of multivariate formal group laws
-- statement:
--   Fix a prime $p$, a commutative ring $R$ and a $d$-dimensional formal group law $\Phi$ over $R$ (a $d$-tuple of power series in two blocks of $d$ variables, with the unit, linearity and associativity axioms as fields). The Witt addition law is packaged as the family `addFam p R n`, the image in $R$ of the Witt addition polynomial `WittVector.wittAdd p n`, read as a power series in the variables indexed by $\mathrm{Fin}\,2\times\mathbb N$ (two blocks $X_m$, $Y_m$). That this family is substitutable rests on a weighted-homogeneity statement proved here for arbitrary Witt structure polynomials: giving the variable $(i,m)$ the weight $c_i p^m$, `wittStructureInt p Φ n` is weighted homogeneous of degree $k p^n$ whenever the $n$-th Witt-polynomial specialisation of $\Phi$ is; applied to $X_0+X_1$ and $X_0X_1$ this gives homogeneity of degree $p^n$ for `wittAdd` (weights $1,1$) and for `wittMul` (weights $0,1$).
--
--   `CartierModule p Φ` is then a structure whose data is a $d$-tuple $f$ of power series in variables $X_0,X_1,\dots$ over $R$, with fields asserting that each $f_j$ has zero constant term and that substituting the Witt addition family into $f_j$ equals substituting $f$ in the first block and $f$ in the second block into $\Phi_j$; that is, $f$ is a homomorphism of formal groups from the $p$-typical Witt law to $\Phi$, presented on this model. For commutative $\Phi$ the set carries an abelian group structure with addition $f+g=\Phi(f,g)$, zero the tuple $0$ and negation given by the inverse series of $\Phi$.
--
--   A predicate `IsEndo p u` records that a family $u$ of series in $X_0,X_1,\dots$ is substitutable, has zero constant terms, and commutes with the Witt addition family in the sense $\,u_n(S_\bullet(X;Y))=S_n(u(X);u(Y))$; each such $u$ gives an additive precomposition operator `precomp`. Two instances are defined: `verFam`, the shift $X_m\mapsto X_{m+1}$ read as $(0,X_0,X_1,\dots)$, whose precomposition operator is named `frobenius`, and, over a base of characteristic $p$, `frobFam`, the family $X_m^p$, whose precomposition operator is named `verschiebung` and equals the $p$-th power expansion operator. The relations $\;$`frobenius`$\circ$`verschiebung`$=$`verschiebung`$\circ$`frobenius`$=p\cdot{}$ and injectivity of `verschiebung` are proved, the former via families `nsmulFam` computing multiplication by $n$ on Witt vectors and the identity $p\cdot x=(0,x_0^p,x_1^p,\dots)$ in characteristic $p$. Homomorphisms $\varphi\colon\Phi\to\Phi'$ act by postcomposition (`map`), additively, functorially and commuting with the two operators, whence a ring homomorphism `endAct` from $\mathrm{End}(\Phi)$ to the additive endomorphisms of the Cartier module, sending $n$ to multiplication by $n$. Finally `tangent` takes the coefficient of $X_0$ in each component, an additive map to $R^d$ killing `verschiebung` and intertwining `map` with the linear part of $\varphi$; `curve` substitutes $X_0\mapsto X$ and $X_m\mapsto 0$ for $m\ge 1$, producing the associated $d$-tuple of one-variable curves, with $\mathrm{coeff}_1$ recovering `tangent` and `verschiebung` becoming $X\mapsto X^p$. An example constructs, for $v\in R^d$, the element $v_i X_0$ of the Cartier module of the additive law, with tangent $v$, so that `tangent` is surjective there.
--
--   **Relation to Mathlib.** Built on Mathlib's Witt vectors (`WittVector.wittAdd`, `wittStructureInt`, `wittNSMul`) and multivariate power-series substitution; Mathlib has no multivariate formal group laws, no Cartier (Dieudonné) modules, and no weighted-homogeneity statement for Witt structure polynomials, all of which are the project's own.
--
--   **Where it is used.** These definitions provide the carrier and elementary operator structure ($F$, $V$, the action of $\mathrm{End}(\Phi)$, the tangent and curve maps) for the covariant Cartier–Dieudonné module of a formal group law, on which the structure theory of special formal modules used in the $p$-adic uniformisation of Shimura curves is then developed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_CartierModule.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace WittLaw

open MvPolynomial

variable (p : ℕ) [hp : Fact p.Prime]

def weight {idx : Type*} (c : idx → ℕ) : idx × ℕ → ℕ := fun im => c im.1 * p ^ im.2

omit hp in
@[simp] theorem weight_apply {idx : Type*} (c : idx → ℕ) (i : idx) (m : ℕ) :
    weight p c (i, m) = c i * p ^ m := rfl

omit hp in

theorem isWeightedHomogeneous_rename_wittPolynomial {idx : Type*} (c : idx → ℕ) (i : idx)
    (n : ℕ) :
    IsWeightedHomogeneous (weight p c) (rename (Prod.mk i) (wittPolynomial p ℤ n))
      (c i * p ^ n) := by
  rw [wittPolynomial_eq_sum_C_mul_X_pow, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun j hj => ?_
  rw [map_mul, rename_C, map_pow, map_pow, rename_X]
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hX := (isWeightedHomogeneous_X (R := ℤ) (weight p c) (i, j)).pow (p ^ (n - j))
  have hdeg : (p ^ (n - j)) • weight p c (i, j) = c i * p ^ n := by
    rw [weight_apply, smul_eq_mul, ← mul_assoc, mul_comm (p ^ (n - j)), mul_assoc,
      ← pow_add, Nat.sub_add_cancel hj']
  rw [hdeg] at hX
  have := hX.C_mul ((p : ℤ) ^ j)
  rwa [map_pow] at this

theorem isWeightedHomogeneous_wittStructureInt {idx : Type*} (c : idx → ℕ)
    (Φ : MvPolynomial idx ℤ) (k : ℕ)
    (hΦ : ∀ n, IsWeightedHomogeneous (weight p c)
      (bind₁ (fun i => rename (Prod.mk i) (wittPolynomial p ℤ n)) Φ) (k * p ^ n)) (n : ℕ) :
    IsWeightedHomogeneous (weight p c) (wittStructureInt p Φ n) (k * p ^ n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have key := wittStructureInt_prop p Φ n
    rw [← aeval_eq_bind₁, aeval_wittPolynomial, Finset.sum_range_succ, Nat.sub_self, pow_zero,
      pow_one] at key

    have hsum : IsWeightedHomogeneous (weight p c)
        (∑ i ∈ Finset.range n, (p : MvPolynomial (idx × ℕ) ℤ) ^ i *
          wittStructureInt p Φ i ^ p ^ (n - i)) (k * p ^ n) := by
      refine IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
      have hi' : i < n := Finset.mem_range.mp hi
      have h1 := (ih i hi').pow (p ^ (n - i))
      have hdeg : (p ^ (n - i)) • (k * p ^ i) = k * p ^ n := by
        rw [smul_eq_mul, mul_left_comm, ← pow_add, Nat.sub_add_cancel hi'.le]
      rw [hdeg] at h1
      have h2 := h1.C_mul ((p : ℤ) ^ i)
      rwa [map_pow, map_natCast] at h2
    intro d hd
    by_contra hne
    have hcoeff : coeff d ((p : MvPolynomial (idx × ℕ) ℤ) ^ n * wittStructureInt p Φ n) = 0 := by
      have := congrArg (coeff d) key
      rw [coeff_add] at this
      have hR : coeff d (bind₁ (fun i => rename (Prod.mk i) (wittPolynomial p ℤ n)) Φ) = 0 :=
        (hΦ n).coeff_eq_zero d hne
      have hS : coeff d (∑ i ∈ Finset.range n, (p : MvPolynomial (idx × ℕ) ℤ) ^ i *
          wittStructureInt p Φ i ^ p ^ (n - i)) = 0 := hsum.coeff_eq_zero d hne
      rw [hR, hS, zero_add] at this
      exact this
    have hC : (p : MvPolynomial (idx × ℕ) ℤ) ^ n = C ((p : ℤ) ^ n) := by
      rw [map_pow, map_natCast]
    rw [hC, coeff_C_mul] at hcoeff
    rcases mul_eq_zero.mp hcoeff with h | h
    · exact absurd h (pow_ne_zero _ (Int.natCast_ne_zero.mpr hp.out.ne_zero))
    · exact hd h

theorem isWeightedHomogeneous_wittAdd (n : ℕ) :
    IsWeightedHomogeneous (weight p fun _ : Fin 2 => 1) (WittVector.wittAdd p n) (p ^ n) := by
  have h := isWeightedHomogeneous_wittStructureInt p (fun _ : Fin 2 => 1) (X 0 + X 1) 1
    (fun m => by
      rw [map_add, bind₁_X_right, bind₁_X_right, one_mul]
      have h0 := isWeightedHomogeneous_rename_wittPolynomial p (fun _ : Fin 2 => 1) 0 m
      have h1 := isWeightedHomogeneous_rename_wittPolynomial p (fun _ : Fin 2 => 1) 1 m
      rw [one_mul] at h0 h1
      exact h0.add h1) n
  rwa [one_mul] at h

theorem isWeightedHomogeneous_wittMul (n : ℕ) :
    IsWeightedHomogeneous (weight p ![0, 1]) (WittVector.wittMul p n) (p ^ n) := by
  have h := isWeightedHomogeneous_wittStructureInt p ![0, 1] (X 0 * X 1) 1
    (fun m => by
      rw [map_mul, bind₁_X_right, bind₁_X_right, one_mul]
      have h0 := isWeightedHomogeneous_rename_wittPolynomial p ![0, 1] 0 m
      have h1 := isWeightedHomogeneous_rename_wittPolynomial p ![0, 1] 1 m
      simp only [Matrix.cons_val_zero, zero_mul, Matrix.cons_val_one, one_mul] at h0 h1
      have := h0.mul h1
      rwa [zero_add] at this) n
  rwa [one_mul] at h

variable (R : Type u) [CommRing R]

def addFam (n : ℕ) : MvPowerSeries (Fin 2 × ℕ) R :=
  ↑(MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p n))

theorem constantCoeff_addFam (n : ℕ) : MvPowerSeries.constantCoeff (addFam p R n) = 0 := by
  rw [addFam, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    coeff_map, ← constantCoeff_eq, WittVector.constantCoeff_wittAdd, map_zero]

theorem weight_eq_of_coeff_addFam_ne_zero {n : ℕ} {d : Fin 2 × ℕ →₀ ℕ}
    (h : MvPowerSeries.coeff d (addFam p R n) ≠ 0) :
    Finsupp.weight (weight p fun _ : Fin 2 => 1) d = p ^ n := by
  rw [addFam, MvPolynomial.coeff_coe, coeff_map] at h
  have h' : coeff d (WittVector.wittAdd p n) ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact isWeightedHomogeneous_wittAdd p n h'

theorem hasSubst_addFam : MvPowerSeries.HasSubst (addFam p R) := by
  refine ⟨fun n => by rw [constantCoeff_addFam]; exact IsNilpotent.zero, fun d => ?_⟩
  · refine (Set.finite_lt_nat (Finsupp.weight (weight p fun _ : Fin 2 => 1) d)).subset ?_
    intro n hn
    have hw := weight_eq_of_coeff_addFam_ne_zero p R hn
    show n < Finsupp.weight (weight p fun _ : Fin 2 => 1) d
    rw [hw]
    exact Nat.lt_pow_self hp.out.one_lt

instance instTendstoCofiniteProdMk (i : Fin 2) :
    Filter.TendstoCofinite (Prod.mk i : ℕ → Fin 2 × ℕ) :=
  Filter.tendstoCofinite_of_injective (Prod.mk_right_injective i)

variable {R}

def blk (i : Fin 2) : ℕ → MvPowerSeries (Fin 2 × ℕ) R := fun m => MvPowerSeries.X (i, m)

omit hp in
@[simp] theorem blk_apply (i : Fin 2) (m : ℕ) : blk (R := R) i m = MvPowerSeries.X (i, m) := rfl

omit hp in
theorem constantCoeff_blk (i : Fin 2) (m : ℕ) :
    MvPowerSeries.constantCoeff (blk (R := R) i m) = 0 :=
  MvPowerSeries.constantCoeff_X _

omit hp in
theorem hasSubst_blk (i : Fin 2) : MvPowerSeries.HasSubst (blk (R := R) i) :=
  MvPowerSeries.HasSubst.X_comp (Prod.mk i)

omit hp in

theorem subst_blk_eq_rename (i : Fin 2) (f : MvPowerSeries ℕ R) :
    MvPowerSeries.subst (blk i) f = MvPowerSeries.rename (Prod.mk i) f :=
  (MvPowerSeries.rename_eq_subst (Prod.mk i) f).symm

end WittLaw

open MvPowerSeries WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {d d' d'' : ℕ} {R : Type u} [CommRing R]

structure CartierModule (p : ℕ) [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R]
    (Φ : MvFormalGroup d R) where

  toPowerSeries : Fin d → MvPowerSeries ℕ R

  constantCoeff_eq_zero : ∀ j, (toPowerSeries j).constantCoeff = 0

  subst_eq : ∀ j,
    subst (WittLaw.addFam p R) (toPowerSeries j) =
      subst
        (Sum.elim
          (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (toPowerSeries l))
          fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (toPowerSeries l))
        (Φ.toPowerSeries j)

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}

@[ext] theorem ext {f g : CartierModule p Φ} (h : f.toPowerSeries = g.toPowerSeries) : f = g := by
  cases f; cases g; cases h; rfl

theorem hasSubst_toPowerSeries (f : CartierModule p Φ) : HasSubst f.toPowerSeries :=
  hasSubst_of_constantCoeff_zero f.constantCoeff_eq_zero

def inBlk (i : Fin 2) (a : Fin d → MvPowerSeries ℕ R) : Fin d → MvPowerSeries (Fin 2 × ℕ) R :=
  fun l => subst (blk i) (a l)

omit hp in
@[simp] theorem inBlk_apply (i : Fin 2) (a : Fin d → MvPowerSeries ℕ R) (l : Fin d) :
    inBlk i a l = subst (blk i) (a l) := rfl

omit hp in
theorem constantCoeff_inBlk (i : Fin 2) {a : Fin d → MvPowerSeries ℕ R}
    (ha : ∀ l, (a l).constantCoeff = 0) (l : Fin d) : (inBlk i a l).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_blk i) (constantCoeff_blk i) (ha l)

omit hp in
theorem inBlk_zero (i : Fin 2) : inBlk i (fun _ : Fin d => (0 : MvPowerSeries ℕ R)) = fun _ => 0 := by
  funext l
  show subst (blk i) (0 : MvPowerSeries ℕ R) = 0
  rw [← coe_substAlgHom (hasSubst_blk i), map_zero]

omit hp in

theorem inBlk_subst_elim (G : MvFormalGroup d' R) (i : Fin 2) {a b : Fin d' → MvPowerSeries ℕ R}
    (ha : ∀ l, (a l).constantCoeff = 0) (hb : ∀ l, (b l).constantCoeff = 0) :
    inBlk i (fun l => subst (Sum.elim a b) (G.toPowerSeries l)) =
      fun l => subst (Sum.elim (inBlk i a) (inBlk i b)) (G.toPowerSeries l) := by
  funext l
  exact subst_subst_elim G ha hb (hasSubst_blk i) l

omit hp in

theorem inBlk_negSeries (G : MvFormalGroup d' R) (i : Fin 2) {a : Fin d' → MvPowerSeries ℕ R}
    (ha : ∀ l, (a l).constantCoeff = 0) :
    inBlk i (negSeries G a) = negSeries G (inBlk i a) := by
  have hneg : ∀ j, (negSeries G a j).constantCoeff = 0 := constantCoeff_negSeries G a
  refine negSeries_unique G (constantCoeff_inBlk i ha) (constantCoeff_inBlk i hneg) fun l => ?_
  have h := congrFun (inBlk_subst_elim G i ha hneg) l
  rw [← h]
  show subst (blk i) (subst (Sum.elim a (negSeries G a)) (G.toPowerSeries l)) = 0
  rw [subst_elim_negSeries G ha l, ← coe_substAlgHom (hasSubst_blk i), map_zero]

theorem subst_addFam (f : CartierModule p Φ) (j : Fin d) :
    subst (WittLaw.addFam p R) (f.toPowerSeries j) =
      subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries)) (Φ.toPowerSeries j) :=
  f.subst_eq j

protected def zero (Φ : MvFormalGroup d R) : CartierModule p Φ where
  toPowerSeries := fun _ => 0
  constantCoeff_eq_zero := fun _ => map_zero _
  subst_eq := by
    intro j
    rw [← coe_substAlgHom (hasSubst_addFam p R), map_zero]
    have h0 : (fun l : Fin d => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R))
        ((fun _ : Fin d => (0 : MvPowerSeries ℕ R)) l)) = fun _ => 0 := inBlk_zero 0
    have h1 : (fun l : Fin d => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R))
        ((fun _ : Fin d => (0 : MvPowerSeries ℕ R)) l)) = fun _ => 0 := inBlk_zero 1
    rw [h0, h1]
    exact (subst_elim_zero_right Φ (fun _ => map_zero _) j).symm

instance instZero : Zero (CartierModule p Φ) := ⟨CartierModule.zero Φ⟩

@[simp] theorem toPowerSeries_zero : (0 : CartierModule p Φ).toPowerSeries = fun _ => 0 := rfl

protected def add [Φ.IsComm] (f g : CartierModule p Φ) : CartierModule p Φ where
  toPowerSeries := fun j => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries j)
  constantCoeff_eq_zero := fun j =>
    constantCoeff_subst_elim Φ f.constantCoeff_eq_zero g.constantCoeff_eq_zero j
  subst_eq := by
    intro j
    have hf := f.constantCoeff_eq_zero
    have hg := g.constantCoeff_eq_zero
    show subst (WittLaw.addFam p R)
        (subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries j)) =
      subst (Sum.elim
        (inBlk 0 fun l => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries l))
        (inBlk 1 fun l => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries l)))
        (Φ.toPowerSeries j)
    rw [subst_subst_elim Φ hf hg (hasSubst_addFam p R) j, inBlk_subst_elim Φ 0 hf hg,
      inBlk_subst_elim Φ 1 hf hg]
    have hfeq : (fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries))
          (Φ.toPowerSeries l) := funext f.subst_addFam
    have hgeq : (fun l => subst (WittLaw.addFam p R) (g.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 g.toPowerSeries) (inBlk 1 g.toPowerSeries))
          (Φ.toPowerSeries l) := funext g.subst_addFam
    rw [hfeq, hgeq]
    exact subst_elim_exchange Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf)
      (constantCoeff_inBlk 0 hg) (constantCoeff_inBlk 1 hg) j

instance instAdd [Φ.IsComm] : Add (CartierModule p Φ) := ⟨CartierModule.add⟩

@[simp] theorem toPowerSeries_add [Φ.IsComm] (f g : CartierModule p Φ) :
    (f + g).toPowerSeries =
      fun j => subst (Sum.elim f.toPowerSeries g.toPowerSeries) (Φ.toPowerSeries j) := rfl

protected def neg [Φ.IsComm] (f : CartierModule p Φ) : CartierModule p Φ where
  toPowerSeries := negSeries Φ f.toPowerSeries
  constantCoeff_eq_zero := constantCoeff_negSeries Φ f.toPowerSeries
  subst_eq := by
    intro j
    have hf := f.constantCoeff_eq_zero
    have hneg : ∀ j, (negSeries Φ f.toPowerSeries j).constantCoeff = 0 :=
      constantCoeff_negSeries Φ _
    show subst (WittLaw.addFam p R) (negSeries Φ f.toPowerSeries j) =
      subst (Sum.elim (inBlk 0 (negSeries Φ f.toPowerSeries)) (inBlk 1 (negSeries Φ f.toPowerSeries)))
        (Φ.toPowerSeries j)

    have hS : (fun l => subst (WittLaw.addFam p R) (negSeries Φ f.toPowerSeries l)) =
        negSeries Φ fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l) := by
      have hA := hasSubst_addFam p R
      have hA0 := constantCoeff_addFam p R
      refine negSeries_unique Φ (fun l => constantCoeff_subst_eq_zero hA hA0 (hf l))
        (fun l => constantCoeff_subst_eq_zero hA hA0 (hneg l)) fun i => ?_
      rw [← subst_subst_elim Φ hf hneg hA i, subst_elim_negSeries Φ hf i, ← coe_substAlgHom hA,
        map_zero]
    have h1 := congrFun hS j
    rw [h1]
    have hfeq : (fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries))
          (Φ.toPowerSeries l) := funext f.subst_addFam
    rw [hfeq, negSeries_elim_add Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf),
      ← inBlk_negSeries Φ 0 hf, ← inBlk_negSeries Φ 1 hf]

instance instNeg [Φ.IsComm] : Neg (CartierModule p Φ) := ⟨CartierModule.neg⟩

@[simp] theorem toPowerSeries_neg [Φ.IsComm] (f : CartierModule p Φ) :
    (-f).toPowerSeries = negSeries Φ f.toPowerSeries := rfl

instance instAddCommGroup [Φ.IsComm] : AddCommGroup (CartierModule p Φ) where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc a b c := CartierModule.ext (funext fun j =>
    subst_elim_assoc Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero c.constantCoeff_eq_zero j)
  zero_add a := CartierModule.ext (funext fun j =>
    subst_elim_zero_left Φ a.constantCoeff_eq_zero j)
  add_zero a := CartierModule.ext (funext fun j =>
    subst_elim_zero_right Φ a.constantCoeff_eq_zero j)
  add_comm a b := CartierModule.ext (funext fun j =>
    subst_elim_comm Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero j)
  neg_add_cancel a := CartierModule.ext (funext fun j =>
    subst_elim_negSeries_left Φ a.constantCoeff_eq_zero j)

@[simp] theorem toPowerSeries_sub [Φ.IsComm] (f g : CartierModule p Φ) :
    (f - g).toPowerSeries =
      fun j => subst (Sum.elim f.toPowerSeries (negSeries Φ g.toPowerSeries)) (Φ.toPowerSeries j) := by
  rw [sub_eq_add_neg]; rfl

end CartierModule

namespace WittLaw

variable (p)

def pairFam (u : ℕ → MvPowerSeries ℕ R) : Fin 2 × ℕ → MvPowerSeries (Fin 2 × ℕ) R :=
  fun im => subst (blk im.1) (u im.2)

structure IsEndo (u : ℕ → MvPowerSeries ℕ R) : Prop where
  hasSubst : HasSubst u
  constantCoeff : ∀ n, (u n).constantCoeff = 0
  subst_addFam : ∀ n, subst (addFam p R) (u n) = subst (pairFam u) (addFam p R n)

variable {p}

omit hp in
@[simp] theorem pairFam_apply (u : ℕ → MvPowerSeries ℕ R) (i : Fin 2) (m : ℕ) :
    pairFam u (i, m) = subst (blk i) (u m) := rfl

omit hp in
theorem constantCoeff_pairFam {u : ℕ → MvPowerSeries ℕ R} (hu : ∀ n, (u n).constantCoeff = 0)
    (im : Fin 2 × ℕ) : (pairFam u im).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_blk im.1) (constantCoeff_blk im.1) (hu im.2)

omit hp in

theorem exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero (i : Fin 2) (f : MvPowerSeries ℕ R)
    {e : Fin 2 × ℕ →₀ ℕ} (h : coeff e (subst (blk (R := R) i) f) ≠ 0) :
    ∃ x : ℕ →₀ ℕ, Finsupp.mapDomain (Prod.mk i) x = e ∧ coeff x f ≠ 0 := by
  rw [subst_blk_eq_rename, coeff_rename] at h
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨x, ?_, hne⟩
  simpa using hx

omit hp in

theorem hasSubst_pairFam {u : ℕ → MvPowerSeries ℕ R} (hu : HasSubst u)
    (hu0 : ∀ n, (u n).constantCoeff = 0) : HasSubst (pairFam u) := by
  refine ⟨fun im => by rw [constantCoeff_pairFam hu0]; exact IsNilpotent.zero, fun e => ?_⟩
  have hfin : ∀ i : Fin 2, {m : ℕ | coeff e (subst (blk (R := R) i) (u m)) ≠ 0}.Finite := by
    intro i
    by_cases hx : ∃ x : ℕ →₀ ℕ, Finsupp.mapDomain (Prod.mk i) x = e
    · obtain ⟨x, rfl⟩ := hx
      refine (hu.coeff_zero x).subset fun m hm => ?_
      obtain ⟨y, hy, hne⟩ := exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero i (u m) hm
      have hyx : y = x := Finsupp.mapDomain_injective (Prod.mk_right_injective i) hy
      rw [hyx] at hne
      exact hne
    · convert Set.finite_empty
      ext m
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      by_contra hm
      obtain ⟨y, hy, -⟩ := exists_coeff_ne_zero_of_coeff_subst_blk_ne_zero i (u m) hm
      exact hx ⟨y, hy⟩
  have hsub : {im : Fin 2 × ℕ | coeff e (pairFam u im) ≠ 0} ⊆
      ⋃ i : Fin 2, Prod.mk i '' {m : ℕ | coeff e (subst (blk (R := R) i) (u m)) ≠ 0} := by
    rintro ⟨i, m⟩ him
    exact Set.mem_iUnion.mpr ⟨i, m, him, rfl⟩
  exact (Set.finite_iUnion fun i => (hfin i).image _).subset hsub

omit hp in

theorem subst_pairFam_subst_blk {u : ℕ → MvPowerSeries ℕ R} (hu : HasSubst u)
    (hu0 : ∀ n, (u n).constantCoeff = 0) (i : Fin 2) (f : MvPowerSeries ℕ R) :
    subst (pairFam u) (subst (blk (R := R) i) f) = subst (blk (R := R) i) (subst u f) := by
  rw [subst_comp_subst_apply (hasSubst_blk i) (hasSubst_pairFam hu hu0),
    subst_comp_subst_apply hu (hasSubst_blk i)]
  congr 1
  funext m
  show subst (pairFam u) (X (i, m)) = subst (blk i) (u m)
  rw [subst_X (hasSubst_pairFam hu hu0)]
  rfl

variable (R)

def verFam : ℕ → MvPowerSeries ℕ R
  | 0 => 0
  | n + 1 => X n

variable {R}

omit hp in
@[simp] theorem verFam_zero : verFam R 0 = 0 := rfl

omit hp in
@[simp] theorem verFam_succ (n : ℕ) : verFam R (n + 1) = X n := rfl

omit hp in
theorem constantCoeff_verFam (n : ℕ) : (verFam R n).constantCoeff = 0 := by
  cases n with
  | zero => exact map_zero _
  | succ n => exact constantCoeff_X _

omit hp in
theorem hasSubst_verFam : HasSubst (verFam R) := by
  classical
  refine ⟨fun n => by rw [constantCoeff_verFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (e.support.image Nat.succ).finite_toSet.subset fun n hn => ?_
  cases n with
  | zero => exact absurd (by simp) hn
  | succ n =>
    have h : coeff e (X n : MvPowerSeries ℕ R) ≠ 0 := hn
    rw [coeff_X] at h
    split_ifs at h with he
    · subst he
      simp
    · exact absurd rfl h

theorem aeval_verschiebung_wittAdd (n : ℕ) :
    MvPolynomial.aeval (fun im : Fin 2 × ℕ =>
        (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : MvPolynomial (Fin 2 × ℕ) ℤ))
      (WittVector.wittAdd p n) =
      Nat.casesOn n 0 fun m => WittVector.wittAdd p m := by

  let A := MvPolynomial (Fin 2 × ℕ) ℤ
  let x : WittVector p A := WittVector.mk p fun m => MvPolynomial.X (0, m)
  let y : WittVector p A := WittVector.mk p fun m => MvPolynomial.X (1, m)
  have key := congrArg (fun z : WittVector p A => z.coeff n)
    (WittVector.verschiebung.map_add x y).symm
  have hval : (fun im : Fin 2 × ℕ =>
      (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : A)) =
      Function.uncurry ![(WittVector.verschiebung x).coeff, (WittVector.verschiebung y).coeff] := by
    funext ⟨i, m⟩
    fin_cases i <;> cases m <;> rfl
  rw [hval]
  change WittVector.peval (WittVector.wittAdd p n)
      ![(WittVector.verschiebung x).coeff, (WittVector.verschiebung y).coeff] = _
  rw [← WittVector.add_coeff, key]
  cases n with
  | zero => exact WittVector.verschiebung_coeff_zero _
  | succ m =>
    rw [WittVector.verschiebung_coeff_succ, WittVector.add_coeff]
    show MvPolynomial.aeval (Function.uncurry ![x.coeff, y.coeff]) (WittVector.wittAdd p m) = _
    have hid : Function.uncurry ![x.coeff, y.coeff] = (MvPolynomial.X : Fin 2 × ℕ → A) := by
      funext ⟨i, k⟩
      fin_cases i <;> rfl
    rw [hid, MvPolynomial.aeval_X_left_apply]

theorem subst_coe_addFam {τ : Type*} (g : Fin 2 × ℕ → MvPolynomial τ ℤ) (n : ℕ) :
    subst (fun im => ((MvPolynomial.map (Int.castRingHom R) (g im) : MvPolynomial τ R) :
      MvPowerSeries τ R)) (addFam p R n) =
      ((MvPolynomial.map (Int.castRingHom R) (MvPolynomial.aeval g (WittVector.wittAdd p n)) :
        MvPolynomial τ R) : MvPowerSeries τ R) := by
  rw [addFam, subst_coe]
  set G : Fin 2 × ℕ → MvPowerSeries τ R := fun im =>
    ((MvPolynomial.map (Int.castRingHom R) (g im) : MvPolynomial τ R) : MvPowerSeries τ R)
  let ψ₁ : MvPolynomial (Fin 2 × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.aeval G).toRingHom.comp (MvPolynomial.map (Int.castRingHom R))
  let ψ₂ : MvPolynomial (Fin 2 × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.coeToMvPowerSeries.ringHom (σ := τ) (R := R)).comp
      ((MvPolynomial.map (Int.castRingHom R)).comp (MvPolynomial.aeval g).toRingHom)
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun im => ?_)
    · have h1 := RingHom.ext_int (ψ₁.comp (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 2 × ℕ) ℤ))
        (ψ₂.comp (MvPolynomial.C : ℤ →+* MvPolynomial (Fin 2 × ℕ) ℤ))
      exact RingHom.congr_fun h1 r
    · simp [ψ₁, ψ₂, G]
  exact RingHom.congr_fun hψ (WittVector.wittAdd p n)

theorem isEndo_verFam : IsEndo p (verFam R) := by
  refine ⟨hasSubst_verFam, constantCoeff_verFam, fun n => ?_⟩
  have hpair : pairFam (verFam R) = fun im : Fin 2 × ℕ =>
      ((MvPolynomial.map (Int.castRingHom R)
        (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : MvPolynomial (Fin 2 × ℕ) ℤ) :
          MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
    funext ⟨i, m⟩
    cases m with
    | zero =>
      show subst (blk i) (0 : MvPowerSeries ℕ R) = _
      rw [← coe_substAlgHom (hasSubst_blk i), map_zero]
      simp
    | succ m =>
      show subst (blk i) (X m : MvPowerSeries ℕ R) = _
      rw [subst_X (hasSubst_blk i)]
      simp [blk]
  rw [hpair, subst_coe_addFam (fun im : Fin 2 × ℕ =>
    (Nat.casesOn im.2 0 fun m => MvPolynomial.X (im.1, m) : MvPolynomial (Fin 2 × ℕ) ℤ)) n,
    aeval_verschiebung_wittAdd]
  cases n with
  | zero =>
    show subst (addFam p R) (0 : MvPowerSeries ℕ R) = _
    rw [← coe_substAlgHom (hasSubst_addFam p R), map_zero]
    simp
  | succ m =>
    show subst (addFam p R) (X m : MvPowerSeries ℕ R) = _
    rw [subst_X (hasSubst_addFam p R)]
    rfl

variable (p R)

def frobFam : ℕ → MvPowerSeries ℕ R := fun n => X n ^ p

variable {p R}

omit hp in
@[simp] theorem frobFam_apply (n : ℕ) : frobFam p R n = X n ^ p := rfl

theorem constantCoeff_frobFam (n : ℕ) : (frobFam p R n).constantCoeff = 0 := by
  rw [frobFam_apply, map_pow, constantCoeff_X, zero_pow hp.out.ne_zero]

theorem hasSubst_frobFam : HasSubst (frobFam p R) := HasSubst.X_pow hp.out.ne_zero

theorem subst_frobFam (f : MvPowerSeries ℕ R) :
    subst (frobFam p R) f = MvPowerSeries.expand p hp.out.ne_zero f := by
  rw [MvPowerSeries.expand, substAlgHom_apply]
  rfl

theorem expand_map_wittAdd [CharP R p] (n : ℕ) :
    MvPolynomial.expand p (MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p n)) =
      MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p n) ^ p := by
  haveI : ExpChar R p := ExpChar.prime hp.out
  rw [← MvPolynomial.map_frobenius_expand p, MvPolynomial.map_expand, MvPolynomial.map_map,
    show (frobenius R p).comp (Int.castRingHom R) = Int.castRingHom R from RingHom.ext_int _ _]

theorem isEndo_frobFam [CharP R p] : IsEndo p (frobFam p R) := by
  refine ⟨hasSubst_frobFam, constantCoeff_frobFam, fun n => ?_⟩
  have hpair : pairFam (frobFam p R) = fun im : Fin 2 × ℕ =>
      ((MvPolynomial.map (Int.castRingHom R) (MvPolynomial.X im ^ p : MvPolynomial (Fin 2 × ℕ) ℤ) :
        MvPolynomial (Fin 2 × ℕ) R) : MvPowerSeries (Fin 2 × ℕ) R) := by
    funext ⟨i, m⟩
    show subst (blk i) (X m ^ p : MvPowerSeries ℕ R) = _
    rw [subst_pow (hasSubst_blk i), subst_X (hasSubst_blk i), map_pow, MvPolynomial.map_X,
      MvPolynomial.coe_pow, MvPolynomial.coe_X]
    rfl
  rw [hpair, frobFam_apply, subst_pow (hasSubst_addFam p R), subst_X (hasSubst_addFam p R),
    subst_coe_addFam (fun im : Fin 2 × ℕ => (MvPolynomial.X im ^ p : MvPolynomial (Fin 2 × ℕ) ℤ)) n]
  have hexp : MvPolynomial.aeval (fun im : Fin 2 × ℕ => (MvPolynomial.X im ^ p :
      MvPolynomial (Fin 2 × ℕ) ℤ)) (WittVector.wittAdd p n) =
      MvPolynomial.expand p (WittVector.wittAdd p n) := by
    rw [MvPolynomial.expand, ← MvPolynomial.aeval_eq_bind₁]
  rw [hexp, MvPolynomial.map_expand, expand_map_wittAdd, MvPolynomial.coe_pow]
  rfl

end WittLaw

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}

def precompFun {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u) (f : CartierModule p Φ) :
    CartierModule p Φ where
  toPowerSeries := fun j => subst u (f.toPowerSeries j)
  constantCoeff_eq_zero := fun j =>
    constantCoeff_subst_eq_zero hu.hasSubst hu.constantCoeff (f.constantCoeff_eq_zero j)
  subst_eq := by
    intro j
    have hf := f.constantCoeff_eq_zero
    have hA := hasSubst_addFam p R
    have hP := hasSubst_pairFam hu.hasSubst hu.constantCoeff
    show subst (WittLaw.addFam p R) (subst u (f.toPowerSeries j)) =
      subst (Sum.elim (inBlk 0 fun l => subst u (f.toPowerSeries l))
        (inBlk 1 fun l => subst u (f.toPowerSeries l))) (Φ.toPowerSeries j)
    rw [subst_comp_subst_apply hu.hasSubst hA]
    have hfam : (fun n => subst (WittLaw.addFam p R) (u n)) =
        fun n => subst (WittLaw.pairFam u) (WittLaw.addFam p R n) := funext hu.subst_addFam
    rw [hfam, ← subst_comp_subst_apply hA hP, f.subst_addFam, subst_subst_elim Φ
      (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) hP]
    congr 1
    funext s
    rcases s with l | l
    · exact WittLaw.subst_pairFam_subst_blk hu.hasSubst hu.constantCoeff 0 (f.toPowerSeries l)
    · exact WittLaw.subst_pairFam_subst_blk hu.hasSubst hu.constantCoeff 1 (f.toPowerSeries l)

@[simp] theorem toPowerSeries_precompFun {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u)
    (f : CartierModule p Φ) :
    (precompFun hu f).toPowerSeries = fun j => subst u (f.toPowerSeries j) := rfl

def precomp [Φ.IsComm] {u : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u) :
    CartierModule p Φ →+ CartierModule p Φ where
  toFun := precompFun hu
  map_zero' := CartierModule.ext (funext fun j => by
    show subst u (0 : MvPowerSeries ℕ R) = 0
    rw [← coe_substAlgHom hu.hasSubst, map_zero])
  map_add' f g := CartierModule.ext (funext fun j =>
    subst_subst_elim Φ f.constantCoeff_eq_zero g.constantCoeff_eq_zero hu.hasSubst j)

@[simp] theorem toPowerSeries_precomp [Φ.IsComm] {u : ℕ → MvPowerSeries ℕ R}
    (hu : WittLaw.IsEndo p u) (f : CartierModule p Φ) :
    (precomp hu f).toPowerSeries = fun j => subst u (f.toPowerSeries j) := rfl

theorem precomp_precomp [Φ.IsComm] {u v : ℕ → MvPowerSeries ℕ R} (hu : WittLaw.IsEndo p u)
    (hv : WittLaw.IsEndo p v) (f : CartierModule p Φ) (j : Fin d) :
    (precomp hv (precomp hu f)).toPowerSeries j = subst (fun n => subst v (u n)) (f.toPowerSeries j) := by
  show subst v (subst u (f.toPowerSeries j)) = _
  rw [subst_comp_subst_apply hu.hasSubst hv.hasSubst]

def frobenius [Φ.IsComm] : CartierModule p Φ →+ CartierModule p Φ :=
  precomp WittLaw.isEndo_verFam

@[simp] theorem toPowerSeries_frobenius [Φ.IsComm] (f : CartierModule p Φ) :
    (frobenius f).toPowerSeries = fun j => subst (WittLaw.verFam R) (f.toPowerSeries j) := rfl

def verschiebung [Φ.IsComm] [CharP R p] : CartierModule p Φ →+ CartierModule p Φ :=
  precomp WittLaw.isEndo_frobFam

@[simp] theorem toPowerSeries_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    (verschiebung f).toPowerSeries = fun j => subst (WittLaw.frobFam p R) (f.toPowerSeries j) := rfl

theorem toPowerSeries_verschiebung_eq_expand [Φ.IsComm] [CharP R p] (f : CartierModule p Φ)
    (j : Fin d) :
    (verschiebung f).toPowerSeries j = MvPowerSeries.expand p hp.out.ne_zero (f.toPowerSeries j) :=
  WittLaw.subst_frobFam _

theorem frobenius_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    frobenius (verschiebung f) = verschiebung (frobenius f) := by
  apply CartierModule.ext
  funext j
  rw [frobenius, verschiebung, precomp_precomp, precomp_precomp]
  congr 1
  funext n
  cases n with
  | zero =>
    show subst (WittLaw.verFam R) (X 0 ^ p : MvPowerSeries ℕ R) =
      subst (WittLaw.frobFam p R) (0 : MvPowerSeries ℕ R)
    rw [subst_pow WittLaw.hasSubst_verFam, subst_X WittLaw.hasSubst_verFam,
      ← coe_substAlgHom WittLaw.hasSubst_frobFam, map_zero, WittLaw.verFam_zero,
      zero_pow hp.out.ne_zero]
  | succ m =>
    show subst (WittLaw.verFam R) (X (m + 1) ^ p : MvPowerSeries ℕ R) =
      subst (WittLaw.frobFam p R) (X m : MvPowerSeries ℕ R)
    rw [subst_pow WittLaw.hasSubst_verFam, subst_X WittLaw.hasSubst_verFam,
      subst_X WittLaw.hasSubst_frobFam, WittLaw.verFam_succ, WittLaw.frobFam_apply]

theorem verschiebung_injective [Φ.IsComm] [CharP R p] :
    Function.Injective (verschiebung : CartierModule p Φ → CartierModule p Φ) := by
  intro f g h
  apply CartierModule.ext
  funext j
  ext m
  have hj := congrArg (fun k : CartierModule p Φ => coeff (p • m) (k.toPowerSeries j)) h
  simpa only [toPowerSeries_verschiebung_eq_expand, MvPowerSeries.coeff_expand_smul] using hj

theorem _root_.MvFormalGroup.Hom.subst_subst_elim {τ : Type*} {F : MvFormalGroup d R}
    {G : MvFormalGroup d' R} (φ : F.Hom G) {a b : Fin d → MvPowerSeries τ R}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) (i : Fin d') :
    subst (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) (φ.toPowerSeries i) =
      subst (Sum.elim (fun j => subst a (φ.toPowerSeries j)) fun j => subst b (φ.toPowerSeries j))
        (G.toPowerSeries i) := by
  have hab : HasSubst (Sum.elim a b) := hasSubst_elim ha hb
  have hXl : HasSubst (fun l : Fin d => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hXr : HasSubst (fun l : Fin d => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
  have hLR : HasSubst (Sum.elim
      (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j))
      fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j)) :=
    hasSubst_elim
      (fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j))
      fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j)
  have key := congrArg (subst (Sum.elim a b)) (φ.subst_eq i)
  rw [subst_comp_subst_apply F.hasSubst_toPowerSeries hab, subst_comp_subst_apply hLR hab] at key
  rw [key]
  congr 1
  funext s
  rcases s with j | j
  · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j)) = subst a (φ.toPowerSeries j)
    rw [subst_comp_subst_apply hXl hab]
    congr 1
    funext l
    exact subst_X hab (Sum.inl l)
  · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) R))
        (φ.toPowerSeries j)) = subst b (φ.toPowerSeries j)
    rw [subst_comp_subst_apply hXr hab]
    congr 1
    funext l
    exact subst_X hab (Sum.inr l)

def mapFun (φ : Φ.Hom Φ') (f : CartierModule p Φ) : CartierModule p Φ' where
  toPowerSeries := fun i => subst f.toPowerSeries (φ.toPowerSeries i)
  constantCoeff_eq_zero := fun i =>
    constantCoeff_subst_eq_zero f.hasSubst_toPowerSeries f.constantCoeff_eq_zero
      (φ.constantCoeff_eq_zero i)
  subst_eq := by
    intro i
    have hf := f.constantCoeff_eq_zero
    show subst (WittLaw.addFam p R) (subst f.toPowerSeries (φ.toPowerSeries i)) =
      subst (Sum.elim (inBlk 0 fun l => subst f.toPowerSeries (φ.toPowerSeries l))
        (inBlk 1 fun l => subst f.toPowerSeries (φ.toPowerSeries l))) (Φ'.toPowerSeries i)
    rw [subst_comp_subst_apply f.hasSubst_toPowerSeries (hasSubst_addFam p R)]
    have hfam : (fun l => subst (WittLaw.addFam p R) (f.toPowerSeries l)) =
        fun l => subst (Sum.elim (inBlk 0 f.toPowerSeries) (inBlk 1 f.toPowerSeries))
          (Φ.toPowerSeries l) := funext f.subst_addFam
    rw [hfam, φ.subst_subst_elim (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) i]
    congr 1
    funext s
    rcases s with l | l
    · show subst (inBlk 0 f.toPowerSeries) (φ.toPowerSeries l) =
        subst (blk 0) (subst f.toPowerSeries (φ.toPowerSeries l))
      rw [subst_comp_subst_apply f.hasSubst_toPowerSeries (hasSubst_blk 0)]
      rfl
    · show subst (inBlk 1 f.toPowerSeries) (φ.toPowerSeries l) =
        subst (blk 1) (subst f.toPowerSeries (φ.toPowerSeries l))
      rw [subst_comp_subst_apply f.hasSubst_toPowerSeries (hasSubst_blk 1)]
      rfl

@[simp] theorem toPowerSeries_mapFun (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    (mapFun φ f).toPowerSeries = fun i => subst f.toPowerSeries (φ.toPowerSeries i) := rfl

def map [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') : CartierModule p Φ →+ CartierModule p Φ' where
  toFun := mapFun φ
  map_zero' := CartierModule.ext (funext fun i =>
    subst_zero_of_constantCoeff_eq_zero (φ.constantCoeff_eq_zero i))
  map_add' f g := CartierModule.ext (funext fun i =>
    φ.subst_subst_elim f.constantCoeff_eq_zero g.constantCoeff_eq_zero i)

@[simp] theorem toPowerSeries_map [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    (map φ f).toPowerSeries = fun i => subst f.toPowerSeries (φ.toPowerSeries i) := rfl

theorem map_id [Φ.IsComm] (f : CartierModule p Φ) : map (MvFormalGroup.Hom.id Φ) f = f :=
  CartierModule.ext (funext fun i => subst_X f.hasSubst_toPowerSeries i)

theorem map_comp [Φ.IsComm] [Φ'.IsComm] [Φ''.IsComm] (ψ : Φ'.Hom Φ'') (φ : Φ.Hom Φ')
    (f : CartierModule p Φ) : map (ψ.comp φ) f = map ψ (map φ f) :=
  CartierModule.ext (funext fun i =>
    subst_comp_subst_apply φ.hasSubst_toPowerSeries f.hasSubst_toPowerSeries (ψ.toPowerSeries i))

theorem map_add_hom [Φ.IsComm] [Φ'.IsComm] (φ ψ : Φ.Hom Φ') (f : CartierModule p Φ) :
    map (φ + ψ) f = map φ f + map ψ f :=
  CartierModule.ext (funext fun i =>
    subst_subst_elim Φ' φ.constantCoeff_eq_zero ψ.constantCoeff_eq_zero f.hasSubst_toPowerSeries i)

theorem map_zero_hom [Φ.IsComm] [Φ'.IsComm] (f : CartierModule p Φ) :
    map (0 : Φ.Hom Φ') f = 0 :=
  CartierModule.ext (funext fun i => by
    show subst f.toPowerSeries (0 : MvPowerSeries (Fin d) R) = 0
    rw [← coe_substAlgHom f.hasSubst_toPowerSeries, map_zero])

theorem map_precomp [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') {u : ℕ → MvPowerSeries ℕ R}
    (hu : WittLaw.IsEndo p u) (f : CartierModule p Φ) :
    map φ (precomp hu f) = precomp hu (map φ f) :=
  CartierModule.ext (funext fun i =>
    (subst_comp_subst_apply f.hasSubst_toPowerSeries hu.hasSubst (φ.toPowerSeries i)).symm)

theorem map_frobenius [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    map φ (frobenius f) = frobenius (map φ f) :=
  map_precomp φ _ f

theorem map_verschiebung [Φ.IsComm] [Φ'.IsComm] [CharP R p] (φ : Φ.Hom Φ')
    (f : CartierModule p Φ) : map φ (verschiebung f) = verschiebung (map φ f) :=
  map_precomp φ _ f

def endAct [Φ.IsComm] : MvFormalGroup.End Φ →+* AddMonoid.End (CartierModule p Φ) where
  toFun φ := map φ
  map_one' := AddMonoidHom.ext map_id
  map_mul' φ ψ := AddMonoidHom.ext (map_comp φ ψ)
  map_zero' := AddMonoidHom.ext map_zero_hom
  map_add' φ ψ := AddMonoidHom.ext (map_add_hom φ ψ)

@[simp] theorem endAct_apply [Φ.IsComm] (φ : MvFormalGroup.End Φ) (f : CartierModule p Φ) :
    endAct φ f = map φ f := rfl

theorem endAct_frobenius [Φ.IsComm] (φ : MvFormalGroup.End Φ) (f : CartierModule p Φ) :
    endAct φ (frobenius f) = frobenius (endAct φ f) :=
  map_frobenius φ f

theorem endAct_verschiebung [Φ.IsComm] [CharP R p] (φ : MvFormalGroup.End Φ)
    (f : CartierModule p Φ) : endAct φ (verschiebung f) = verschiebung (endAct φ f) :=
  map_verschiebung φ f

theorem endAct_natCast [Φ.IsComm] (n : ℕ) (f : CartierModule p Φ) :
    endAct (n : MvFormalGroup.End Φ) f = n • f := by
  rw [map_natCast]; rfl

end CartierModule

namespace WittLaw

def nsmulFam (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (n : ℕ) : ℕ → MvPowerSeries ℕ R :=
  fun k => ((MvPolynomial.map (Int.castRingHom R)
    (MvPolynomial.rename Prod.snd (WittVector.wittNSMul p n k)) : MvPolynomial ℕ R) :
      MvPowerSeries ℕ R)

theorem isWeightedHomogeneous_wittNSMul (n k : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (weight p fun _ : Fin 1 => 1) (WittVector.wittNSMul p n k)
      (p ^ k) := by
  have h := isWeightedHomogeneous_wittStructureInt p (fun _ : Fin 1 => 1)
    (n • MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℤ) 1
    (fun m => by
      rw [map_nsmul, MvPolynomial.bind₁_X_right, one_mul, nsmul_eq_mul, ← map_natCast MvPolynomial.C]
      have h0 := isWeightedHomogeneous_rename_wittPolynomial p (fun _ : Fin 1 => 1) 0 m
      rw [one_mul] at h0
      exact h0.C_mul _) k
  rwa [one_mul] at h

theorem constantCoeff_nsmulFam (n k : ℕ) : (nsmulFam p R n k).constantCoeff = 0 := by
  rw [nsmulFam, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_map, ← MvPolynomial.constantCoeff_eq, MvPolynomial.constantCoeff_rename,
    WittVector.constantCoeff_wittNSMul, map_zero]

theorem weight_eq_of_coeff_nsmulFam_ne_zero {n k : ℕ} {e : ℕ →₀ ℕ}
    (h : coeff e (nsmulFam p R n k) ≠ 0) : Finsupp.weight (fun m => p ^ m) e = p ^ k := by
  classical
  rw [nsmulFam, MvPolynomial.coeff_coe, MvPolynomial.coeff_map] at h
  have h' : MvPolynomial.coeff e (MvPolynomial.rename Prod.snd (WittVector.wittNSMul p n k)) ≠ 0 :=
    fun h0 => h (by rw [h0, map_zero])
  obtain ⟨x, hx, hne⟩ := MvPolynomial.coeff_rename_ne_zero _ _ _ h'
  have hw := isWeightedHomogeneous_wittNSMul (p := p) n k hne
  rw [← hx, ← hw, Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_mapDomain_index (h := fun i c => c • p ^ i) (fun _ => zero_smul ℕ _)
      (fun _ _ _ => add_smul _ _ _)]
  refine Finsupp.sum_congr fun im _ => ?_
  simp [weight]

theorem hasSubst_nsmulFam (n : ℕ) : HasSubst (nsmulFam p R n) := by
  refine ⟨fun k => by rw [constantCoeff_nsmulFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight (fun m => p ^ m) e)).subset fun k hk => ?_
  have hw := weight_eq_of_coeff_nsmulFam_ne_zero (p := p) (R := R) hk
  show k < Finsupp.weight (fun m => p ^ m) e
  rw [hw]
  exact Nat.lt_pow_self hp.out.one_lt

omit hp in

private theorem peval_tautological (φ : MvPolynomial (Fin 1 × ℕ) ℤ) :
    WittVector.peval φ ![(WittVector.mk p fun m => (MvPolynomial.X (0, m) :
      MvPolynomial (Fin 1 × ℕ) ℤ)).coeff] = φ := by
  have hid : Function.uncurry ![(WittVector.mk p fun m => (MvPolynomial.X (0, m) :
      MvPolynomial (Fin 1 × ℕ) ℤ)).coeff] = (MvPolynomial.X : Fin 1 × ℕ → _) := by
    funext ⟨i, m⟩
    fin_cases i; rfl
  show MvPolynomial.aeval _ φ = φ
  rw [hid, MvPolynomial.aeval_X_left_apply]

theorem wittNSMul_zero (k : ℕ) : WittVector.wittNSMul p 0 k = 0 := by
  let x : WittVector p (MvPolynomial (Fin 1 × ℕ) ℤ) := WittVector.mk p fun m => MvPolynomial.X (0, m)
  have h := WittVector.nsmul_coeff 0 x k
  rw [zero_nsmul, WittVector.zero_coeff, peval_tautological] at h
  exact h.symm

theorem aeval_wittNSMul_wittAdd (n k : ℕ) :
    MvPolynomial.aeval (fun im : Fin 2 × ℕ =>
        (Fin.cases (WittVector.wittNSMul p n im.2) (fun _ => MvPolynomial.X (0, im.2)) im.1 :
          MvPolynomial (Fin 1 × ℕ) ℤ)) (WittVector.wittAdd p k) =
      WittVector.wittNSMul p (n + 1) k := by
  let x : WittVector p (MvPolynomial (Fin 1 × ℕ) ℤ) := WittVector.mk p fun m => MvPolynomial.X (0, m)
  have h := WittVector.nsmul_coeff (n + 1) x k
  rw [peval_tautological, succ_nsmul, WittVector.add_coeff] at h
  have hval : (fun im : Fin 2 × ℕ =>
      (Fin.cases (WittVector.wittNSMul p n im.2) (fun _ => MvPolynomial.X (0, im.2)) im.1 :
        MvPolynomial (Fin 1 × ℕ) ℤ)) = Function.uncurry ![(n • x).coeff, x.coeff] := by
    funext ⟨i, m⟩
    refine Fin.cases ?_ (fun l => ?_) i
    · show WittVector.wittNSMul p n m = (n • x).coeff m
      rw [WittVector.nsmul_coeff, peval_tautological]
    · fin_cases l; rfl
  rw [hval]
  exact h

private theorem aeval_X_eq_map {σ : Type*} (S : Type*) [CommRing S] (φ : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S) φ =
      MvPolynomial.map (Int.castRingHom S) φ := by
  refine RingHom.congr_fun (?_ :
    (MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S)).toRingHom =
      MvPolynomial.map (Int.castRingHom S)) φ
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · exact RingHom.congr_fun (RingHom.ext_int
      ((MvPolynomial.aeval (MvPolynomial.X : σ → MvPolynomial σ S)).toRingHom.comp
        (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ))
      ((MvPolynomial.map (Int.castRingHom S)).comp (MvPolynomial.C : ℤ →+* MvPolynomial σ ℤ))) r
  · simp

theorem map_wittNSMul_self (k : ℕ) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) (WittVector.wittNSMul p p k) =
      Nat.casesOn k 0 fun m => MvPolynomial.X (0, m) ^ p := by
  let A := MvPolynomial (Fin 1 × ℕ) (ZMod p)
  let x : WittVector p A := WittVector.mk p fun m => MvPolynomial.X (0, m)
  have h := WittVector.nsmul_coeff p x k
  have hid : Function.uncurry ![x.coeff] = (MvPolynomial.X : Fin 1 × ℕ → A) := by
    funext ⟨i, m⟩
    fin_cases i; rfl
  have hev : WittVector.peval (WittVector.wittNSMul p p k) ![x.coeff] =
      MvPolynomial.map (Int.castRingHom (ZMod p)) (WittVector.wittNSMul p p k) := by
    show MvPolynomial.aeval _ _ = _
    rw [hid]
    exact aeval_X_eq_map (ZMod p) _
  rw [← hev, ← h, nsmul_eq_mul, mul_comm]
  cases k with
  | zero => exact WittVector.mul_charP_coeff_zero x
  | succ m => exact WittVector.mul_charP_coeff_succ x m

omit hp in

theorem hasSubst_finCases {τ : Type*} {u₀ u₁ : ℕ → MvPowerSeries τ R} (h₀ : HasSubst u₀)
    (h₁ : HasSubst u₁) :
    HasSubst (fun im : Fin 2 × ℕ => (Fin.cases (u₀ im.2) (fun _ => u₁ im.2) im.1 : MvPowerSeries τ R)) := by
  refine ⟨fun ⟨i, m⟩ => Fin.cases (h₀.const_coeff m) (fun _ => h₁.const_coeff m) i, fun e => ?_⟩
  refine (((h₀.coeff_zero e).image (Prod.mk 0)).union ((h₁.coeff_zero e).image (Prod.mk 1))).subset ?_
  rintro ⟨i, m⟩ him
  revert him
  refine Fin.cases (fun him => Or.inl ⟨m, him, rfl⟩) (fun l him => Or.inr ⟨m, him, ?_⟩) i
  fin_cases l; rfl

variable (p R) in

def stepFam (n : ℕ) : Fin 2 × ℕ → MvPowerSeries ℕ R :=
  fun im => Fin.cases (nsmulFam p R n im.2) (fun _ => X im.2) im.1

theorem hasSubst_stepFam (n : ℕ) : HasSubst (stepFam p R n) :=
  hasSubst_finCases (hasSubst_nsmulFam n) HasSubst.X

theorem stepFam_eq (n : ℕ) : stepFam p R n = fun im : Fin 2 × ℕ =>
    ((MvPolynomial.map (Int.castRingHom R) (Fin.cases
      (MvPolynomial.rename Prod.snd (WittVector.wittNSMul p n im.2)) (fun _ => MvPolynomial.X im.2)
        im.1 : MvPolynomial ℕ ℤ) : MvPolynomial ℕ R) : MvPowerSeries ℕ R) := by
  funext ⟨i, m⟩
  refine Fin.cases rfl (fun l => ?_) i
  simp [stepFam]

theorem nsmulFam_succ (n k : ℕ) :
    nsmulFam p R (n + 1) k = subst (stepFam p R n) (addFam p R k) := by
  have hfun : (fun im : Fin 2 × ℕ => MvPolynomial.rename Prod.snd
      (Fin.cases (WittVector.wittNSMul p n im.2) (fun _ => MvPolynomial.X (0, im.2)) im.1 :
        MvPolynomial (Fin 1 × ℕ) ℤ)) =
      fun im => (Fin.cases (MvPolynomial.rename Prod.snd (WittVector.wittNSMul p n im.2))
        (fun _ => MvPolynomial.X im.2) im.1 : MvPolynomial ℕ ℤ) := by
    funext ⟨i, m⟩
    refine Fin.cases rfl (fun l => ?_) i
    simp
  rw [stepFam_eq, subst_coe_addFam, nsmulFam, ← aeval_wittNSMul_wittAdd,
    MvPolynomial.comp_aeval_apply, hfun]

theorem nsmulFam_zero (k : ℕ) : nsmulFam p R 0 k = 0 := by
  rw [nsmulFam, wittNSMul_zero, map_zero, map_zero, MvPolynomial.coe_zero]

theorem nsmulFam_self [CharP R p] (k : ℕ) :
    nsmulFam p R p k = subst (frobFam p R) (verFam R k) := by
  have hcast : Int.castRingHom R = (ZMod.castHom (dvd_refl p) R).comp (Int.castRingHom (ZMod p)) :=
    RingHom.ext_int _ _
  rw [nsmulFam, hcast, ← MvPolynomial.map_map, MvPolynomial.map_rename, map_wittNSMul_self]
  cases k with
  | zero =>
    show ((MvPolynomial.map _ (MvPolynomial.rename Prod.snd (0 : MvPolynomial (Fin 1 × ℕ) (ZMod p))) :
      MvPolynomial ℕ R) : MvPowerSeries ℕ R) = subst (frobFam p R) 0
    rw [map_zero, map_zero, MvPolynomial.coe_zero, ← coe_substAlgHom hasSubst_frobFam, map_zero]
  | succ m =>
    show ((MvPolynomial.map _ (MvPolynomial.rename Prod.snd
        (MvPolynomial.X ((0 : Fin 1), m) ^ p : MvPolynomial (Fin 1 × ℕ) (ZMod p))) :
      MvPolynomial ℕ R) : MvPowerSeries ℕ R) = subst (frobFam p R) (X m)
    rw [map_pow, MvPolynomial.rename_X, map_pow, MvPolynomial.map_X, MvPolynomial.coe_pow,
      MvPolynomial.coe_X, subst_X hasSubst_frobFam]
    rfl

end WittLaw

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}

theorem subst_nsmulFam [Φ.IsComm] (f : CartierModule p Φ) (n : ℕ) (j : Fin d) :
    subst (WittLaw.nsmulFam p R n) (f.toPowerSeries j) = (n • f).toPowerSeries j := by
  induction n generalizing j with
  | zero =>
    rw [zero_nsmul]
    have h0 : WittLaw.nsmulFam p R 0 = fun _ => 0 := funext WittLaw.nsmulFam_zero
    rw [h0]
    exact subst_zero_of_constantCoeff_eq_zero (f.constantCoeff_eq_zero j)
  | succ n ih =>
    have hf := f.constantCoeff_eq_zero
    have hS := WittLaw.hasSubst_stepFam (p := p) (R := R) n
    have hfam : WittLaw.nsmulFam p R (n + 1) =
        fun k => subst (WittLaw.stepFam p R n) (WittLaw.addFam p R k) :=
      funext (WittLaw.nsmulFam_succ n)
    rw [hfam, ← subst_comp_subst_apply (hasSubst_addFam p R) hS, f.subst_addFam,
      subst_subst_elim Φ (constantCoeff_inBlk 0 hf) (constantCoeff_inBlk 1 hf) hS, succ_nsmul,
      toPowerSeries_add]
    congr 1
    funext s
    rcases s with l | l
    · show subst (WittLaw.stepFam p R n) (subst (blk 0) (f.toPowerSeries l)) =
        (n • f).toPowerSeries l
      rw [subst_comp_subst_apply (hasSubst_blk 0) hS, ← ih l]
      congr 1
      funext m
      exact subst_X hS ((0 : Fin 2), m)
    · show subst (WittLaw.stepFam p R n) (subst (blk 1) (f.toPowerSeries l)) = f.toPowerSeries l
      rw [subst_comp_subst_apply (hasSubst_blk 1) hS]
      have hX : (fun m => subst (WittLaw.stepFam p R n) (blk (R := R) 1 m)) =
          fun m => (X m : MvPowerSeries ℕ R) := by
        funext m
        exact subst_X hS ((1 : Fin 2), m)
      rw [hX]
      exact congrFun subst_self _

theorem verschiebung_frobenius [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    verschiebung (frobenius f) = (p : ℕ) • f := by
  apply CartierModule.ext
  funext j
  rw [verschiebung, frobenius, precomp_precomp, ← subst_nsmulFam]
  congr 1
  funext k
  exact (WittLaw.nsmulFam_self k).symm

theorem frobenius_verschiebung_eq_nsmul [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    frobenius (verschiebung f) = (p : ℕ) • f := by
  rw [frobenius_verschiebung, verschiebung_frobenius]

def tangent [Φ.IsComm] : CartierModule p Φ →+ (Fin d → R) where
  toFun f := fun j => coeff (Finsupp.single 0 1) (f.toPowerSeries j)
  map_zero' := by
    funext j
    simp
  map_add' f g := by
    funext j
    show coeff (Finsupp.single 0 1) (subst (Sum.elim f.toPowerSeries g.toPowerSeries)
      (Φ.toPowerSeries j)) = _
    have h0 : ∀ s, ((Sum.elim f.toPowerSeries g.toPowerSeries) s).constantCoeff = 0 := by
      rintro (l | l)
      exacts [f.constantCoeff_eq_zero l, g.constantCoeff_eq_zero l]
    rw [coeff_single_subst h0, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Φ.coeff_single_inl, Φ.coeff_single_inr, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl

@[simp] theorem tangent_apply [Φ.IsComm] (f : CartierModule p Φ) (j : Fin d) :
    tangent f j = coeff (Finsupp.single 0 1) (f.toPowerSeries j) := rfl

theorem tangent_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) :
    tangent (verschiebung f) = 0 := by
  funext j
  rw [tangent_apply, toPowerSeries_verschiebung_eq_expand]
  exact MvPowerSeries.coeff_expand_of_not_dvd p hp.out.ne_zero _ (i := 0)
    (by simpa using hp.out.one_lt.ne')

theorem tangent_map [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (f : CartierModule p Φ) :
    tangent (map φ f) = (MvFormalGroup.linearPart φ.toPowerSeries).mulVec (tangent f) := by
  funext i
  show coeff (Finsupp.single 0 1) (subst f.toPowerSeries (φ.toPowerSeries i)) = _
  rw [coeff_single_subst f.constantCoeff_eq_zero, Matrix.mulVec]
  rfl

def curveFam (R : Type u) [CommRing R] : ℕ → PowerSeries R
  | 0 => PowerSeries.X
  | _ + 1 => 0

omit hp in
theorem constantCoeff_curveFam (n : ℕ) : MvPowerSeries.constantCoeff (curveFam R n) = 0 := by
  cases n with
  | zero => exact MvPowerSeries.constantCoeff_X _
  | succ n => exact map_zero _

omit hp in
theorem hasSubst_curveFam : HasSubst (curveFam R) := by
  refine ⟨fun n => by rw [constantCoeff_curveFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_singleton 0).subset fun n hn => ?_
  cases n with
  | zero => rfl
  | succ n => exact absurd (by simp [curveFam]) hn

def curve (f : CartierModule p Φ) : Fin d → PowerSeries R :=
  fun j => subst (curveFam R) (f.toPowerSeries j)

theorem curve_apply (f : CartierModule p Φ) (j : Fin d) :
    curve f j = subst (curveFam R) (f.toPowerSeries j) := rfl

theorem constantCoeff_curve (f : CartierModule p Φ) (j : Fin d) :
    PowerSeries.constantCoeff (curve f j) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_curveFam constantCoeff_curveFam (f.constantCoeff_eq_zero j)

theorem curve_add [Φ.IsComm] (f g : CartierModule p Φ) (j : Fin d) :
    curve (f + g) j = subst (Sum.elim (curve f) (curve g)) (Φ.toPowerSeries j) :=
  subst_subst_elim Φ f.constantCoeff_eq_zero g.constantCoeff_eq_zero hasSubst_curveFam j

theorem curve_verschiebung [Φ.IsComm] [CharP R p] (f : CartierModule p Φ) (j : Fin d) :
    curve (verschiebung f) j = PowerSeries.expand p hp.out.ne_zero (curve f j) := by
  show subst (curveFam R) (subst (WittLaw.frobFam p R) (f.toPowerSeries j)) =
    MvPowerSeries.expand p hp.out.ne_zero (subst (curveFam R) (f.toPowerSeries j))
  rw [MvPowerSeries.expand, substAlgHom_apply,
    subst_comp_subst_apply WittLaw.hasSubst_frobFam hasSubst_curveFam,
    subst_comp_subst_apply hasSubst_curveFam (HasSubst.X_pow hp.out.ne_zero)]
  congr 1
  funext n
  cases n with
  | zero =>
    show subst (curveFam R) (X 0 ^ p : MvPowerSeries ℕ R) =
      subst (fun s : Unit => (X s : MvPowerSeries Unit R) ^ p) PowerSeries.X
    rw [subst_pow hasSubst_curveFam, subst_X hasSubst_curveFam, PowerSeries.X,
      subst_X (HasSubst.X_pow hp.out.ne_zero)]
    rfl
  | succ m =>
    show subst (curveFam R) (X (m + 1) ^ p : MvPowerSeries ℕ R) =
      subst (fun s : Unit => (X s : MvPowerSeries Unit R) ^ p) (0 : PowerSeries R)
    rw [subst_pow hasSubst_curveFam, subst_X hasSubst_curveFam,
      ← coe_substAlgHom (HasSubst.X_pow hp.out.ne_zero), map_zero]
    exact zero_pow hp.out.ne_zero

theorem coeff_one_curve [Φ.IsComm] (f : CartierModule p Φ) (j : Fin d) :
    PowerSeries.coeff 1 (curve f j) = tangent f j := by
  classical
  rw [tangent_apply, curve_apply]
  show MvPowerSeries.coeff (Finsupp.single () 1) (subst (curveFam R) (f.toPowerSeries j)) = _
  rw [coeff_subst hasSubst_curveFam]

  have hterm : ∀ e : ℕ →₀ ℕ, e ≠ Finsupp.single 0 1 →
      coeff e (f.toPowerSeries j) •
        coeff (Finsupp.single () 1) (e.prod fun n k => curveFam R n ^ k) = 0 := by
    intro e he
    by_cases hsupp : ∃ n ∈ e.support, n ≠ 0
    · obtain ⟨n, hn, hn0⟩ := hsupp
      have hzero : (e.prod fun n k => curveFam R n ^ k) = 0 := by
        rw [Finsupp.prod]
        refine Finset.prod_eq_zero hn ?_
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        show (0 : PowerSeries R) ^ e (m + 1) = 0
        exact zero_pow (Finsupp.mem_support_iff.mp hn)
      rw [hzero, map_zero, smul_zero]
    · push Not at hsupp
      have he0 : e = Finsupp.single 0 (e 0) := by
        ext n
        by_cases hn : n = 0
        · subst hn; simp
        · rw [Finsupp.single_apply, if_neg (Ne.symm hn)]
          by_contra hne
          exact hn (hsupp n (Finsupp.mem_support_iff.mpr hne))
      have hk : e 0 ≠ 1 := fun h1 => he (by rw [he0, h1])
      rw [he0, Finsupp.prod_single_index (by simp)]
      show coeff _ (f.toPowerSeries j) • coeff (Finsupp.single () 1)
        ((PowerSeries.X : PowerSeries R) ^ e 0) = 0
      rw [PowerSeries.X, coeff_X_pow, if_neg, smul_zero]
      intro h
      exact hk ((Finsupp.single_injective ()) h).symm
  rw [finsum_eq_single _ (Finsupp.single 0 1) hterm, Finsupp.prod_single_index (by simp)]
  show coeff _ (f.toPowerSeries j) • coeff (Finsupp.single () 1)
    ((PowerSeries.X : PowerSeries R) ^ 1) = _
  rw [pow_one, PowerSeries.X, coeff_X, if_pos rfl, smul_eq_mul, mul_one]

namespace Examples

def addLinear (p : ℕ) [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R] (v : Fin d → R) :
    CartierModule p (addMv d R) where
  toPowerSeries := fun i => v i • (X 0 : MvPowerSeries ℕ R)
  constantCoeff_eq_zero := fun i => by simp
  subst_eq := by
    intro i
    have hc : ∀ l, ((fun l => v l • (X 0 : MvPowerSeries ℕ R)) l).constantCoeff = 0 :=
      fun l => by simp
    have h0 : ∀ s, ((Sum.elim (inBlk 0 fun l => v l • (X 0 : MvPowerSeries ℕ R))
        (inBlk 1 fun l => v l • (X 0 : MvPowerSeries ℕ R))) s).constantCoeff = 0 := by
      rintro (l | l)
      exacts [constantCoeff_inBlk 0 hc l, constantCoeff_inBlk 1 hc l]
    show subst (WittLaw.addFam p R) (v i • (X 0 : MvPowerSeries ℕ R)) =
      subst (Sum.elim (inBlk 0 fun l => v l • (X 0 : MvPowerSeries ℕ R))
        (inBlk 1 fun l => v l • (X 0 : MvPowerSeries ℕ R)))
        ((X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R) + X (Sum.inr i))
    rw [subst_X_add_X h0]
    simp only [Sum.elim_inl, Sum.elim_inr, inBlk_apply]
    rw [← coe_substAlgHom (hasSubst_addFam p R), ← coe_substAlgHom (hasSubst_blk 0),
      ← coe_substAlgHom (hasSubst_blk 1), AlgHom.map_smul_of_tower, AlgHom.map_smul_of_tower,
      AlgHom.map_smul_of_tower, coe_substAlgHom, coe_substAlgHom, coe_substAlgHom,
      subst_X (hasSubst_addFam p R), subst_X (hasSubst_blk 0), subst_X (hasSubst_blk 1),
      WittLaw.addFam, WittVector.wittAdd_zero, ← smul_add]
    congr 1
    simp [WittLaw.blk]

@[simp] theorem toPowerSeries_addLinear (v : Fin d → R) (i : Fin d) :
    (addLinear p v).toPowerSeries i = v i • (X 0 : MvPowerSeries ℕ R) := rfl

theorem tangent_addLinear (v : Fin d → R) : tangent (addLinear p v) = v := by
  classical
  funext i
  rw [tangent_apply, toPowerSeries_addLinear, map_smul, coeff_X, if_pos rfl, smul_eq_mul, mul_one]

theorem tangent_surjective_addMv :
    Function.Surjective (tangent : CartierModule p (addMv d R) → Fin d → R) :=
  fun v => ⟨addLinear p v, tangent_addLinear v⟩

theorem addLinear_ne_zero [Nontrivial R] {v : Fin d → R} (hv : v ≠ 0) : addLinear p v ≠ 0 := by
  intro h
  apply hv
  have := tangent_addLinear (p := p) v
  rw [h, map_zero] at this
  exact this.symm

end Examples

end CartierModule

end MvFormalGroup

end


