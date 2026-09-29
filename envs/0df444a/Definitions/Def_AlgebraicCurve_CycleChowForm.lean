-- Prove2me | Definitions.Def_AlgebraicCurve_CycleChowForm
-- name    : AlgebraicCurve_CycleChowForm
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/35f06e82-07dc-50e8-8f2c-6d38836a703a
-- title:
--   Chow forms of cycles, Chow sides and Chow reciprocity
-- statement:
--   Throughout, $F$ is a field equipped with an algebra structure over $\overline{\mathbb Q}$, $r$ is a natural number, $s : \mathrm{Fin}\,r \to F$ is a family of elements of $F$, and divisors are finitely supported $\mathbb Z$-valued functions on the places of $F/\overline{\mathbb Q}$. Each place $w$ carries the pivot-normalised coordinate vector `evalVec s w`, whose $i$-th entry is the value at $w$ of $s_i\,s_{p(w)}^{-1}$ with $p(w)$ an index of least order, and the scalar `secVal s w k u`, the value at $w$ of $u\,s_{p(w)}^{-k}$. Four constructions are made. `linSec s a` $= \sum_i a_i s_i$ is the section of a covector $a \in \overline{\mathbb Q}^r$. `chowForm s Z` is the product over the support of $Z$ of $\bigl(\sum_i \mathrm{evalVec}\,s\,w\,i \cdot X_i\bigr)^{\max(Z_w,0)}$ in $\overline{\mathbb Q}[X_1,\dots,X_r]$ (negative multiplicities are clipped to $0$ by `Int.toNat`), a form whose zero locus consists of the covectors cutting hyperplanes through the points of $Z$. `secProd s k u Z` is the corresponding product $\prod_w (\mathrm{secVal}\,s\,w\,k\,u)^{\max(Z_w,0)}$. Given $\nu : \overline{\mathbb Q}\to\mathbb R$ and a place $v$, `chowLogAt` is the logarithm of the supremum, over the nonzero covectors $a$ with $\sum_i \mathrm{evalVec}\,s\,v\,i\cdot a_i = 0$, of $\nu(F_Z(a))$ divided by $(\sup_i \nu(a_i))^{\sum_w \max(Z_w,0)}$, and `chowSide` subtracts this from $\sum_w Z_w \log \sup_i \nu(\mathrm{evalVec}\,s\,w\,i)$.
--
--   `ChowReciprocity s E k u B` is a predicate on the data $(s,E,k,u,B)$: for all covectors $a,b,c$ with $\mathrm{linSec}$ nonzero and all divisors $Z_a,Z_b,Z_c$ given pointwise by $\operatorname{ord}_w(\mathrm{linSec})+E_w$, such that at every place either $Z_a=Z_b=0$ or $B=Z_c=0$, the identity $F_B(a)F_{Z_c}(b)^kF_{Z_a}(c)^k\,u\langle Z_b\rangle = F_B(b)F_{Z_c}(a)^kF_{Z_b}(c)^k\,u\langle Z_a\rangle$ holds. Accompanying lemmas evaluate `chowForm` and `secProd` on $0$ and on single-place divisors, give the evaluation formula $F_Z(a) = \prod_w (\sum_i \mathrm{evalVec}\,s\,w\,i\cdot a_i)^{\max(Z_w,0)}$, show `chowForm` homogeneous of degree $\sum_w \max(Z_w,0)$ and, when every place in the support has some coordinate equal to $1$ (which holds at pivot indices with $s_{p(w)}\neq 0$), nonzero of exactly that total degree. Two archimedean estimates bound $\|\sigma(\sum_i x_i a_i)\|$ by $r\,(\sup_i\|\sigma(a_i)\|)(\sup_i\|\sigma(x_i)\|)$ for a ring homomorphism $\sigma : \overline{\mathbb Q}\to\mathbb C$, and correspondingly $\|\sigma(F_Z(a))\|$ by the product of these bounds over the support. For $r = 0$ the reciprocity predicate holds vacuously, since every section vanishes.
--
--   **Relation to Mathlib.** Places, divisors and the evaluation maps `evalVec`, `secVal` are the project's own; Mathlib has no Chow forms of cycles on a curve. Homogeneity and total degree are expressed through Mathlib's `MvPolynomial.IsHomogeneous`.
--
--   **Where it is used.** These forms supply the geometric input to the height machinery on divisors of the modular function field: the Chow side at a place compares the naive coordinate height of a cycle with the chordal proximity data used in the height form on $J_0(N)$, and `ChowReciprocity` packages the Weil reciprocity identity, read in the pivot trivialisation, for the two functions $u_a/u_b$ and $u/u_c^{\,k}$ whose divisors $Z_a - Z_b$ and $B - kZ_c$ have disjoint supports.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_CycleChowForm.lean

import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

def linSec {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (a : Fin r → AlgebraicClosure ℚ) : F :=
  ∑ i, a i • s i

def chowForm {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (Z : Divisor (AlgebraicClosure ℚ) F) : MvPolynomial (Fin r) (AlgebraicClosure ℚ) :=
  Z.prod fun w n => (∑ i, MvPolynomial.C (evalVec s w i) * MvPolynomial.X i) ^ n.toNat

def secProd {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F) (k : ℕ)
    (u : F) (Z : Divisor (AlgebraicClosure ℚ) F) : AlgebraicClosure ℚ :=
  Z.prod fun w n => secVal s w k u ^ n.toNat

def chowLogAt {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (ν : AlgebraicClosure ℚ → ℝ)
    (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F) (v : Place (AlgebraicClosure ℚ) F) : ℝ :=
  Real.log (⨆ a : {a : Fin r → AlgebraicClosure ℚ // ∑ i, evalVec s v i * a i = 0 ∧ a ≠ 0},
    ν (MvPolynomial.eval a.1 (chowForm s Z)) / (⨆ i, ν (a.1 i)) ^ (Z.sum fun _ n => n.toNat))

def chowSide {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (ν : AlgebraicClosure ℚ → ℝ)
    (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F) (v : Place (AlgebraicClosure ℚ) F) : ℝ :=
  (Z.sum fun w n => (n : ℝ) * Real.log (⨆ i, ν (evalVec s w i))) - chowLogAt ν s Z v

def ChowReciprocity {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (E : Divisor (AlgebraicClosure ℚ) F) (k : ℕ) (u : F) (B : Divisor (AlgebraicClosure ℚ) F) : Prop :=
  ∀ (a b c : Fin r → AlgebraicClosure ℚ) (Za Zb Zc : Divisor (AlgebraicClosure ℚ) F),
    linSec s a ≠ 0 → linSec s b ≠ 0 → linSec s c ≠ 0 →
    (∀ w, Za w = w.ord (linSec s a) + E w) → (∀ w, Zb w = w.ord (linSec s b) + E w) →
    (∀ w, Zc w = w.ord (linSec s c) + E w) →
    (∀ w, (Za w = 0 ∧ Zb w = 0) ∨ (B w = 0 ∧ Zc w = 0)) →
    MvPolynomial.eval a (chowForm s B) * MvPolynomial.eval b (chowForm s Zc) ^ k
        * MvPolynomial.eval c (chowForm s Za) ^ k * secProd s k u Zb
      = MvPolynomial.eval b (chowForm s B) * MvPolynomial.eval a (chowForm s Zc) ^ k
        * MvPolynomial.eval c (chowForm s Zb) ^ k * secProd s k u Za

@[simp]
theorem chowForm_zero {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) : chowForm s 0 = 1 :=
  Finsupp.prod_zero_index

theorem chowForm_single {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (w : Place (AlgebraicClosure ℚ) F) (n : ℤ) :
    chowForm s (Finsupp.single w n)
      = (∑ i, MvPolynomial.C (evalVec s w i) * MvPolynomial.X i) ^ n.toNat :=
  Finsupp.prod_single_index (by simp)

theorem eval_chowForm {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F)
    (a : Fin r → AlgebraicClosure ℚ) :
    MvPolynomial.eval a (chowForm s Z) = Z.prod fun w n => (∑ i, evalVec s w i * a i) ^ n.toNat := by
  simp only [chowForm, map_finsuppProd, map_pow, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]

@[simp]
theorem secProd_zero {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (k : ℕ) (u : F) : secProd s k u 0 = 1 :=
  Finsupp.prod_zero_index

theorem secProd_single {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (k : ℕ) (u : F) (w : Place (AlgebraicClosure ℚ) F) (n : ℤ) :
    secProd s k u (Finsupp.single w n) = secVal s w k u ^ n.toNat :=
  Finsupp.prod_single_index (by simp)

theorem chowForm_isHomogeneous {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F) :
    (chowForm s Z).IsHomogeneous (Z.sum fun _ n => n.toNat) := by
  refine MvPolynomial.IsHomogeneous.prod Z.support _ (fun w => (Z w).toNat) fun w _ => ?_
  have h1 : (∑ i, MvPolynomial.C (evalVec s w i) * MvPolynomial.X i :
      MvPolynomial (Fin r) (AlgebraicClosure ℚ)).IsHomogeneous 1 :=
    MvPolynomial.IsHomogeneous.sum Finset.univ _ 1 fun i _ =>
      (MvPolynomial.isHomogeneous_X (AlgebraicClosure ℚ) i).C_mul (evalVec s w i)
  simpa only [one_mul] using h1.pow (Z w).toNat

theorem evalVec_pivotIndex {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (w : Place (AlgebraicClosure ℚ) F) (hr : 0 < r)
    (h : s (pivotIndex s w hr) ≠ 0) : evalVec s w (pivotIndex s w hr) = 1 := by
  simp only [evalVec, dif_pos hr, mul_inv_cancel₀ h, Place.evalAt_one]

theorem linearForm_ne_zero {r : ℕ} {x : Fin r → AlgebraicClosure ℚ} {p : Fin r} (hp : x p = 1) :
    (∑ i, MvPolynomial.C (x i) * MvPolynomial.X i : MvPolynomial (Fin r) (AlgebraicClosure ℚ)) ≠ 0 := by
  intro h0
  have h1 := congrArg (MvPolynomial.eval (Pi.single p (1 : AlgebraicClosure ℚ))) h0
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, map_zero, Pi.single_apply,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hp] at h1
  exact one_ne_zero h1

theorem chowForm_ne_zero {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F)
    (h : ∀ w ∈ Z.support, ∃ p, evalVec s w p = 1) : chowForm s Z ≠ 0 := by
  rw [chowForm, Finsupp.prod, Finset.prod_ne_zero_iff]
  intro w hw
  obtain ⟨p, hp⟩ := h w hw
  exact pow_ne_zero _ (linearForm_ne_zero hp)

theorem totalDegree_chowForm {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F)
    (h : ∀ w ∈ Z.support, ∃ p, evalVec s w p = 1) :
    (chowForm s Z).totalDegree = Z.sum fun _ n => n.toNat :=
  (chowForm_isHomogeneous s Z).totalDegree (chowForm_ne_zero s Z h)

theorem norm_linearForm_apply_le {r : ℕ} (σ : AlgebraicClosure ℚ →+* ℂ)
    (x a : Fin r → AlgebraicClosure ℚ) :
    ‖σ (∑ i, x i * a i)‖ ≤ r * ((⨆ i, ‖σ (a i)‖) * ⨆ i, ‖σ (x i)‖) := by
  rw [map_sum]
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ i ∈ (Finset.univ : Finset (Fin r)),
      ‖σ (x i * a i)‖ ≤ (⨆ i, ‖σ (a i)‖) * ⨆ i, ‖σ (x i)‖ := fun i _ => by
    rw [map_mul, norm_mul, mul_comm]
    exact mul_le_mul (le_ciSup (f := fun i => ‖σ (a i)‖) (Finite.bddAbove_range _) i)
      (le_ciSup (f := fun i => ‖σ (x i)‖) (Finite.bddAbove_range _) i)
      (norm_nonneg _) (Real.iSup_nonneg fun _ => norm_nonneg _)
  refine (Finset.sum_le_card_nsmul _ _ _ h).trans ?_
  rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem norm_eval_chowForm_le {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (σ : AlgebraicClosure ℚ →+* ℂ) (s : Fin r → F) (Z : Divisor (AlgebraicClosure ℚ) F)
    (a : Fin r → AlgebraicClosure ℚ) :
    ‖σ (MvPolynomial.eval a (chowForm s Z))‖
      ≤ Z.prod fun w n => (r * ((⨆ i, ‖σ (a i)‖) * ⨆ i, ‖σ (evalVec s w i)‖)) ^ n.toNat := by
  rw [eval_chowForm, map_finsuppProd, Finsupp.prod, norm_prod, Finsupp.prod]
  refine Finset.prod_le_prod (fun w _ => norm_nonneg _) fun w _ => ?_
  rw [map_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_linearForm_apply_le σ (evalVec s w) a) _

example {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] (s : Fin 0 → F)
    (E B : Divisor (AlgebraicClosure ℚ) F) (k : ℕ) (u : F) : ChowReciprocity s E k u B :=
  fun a _ _ _ _ _ ha => (ha (by simp [linSec])).elim

example {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F)
    (a : Fin r → AlgebraicClosure ℚ) : MvPolynomial.eval a (chowForm s 0) = 1 := by
  simp

end AlgebraicCurve

end


