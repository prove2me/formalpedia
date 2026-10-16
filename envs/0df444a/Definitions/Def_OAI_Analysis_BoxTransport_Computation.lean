-- Prove2me | Definitions.Def_OAI_Analysis_BoxTransport_Computation
-- name    : OAI_Analysis_BoxTransport_Computation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T13:08:14.635114+00:00
-- url     : https://prove2.me/theorems/d83e23d5-cdfc-4e6c-96c7-47a73d9642e6
-- title:
--   Exact rational arithmetic on natural-number codes and computable approximation of $e^x$ and $x^{-m}e^{-1/x}$
-- statement:
--   This file develops exact rational arithmetic on codes made of natural numbers, shows that the operations are primitive recursive, and uses them to approximate the exponential function and the flat functions $x^{-m}e^{-1/x}$ by computable rational procedures. Primitive recursive and computable refer to the standard notions for functions between countable data types (natural numbers, tuples, lists) under their standard encodings.
--
--   1. **Rational codes.** A code is a triple $q=(p,s,d)\in\mathbb{N}^3$; it denotes the rational number
--   $$[q]=\frac{p-s}{d+1}\in\mathbb{Q}.$$
--   Every rational number has a code.
--
--   2. **Exact code arithmetic.** For codes $q=(p,s,d)$ and $q'=(p',s',d')$ define $\underline0=(0,0,0)$, $\underline1=(1,0,0)$, $\underline N=(N,0,0)$ for $N\in\mathbb{N}$, $-q=(s,p,d)$,
--   $$q\oplus q'=\bigl(p(d'+1)+p'(d+1),\ s(d'+1)+s'(d+1),\ (d+1)(d'+1)-1\bigr),\qquad q\otimes q'=\bigl(pp'+ss',\ ps'+sp',\ (d+1)(d'+1)-1\bigr),$$
--   the reciprocal $q^{-1}=(d+1,0,p-s-1)$ if $p>s$, $q^{-1}=(0,d+1,s-p-1)$ if $p<s$, and $q^{-1}=\underline0$ if $p=s$; subtraction $q\oplus(-q')$, division $q\otimes(q')^{-1}$, powers $q^{\otimes N}$ (the $N$-fold product starting from $\underline1$), the comparison $q\preceq q'$ meaning $p(d'+1)+s'(d+1)\le p'(d+1)+s(d'+1)$, and the absolute value $|q|$, equal to $q$ if $\underline0\preceq q$ and to $-q$ otherwise. These operations are exact: $[q\oplus q']=[q]+[q']$, $[q\otimes q']=[q]\,[q']$, $[-q]=-[q]$, $[q^{-1}]=[q]^{-1}$ (with $0^{-1}=0$), and likewise for $\underline N$, subtraction, division, powers and absolute value, while $q\preceq q'$ holds if and only if $[q]\le[q']$. The maps $N\mapsto\underline N$, negation, addition, multiplication, reciprocal, division, powers, the comparison relation, the absolute value and the factorial $N\mapsto N!$ are primitive recursive.
--
--   3. **Taylor sums and the exponential.** $T(q,K)$ is the code obtained by adding up $q^{\otimes i}$ divided by $\underline{i!}$ for $i<K$, so that $[T(q,K)]=\sum_{i<K}[q]^i/i!$; it is primitive recursive in $(q,K)$. For a code $q$ and a precision $N\in\mathbb{N}$, call $K\in\mathbb{N}$ a stopping index if
--   $$\frac{|[q]|}{K+1}\le\frac12\qquad\text{and}\qquad\frac{2\,|[q]|^K}{K!}\le\frac{1}{N+1}.$$
--   This condition is decided by a primitive recursive procedure on codes, and a stopping index always exists. The approximate exponential is $\operatorname{Exp}(q,N)=T(q,K^\ast)$, where $K^\ast$ is the least stopping index; it is a computable function of $(q,N)$. Comparison of the tail with a geometric series of ratio $\frac12$ shows that the two conditions force $\bigl|e^{[q]}-[\operatorname{Exp}(q,N)]\bigr|\le 1/(N+1)$.
--
--   4. **Flat functions.** Let $\psi(x)=e^{-1/x}$ for $x>0$ and $\psi(x)=0$ for $x\le0$, and for $m\in\mathbb{N}$ let $f_m(x)=x^{-m}\psi(x)$, so that $f_m(x)=x^{-m}e^{-1/x}$ for $x>0$ and $f_m(x)=0$ for $x\le0$. Then $f_0=\psi$, every $f_m$ is $C^\infty$ on $\mathbb{R}$, and
--   $$f_m'(x)=f_{m+2}(x)-m\,f_{m+1}(x)\qquad\text{for all }x\in\mathbb{R}.$$
--   The number $L_m=(m+2)!+m\,(m+1)!$ is a Lipschitz constant for $f_m$.
--
--   5. **Approximating flat functions.** For a code $q=(p,s,d)$ let $\|q\|=p+s\in\mathbb{N}$, a natural-number upper bound for $|[q]|$; this map is primitive recursive. For $m,N\in\mathbb{N}$ and a code $q$ define $\operatorname{Flat}(m,q,N)=\underline0$ if $[q]\le0$, and otherwise
--   $$\operatorname{Flat}(m,q,N)=w\otimes\operatorname{Exp}\bigl(-q^{-1},\ (N+1)(\|w\|+1)\bigr),\qquad w=(q^{-1})^{\otimes m}.$$
--   This is a computable function of $(m,q,N)$, and its value approximates $f_m([q])$ to within $1/(N+1)$.
--
--   These are the exact-arithmetic primitives behind the effectivity of the constructed vector field: its smooth cutoffs are built from $\psi$, and by the derivative formula all derivatives of $\psi$ are combinations of the flat functions $f_m$, so certified rational approximations of $f_m$ at rational points, together with exact arithmetic, let derivatives of the field be approximated by a computable procedure.
--
--   **Formalization Note** Codes are `QCode = ℕ × ℕ × ℕ` with value `Qval`, the same encoding as the mission's `RationalCode` and `rationalValue`. In $(d+1)(d'+1)-1$ the subtraction is truncated natural-number subtraction, harmless because the product is at least $1$ (`denominator_product`). Primitive recursive and computable mean Mathlib's `Primrec`, `Primrec₂`, `PrimrecRel` and `Computable`; `pr_plus`, `pr_times` and `computable_ite` are closure helpers. `qExp` is a `noncomputable def` in Lean because it uses `Nat.find`, but `computable_qExp` proves that it is a computable function in the sense of computability theory. The flat functions are `flatTerm m x = x⁻¹ ^ m * expNegInvGlue x` (Lean's $0^{-1}=0$ gives $f_m(0)=0$), $L_m$ is `flatLipschitzBound m`, $\|q\|$ is `qBound`, and $\operatorname{Flat}$ is `qFlat`. The Lipschitz property of $L_m$ and the accuracy bounds for `qExp` and `qFlat` are proved as separate results.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Computation.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Computation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BalancedBoxRouting mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Computable rational arithmetic and exponential/flat-function approximation. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff

namespace BoxTransport.Routing.Computation

abbrev QCode := ℕ × ℕ × ℕ

def Qval (q : QCode) : ℚ := ((q.1 : ℚ) - q.2.1) / (q.2.2 + 1)

def qZero : QCode := (0, 0, 0)
def qOne : QCode := (1, 0, 0)
def qNat (n : ℕ) : QCode := (n, 0, 0)
def qNeg (q : QCode) : QCode := (q.2.1, q.1, q.2.2)
def qAdd (q r : QCode) : QCode :=
  (q.1 * (r.2.2 + 1) + r.1 * (q.2.2 + 1),
   q.2.1 * (r.2.2 + 1) + r.2.1 * (q.2.2 + 1),
   (q.2.2 + 1) * (r.2.2 + 1) - 1)
def qMul (q r : QCode) : QCode :=
  (q.1 * r.1 + q.2.1 * r.2.1, q.1 * r.2.1 + q.2.1 * r.1,
   (q.2.2 + 1) * (r.2.2 + 1) - 1)
def qInv (q : QCode) : QCode :=
  if q.2.1 < q.1 then (q.2.2 + 1, 0, q.1 - q.2.1 - 1)
  else if q.1 < q.2.1 then (0, q.2.2 + 1, q.2.1 - q.1 - 1)
  else qZero

def qSub (q r : QCode) : QCode := qAdd q (qNeg r)
def qDiv (q r : QCode) : QCode := qMul q (qInv r)
def qPow (q : QCode) (n : ℕ) : QCode := (qMul q)^[n] qOne

def qLe (q r : QCode) : Prop :=
  q.1 * (r.2.2 + 1) + r.2.1 * (q.2.2 + 1) ≤
    r.1 * (q.2.2 + 1) + q.2.1 * (r.2.2 + 1)
instance : DecidableRel qLe := fun _ _ => Nat.decLe _ _

@[simp] theorem Qval_zero : Qval qZero = 0 := by norm_num [Qval, qZero]
@[simp] theorem Qval_one : Qval qOne = 1 := by norm_num [Qval, qOne]
@[simp] theorem Qval_nat (n : ℕ) : Qval (qNat n) = n := by simp [Qval, qNat]
@[simp] theorem Qval_neg (q : QCode) : Qval (qNeg q) = -Qval q := by
  dsimp [Qval, qNeg]
  ring

theorem denominator_product (d e : ℕ) :
    (((d + 1) * (e + 1) - 1 : ℕ) : ℚ) + 1 = (d + 1) * (e + 1) := by
  have h : 1 ≤ (d + 1) * (e + 1) := by nlinarith
  rw [Nat.cast_sub h]
  push_cast
  ring

@[simp] theorem Qval_add (q r : QCode) : Qval (qAdd q r) = Qval q + Qval r := by
  simp only [Qval, qAdd, Nat.cast_add, Nat.cast_mul, Nat.cast_one, denominator_product]
  field_simp
  ring

@[simp] theorem Qval_mul (q r : QCode) : Qval (qMul q r) = Qval q * Qval r := by
  simp only [Qval, qMul, Nat.cast_add, Nat.cast_mul, denominator_product]
  rw [div_mul_div_comm]
  congr 1
  ring

@[simp] theorem Qval_inv (q : QCode) : Qval (qInv q) = (Qval q)⁻¹ := by
  unfold qInv
  split_ifs with h h'
  · have hd : 1 ≤ q.1 - q.2.1 := by omega
    have he : ((((q.1 - q.2.1) - 1 : ℕ) : ℚ) + 1) = (q.1 : ℚ) - q.2.1 := by
      rw [Nat.cast_sub hd, Nat.cast_sub (by omega : q.2.1 ≤ q.1)]
      norm_num
    simp only [Qval, Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero, he, inv_div]
  · have hd : 1 ≤ q.2.1 - q.1 := by omega
    have he : ((((q.2.1 - q.1) - 1 : ℕ) : ℚ) + 1) = (q.2.1 : ℚ) - q.1 := by
      rw [Nat.cast_sub hd, Nat.cast_sub (by omega : q.1 ≤ q.2.1)]
      norm_num
    simp only [Qval, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_sub, he, inv_div]
    rw [← neg_sub (q.1 : ℚ) q.2.1, div_neg, neg_div, neg_neg]
  · have he : q.1 = q.2.1 := by omega
    simp [Qval, qZero, he]

@[simp] theorem Qval_sub (q r : QCode) : Qval (qSub q r) = Qval q - Qval r := by
  simp [qSub, sub_eq_add_neg]
@[simp] theorem Qval_div (q r : QCode) : Qval (qDiv q r) = Qval q / Qval r := by
  simp [qDiv, div_eq_mul_inv]
@[simp] theorem Qval_pow (q : QCode) (n : ℕ) : Qval (qPow q n) = Qval q ^ n := by
  induction n with
  | zero => simp [qPow]
  | succ n ih =>
    simp only [qPow, Function.iterate_succ_apply', Qval_mul]
    rw [← qPow, ih, pow_succ']

theorem qLe_iff (q r : QCode) : qLe q r ↔ Qval q ≤ Qval r := by
  rw [Qval, Qval, div_le_div_iff₀ (by positivity) (by positivity)]
  rw [qLe]
  have :
      q.1 * (r.2.2 + 1) + r.2.1 * (q.2.2 + 1) ≤
        r.1 * (q.2.2 + 1) + q.2.1 * (r.2.2 + 1) ↔
      (q.1 : ℚ) * (r.2.2 + 1) + r.2.1 * (q.2.2 + 1) ≤
        r.1 * (q.2.2 + 1) + q.2.1 * (r.2.2 + 1) := by norm_cast
  rw [this]
  constructor <;> intro h <;> nlinarith

theorem Qval_surjective : Function.Surjective Qval := by
  intro q
  let p := q.num.toNat
  let n := (-q.num).toNat
  have hpn : q.num = (p : ℤ) - n := (Int.toNat_sub_toNat_neg q.num).symm
  refine ⟨(p, n, q.den - 1), ?_⟩
  have hd : 1 ≤ q.den := q.pos
  have he : ((q.den - 1 : ℕ) : ℚ) + 1 = q.den := by
    rw [Nat.cast_sub hd]
    norm_num
  rw [Qval, he, ← Int.cast_natCast p, ← Int.cast_natCast n, ← Int.cast_sub, ← hpn]
  exact Rat.num_div_den q

 theorem pr_plus {α} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a + g a :=
  Primrec.nat_add.comp hf hg
 theorem pr_times {α} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f a * g a :=
  Primrec.nat_mul.comp hf hg

 theorem primrec_qNat : Primrec qNat := (Primrec.id.pair ((Primrec.const 0).pair (.const 0)))
 theorem primrec_qNeg : Primrec qNeg :=
  (Primrec.fst.comp Primrec.snd).pair (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))
 theorem primrec_qAdd : Primrec₂ qAdd := by
  unfold qAdd
  apply Primrec.pair
  · exact pr_plus
      (pr_times (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (pr_times (Primrec.fst.comp Primrec.snd)
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  apply Primrec.pair
  · exact pr_plus
      (pr_times (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (pr_times (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  exact Primrec.nat_sub.comp
    (pr_times (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))) (Primrec.const 1)

 theorem primrec_qMul : Primrec₂ qMul := by
  unfold qMul
  apply Primrec.pair
  · exact pr_plus (pr_times (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (pr_times (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  apply Primrec.pair
  · exact pr_plus
      (pr_times (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (pr_times (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
  exact Primrec.nat_sub.comp
    (pr_times (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))) (Primrec.const 1)

 theorem primrec_qInv : Primrec qInv := by
  unfold qInv
  apply Primrec.ite (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
  · apply Primrec.pair
    · exact Primrec.succ.comp (Primrec.snd.comp Primrec.snd)
    apply Primrec.pair (Primrec.const 0)
    exact Primrec.nat_sub.comp
      (Primrec.nat_sub.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.const 1)
  apply Primrec.ite (Primrec.nat_lt.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
  · apply Primrec.pair (Primrec.const 0)
    apply Primrec.pair (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
    exact Primrec.nat_sub.comp
      (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.snd) Primrec.fst) (Primrec.const 1)
  exact Primrec.const qZero

 theorem primrec_qDiv : Primrec₂ qDiv :=
  primrec_qMul.comp Primrec.fst (primrec_qInv.comp Primrec.snd)
 theorem primrec_qPow : Primrec₂ qPow := by
  exact Primrec.nat_iterate Primrec.snd (Primrec.const qOne)
    (primrec_qMul.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

 theorem primrec_qLe : PrimrecRel qLe := by
  exact Primrec.nat_le.comp
    (pr_plus
      (pr_times (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (pr_times (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))
    (pr_plus
      (pr_times (Primrec.fst.comp Primrec.snd)
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (pr_times (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

def qAbs (q : QCode) : QCode := if qLe qZero q then q else qNeg q

@[simp] theorem Qval_abs (q : QCode) : Qval (qAbs q) = |Qval q| := by
  unfold qAbs
  split_ifs with h
  · rw [abs_of_nonneg (by simpa only [qLe_iff, Qval_zero] using h)]
  · rw [Qval_neg, abs_of_neg (lt_of_not_ge (by simpa only [qLe_iff, Qval_zero] using h))]

theorem primrec_qAbs : Primrec qAbs :=
  Primrec.ite (primrec_qLe.comp (.const qZero) .id) .id primrec_qNeg

theorem primrec_factorial : Primrec Nat.factorial := by
  have hp : Primrec (Nat.rec 1 (fun n s => (n + 1) * s)) :=
    Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd)
  apply hp.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => dsimp; rw [ih, Nat.factorial_succ]

def qTaylor (q : QCode) (n : ℕ) : QCode :=
  ((List.range n).map fun m => qDiv (qPow q m) (qNat m.factorial)).foldr qAdd qZero

@[simp] theorem Qval_taylor (q : QCode) (n : ℕ) :
    Qval (qTaylor q n) = ∑ m ∈ Finset.range n, Qval q ^ m / m.factorial := by
  have hsum (l : List QCode) : Qval (l.foldr qAdd qZero) = (l.map Qval).sum := by
    induction l with
    | nil => simp
    | cons q l ih => simp [ih]
  rw [qTaylor, hsum, List.map_map]
  simp only [Function.comp_def, Qval_div, Qval_pow, Qval_nat]
  simpa only [List.toFinset_range] using (List.sum_toFinset (fun m => Qval q ^ m / m.factorial) (List.nodup_range (n := n))).symm

theorem primrec_qTaylor : Primrec₂ qTaylor := by
  unfold Primrec₂ qTaylor
  apply Primrec.list_foldr (h := fun _ p => qAdd p.1 p.2)
  · exact Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      (primrec_qDiv.comp (primrec_qPow.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (primrec_qNat.comp (primrec_factorial.comp Primrec.snd)))
  · exact Primrec.const qZero
  exact primrec_qAdd.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)

def expStop (r : QCode × ℕ) (m : ℕ) : Prop :=
  qLe (qDiv (qAbs r.1) (qNat (m + 1))) (qInv (qNat 2)) ∧
    qLe (qMul (qDiv (qPow (qAbs r.1) m) (qNat m.factorial)) (qNat 2))
      (qInv (qNat (r.2 + 1)))

instance : DecidableRel expStop := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

theorem primrec_expStop : PrimrecRel expStop := by
  apply PrimrecPred.and
  · exact primrec_qLe.comp
      (primrec_qDiv.comp (primrec_qAbs.comp (Primrec.fst.comp Primrec.fst))
        (primrec_qNat.comp (Primrec.succ.comp Primrec.snd))) (Primrec.const _)
  exact primrec_qLe.comp
    (primrec_qMul.comp
      (primrec_qDiv.comp
        (primrec_qPow.comp (primrec_qAbs.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
        (primrec_qNat.comp (primrec_factorial.comp Primrec.snd))) (Primrec.const _))
    (primrec_qInv.comp (primrec_qNat.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.fst))))

theorem expStop_iff (q : QCode) (N m : ℕ) : expStop (q, N) m ↔
    |(Qval q : ℝ)| / (m + 1) ≤ 1 / 2 ∧
    |(Qval q : ℝ)| ^ m / m.factorial * 2 ≤ ((N : ℝ) + 1)⁻¹ := by
  simp only [expStop, qLe_iff, Qval_div, Qval_abs, Qval_nat, Qval_inv,
    Qval_mul, Qval_pow]
  rw [← Rat.cast_le (K := ℝ), ← Rat.cast_le (K := ℝ)]
  push_cast
  norm_num

theorem exists_expStop (r : QCode × ℕ) : ∃ m, expStop r m := by
  let x : ℝ := Qval r.1
  have htail : Filter.Tendsto (fun m : ℕ => |x| ^ m / m.factorial * 2)
      Filter.atTop (nhds 0) := by
    simpa using (Real.summable_pow_div_factorial |x|).tendsto_atTop_zero.mul_const 2
  have hp : (0 : ℝ) < ((r.2 : ℝ) + 1)⁻¹ := by positivity
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (htail.eventually_lt_const hp)
  obtain ⟨M : ℕ, hM⟩ := exists_nat_gt (2 * |x|)
  refine ⟨max K M, (expStop_iff r.1 r.2 _).2 ⟨?_, (hK _ (le_max_left ..)).le⟩⟩
  rw [div_le_iff₀ (by positivity)]
  have hm : (M : ℝ) ≤ (max K M : ℕ) := by exact_mod_cast le_max_right K M
  dsimp [x] at hM
  linarith

noncomputable def qExp (r : QCode × ℕ) : QCode := qTaylor r.1 (Nat.find (exists_expStop r))

theorem computable_qExp : Computable qExp :=
  primrec_qTaylor.to_comp.comp Computable.fst (Computable.find primrec_expStop.computablePred exists_expStop)

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

noncomputable def flatTerm (m : ℕ) (x : ℝ) : ℝ := x⁻¹ ^ m * expNegInvGlue x

@[simp] theorem flatTerm_zero_index : flatTerm 0 = expNegInvGlue := by
  funext x
  simp [flatTerm]

theorem contDiff_flatTerm (m : ℕ) : ContDiff ℝ ∞ (flatTerm m) := by
  convert! (expNegInvGlue.contDiff_polynomial_eval_inv_mul (n := ⊤) (Polynomial.X ^ m)) using 1
  ext x
  simp only [flatTerm, Polynomial.eval_pow, Polynomial.eval_X]

theorem hasDerivAt_flatTerm (m : ℕ) (x : ℝ) :
    HasDerivAt (flatTerm m) (flatTerm (m + 2) x - m * flatTerm (m + 1) x) x := by
  convert expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (Polynomial.X ^ m) x using 1
  · ext y
    simp [flatTerm]
  · cases m with
    | zero => simp [flatTerm]
    | succ m =>
      rw [Polynomial.derivative_X_pow]
      simp only [flatTerm, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_sub, Polynomial.eval_C, Nat.succ_sub_one, Nat.cast_succ]
      simp only [pow_succ]
      ring

def flatLipschitzBound (m : ℕ) : ℕ := (m + 2).factorial + m * (m + 1).factorial

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
namespace BoxTransport.Routing.Computation

theorem computable_ite {α β} [Primcodable α] [Primcodable β]
    {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : ComputablePred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hp.decide hf hg

def qBound (q : QCode) : ℕ := q.1 + q.2.1

theorem primrec_qBound : Primrec qBound :=
  Primrec.nat_add.comp Primrec.fst (Primrec.fst.comp Primrec.snd)

noncomputable def qFlat (r : ℕ × QCode × ℕ) : QCode :=
  if qLe r.2.1 qZero then qZero else
    let w := qPow (qInv r.2.1) r.1
    qMul w (qExp (qNeg (qInv r.2.1), (r.2.2 + 1) * (qBound w + 1)))

theorem computable_qFlat : Computable qFlat := by
  unfold qFlat
  apply computable_ite (primrec_qLe.comp (Primrec.fst.comp Primrec.snd) (.const qZero)).computablePred
  · exact .const qZero
  have hw : Primrec fun r : ℕ × QCode × ℕ => qPow (qInv r.2.1) r.1 :=
    primrec_qPow.comp (primrec_qInv.comp (Primrec.fst.comp Primrec.snd)) Primrec.fst
  exact primrec_qMul.to_comp.comp hw.to_comp (computable_qExp.comp
    ((primrec_qNeg.comp (primrec_qInv.comp (Primrec.fst.comp Primrec.snd))).pair
      (Primrec.nat_mul.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.succ.comp (primrec_qBound.comp hw)))).to_comp)

end BoxTransport.Routing.Computation

end

end OAI


