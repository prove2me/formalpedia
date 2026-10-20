-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
-- name    : OAI_NumberTheory_SingleFold_RationalCodes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:02:53.719016+00:00
-- url     : https://prove2.me/theorems/2ecee4a5-7dae-46e2-ac07-e07494c75f59
-- title:
--   Unique natural-number codes for rationals and rational expressions
-- statement:
--   1. **Rational codes.** A code is a $6$-tuple $(p,n,d,t,s,q)\in\mathbb{N}^6$. It is valid if
--   $$
--   pn=0,\qquad d=1+t+s,\qquad (p+n)t+d=1+qd,
--   $$
--      and its value is $(p-n)/d$. Validity forces $d>0$, $t<d$, and $(p+n)t\equiv1\pmod d$, so $p+n$ is coprime to $d$ and $t$ is the inverse of $p+n$ modulo $d$. Every rational number is the value of exactly one valid code; $\mathrm{encode}(r)$ denotes it.
--   2. **Fraction polynomials.** A pair of integer polynomials (numerator, denominator) with value $\mathrm{num}(z)/\mathrm{den}(z)$, and the sum, product, negation and constants computed by the usual fraction rules.
--   3. **Rational expressions.** The syntax of variables, rational constants, $+$, $\times$ and negation, with evaluation in $\mathbb{Q}$ and powers. An expression in variables $\alpha$ compiles to a fraction polynomial in the code coordinates $\alpha\times\{0,\dots,5\}$; the variable $i$ becomes $(p_i-n_i)/d_i$.
--   4. **Semi-representability.** A relation $R$ is semi-representable if both $R$ and its negation are SF.
--
--   Rational unknowns can therefore be replaced by six natural-number unknowns each, without losing uniqueness of the witness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/RationalCodes.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/RationalCodes.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler

namespace OAI

namespace SingleFold

@[ext] structure RationalCode where
  p : ℕ
  n : ℕ
  d : ℕ
  t : ℕ
  s : ℕ
  q : ℕ
  deriving DecidableEq

namespace RationalCode

def Valid (z : RationalCode) : Prop :=
  z.p * z.n = 0 ∧ z.d = 1 + z.t + z.s ∧
  (z.p + z.n) * z.t + z.d = 1 + z.q * z.d

def value (z : RationalCode) : ℚ := ((z.p : ℚ) - z.n) / z.d

lemma den_pos {z : RationalCode} (h : z.Valid) : 0 < z.d := by
  have := h.2.1
  omega

lemma inverse_lt {z : RationalCode} (h : z.Valid) : z.t < z.d := by
  have := h.2.1
  omega

lemma inverse_mod {z : RationalCode} (h : z.Valid) :
    (z.p + z.n) * z.t ≡ 1 [MOD z.d] := by
  change ((z.p + z.n) * z.t) % z.d = 1 % z.d
  have hm := congrArg (fun a : ℕ => a % z.d) h.2.2
  simpa [Nat.add_mod, Nat.mul_mod] using hm

lemma reduced {z : RationalCode} (h : z.Valid) : (z.p + z.n).Coprime z.d :=
  Nat.coprime_of_mul_modEq_one z.t (inverse_mod h)

lemma abs_num {z : RationalCode} (h : z.Valid) :
    ((z.p : ℤ) - z.n).natAbs = z.p + z.n := by
  rcases Nat.mul_eq_zero.mp h.1 with hp | hn
  · simp [hp]
  · simp [hn]

lemma canonical {z : RationalCode} (h : z.Valid) :
    z.value.num = (z.p : ℤ) - z.n ∧ z.value.den = z.d := by
  have hr : ((z.p : ℤ) - z.n).natAbs.Coprime z.d := by
    rw [abs_num h]
    exact reduced h
  let r := Rat.mk' ((z.p : ℤ) - z.n) z.d (den_pos h).ne' hr
  have hv : z.value = r := by
    simpa only [r, Rat.mk', value, Int.cast_sub, Int.cast_natCast] using Rat.num_div_den r
  rw [hv]
  exact ⟨rfl, rfl⟩

lemma positive_num {z : RationalCode} (h : z.Valid) : z.value.num.toNat = z.p := by
  rw [(canonical h).1]
  rcases Nat.mul_eq_zero.mp h.1 with hp | hn
  · simp [hp]
  · simp [hn]

lemma negative_num {z : RationalCode} (h : z.Valid) : (-z.value.num).toNat = z.n := by
  rw [(canonical h).1]
  rcases Nat.mul_eq_zero.mp h.1 with hp | hn
  · simp [hp]
  · simp [hn]

theorem unique {z z' : RationalCode} (h : z.Valid) (h' : z'.Valid)
    (heq : z.value = z'.value) : z = z' := by
  have hp : z.p = z'.p := by rw [← positive_num h, ← positive_num h', heq]
  have hn : z.n = z'.n := by rw [← negative_num h, ← negative_num h', heq]
  have hd : z.d = z'.d := by rw [← (canonical h).2, ← (canonical h').2, heq]
  have hm : (z.p + z.n) * z.t ≡ (z.p + z.n) * z'.t [MOD z.d] := by
    have hi' := inverse_mod h'
    rw [← hp, ← hn, ← hd] at hi'
    exact (inverse_mod h).trans hi'.symm
  have ht : z.t = z'.t := by
    apply (hm.cancel_left_of_coprime (reduced h).symm).eq_of_lt_of_lt (inverse_lt h)
    rw [hd]
    exact inverse_lt h'
  have hs : z.s = z'.s := by
    have hd₁ := h.2.1
    have hd₂ := h'.2.1
    omega
  have hq : z.q = z'.q := by
    have he₁ := h.2.2
    have he₂ := h'.2.2
    rw [← hp, ← hn, ← hd, ← ht] at he₂
    have hx : z.q * z.d = z'.q * z.d := by omega
    exact Nat.eq_of_mul_eq_mul_right (den_pos h) hx
  exact RationalCode.ext hp hn hd ht hs hq

lemma inverse_exists {a d : ℕ} (hd : 0 < d) (hcop : a.Coprime d) :
    ∃ t s q : ℕ, d = 1 + t + s ∧ a * t + d = 1 + q * d := by
  by_cases hd1 : d = 1
  · subst d
    exact ⟨0, 0, 0, by omega, by simp⟩
  · obtain ⟨t, ht, hinv⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
    refine ⟨t, d - 1 - t, (a * t) / d + 1, by omega, ?_⟩
    have hdiv := Nat.mod_add_div (a * t) d
    rw [hinv] at hdiv
    nlinarith

theorem existsUnique (r : ℚ) : ∃! z : RationalCode, z.Valid ∧ z.value = r := by
  let p := r.num.toNat
  let n := (-r.num).toNat
  have hpn : p * n = 0 := by
    rcases le_total 0 r.num with hn | hn
    · have : n = 0 := Int.toNat_eq_zero.mpr (neg_nonpos.mpr hn)
      simp [this]
    · have : p = 0 := Int.toNat_eq_zero.mpr hn
      simp [this]
  have habs : p + n = r.num.natAbs := Int.toNat_add_toNat_neg_eq_natAbs _
  obtain ⟨t, s, q, hd, hi⟩ := inverse_exists r.den_pos (habs ▸ r.reduced)
  let z : RationalCode := ⟨p, n, r.den, t, s, q⟩
  have hz : z.Valid := ⟨hpn, hd, hi⟩
  have hv : z.value = r := by
    have hn := Int.toNat_sub_toNat_neg r.num
    have hn' : (p : ℚ) - n = (r.num : ℚ) := by exact_mod_cast hn
    dsimp [value, z]
    rw [hn']
    exact r.num_div_den
  refine ⟨z, ⟨hz, hv⟩, ?_⟩
  intro z' hz'
  exact unique hz'.1 hz (hz'.2.trans hv.symm)

end RationalCode
end SingleFold

namespace SingleFold.Compiler.SF
variable {α β : Type} {R S : (α → ℕ) → Prop}

end SingleFold.Compiler.SF

namespace SingleFold.RationalCompiler
open Compiler

structure FractionPoly (α : Type) where
  num : Poly α
  den : Poly α

namespace FractionPoly
variable {α : Type}
def value (p : FractionPoly α) (z : α → ℕ) : ℚ := (p.num z : ℚ)/(p.den z : ℚ)
def const (r : ℚ) : FractionPoly α := ⟨Poly.const r.num,Poly.const r.den⟩
def add (p q : FractionPoly α) : FractionPoly α := ⟨p.num*q.den+q.num*p.den,p.den*q.den⟩
def mul (p q : FractionPoly α) : FractionPoly α := ⟨p.num*q.num,p.den*q.den⟩
def neg (p : FractionPoly α) : FractionPoly α := ⟨-p.num,p.den⟩

end FractionPoly

def code (z : Fin 6 → ℕ) : RationalCode := ⟨z 0,z 1,z 2,z 3,z 4,z 5⟩
def tuple (z : RationalCode) : Fin 6 → ℕ := ![z.p,z.n,z.d,z.t,z.s,z.q]
@[simp] lemma code_tuple (z : RationalCode) : code (tuple z)=z := by cases z; rfl
@[simp] lemma tuple_code (z : Fin 6 → ℕ) : tuple (code z)=z := by funext i; fin_cases i <;> rfl

def Valid {α : Type} (z : α × Fin 6 → ℕ) : Prop := ∀ i, (code (fun j => z (i,j))).Valid
def value {α : Type} (z : α × Fin 6 → ℕ) (i : α) : ℚ := (code (fun j => z (i,j))).value

def input {α : Type} (i : α) : FractionPoly (α × Fin 6) :=
  ⟨Poly.proj (i,0)-Poly.proj (i,1),Poly.proj (i,2)⟩
inductive Expr (α : Type)
  | var (i : α)
  | const (q : ℚ)
  | add (p q : Expr α)
  | mul (p q : Expr α)
  | neg (p : Expr α)
namespace Expr
variable {α : Type}
def eval (x : α → ℚ) : Expr α → ℚ
  | var i => x i
  | const q => q
  | add p q => eval x p+eval x q
  | mul p q => eval x p*eval x q
  | neg p => -eval x p
def compile : Expr α → FractionPoly (α × Fin 6)
  | var i => input i
  | const q => FractionPoly.const q
  | add p q => (compile p).add (compile q)
  | mul p q => (compile p).mul (compile q)
  | neg p => (compile p).neg
end Expr
end SingleFold.RationalCompiler

namespace SingleFold.Compiler

def Semi {α : Type} (R : (α → ℕ) → Prop) : Prop := SF R ∧ SF (fun x => ¬R x)
namespace Semi
variable {α β : Type} {R S : (α → ℕ) → Prop}
end Semi
end SingleFold.Compiler

namespace SingleFold.RationalCompiler
open Compiler

namespace Expr
variable {α β : Type}
instance : Add (Expr α) := ⟨Expr.add⟩
instance : Mul (Expr α) := ⟨Expr.mul⟩
instance : Neg (Expr α) := ⟨Expr.neg⟩
instance : Sub (Expr α) := ⟨fun p q => p+ -q⟩
instance (n : ℕ) : OfNat (Expr α) n := ⟨const n⟩
instance : Pow (Expr α) ℕ := ⟨fun p n => Nat.rec (1:Expr α) (fun _ q => p*q) n⟩
@[simp] lemma eval_add (p q : Expr α) (x) : (p+q).eval x=p.eval x+q.eval x := rfl
@[simp] lemma eval_mul (p q : Expr α) (x) : (p*q).eval x=p.eval x*q.eval x := rfl
@[simp] lemma eval_neg (p : Expr α) (x) : (-p).eval x= -p.eval x := rfl
@[simp] lemma eval_sub (p q : Expr α) (x) : (p-q).eval x=p.eval x-q.eval x := by change p.eval x+ -q.eval x=_; rw [sub_eq_add_neg]
@[simp] lemma eval_nat (n : ℕ) (x : α → ℚ) : (const n).eval x=n := rfl
@[simp] lemma eval_ofNat (n : ℕ) [n.AtLeastTwo] (x : α → ℚ) : (OfNat.ofNat n : Expr α).eval x=n := rfl
@[simp] lemma eval_zero (x : α → ℚ) : (0:Expr α).eval x=0 := rfl
@[simp] lemma eval_one (x : α → ℚ) : (1:Expr α).eval x=1 := rfl
@[simp] lemma eval_var (i : α) (x) : (var i).eval x=x i := rfl
@[simp] lemma eval_pow (p : Expr α) (n : ℕ) (x) : (p^n).eval x=(p.eval x)^n := by
  induction n with
  | zero => change (1:ℚ)=_; simp
  | succ n ih => change (p*(p^n)).eval x=_; rw [eval_mul,ih,pow_succ']

end Expr
end SingleFold.RationalCompiler

namespace SingleFold.RationalCode
noncomputable def encode (q : ℚ) : RationalCode := Classical.choose (existsUnique q)
lemma encode_valid (q : ℚ) : (encode q).Valid := (Classical.choose_spec (existsUnique q)).1.1
lemma encode_value (q : ℚ) : (encode q).value=q := (Classical.choose_spec (existsUnique q)).1.2
end SingleFold.RationalCode

end OAI


