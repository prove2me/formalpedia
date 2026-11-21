-- Prove2me | Definitions.Def_AutoformalisationSCI_Oracle
-- name    : AutoformalisationSCI_Oracle
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T14:47:09.675361+00:00
-- url     : https://prove2.me/theorems/dac61eaa-7d4d-4427-985d-3d0521f9ed63
-- title:
--   Set Turing reducibility, oracle codes, and the Turing jump
-- statement:
--   This file packages **Turing reducibility between sets of natural numbers** and defines the **Turing jump** and its iterates, as used in Theorems A.3, A.4 and the degree remarks.
--
--   For $A\subseteq\mathbb N$, its oracle is the total characteristic function $\chi_A(n)=1$ if $n\in A$ and $0$ otherwise, viewed as a partial function. Then $A\le_T B$ means $\chi_A$ is computable with oracle $\chi_B$ (Mathlib's `RecursiveIn` / `TuringReducible`), and $A\equiv_T B$ means reducibility in both directions (equal Turing degree).
--
--   Oracle machines are represented by an inductive code type `OracleCode` whose constructors mirror those of Mathlib's `Nat.RecursiveIn` (zero, successor, the two unpair projections, the oracle, pairing, composition, primitive recursion, and unbounded search). `OracleCode.eval B c` is the partial function computed by code $c$ with oracle $B$. The **Turing jump** $B'$ is the halting set of these machines, encoded as a set of naturals via $\langle\text{code},\text{input}\rangle$; the iterates are $\emptyset^{(0)}=\emptyset$ and $\emptyset^{(j+1)}=(\emptyset^{(j)})'$, so $\emptyset^{(1)}$ is the halting problem.
--
--   **Formalization Note.** The code type is given a Gödel numbering and an `Encodable` instance so that machines can be encoded as natural numbers. That `OracleCode.eval B` enumerates exactly the `RecursiveIn {χ_B}` partial functions is the expected universality lemma for solvers to prove.
-- source:
--   A. Bastounis, F. Circelli, A. C. Hansen, Navier–Stokes lost in translation, arXiv:2610.08144 (2026), Appendix A (pp. 17–23); https://arxiv.org/abs/2610.08144. Standard background: R. I. Soare, Turing Computability, Springer 2016, Ch. 4.

import Mathlib.Computability.RecursiveIn
import Mathlib.Computability.TuringDegree
import Mathlib.Data.Nat.Pairing

open Encodable Part

namespace AutoformalisationSCI

open scoped Computability

noncomputable def setOracle (A : Set ℕ) : ℕ →. ℕ := by
  classical
  exact PFun.lift (fun n => if n ∈ A then 1 else 0)

def SetTuringReducible (A B : Set ℕ) : Prop := setOracle A ≤ᵀ setOracle B

def SetTuringEquivalent (A B : Set ℕ) : Prop := SetTuringReducible A B ∧ SetTuringReducible B A

inductive OracleCode : Type
  | zero : OracleCode
  | succ : OracleCode
  | left : OracleCode
  | right : OracleCode
  | oracle : OracleCode
  | pair : OracleCode → OracleCode → OracleCode
  | comp : OracleCode → OracleCode → OracleCode
  | prec : OracleCode → OracleCode → OracleCode
  | rfind : OracleCode → OracleCode

noncomputable def OracleCode.eval (B : Set ℕ) : OracleCode → ℕ →. ℕ
  | .zero => fun _ => 0
  | .succ => Nat.succ
  | .left => fun n => (Nat.unpair n).1
  | .right => fun n => (Nat.unpair n).2
  | .oracle => setOracle B
  | .pair f h => fun n => (Nat.pair <$> eval B f n <*> eval B h n)
  | .comp f h => fun n => eval B h n >>= eval B f
  | .prec f h => fun p =>
      let (a, n) := Nat.unpair p
      n.rec (eval B f a) fun y IH => do
        let i ← IH
        eval B h (Nat.pair a (Nat.pair y i))
  | .rfind f => fun a =>
      Nat.rfind fun n => (fun m => m = 0) <$> eval B f (Nat.pair a n)

def OracleCode.toNat : OracleCode → ℕ
  | .zero => Nat.pair 0 0
  | .succ => Nat.pair 1 0
  | .left => Nat.pair 2 0
  | .right => Nat.pair 3 0
  | .oracle => Nat.pair 4 0
  | .pair a b => Nat.pair 5 (Nat.pair a.toNat b.toNat)
  | .comp a b => Nat.pair 6 (Nat.pair a.toNat b.toNat)
  | .prec a b => Nat.pair 7 (Nat.pair a.toNat b.toNat)
  | .rfind a => Nat.pair 8 a.toNat

private theorem pair_inj {a b c d : ℕ} (h : Nat.pair a b = Nat.pair c d) : a = c ∧ b = d := by
  have := congrArg Nat.unpair h
  rw [Nat.unpair_pair, Nat.unpair_pair] at this
  exact Prod.mk.inj this

theorem OracleCode.toNat_injective : Function.Injective OracleCode.toNat := by
  have key : ∀ a b : OracleCode, a.toNat = b.toNat → a = b := by
    intro a
    induction a with
    | zero => intro b h; cases b with
        | zero => rfl
        | _ => have := congrArg Nat.unpair h; simp_all [OracleCode.toNat, Nat.unpair_pair]
    | succ => intro b h; cases b with
        | succ => rfl
        | _ => have := congrArg Nat.unpair h; simp_all [OracleCode.toNat, Nat.unpair_pair]
    | left => intro b h; cases b with
        | left => rfl
        | _ => have := congrArg Nat.unpair h; simp_all [OracleCode.toNat, Nat.unpair_pair]
    | right => intro b h; cases b with
        | right => rfl
        | _ => have := congrArg Nat.unpair h; simp_all [OracleCode.toNat, Nat.unpair_pair]
    | oracle => intro b h; cases b with
        | oracle => rfl
        | _ => have := congrArg Nat.unpair h; simp_all [OracleCode.toNat, Nat.unpair_pair]
    | pair a₁ a₂ ih₁ ih₂ => intro b h; cases b with
        | pair b₁ b₂ =>
            have h₂ := pair_inj (pair_inj h).2
            rw [ih₁ _ h₂.1, ih₂ _ h₂.2]
        | _ => have := congrArg Nat.unpair h; simp_all [OracleCode.toNat, Nat.unpair_pair]
    | comp a₁ a₂ ih₁ ih₂ => intro b h; cases b with
        | comp b₁ b₂ =>
            have h₂ := pair_inj (pair_inj h).2
            rw [ih₁ _ h₂.1, ih₂ _ h₂.2]
        | _ => have := congrArg Nat.unpair h; simp_all [OracleCode.toNat, Nat.unpair_pair]
    | prec a₁ a₂ ih₁ ih₂ => intro b h; cases b with
        | prec b₁ b₂ =>
            have h₂ := pair_inj (pair_inj h).2
            rw [ih₁ _ h₂.1, ih₂ _ h₂.2]
        | _ => have := congrArg Nat.unpair h; simp_all [OracleCode.toNat, Nat.unpair_pair]
    | rfind a ih => intro b h; cases b with
        | rfind b₁ => rw [ih _ (pair_inj h).2]
        | _ => have := congrArg Nat.unpair h; simp_all [OracleCode.toNat, Nat.unpair_pair]
  exact key

noncomputable instance : Encodable OracleCode :=
  Encodable.ofInj OracleCode.toNat OracleCode.toNat_injective

noncomputable def turingJump (B : Set ℕ) : Set ℕ :=
  {p | ∃ c : OracleCode, Encodable.encode c = p.unpair.1 ∧ (OracleCode.eval B c p.unpair.2).Dom}

noncomputable def jumpIter : ℕ → Set ℕ
  | 0 => ∅
  | j + 1 => turingJump (jumpIter j)

end AutoformalisationSCI


