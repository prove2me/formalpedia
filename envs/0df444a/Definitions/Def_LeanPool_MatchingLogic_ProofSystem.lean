-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_ProofSystem
-- name    : LeanPool_MatchingLogic_ProofSystem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:15:00.339832+00:00
-- url     : https://prove2.me/theorems/1793bba8-48e7-46a8-8008-67f31d185116
-- title:
--   Proof System
-- statement:
--   Definitions and structural lemmas for Proof System, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/ProofSystem.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_Boxes
public import Mathlib.Data.Set.Insert
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
inductive PForm where
  | atom : Nat → PForm
  | bot : PForm
  | imp : PForm → PForm → PForm
  deriving DecidableEq
def PForm.eval (v : Nat → Bool) : PForm → Bool
  | .atom n => v n
  | .bot => false
  | .imp a b => !(a.eval v) || b.eval v
def PForm.Taut (p : PForm) : Prop := ∀ v, p.eval v = true
def PForm.subst (θ : Nat → Pattern S Var) : PForm → Pattern S Var
  | .atom n => θ n
  | .bot => .bot
  | .imp a b => .imp (PForm.subst θ a) (PForm.subst θ b)
def substVar (x y : Var) : Pattern S Var → Pattern S Var
  | .var z => if z = x then .var y else .var z
  | .bot => .bot
  | .app σ f => .app σ (fun i => substVar x y (f i))
  | .imp a b => .imp (substVar x y a) (substVar x y b)
  | .ex z a => if z = x then .ex z a else .ex z (substVar x y a)
def CaptureFree (x y : Var) : Pattern S Var → Prop
  | .var _ => True
  | .bot => True
  | .app _ f => ∀ i, CaptureFree x y (f i)
  | .imp a b => CaptureFree x y a ∧ CaptureFree x y b
  | .ex z a => z = x ∨ x ∉ FV a ∨ (z ≠ y ∧ CaptureFree x y a)
inductive AppCtx (S : Signature) (Var : Type) where
  | hole : AppCtx S Var
  | node : (σ : S.Sym) → (i : Fin (S.arity σ)) →
      (Fin (S.arity σ) → Pattern S Var) → AppCtx S Var → AppCtx S Var
def AppCtx.plug : AppCtx S Var → Pattern S Var → Pattern S Var
  | .hole, φ => φ
  | .node σ i args c, φ => .app σ (Function.update args i (c.plug φ))
inductive Provable (Γ : Set (Pattern S Var)) : Pattern S Var → Prop
  /-- Membership in the theory. -/
  | hyp {φ} : φ ∈ Γ → Provable Γ φ
  /-- (1) Tautology. -/
  | taut {p : PForm} {θ : Nat → Pattern S Var} : p.Taut → Provable Γ (p.subst θ)
  /-- (2) Modus ponens. -/
  | mp {φ₁ φ₂} : Provable Γ φ₁ → Provable Γ (.imp φ₁ φ₂) → Provable Γ φ₂
  /-- (3) ∃-quantifier, capture-avoiding. -/
  | exQuant {x y : Var} {φ} : CaptureFree x y φ →
      Provable Γ (.imp (substVar x y φ) (.ex x φ))
  /-- (4) ∃-generalization. -/
  | exGen {x : Var} {φ₁ φ₂} : Provable Γ (.imp φ₁ φ₂) → x ∉ FV φ₂ →
      Provable Γ (.imp (.ex x φ₁) φ₂)
  /-- (5) Propagation of `⊥`. -/
  | propBot {σ : S.Sym} {i : Fin (S.arity σ)} {args} :
      Provable Γ (.imp (.app σ (Function.update args i .bot)) .bot)
  /-- (6) Propagation of `∨`. -/
  | propOr {σ : S.Sym} {i : Fin (S.arity σ)} {args} {φ₁ φ₂} :
      Provable Γ (.imp (.app σ (Function.update args i (Pattern.or φ₁ φ₂)))
        (Pattern.or (.app σ (Function.update args i φ₁))
                    (.app σ (Function.update args i φ₂))))
  /-- (7) Propagation of `∃`. -/
  | propEx {σ : S.Sym} {i : Fin (S.arity σ)} {args} {x : Var} {φ} :
      (∀ j, j ≠ i → x ∉ FV (args j)) →
      Provable Γ (.imp (.app σ (Function.update args i (.ex x φ)))
        (.ex x (.app σ (Function.update args i φ))))
  /-- (8) Framing. -/
  | framing {σ : S.Sym} {i : Fin (S.arity σ)} {args} {φ₁ φ₂} :
      Provable Γ (.imp φ₁ φ₂) →
      Provable Γ (.imp (.app σ (Function.update args i φ₁))
                       (.app σ (Function.update args i φ₂)))
  /-- (9) Existence. -/
  | existence {x : Var} : Provable Γ (.ex x (.var x))
  /-- (10) Singleton variable. -/
  | singleton {x : Var} {φ} (C₁ C₂ : AppCtx S Var) :
      Provable Γ (.imp (C₁.plug (Pattern.and (.var x) φ))
        (Pattern.nt (C₂.plug (Pattern.and (.var x) (Pattern.nt φ)))))
def doubleNegIntro : PForm :=
  .imp (.atom 0) (.imp (.imp (.atom 0) .bot) .bot)
def implicationTransitivity : PForm :=
  .imp (.imp (.atom 0) (.atom 1))
    (.imp (.imp (.atom 1) (.atom 2)) (.imp (.atom 0) (.atom 2)))
def conj : List (Pattern S Var) → Pattern S Var
  | [] => Pattern.tp
  | φ :: l => Pattern.and φ (conj l)
def StrongLocalCompleteness (S : Signature) (Var : Type) [DecidableEq Var] : Prop :=
  ∀ (Δ : Set (Pattern S Var)) (φ : Pattern S Var), LocalCons Δ φ →
    ∃ l : List (Pattern S Var), (∀ δ ∈ l, δ ∈ Δ) ∧
      Provable (∅ : Set (Pattern S Var)) (.imp (conj l) φ)
def Soundness (S : Signature) (Var : Type) [DecidableEq Var] : Prop :=
  ∀ (Γ : Set (Pattern S Var)) (φ : Pattern S Var), Provable Γ φ → GlobalCons Γ φ
end MatchingLogic


