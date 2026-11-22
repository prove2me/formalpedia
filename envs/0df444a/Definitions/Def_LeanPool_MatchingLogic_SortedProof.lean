-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_SortedProof
-- name    : LeanPool_MatchingLogic_SortedProof
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:18:36.166897+00:00
-- url     : https://prove2.me/theorems/33e9cc94-6722-4ea1-9aff-8896c7da0f94
-- title:
--   Sorted Proof
-- statement:
--   Definitions and structural lemmas for Sorted Proof, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/SortedProof.lean

module
public import Definitions.Def_LeanPool_MatchingLogic_Sorted
public import Definitions.Def_LeanPool_MatchingLogic_ProofSystem
public import Definitions.Def_LeanPool_MatchingLogic_EntryPoints
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Theorems.Thm_MatchingLogic_AgreeOn_update

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
namespace Sorted
variable {S : MSignature} {Var : Type} [DecidableEq S.Srt] [DecidableEq Var]
def MFV : {s : S.Srt} → MPattern S Var s → Set (S.Srt × Var)
  | _, .var x s => {(s, x)}
  | _, .bot => ∅
  | _, .app _ f => ⋃ i, MFV (f i)
  | _, .imp a b => MFV a ∪ MFV b
  | _, .ex x s' a => MFV a \ {(s', x)}
inductive MAppCtx (S : MSignature) (Var : Type) : S.Srt → S.Srt → Type where
  | hole : {s : S.Srt} → MAppCtx S Var s s
  | node : {sh : S.Srt} → (σ : S.Sym) → (i : Fin (S.arity σ)) →
      ((j : Fin (S.arity σ)) → MPattern S Var (S.argSort σ j)) →
      MAppCtx S Var sh (S.argSort σ i) → MAppCtx S Var sh (S.resSort σ)
def MAppCtx.plug : {sh st : S.Srt} → MAppCtx S Var sh st → MPattern S Var sh →
    MPattern S Var st
  | _, _, .hole, φ => φ
  | _, _, .node σ i args c, φ => .app σ (Function.update args i (c.plug φ))
def msubstVar (s' : S.Srt) (x y : Var) :
    {s : S.Srt} → MPattern S Var s → MPattern S Var s
  | _, .var z t => if t = s' ∧ z = x then .var y t else .var z t
  | _, .bot => .bot
  | _, .app σ f => .app σ (fun i => msubstVar s' x y (f i))
  | _, .imp a b => .imp (msubstVar s' x y a) (msubstVar s' x y b)
  | _, .ex z t a =>
      if t = s' ∧ z = x then .ex z t a else .ex z t (msubstVar s' x y a)
def MCaptureFree (s' : S.Srt) (x y : Var) :
    {s : S.Srt} → MPattern S Var s → Prop
  | _, .var _ _ => True
  | _, .bot => True
  | _, .app _ f => ∀ i, MCaptureFree s' x y (f i)
  | _, .imp a b => MCaptureFree s' x y a ∧ MCaptureFree s' x y b
  | _, .ex z t a =>
      (t = s' ∧ z = x) ∨ (s', x) ∉ MFV a ∨
        (¬ (t = s' ∧ z = y) ∧ MCaptureFree s' x y a)
def substPF {s : S.Srt} (θ : Nat → MPattern S Var s) :
    PForm → MPattern S Var s
  | PForm.atom n => θ n
  | PForm.bot => MPattern.bot
  | PForm.imp a b => MPattern.imp (substPF θ a) (substPF θ b)
inductive MProvable {sΓ : S.Srt} (Γ : Set (MPattern S Var sΓ)) :
    {s : S.Srt} → MPattern S Var s → Prop
  | hyp {φ} : φ ∈ Γ → MProvable Γ φ
  | taut {s : S.Srt} {p : PForm} {θ : Nat → MPattern S Var s} :
      PForm.Taut p → MProvable Γ (substPF θ p)
  | mp {s : S.Srt} {φ₁ φ₂ : MPattern S Var s} :
      MProvable Γ φ₁ → MProvable Γ (.imp φ₁ φ₂) → MProvable Γ φ₂
  | exQuant {s s' : S.Srt} {x y : Var} {φ : MPattern S Var s} :
      MCaptureFree s' x y φ →
      MProvable Γ (.imp (msubstVar s' x y φ) (.ex x s' φ))
  | exGen {s s' : S.Srt} {x : Var} {φ₁ φ₂ : MPattern S Var s} :
      MProvable Γ (.imp φ₁ φ₂) → (s', x) ∉ MFV φ₂ →
      MProvable Γ (.imp (.ex x s' φ₁) φ₂)
  | propBot {σ : S.Sym} {i : Fin (S.arity σ)} {args} :
      MProvable Γ (.imp (.app σ (Function.update args i .bot)) .bot)
  | propOr {σ : S.Sym} {i : Fin (S.arity σ)} {args} {φ₁ φ₂} :
      MProvable Γ (.imp (.app σ (Function.update args i (MPattern.orP φ₁ φ₂)))
        (MPattern.orP (.app σ (Function.update args i φ₁))
                      (.app σ (Function.update args i φ₂))))
  | propEx {σ : S.Sym} {i : Fin (S.arity σ)} {args} {s' : S.Srt} {x : Var} {φ} :
      (∀ j, j ≠ i → (s', x) ∉ MFV (args j)) →
      MProvable Γ (.imp (.app σ (Function.update args i (.ex x s' φ)))
        (.ex x s' (.app σ (Function.update args i φ))))
  | framing {σ : S.Sym} {i : Fin (S.arity σ)} {args} {φ₁ φ₂} :
      MProvable Γ (.imp φ₁ φ₂) →
      MProvable Γ (.imp (.app σ (Function.update args i φ₁))
                        (.app σ (Function.update args i φ₂)))
  | existence {s : S.Srt} {x : Var} :
      MProvable Γ (.ex x s (.var x s))
  | singleton {sh st : S.Srt} {x : Var} {φ : MPattern S Var sh}
      (C₁ C₂ : MAppCtx S Var sh st) :
      MProvable Γ (.imp (C₁.plug (MPattern.and (.var x sh) φ))
        (MPattern.nt (C₂.plug (MPattern.and (.var x sh) (MPattern.nt φ)))))
def Feeds (S : MSignature) (s t : S.Srt) : Prop :=
  s = t ∨ ∃ (σ : S.Sym) (i : Fin (S.arity σ)), S.argSort σ i = s ∧ S.resSort σ = t
abbrev FeedsStar (S : MSignature) : S.Srt → S.Srt → Prop :=
  Relation.ReflTransGen (Feeds S)
def MSoundness (S : MSignature) (Var : Type) [DecidableEq S.Srt] [DecidableEq Var] : Prop :=
  ∀ {sΓ sφ : S.Srt} (Γ : Set (MPattern S Var sΓ)) (φ : MPattern S Var sφ),
    MProvable Γ φ → MGlobalCons Γ φ
end Sorted
end MatchingLogic


