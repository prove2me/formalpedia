-- Prove2me | Definitions.Def_LeanPool_MatchingLogic_Sorted
-- name    : LeanPool_MatchingLogic_Sorted
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:13:54.728899+00:00
-- url     : https://prove2.me/theorems/93310743-2828-4371-bc05-1caa476ef28a
-- title:
--   Sorted
-- statement:
--   Definitions and structural lemmas for Sorted, from Aurélien Eveil; Anthropic; OpenAI; LeanPool contributors's pinned Global completeness of one-sorted definedness-free matching logic development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/MatchingLogic/Sorted.lean

module
public import Aesop.BuiltinRules
public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.ToAdditive
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Lattice
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace MatchingLogic
namespace Sorted
structure MSignature where
  /-- The type of sorts. -/
  Srt : Type
  /-- The type of operation symbols. -/
  Sym : Type
  /-- The number of arguments of each operation symbol. -/
  arity : Sym → Nat
  /-- The sort of each argument position. -/
  argSort : (σ : Sym) → Fin (arity σ) → Srt
  /-- The result sort of each operation symbol. -/
  resSort : Sym → Srt
variable {S : MSignature} {Var : Type}
inductive MPattern (S : MSignature) (Var : Type) : S.Srt → Type where
  | var : Var → (s : S.Srt) → MPattern S Var s
  | app : (σ : S.Sym) →
      ((i : Fin (S.arity σ)) → MPattern S Var (S.argSort σ i)) →
      MPattern S Var (S.resSort σ)
  | imp : {s : S.Srt} → MPattern S Var s → MPattern S Var s → MPattern S Var s
  | bot : {s : S.Srt} → MPattern S Var s
  | ex : {s : S.Srt} → Var → (s' : S.Srt) → MPattern S Var s → MPattern S Var s
namespace MPattern
variable {s : S.Srt}
abbrev nt (φ : MPattern S Var s) : MPattern S Var s := imp φ bot
abbrev tp : MPattern S Var s := imp bot bot
abbrev and (φ ψ : MPattern S Var s) : MPattern S Var s := nt (imp φ (nt ψ))
abbrev orP (φ ψ : MPattern S Var s) : MPattern S Var s := imp (nt φ) ψ
abbrev iff (φ ψ : MPattern S Var s) : MPattern S Var s := and (imp φ ψ) (imp ψ φ)
abbrev al (x : Var) (s' : S.Srt) (φ : MPattern S Var s) : MPattern S Var s :=
  nt (ex x s' (nt φ))
end MPattern
structure MModel (S : MSignature) where
  /-- The carrier type at each sort. -/
  carrier : S.Srt → Type
  nonempty : ∀ s, Nonempty (carrier s)
  /-- The set-valued interpretation of each operation symbol. -/
  interp : (σ : S.Sym) →
    ((i : Fin (S.arity σ)) → carrier (S.argSort σ i)) → Set (carrier (S.resSort σ))
abbrev MVal (M : MModel S) (Var : Type) : Type := (s : S.Srt) → Var → M.carrier s
noncomputable def mupdate (M : MModel S) (ρ : MVal M Var) (s' : S.Srt) (x : Var)
    (a : M.carrier s') : MVal M Var :=
  letI := Classical.decEq S.Srt
  letI := Classical.decEq Var
  fun t y => if y = x then (if ht : t = s' then ht ▸ a else ρ t y) else ρ t y
def MModel.app (M : MModel S) (σ : S.Sym)
    (A : (i : Fin (S.arity σ)) → Set (M.carrier (S.argSort σ i))) :
    Set (M.carrier (S.resSort σ)) :=
  {u | ∃ a : (i : Fin (S.arity σ)) → M.carrier (S.argSort σ i),
        (∀ i, a i ∈ A i) ∧ u ∈ M.interp σ a}
noncomputable def mdenote (M : MModel S) (ρ : MVal M Var) :
    {s : S.Srt} → MPattern S Var s → Set (M.carrier s)
  | _, .var x s => {ρ s x}
  | _, .bot => ∅
  | _, .app σ f => M.app σ (fun i => mdenote M ρ (f i))
  | _, .imp φ ψ => (mdenote M ρ φ)ᶜ ∪ mdenote M ρ ψ
  | _, .ex x s' φ => ⋃ a : M.carrier s', mdenote M (mupdate M ρ s' x a) φ
def MModel.Sat (M : MModel S) {s : S.Srt} (φ : MPattern S Var s) : Prop :=
  ∀ ρ : MVal M Var, mdenote M ρ φ = Set.univ
def MModel.SatSetHet (M : MModel S)
    (Γ : Set ((s : S.Srt) × MPattern S Var s)) : Prop :=
  ∀ p ∈ Γ, M.Sat p.2
def MModel.SatSet (M : MModel S) {s : S.Srt} (Γ : Set (MPattern S Var s)) : Prop :=
  ∀ γ ∈ Γ, M.Sat γ
def MGlobalCons {sΓ sφ : S.Srt} (Γ : Set (MPattern S Var sΓ))
    (φ : MPattern S Var sφ) : Prop :=
  ∀ M : MModel S, M.SatSet Γ → M.Sat φ
def MGlobalConsHet (Γ : Set ((s : S.Srt) × MPattern S Var s)) {sφ : S.Srt}
    (φ : MPattern S Var sφ) : Prop :=
  ∀ M : MModel S, M.SatSetHet Γ → M.Sat φ
inductive Srt3 where | b | a | c
  deriving DecidableEq
inductive Sym3 where | f | g
  deriving DecidableEq
abbrev S3 : MSignature where
  Srt := Srt3
  Sym := Sym3
  arity := fun _ => 1
  argSort := fun _ _ => Srt3.b
  resSort := fun σ => match σ with | .f => Srt3.a | .g => Srt3.c
abbrev fAp (ψ : MPattern S3 Var Srt3.b) : MPattern S3 Var Srt3.a :=
  MPattern.app (S := S3) Sym3.f (fun _ => ψ)
abbrev gAp (ψ : MPattern S3 Var Srt3.b) : MPattern S3 Var Srt3.c :=
  MPattern.app (S := S3) Sym3.g (fun _ => ψ)
abbrev Γ3 (x y : Var) : Set (MPattern S3 Var Srt3.a) :=
  { MPattern.al x Srt3.b (MPattern.al y Srt3.b
      (fAp (MPattern.and (MPattern.var (S := S3) x Srt3.b)
        (MPattern.var (S := S3) y Srt3.b)))) }
abbrev φ3 (x y : Var) : MPattern S3 Var Srt3.c :=
  MPattern.al x Srt3.b (MPattern.al y Srt3.b
    (MPattern.iff (gAp (MPattern.var (S := S3) x Srt3.b))
      (gAp (MPattern.var (S := S3) y Srt3.b))))
abbrev singletonM3 : MModel S3 where
  carrier := fun _ => PUnit
  nonempty := fun _ => ⟨PUnit.unit⟩
  interp := fun _ _ => Set.univ
end Sorted
end MatchingLogic


