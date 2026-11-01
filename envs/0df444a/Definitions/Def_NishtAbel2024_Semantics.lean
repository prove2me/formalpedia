-- Prove2me | Definitions.Def_NishtAbel2024_Semantics
-- name    : NishtAbel2024_Semantics
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-31T19:02:47.419699+00:00
-- url     : https://prove2.me/theorems/72cdb9bd-1628-44bd-9ccf-774fc02f5810
-- title:
--   Chapter 5: Operational Semantics, Strong Normalization, Girard–Tait Reducibility Candidates, and Semantic SCT_G
-- statement:
--   Formalizes Chapter 5 (pp. 31–38) of Nisht & Abel (2024): size/type/term substitutions, pattern and copattern-spine matching (`MatchPat`, `MatchCopat`, `MatchSpine`), weak-head and full reduction (`WhdStep`, `RedStep`), strong normalization (`SN`), neutral and introduction terms, simulation (`Simulates`), Girard–Tait reducibility candidates (`IsCandidate`, `candClosure`), semantic size ordinals `SizeOrd`, ordinal-indexed inflationary/deflationary fixpoints (`muFixpoint`, `nuFixpoint`), the full candidate interpretation `evalTypeWith`, the semantic call relation `SCTCallRel`, and semantic typing judgments (`SemSigValid`, `SemBlockGuardedValid`, `SemExprTyping`, `SemMutualBlockValid`, `SemProgramValid`).
-- source:
--   Kanstantsin Nisht, 'Type-Based Termination Checking in Agda', Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, 30th International Conference on Types for Proofs and Programs (TYPES 2024). Chapter 5, Sections 5.1–5.4 (pp. 31–38).

import Mathlib
import Definitions.Def_NishtAbel2024_Syntax

/-!
# Chapter 5 of Nisht & Abel (2024): Operational Semantics, Reducibility Candidates, and `SCT_G`

This module formalizes the semantic definitions of Chapter 5 (pp. 31–38) of
Kanstantsin Nisht and Andreas Abel, *"Type-Based Termination Checking in Agda"* (2024):

1. **Section 5.1 (pp. 31–32)**:
   - Type and term substitutions `τ` and `σ` on expressions, eliminations, and clauses
   - Pattern matching `t / p ↘ τ; σ` (`MatchPat`), copattern matching `e / q ↘ τ; σ` (`MatchCopat`),
     and pattern-spine matching `e⃗ / q⃗ ↘ τ; σ` (`MatchSpine`)
   - Weak-head reduction `t ↦ t'` (`WhdStep`) and one-step reduction `t ⟶ t'` (`RedStep`,
     `ClauseRedStep`, `ClausesRedStep`)
   - Strong normalization `SN` (`t ∈ SN`)
2. **Section 5.2 (pp. 32–34)**:
   - Introduction terms `Intro` (`IsIntro`) and neutral terms `NE` (`IsNeutral`)
   - Weak-head spine simulation `r' ▷ r⃗` (`Simulates`: `∀ e⃗ t, r' e⃗ ↦ t ⟹ ∃ rₖ ∈ r⃗, rₖ e⃗ ↦ t`)
   - Girard–Tait reducibility candidates `CR` (`IsCandidate`), least candidate closure
     `candClosure`, and inflationary/deflationary fixpoints `μ^α F` and `ν^α F`
3. **Section 5.3 (pp. 34–35)**:
   - Semantic size ordinals `SizeOrd` (`O`), ordinal tuple conformance `β⃗ ≺_G α⃗`
     (`OrdConformsToGraph`), carrier `T := Fun × O⁺` (`SCTState`), and the semantic transition
     relation `SCT_G` (`SCTStep`)
4. **Section 5.4 (pp. 35–38)**:
   - Semantic evaluation of size expressions `⟦a⟧_ρ` (`evalSizeExp`) and semantic size contexts
     `ρ ∈ ⟦Ψ⟧` (`ValidSizeVal`, ordered by `SizeValLe`)
   - Semantic type and context interpretations `⟦A⟧_ρ`, `⟦Δ⟧`, `⟦Γ⟧_ρ`
   - Semantic validity of global signatures `⊨ Σ` (`SemSigValid`), guarded mutual-block validity
     `G, ⟦Ψ_f⟧ ⊨ Ξ` (`SemBlockGuardedValid`), semantic expression typing `𝒟, ℰ ⊨ r ∈ 𝒞`
     (`SemExprTyping`, `SemClausesTyping`), mutual block soundness `Σ ⊨ Ξ`
     (`SemMutualBlockValid`), and program soundness `⊨ (Σ; u)` (`SemProgramValid`)
-/

namespace NishtAbel2024

/-! ## Section 5.1: Pattern Matching, Weak-Head Reduction, and Strong Normalization (pp. 31–32) -/

/-- Type substitution `τ : List (TyVar × TypeExpr)` (Section 5.1, p. 31). -/
abbrev TySubst := List (TyVar × TypeExpr)

/-- Term substitution `σ : List (TermVar × Term)` (Section 5.1, p. 31). -/
abbrev TermSubst := List (TermVar × Term)

/-- Simultaneous size substitution `σ_s : List (SizeVar × SizeExp)`. -/
abbrev SizeSubst := List (SizeVar × SizeExp)

/-- Apply a list of type substitutions `τ` sequentially to a type expression `A`. -/
def TypeExpr.substTyList (τ : TySubst) (A : TypeExpr) : TypeExpr :=
  τ.foldl (fun acc p => acc.substTyVar p.1 p.2) A

/-- Bound term variables of a pattern `p`. -/
def Pat.boundTermVars : Pat → List TermVar
  | .var x => [x]
  | .unit => []
  | .pair p₁ p₂ => p₁.boundTermVars ++ p₂.boundTermVars
  | .cons _ p => p.boundTermVars
  | .tyPack _ p => p.boundTermVars

/-- Bound type variables of a pattern `p`. -/
def Pat.boundTyVars : Pat → List TyVar
  | .var _ => []
  | .unit => []
  | .pair p₁ p₂ => p₁.boundTyVars ++ p₂.boundTyVars
  | .cons _ p => p.boundTyVars
  | .tyPack X p => X :: p.boundTyVars

/-- Bound term variables of a copattern `q`. -/
def Copat.boundTermVars : Copat → List TermVar
  | .pat p => p.boundTermVars
  | .tyVar _ => []
  | .proj _ => []

/-- Bound type variables of a copattern `q`. -/
def Copat.boundTyVars : Copat → List TyVar
  | .pat p => p.boundTyVars
  | .tyVar X => [X]
  | .proj _ => []

/-- Bound term variables of a copattern spine `q⃗`. -/
def PatSpine.boundTermVars (qs : PatSpine) : List TermVar :=
  qs.flatMap Copat.boundTermVars

/-- Bound type variables of a copattern spine `q⃗`. -/
def PatSpine.boundTyVars (qs : PatSpine) : List TyVar :=
  qs.flatMap Copat.boundTyVars

mutual

/-- Substitute size expressions `σ_s` throughout a term `t` (`t[a⃗ / Ψ̂]`). -/
def Term.substSizes (σs : SizeSubst) : Term → Term
  | .var x => .var x
  | .funRef f as => .funRef f (as.map (·.subst σs))
  | .app r e => .app (r.substSizes σs) (e.substSizes σs)
  | .unit => .unit
  | .pair t₁ t₂ => .pair (t₁.substSizes σs) (t₂.substSizes σs)
  | .cons c ma t => .cons c (ma.map (·.subst σs)) (t.substSizes σs)
  | .pack G t => .pack (G.substSizes σs) (t.substSizes σs)
  | .lamClauses Ds => .lamClauses ( substSizesClauses σs Ds )
  | .ascr t A => .ascr (t.substSizes σs) (A.substSizes σs)

/-- Substitute size expressions `σ_s` in an elimination `e`. -/
def Elim.substSizes (σs : SizeSubst) : Elim → Elim
  | .term t => .term (t.substSizes σs)
  | .tyArg G => .tyArg (G.substSizes σs)
  | .proj d ma => .proj d (ma.map (·.subst σs))

/-- Substitute size expressions `σ_s` in a clause `D`. -/
def Clause.substSizes (σs : SizeSubst) : Clause → Clause
  | .mk qs t =>
      let bound := PatSpine.boundTyVars qs
      let σs' := σs.filter (fun p => !bound.contains p.1)
      .mk qs (t.substSizes σs')

/-- Helper: substitute size expressions `σ_s` across a list of clauses. -/
def substSizesClauses (σs : SizeSubst) : List Clause → List Clause
  | [] => []
  | D :: rest => D.substSizes σs :: substSizesClauses σs rest

end

mutual

/-- Substitute type expressions `τ` throughout a term `t` (`t τ`, Section 5.1, p. 31). -/
def Term.substTypes (τ : TySubst) : Term → Term
  | .var x => .var x
  | .funRef f as => .funRef f as
  | .app r e => .app (r.substTypes τ) (e.substTypes τ)
  | .unit => .unit
  | .pair t₁ t₂ => .pair (t₁.substTypes τ) (t₂.substTypes τ)
  | .cons c ma t => .cons c ma (t.substTypes τ)
  | .pack G t => .pack (G.substTyList τ) (t.substTypes τ)
  | .lamClauses Ds => .lamClauses (substTypesClauses τ Ds)
  | .ascr t A => .ascr (t.substTypes τ) (A.substTyList τ)

/-- Substitute type expressions `τ` in an elimination `e`. -/
def Elim.substTypes (τ : TySubst) : Elim → Elim
  | .term t => .term (t.substTypes τ)
  | .tyArg G => .tyArg (G.substTyList τ)
  | .proj d ma => .proj d ma

/-- Substitute type expressions `τ` in a clause `D`. -/
def Clause.substTypes (τ : TySubst) : Clause → Clause
  | .mk qs t =>
      let bound := PatSpine.boundTyVars qs
      let τ' := τ.filter (fun p => !bound.contains p.1)
      .mk qs (t.substTypes τ')

/-- Helper: substitute type expressions `τ` across a list of clauses. -/
def substTypesClauses (τ : TySubst) : List Clause → List Clause
  | [] => []
  | D :: rest => D.substTypes τ :: substTypesClauses τ rest

end

mutual

/-- Substitute terms `σ` for term variables throughout a term `t` (`t σ`, Section 5.1, p. 31). -/
def Term.substTerms (σ : TermSubst) : Term → Term
  | .var x =>
      match σ.find? (fun p => p.1 == x) with
      | some (_, s) => s
      | none => .var x
  | .funRef f as => .funRef f as
  | .app r e => .app (r.substTerms σ) (e.substTerms σ)
  | .unit => .unit
  | .pair t₁ t₂ => .pair (t₁.substTerms σ) (t₂.substTerms σ)
  | .cons c ma t => .cons c ma (t.substTerms σ)
  | .pack G t => .pack G (t.substTerms σ)
  | .lamClauses Ds => .lamClauses (substTermsClauses σ Ds)
  | .ascr t A => .ascr (t.substTerms σ) A

/-- Substitute terms `σ` in an elimination `e`. -/
def Elim.substTerms (σ : TermSubst) : Elim → Elim
  | .term t => .term (t.substTerms σ)
  | .tyArg G => .tyArg G
  | .proj d ma => .proj d ma

/-- Substitute terms `σ` in a clause `D`. -/
def Clause.substTerms (σ : TermSubst) : Clause → Clause
  | .mk qs t =>
      let bound := PatSpine.boundTermVars qs
      let σ' := σ.filter (fun p => !bound.contains p.1)
      .mk qs (t.substTerms σ')

/-- Helper: substitute terms `σ` across a list of clauses. -/
def substTermsClauses (σ : TermSubst) : List Clause → List Clause
  | [] => []
  | D :: rest => D.substTerms σ :: substTermsClauses σ rest

end

/-- Pattern matching judgment `t / p ↘ τ; σ` (Section 5.1, p. 31). -/
inductive MatchPat : Term → Pat → TySubst → TermSubst → Prop where
  | unit (t : Term) :
      MatchPat t .unit [] []
  | var (t : Term) (x : TermVar) :
      MatchPat t (.var x) [] [(x, t)]
  | pair {t₁ t₂ : Term} {p₁ p₂ : Pat} {τ₁ τ₂ : TySubst} {σ₁ σ₂ : TermSubst} :
      MatchPat t₁ p₁ τ₁ σ₁ →
      MatchPat t₂ p₂ τ₂ σ₂ →
      MatchPat (.pair t₁ t₂) (.pair p₁ p₂) (τ₁ ++ τ₂) (σ₁ ++ σ₂)
  | cons {c : ConsName} {ma : Option SizeExp} {t : Term} {p : Pat}
      {τ : TySubst} {σ : TermSubst} :
      MatchPat t p τ σ →
      MatchPat (.cons c ma t) (.cons c p) τ σ
  | tyPack {G : TypeExpr} {t : Term} {X : TyVar} {p : Pat}
      {τ : TySubst} {σ : TermSubst} :
      MatchPat t p τ σ →
      MatchPat (.pack G t) (.tyPack X p) ((X, G) :: τ) σ

/-- Copattern matching judgment `e / q ↘ τ; σ` (Section 5.1, pp. 31–32). -/
inductive MatchCopat : Elim → Copat → TySubst → TermSubst → Prop where
  | pat {t : Term} {p : Pat} {τ : TySubst} {σ : TermSubst} :
      MatchPat t p τ σ →
      MatchCopat (.term t) (.pat p) τ σ
  | tyVar (G : TypeExpr) (X : TyVar) :
      MatchCopat (.tyArg G) (.tyVar X) [(X, G)] []
  | proj (d : ProjName) (ma : Option SizeExp) :
      MatchCopat (.proj d ma) (.proj d) [] []

/-- Spine matching judgment `e⃗ / q⃗ ↘ τ; σ` (Section 5.1, p. 32). -/
inductive MatchSpine : List Elim → PatSpine → TySubst → TermSubst → Prop where
  | nil :
      MatchSpine [] [] [] []
  | cons {e : Elim} {es : List Elim} {q : Copat} {qs : PatSpine}
      {τ₁ τ₂ : TySubst} {σ₁ σ₂ : TermSubst} :
      MatchCopat e q τ₁ σ₁ →
      MatchSpine es qs τ₂ σ₂ →
      MatchSpine (e :: es) (q :: qs) (τ₁ ++ τ₂) (σ₁ ++ σ₂)

/-- Weak-head reduction `t ↦ t'` in global signature `sig` and mutual block `Ξ`
(Section 5.1, pp. 31–32):
- `(t : A) e⃗ ↦ t e⃗` (type ascription erasure)
- `λ D⃗ e⃗ e⃗' ↦ (t[τ][σ]) e⃗'` when `{q⃗ → t} ∈ D⃗` and `e⃗ / q⃗ ↘ τ; σ`
- `(f a⃗) e⃗ e⃗' ↦ (t[a⃗ / Ψ̂][τ][σ]) e⃗'` when `(f : ∀Ψ. A = D⃗) ∈ sig ++ Ξ`, `{q⃗ → t} ∈ D⃗`,
  and `e⃗ / q⃗ ↘ τ; σ`. -/
inductive WhdStep (sig : GlobalSig) (Ξ : MutualBlock) : Term → Term → Prop where
  | ascr (t : Term) (A : TypeExpr) (es : List Elim) :
      WhdStep sig Ξ (Term.appSpine (.ascr t A) es) (Term.appSpine t es)
  | lamClause {Ds : List Clause} {qs : PatSpine} {t : Term}
      {es es' : List Elim} {τ : TySubst} {σ : TermSubst} :
      Clause.mk qs t ∈ Ds →
      MatchSpine es qs τ σ →
      WhdStep sig Ξ
        (Term.appSpine (.lamClauses Ds) (es ++ es'))
        (Term.appSpine ((t.substTypes τ).substTerms σ) es')
  | funClause {decl : FunDecl} {as : List SizeExp} {qs : PatSpine} {t : Term}
      {es es' : List Elim} {τ : TySubst} {σ : TermSubst} :
      decl ∈ sig ++ Ξ →
      Clause.mk qs t ∈ decl.clauses →
      MatchSpine es qs τ σ →
      WhdStep sig Ξ
        (Term.appSpine (.funRef decl.name as) (es ++ es'))
        (Term.appSpine (((t.substSizes (decl.sizeParams.dom.zip as)).substTypes τ).substTerms σ) es')

mutual

/-- One-step full reduction `t ⟶ t'` on terms (Section 5.1, p. 32). -/
inductive RedStep (sig : GlobalSig) (Ξ : MutualBlock) : Term → Term → Prop where
  | whd {t t' : Term} :
      WhdStep sig Ξ t t' →
      RedStep sig Ξ t t'
  | pairLeft {t₁ t₁' t₂ : Term} :
      RedStep sig Ξ t₁ t₁' →
      RedStep sig Ξ (.pair t₁ t₂) (.pair t₁' t₂)
  | pairRight {t₁ t₂ t₂' : Term} :
      RedStep sig Ξ t₂ t₂' →
      RedStep sig Ξ (.pair t₁ t₂) (.pair t₁ t₂')
  | cons {c : ConsName} {ma : Option SizeExp} {t t' : Term} :
      RedStep sig Ξ t t' →
      RedStep sig Ξ (.cons c ma t) (.cons c ma t')
  | pack {G : TypeExpr} {t t' : Term} :
      RedStep sig Ξ t t' →
      RedStep sig Ξ (.pack G t) (.pack G t')
  | appFun {r r' : Term} {e : Elim} :
      RedStep sig Ξ r r' →
      RedStep sig Ξ (.app r e) (.app r' e)
  | appArg {r s s' : Term} :
      RedStep sig Ξ s s' →
      RedStep sig Ξ (.app r (.term s)) (.app r (.term s'))
  | ascr {t t' : Term} {A : TypeExpr} :
      RedStep sig Ξ t t' →
      RedStep sig Ξ (.ascr t A) (.ascr t' A)
  | lamClauses {Ds Ds' : List Clause} :
      ClausesRedStep sig Ξ Ds Ds' →
      RedStep sig Ξ (.lamClauses Ds) (.lamClauses Ds')

/-- One-step reduction `D ⟶ D'` on a single clause `{q⃗ → t}` (Section 5.1, p. 32). -/
inductive ClauseRedStep (sig : GlobalSig) (Ξ : MutualBlock) : Clause → Clause → Prop where
  | body {qs : PatSpine} {t t' : Term} :
      RedStep sig Ξ t t' →
      ClauseRedStep sig Ξ (.mk qs t) (.mk qs t')

/-- One-step reduction `D⃗₁, D, D⃗₂ ⟶ D⃗₁, D', D⃗₂` on a list of clauses (Section 5.1, p. 32). -/
inductive ClausesRedStep (sig : GlobalSig) (Ξ : MutualBlock) :
    List Clause → List Clause → Prop where
  | head {D D' : Clause} {rest : List Clause} :
      ClauseRedStep sig Ξ D D' →
      ClausesRedStep sig Ξ (D :: rest) (D' :: rest)
  | tail {D : Clause} {rest rest' : List Clause} :
      ClausesRedStep sig Ξ rest rest' →
      ClausesRedStep sig Ξ (D :: rest) (D :: rest')

end

/-- Strong normalization `t ∈ SN` with respect to `RedStep sig Ξ` (Section 5.2, p. 32):
every reduction sequence starting from `t` terminates. -/
def SN (sig : GlobalSig) (Ξ : MutualBlock) (t : Term) : Prop :=
  Acc (fun t' t => RedStep sig Ξ t t') t

/-! ## Section 5.2: Reducibility Candidates and Simulation (pp. 32–34) -/

/-- The set `Intro` of introduction terms `() | (t₁, t₂) | c [a] t | ⟨G, t⟩`
(Section 5.2, p. 33). -/
def IsIntro : Term → Prop
  | .unit => True
  | .pair _ _ => True
  | .cons _ _ _ => True
  | .pack _ _ => True
  | _ => False

/-- Neutral terms `t ∈ NE` (Section 5.2, p. 33): `t` is not an introduction form (`t ∉ Intro`),
and either `t` is a weak-head redex or `t e⃗` is not a weak-head redex for any elimination spine `e⃗`. -/
def IsNeutral (sig : GlobalSig) (Ξ : MutualBlock) (t : Term) : Prop :=
  ¬ IsIntro t ∧
  ((∃ t', WhdStep sig Ξ t t') ∨
   (∀ (es : List Elim) (t' : Term), ¬ WhdStep sig Ξ (Term.appSpine t es) t'))

/-- Weak-head spine simulation `r' ▷ r⃗` (Section 5.2, p. 33):
`∀ e⃗, ∀ t, r' e⃗ ↦ t ⟹ ∃ rₖ ∈ r⃗, rₖ e⃗ ↦ t`. -/
def Simulates (sig : GlobalSig) (Ξ : MutualBlock) (r' : Term) (rs : List Term) : Prop :=
  ∀ (es : List Elim) (t : Term),
    WhdStep sig Ξ (Term.appSpine r' es) t →
    ∃ rₖ ∈ rs, WhdStep sig Ξ (Term.appSpine rₖ es) t

/-- Girard–Tait reducibility candidate `𝒜 ∈ CR` (Section 5.2, p. 33):
1. `𝒜 ⊆ SN`
2. If `t ∈ 𝒜` and `t ⟶ t'`, then `t' ∈ 𝒜` (closure under reduction)
3. If `t ∈ NE` and `{t' | t ⟶ t'} ⊆ 𝒜`, then `t ∈ 𝒜` (neutral closure)
4. If `t ∉ Intro`, `{t' | t ⟶ t'} ⊆ 𝒜`, and `t ▷ t⃗` with `t⃗ ⊆ 𝒜`, then `t ∈ 𝒜`
   (closure under simulation). -/
structure IsCandidate (sig : GlobalSig) (Ξ : MutualBlock) (𝒜 : Set Term) : Prop where
  subset_sn : ∀ t ∈ 𝒜, SN sig Ξ t
  red_closed : ∀ t ∈ 𝒜, ∀ t', RedStep sig Ξ t t' → t' ∈ 𝒜
  neutral_closed :
    ∀ t, IsNeutral sig Ξ t → (∀ t', RedStep sig Ξ t t' → t' ∈ 𝒜) → t ∈ 𝒜
  sim_closed :
    ∀ t (ts : List Term),
      ¬ IsIntro t →
      (∀ t', RedStep sig Ξ t t' → t' ∈ 𝒜) →
      (∀ s ∈ ts, s ∈ 𝒜) →
      Simulates sig Ξ t ts →
      t ∈ 𝒜

/-- Least reducibility candidate `𝒜̄` containing `X ⊆ SN` (Section 5.2, p. 33):
intersection of all reducibility candidates `𝒞 ∈ CR` such that `X ∩ SN ⊆ 𝒞`. -/
def candClosure (sig : GlobalSig) (Ξ : MutualBlock) (X : Set Term) : Set Term :=
  { t | SN sig Ξ t ∧ ∀ 𝒞 : Set Term, IsCandidate sig Ξ 𝒞 → (∀ s ∈ X, SN sig Ξ s → s ∈ 𝒞) → t ∈ 𝒞 }

/-! ## Section 5.3: Semantics of Invocation Graphs and `SCT_G` (pp. 34–35) -/

/-- Semantic size ordinals `α, β ∈ O` (Section 5.2, p. 33 & Section 5.4.1, p. 35):
represented as pairs `(tier, offset)` ordered lexicographically, where finite ordinals `< ∞`
have `tier = 0` (`⟨0, n⟩`) and transfinite ordinals `∞ + n` have `tier = 1` (`⟨1, n⟩`). -/
structure SizeOrd where
  tier : Nat
  offset : Nat
  deriving DecidableEq, Repr

namespace SizeOrd

/-- Ordinal `0`. -/
def zero : SizeOrd := ⟨0, 0⟩

/-- Limit ordinal `∞` (`ω₁`, p. 33). -/
def infty : SizeOrd := ⟨1, 0⟩

/-- Finite ordinal `< ∞` from a natural number `n`. -/
def fin (n : Nat) : SizeOrd := ⟨0, n⟩

/-- Ordinal `∞ + n`. -/
def infAdd (n : Nat) : SizeOrd := ⟨1, n⟩

/-- Shift an ordinal `α` by `+ n`: `(tier, offset) + n = (tier, offset + n)`. -/
def shift (α : SizeOrd) (n : Nat) : SizeOrd :=
  ⟨α.tier, α.offset + n⟩

/-- Strict order `α < β` on `SizeOrd`. -/
def lt (α β : SizeOrd) : Prop :=
  α.tier < β.tier ∨ (α.tier = β.tier ∧ α.offset < β.offset)

/-- Non-strict order `α ≤ β` on `SizeOrd`. -/
def le (α β : SizeOrd) : Prop :=
  α.tier < β.tier ∨ (α.tier = β.tier ∧ α.offset ≤ β.offset)

instance : DecidableRel lt := fun α β =>
  inferInstanceAs (Decidable (α.tier < β.tier ∨ (α.tier = β.tier ∧ α.offset < β.offset)))

instance : DecidableRel le := fun α β =>
  inferInstanceAs (Decidable (α.tier < β.tier ∨ (α.tier = β.tier ∧ α.offset ≤ β.offset)))

instance : LT SizeOrd := ⟨lt⟩
instance : LE SizeOrd := ⟨le⟩

/-- Minimum `min(α, β)` of two semantic ordinals (Section 5.4.1, p. 35). -/
def min (α β : SizeOrd) : SizeOrd :=
  if le α β then α else β

end SizeOrd

/-- Semantic conformance `β⃗ ≺_G α⃗` of ordinal tuples `α⃗, β⃗ ∈ O⁺` to an invocation graph `G`
(Section 4.4, p. 26 & Section 5.3, p. 34):
Notice that in Section 5.3 (p. 34, Theorem 1), `((f, α⃗), (g, β⃗)) ∈ SCT_G` iff
`∃ G ∈ G(f, g), β⃗ ≺_G α⃗`, where `L_G` indexes `β⃗` (`|β⃗| = |L_G|`) and `R_G` indexes `α⃗`
(`|α⃗| = |R_G|`), so `E_G(lᵢ, rⱼ) = < ⟹ βᵢ < αⱼ` and `E_G(lᵢ, rⱼ) = ≤ ⟹ βᵢ ≤ αⱼ`. -/
def OrdConformsToGraph (G : InvGraph) (βs αs : List SizeOrd) : Prop :=
  ConformsToGraph SizeOrd.lt SizeOrd.le G βs αs

/-- Carrier element `(f, α⃗) ∈ T := Fun × O⁺` of the semantic termination relation `SCT_G`
(Section 5.3, p. 34). -/
structure SCTState where
  fn : FunName
  sizes : List SizeOrd
  deriving DecidableEq, Repr

/-- The semantic invocation-graph transition relation `SCT_G ⊂ T × T` (Section 5.3, p. 34):
`((f, α⃗), (g, β⃗)) ∈ SCT_G` iff `∃ G ∈ G(f, g), β⃗ ≺_G α⃗`. -/
def SCTStep (𝒢 : InvGraphFamily) (src dst : SCTState) : Prop :=
  ∃ G ∈ 𝒢.graphs src.fn dst.fn, OrdConformsToGraph G dst.sizes src.sizes

/-- A call-chain step `(g, β⃗) ≺ (f, α⃗)` in the reversed orientation used for well-foundedness
in Lean (`WellFounded (SCTCallRel 𝒢)` means there is no infinite chain `(f₁, α⃗₁), (f₂, α⃗₂), ...`
with `SCTStep 𝒢 (fᵢ, α⃗ᵢ) (fᵢ₊₁, α⃗ᵢ₊₁)`, Theorem 1, pp. 34–35). -/
def SCTCallRel (𝒢 : InvGraphFamily) (callee caller : SCTState) : Prop :=
  SCTStep 𝒢 caller callee

/-! ## Section 5.4: Interpretation of Sizes, Types, Mutual Blocks, and Programs (pp. 35–38) -/

/-- Semantic size valuation `ρ : SizeVar → SizeOrd` (Section 5.4.1, p. 35). -/
abbrev SizeVal := SizeVar → SizeOrd

/-- Update a size valuation `ρ` at variable `i` with ordinal `α`. -/
def SizeVal.update (ρ : SizeVal) (i : SizeVar) (α : SizeOrd) : SizeVal :=
  fun j => if j == i then α else ρ j

/-- Construct a size valuation from a list of bindings `(iₖ, αₖ)`, defaulting to `0`. -/
def SizeVal.ofList (bindings : List (SizeVar × SizeOrd)) : SizeVal :=
  fun i =>
    match bindings.find? (fun p => p.1 == i) with
    | some (_, α) => α
    | none => SizeOrd.zero

/-- Semantic evaluation `⟦a^∧⟧_ρ ∈ O` of a formal minimum `a^∧` (Section 5.4.1, p. 35):
- `⟦(i + n)⟧_ρ = ρ(i) + n`
- `⟦a^∧ ∧ (i + n)⟧_ρ = min(⟦a^∧⟧_ρ, ρ(i) + n)`. -/
def evalSizeMin (ρ : SizeVal) (m : SizeMin) : SizeOrd :=
  m.tail.foldl (fun acc sv => SizeOrd.min acc ((ρ sv.var).shift sv.shift))
    ((ρ m.head.var).shift m.head.shift)

/-- Semantic evaluation `⟦a⟧_ρ ∈ O` of a size expression `a` (Section 5.4.1, p. 35):
- `⟦∞ + n⟧_ρ = ∞ + n`
- `⟦a^∧⟧_ρ = evalSizeMin ρ a^∧`. -/
def evalSizeExp (ρ : SizeVal) : SizeExp → SizeOrd
  | .inf n => SizeOrd.infAdd n
  | .meet a => evalSizeMin ρ a

/-- Valid semantic size valuation `ρ ∈ ⟦Ψ⟧` (Section 5.4.1, pp. 35–36):
for every declaration `(i : π(< a)) ∈ Ψ`, `ρ(i) < ⟦a⟧_ρ`. -/
def ValidSizeVal (Ψ : SizeCtx) (ρ : SizeVal) : Prop :=
  ∀ d ∈ Ψ, SizeOrd.lt (ρ d.var) (evalSizeExp ρ d.bound)

/-- Polarized semantic valuation ordering `ρ ≤ ρ' ∈ 𝒟 := ⟦Ψ⟧` (Section 5.4.1, Theorem 2, p. 36):
both `ρ` and `ρ'` belong to `⟦Ψ⟧`, and for every variable `(i : π(< a)) ∈ Ψ`:
- if `π = ◦`, `ρ(i) = ρ'(i)`
- if `π = +`, `ρ(i) ≤ ρ'(i)`
- if `π = −`, `ρ'(i) ≤ ρ(i)`. -/
def SizeValLe (Ψ : SizeCtx) (ρ ρ' : SizeVal) : Prop :=
  ValidSizeVal Ψ ρ ∧
  ValidSizeVal Ψ ρ' ∧
  ∀ d ∈ Ψ,
    match d.pol with
    | .mixed => ρ d.var = ρ' d.var
    | .pos => SizeOrd.le (ρ d.var) (ρ' d.var)
    | .neg => SizeOrd.le (ρ' d.var) (ρ d.var)
    | .top => True

/-- A tuple of semantic ordinals `α⃗` belongs to `⟦Ψ⟧` (`α⃗ ∈ ⟦Ψ⟧`, Section 5.4.2, p. 36)
when `|α⃗| = |Ψ|` and the induced valuation `ρ = [α⃗ / Ψ̂]` satisfies `ValidSizeVal Ψ ρ`. -/
def ValidSizeTuple (Ψ : SizeCtx) (αs : List SizeOrd) : Prop :=
  αs.length = Ψ.length ∧
  ValidSizeVal Ψ (SizeVal.ofList (Ψ.dom.zip αs))

/-- Well-foundedness of the strict order `SizeOrd.lt` on semantic ordinals `O`. -/
theorem SizeOrd.lt_wf : WellFounded SizeOrd.lt := by
  constructor
  intro α
  rcases α with ⟨t, o⟩
  induction t using Nat.strongRecOn generalizing o with
  | ind t iht =>
    induction o using Nat.strongRecOn with
    | ind o iho =>
      constructor
      rintro ⟨t', o'⟩ (ht | ⟨rfl, ho⟩)
      · exact iht t' ht o'
      · exact iho o' ho

/-- Inflationary fixpoint operator `μ^α F = ⋃_{β < α} F(μ^β F)` on reducibility candidates
(Section 5.2, p. 33), closed under `candClosure`. -/
def muFixpoint (sig : GlobalSig) (Ξ : MutualBlock)
    (F : Set Term → Set Term) (α : SizeOrd) : Set Term :=
  WellFounded.fix SizeOrd.lt_wf
    (fun α ih =>
      candClosure sig Ξ
        { t | ∃ (β : SizeOrd) (hβ : SizeOrd.lt β α), t ∈ F (ih β hβ) })
    α

/-- Deflationary fixpoint operator `ν^α F = ⋂_{β < α} F(ν^β F)` on reducibility candidates
(Section 5.2, p. 33), closed under `candClosure`. -/
def nuFixpoint (sig : GlobalSig) (Ξ : MutualBlock)
    (F : Set Term → Set Term) (α : SizeOrd) : Set Term :=
  WellFounded.fix SizeOrd.lt_wf
    (fun α ih =>
      candClosure sig Ξ
        { t | ∀ (β : SizeOrd) (hβ : SizeOrd.lt β α), t ∈ F (ih β hβ) })
    α

/-- Semantic candidate environment `η : TyVar → Set Term` mapping type variables `X` to
reducibility candidates (Section 5.2, p. 33). -/
abbrev CandEnv := TyVar → Set Term

/-- Update a candidate environment `η` at type variable `X` with candidate `𝒳`. -/
def CandEnv.update (η : CandEnv) (X : TyVar) (𝒳 : Set Term) : CandEnv :=
  fun Y => if Y == X then 𝒳 else η Y

/-- Default candidate environment mapping every type variable `X` to `candClosure sig Ξ ∅`. -/
def CandEnv.empty (sig : GlobalSig) (Ξ : MutualBlock) : CandEnv :=
  fun _ => candClosure sig Ξ ∅

/-- Evaluate a functor branch/field `F` (`λX : ι. body` or general `TypeExpr`) at a candidate `𝒳`
by extending `η` at `X` (or variable `0` if unannotated) and calling `evalfn`. -/
def evalBranchAt (evalfn : SizeVal → CandEnv → TypeExpr → Set Term)
    (ρ : SizeVal) (η : CandEnv) (F : TypeExpr) (𝒳 : Set Term) : Set Term :=
  match F with
  | .lam X _ body => evalfn ρ (η.update X 𝒳) body
  | body => evalfn ρ (η.update 0 𝒳) body

mutual

/-- Semantic Girard–Tait reducibility candidate interpretation `⟦A⟧_{ρ, η} ⊆ SN` of a type
expression `A` under size valuation `ρ` and candidate environment `η` (Section 5.2, pp. 32–34 &
Section 5.4, pp. 35–37):
- `⟦1⟧_{ρ, η} = candClosure { () }`
- `⟦A₁ × A₂⟧_{ρ, η} = candClosure { (t₁, t₂) | t₁ ∈ ⟦A₁⟧_{ρ, η} ∧ t₂ ∈ ⟦A₂⟧_{ρ, η} }`
- `⟦A → B⟧_{ρ, η} = candClosure { r | ∀ s ∈ ⟦A⟧_{ρ, η}, r s ∈ ⟦B⟧_{ρ, η} }`
- `⟦∀(j < a). B⟧_{ρ, η} = candClosure { r | ∀ β < ⟦a^↑⟧_ρ, ∀ b, ⟦b⟧_ρ = β → r b ∈ ⟦B⟧_{ρ[j ↦ β], η} }`
- `⟦∀_κ (λX. B)⟧_{ρ, η} = candClosure { r | ∀ G 𝒳, IsCandidate 𝒳 → r G ∈ ⟦B⟧_{ρ, η[X ↦ 𝒳]} }`
- `⟦∃(j < a). B⟧_{ρ, η} = candClosure { ⟨b, t⟩ | ∃ β < ⟦a^↑⟧_ρ, t ∈ ⟦B⟧_{ρ[j ↦ β], η} }`
- `⟦∃_κ (λX. B)⟧_{ρ, η} = candClosure { ⟨G, t⟩ | ∃ 𝒳, IsCandidate 𝒳 ∧ t ∈ ⟦B⟧_{ρ, η[X ↦ 𝒳]} }`
- `⟦μ^a S⟧_{ρ, η} = μ^{⟦a^↑⟧_ρ} (fun 𝒳 => ⋃_{(c, Sc) ∈ S} { c [b] t | t ∈ ⟦Sc⟧(𝒳) })`
- `⟦ν^a R⟧_{ρ, η} = ν^{⟦a^↑⟧_ρ} (fun 𝒳 => { r | ∀ (d, Rd) ∈ R, ∀ ma, r .d [ma] ∈ ⟦Rd⟧(𝒳) })`. -/
def evalTypeWith (sig : GlobalSig) (Ξ : MutualBlock)
    (ρ : SizeVal) (η : CandEnv) : TypeExpr → Set Term
  | .atom .unit =>
      candClosure sig Ξ { t | t = .unit }
  | .atom (.var X) =>
      candClosure sig Ξ (η X)
  | .atom _ =>
      candClosure sig Ξ ∅
  | .lam X _ body =>
      evalTypeWith sig Ξ ρ (η.update X (candClosure sig Ξ ∅)) body
  | .app (.app (.atom .prod) A₁) A₂ =>
      let C₁ := evalTypeWith sig Ξ ρ η A₁
      let C₂ := evalTypeWith sig Ξ ρ η A₂
      candClosure sig Ξ { t | ∃ t₁ ∈ C₁, ∃ t₂ ∈ C₂, t = .pair t₁ t₂ }
  | .app (.app (.atom .arr) A) B =>
      let CA := evalTypeWith sig Ξ ρ η A
      let CB := evalTypeWith sig Ξ ρ η B
      candClosure sig Ξ { r | ∀ s ∈ CA, Term.app r (.term s) ∈ CB }
  | .app (.atom (.all (.lt a))) (.lam j _ B) =>
      candClosure sig Ξ
        { r | ∀ (β : SizeOrd) (b : SizeExp),
            SizeOrd.lt β (evalSizeExp ρ a.boundNorm) →
            Term.app r (.tyArg (.atom (.size b))) ∈
              evalTypeWith sig Ξ (ρ.update j β) η B }
  | .app (.atom (.all _)) (.lam X _ B) =>
      candClosure sig Ξ
        { r | ∀ (G : TypeExpr) (𝒳 : Set Term),
            IsCandidate sig Ξ 𝒳 →
            Term.app r (.tyArg G) ∈ evalTypeWith sig Ξ ρ (η.update X 𝒳) B }
  | .app (.atom (.ex (.lt a))) (.lam j _ B) =>
      candClosure sig Ξ
        { p | ∃ (β : SizeOrd) (b : SizeExp) (t : Term),
            SizeOrd.lt β (evalSizeExp ρ a.boundNorm) ∧
            t ∈ evalTypeWith sig Ξ (ρ.update j β) η B ∧
            p = .pack (.atom (.size b)) t }
  | .app (.atom (.ex _)) (.lam X _ B) =>
      candClosure sig Ξ
        { p | ∃ (G : TypeExpr) (𝒳 : Set Term) (t : Term),
            IsCandidate sig Ξ 𝒳 ∧
            t ∈ evalTypeWith sig Ξ ρ (η.update X 𝒳) B ∧
            p = .pack G t }
  | .app (.lam X _ body) G =>
      let CG := evalTypeWith sig Ξ ρ η G
      evalTypeWith sig Ξ ρ (η.update X CG) body
  | .app F G =>
      let CG := evalTypeWith sig Ξ ρ η G
      evalTypeWith sig Ξ ρ (η.update 0 CG) F
  | .mu a S =>
      muFixpoint sig Ξ
        (fun 𝒳 => evalDataBranches sig Ξ ρ η 𝒳 S)
        (evalSizeExp ρ a.boundNorm)
  | .nu a R =>
      nuFixpoint sig Ξ
        (fun 𝒳 => evalCodataFields sig Ξ ρ η 𝒳 R)
        (evalSizeExp ρ a.boundNorm)

/-- Helper: interpret inductive constructor branches `S` at recursive step candidate `𝒳`. -/
def evalDataBranches (sig : GlobalSig) (Ξ : MutualBlock)
    (ρ : SizeVal) (η : CandEnv) (𝒳 : Set Term) :
    List (Nat × TypeExpr) → Set Term
  | [] => ∅
  | (c, .lam X _ body) :: rest =>
      { term | ∃ (ma : Option SizeExp) (t : Term),
          t ∈ evalTypeWith sig Ξ ρ (η.update X 𝒳) body ∧
          term = .cons c ma t } ∪
      evalDataBranches sig Ξ ρ η 𝒳 rest
  | (c, body) :: rest =>
      { term | ∃ (ma : Option SizeExp) (t : Term),
          t ∈ evalTypeWith sig Ξ ρ (η.update 0 𝒳) body ∧
          term = .cons c ma t } ∪
      evalDataBranches sig Ξ ρ η 𝒳 rest

/-- Helper: interpret coinductive record projection fields `R` at recursive step candidate `𝒳`. -/
def evalCodataFields (sig : GlobalSig) (Ξ : MutualBlock)
    (ρ : SizeVal) (η : CandEnv) (𝒳 : Set Term) :
    List (Nat × TypeExpr) → Set Term
  | [] => { r | SN sig Ξ r }
  | (d, .lam X _ body) :: rest =>
      { r | ∀ ma : Option SizeExp,
          Term.app r (.proj d ma) ∈ evalTypeWith sig Ξ ρ (η.update X 𝒳) body } ∩
      evalCodataFields sig Ξ ρ η 𝒳 rest
  | (d, body) :: rest =>
      { r | ∀ ma : Option SizeExp,
          Term.app r (.proj d ma) ∈ evalTypeWith sig Ξ ρ (η.update 0 𝒳) body } ∩
      evalCodataFields sig Ξ ρ η 𝒳 rest

end

/-- Semantic interpretation `⟦A⟧_ρ ⊆ SN` of a type expression `A` under size valuation `ρ`
in global signature `sig` and mutual block `Ξ` (Section 5.2, p. 33 & Section 5.4, p. 36). -/
def evalType (sig : GlobalSig) (Ξ : MutualBlock) (ρ : SizeVal) (A : TypeExpr) : Set Term :=
  evalTypeWith sig Ξ ρ (CandEnv.empty sig Ξ) A

/-- Semantic kinding context `𝒟 := ⟦Δ⟧` (Section 5.4.2, p. 36):
the set of valid size valuations `ρ ∈ ⟦Δ.sizes⟧`. -/
def evalKindingCtx (Δ : KindingCtx) : Set SizeVal :=
  { ρ | ValidSizeVal Δ.sizes ρ }

/-- Semantic term context `ℰ(ρ) := ⟦Γ⟧_ρ` (Section 5.4.2, p. 36):
term substitutions `σ` mapping every `(x, A) ∈ Γ` to a term `s ∈ ⟦A⟧_ρ`. -/
def evalTermCtx (sig : GlobalSig) (Ξ : MutualBlock) (Γ : TermCtx) (ρ : SizeVal) : Set TermSubst :=
  { σ | ∀ x A, (x, A) ∈ Γ →
      ∃ s, σ.find? (fun p => p.1 == x) = some (x, s) ∧ s ∈ evalType sig Ξ ρ A }

/-- Semantic validity of a global signature `⊨ Σ` (Section 5.4.2, p. 36):
for every `(f : ∀Ψ. A = D⃗) ∈ Σ` and every well-formed size argument tuple `Ψ' ⊢ a⃗ ⇐ Ψ`
with `ρ ∈ ⟦Ψ'⟧`, `f a⃗ ∈ ⟦A⟧_{⟦a⃗⟧_ρ / Ψ̂}` (and `λ D⃗ ∈ SN`). -/
def SemSigValid (sig : GlobalSig) : Prop :=
  ∀ decl ∈ sig,
    SN sig [] (.lamClauses decl.clauses) ∧
    ∀ (as : List SizeExp) (ρ : SizeVal),
      ValidSizeTuple decl.sizeParams (as.map (evalSizeExp ρ)) →
      Term.funRef decl.name as ∈
        evalType sig [] (SizeVal.ofList (decl.sizeParams.dom.zip (as.map (evalSizeExp ρ)))) decl.ty

/-- Guarded semantic validity of a mutual block `G, ⟦Ψ_f⟧_ρ ⊨ Ξ` (Section 5.4.2, p. 36):
for every `(g : ∀Ψ_g. A = D⃗) ∈ Ξ` and every `α⃗ ∈ ⟦Ψ_g⟧`, if there exists `G ∈ G(f, g)`
such that `α⃗ ≺_G ⟦Ψ_f⟧_ρ`, then `g a⃗ ∈ ⟦A⟧_{α⃗ / Ψ̂_g}` for any `a⃗` with `⟦a⃗⟧_ρ = α⃗`. -/
def SemBlockGuardedValid (sig : GlobalSig) (Ξ : MutualBlock) (𝒢 : InvGraphFamily)
    (caller : FunName) (callerSizes : SizeCtx) (ρcaller : SizeVal) : Prop :=
  let αcaller := callerSizes.map (fun d => ρcaller d.var)
  ∀ decl ∈ Ξ, ∀ (as : List SizeExp) (ρ : SizeVal),
    let αcallee := as.map (evalSizeExp ρ)
    ValidSizeTuple decl.sizeParams αcallee →
    (∃ G ∈ 𝒢.graphs caller decl.name, OrdConformsToGraph G αcallee αcaller) →
    Term.funRef decl.name as ∈
      evalType sig Ξ (SizeVal.ofList (decl.sizeParams.dom.zip αcallee)) decl.ty

/-- Semantic expression typing judgment `𝒟, ℰ ⊨ r ∈ 𝒞` (Section 5.4.2, Theorem 3, pp. 36–37):
for every valuation `ρ ∈ 𝒟 = ⟦Δ⟧`, every type substitution `τ` mapping `Δ.types` to well-formed
types, and every term substitution `σ ∈ ℰ(ρ) = ⟦Γ⟧_ρ`, the substituted expression `(r[τ])[σ]`
belongs to `𝒞(ρ) = ⟦C⟧_ρ`. -/
def SemExprTyping (sig : GlobalSig) (Ξ : MutualBlock)
    (Δ : KindingCtx) (Γ : TermCtx) (r : Term) (C : TypeExpr) : Prop :=
  ∀ ρ ∈ evalKindingCtx Δ,
    ∀ σ ∈ evalTermCtx sig Ξ Γ ρ,
      r.substTerms σ ∈ evalType sig Ξ ρ C

/-- Semantic clause-list typing `𝒟, ℰ ⊨ λ D⃗ ∈ 𝒞` (Section 5.4.2, Theorem 3(3), p. 37). -/
def SemClausesTyping (sig : GlobalSig) (Ξ : MutualBlock)
    (Δ : KindingCtx) (Γ : TermCtx) (Ds : List Clause) (C : TypeExpr) : Prop :=
  SemExprTyping sig Ξ Δ Γ (.lamClauses Ds) C

/-- Semantic soundness of a mutual block `Σ ⊨ Ξ` (Section 5.4.3, p. 37):
every function `(f : (∀Ψ. A) = D⃗) ∈ Ξ` belongs to its semantic type candidate `⟦∀Ψ. A⟧`
(both its clause abstraction `λ D⃗` and every well-sized instantiation `f a⃗` are in `⟦A⟧_{α⃗ / Ψ̂}`). -/
def SemMutualBlockValid (sig : GlobalSig) (Ξ : MutualBlock) : Prop :=
  ∀ decl ∈ Ξ,
    SN (sig ++ Ξ) [] (.lamClauses decl.clauses) ∧
    ∀ (as : List SizeExp) (ρ : SizeVal),
      ValidSizeTuple decl.sizeParams (as.map (evalSizeExp ρ)) →
      Term.funRef decl.name as ∈
        evalType (sig ++ Ξ) []
          (SizeVal.ofList (decl.sizeParams.dom.zip (as.map (evalSizeExp ρ)))) decl.ty

/-- Semantic soundness of a complete program `⊨ (Σ; u)` defined as `u ∈ SN` (Section 5.4.3, p. 38). -/
def SemProgramValid (P : Program) : Prop :=
  SN P.sig.flatten [] P.main

end NishtAbel2024


