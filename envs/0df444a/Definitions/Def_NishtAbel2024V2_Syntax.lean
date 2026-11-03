-- Prove2me | Definitions.Def_NishtAbel2024V2_Syntax
-- name    : NishtAbel2024V2_Syntax
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-02T21:41:13.410201+00:00
-- url     : https://prove2.me/theorems/db165e17-6d93-4a2d-9aac-d40272f4a95f
-- title:
--   Repaired V2 Chapter 4 & Section 5.5: System F_ω^{cop, SCT} Syntax, Binder-Kind Shapes, Scope Discipline, and F_ω^{cop} Erasure
-- statement:
--   Repaired V2 formalization of Chapter 4 (pp. 19–30) and Section 5.5 (pp. 38–40) of Nisht & Abel (2024): adds binder kind-shape compatibility (`BinderKindShape`, `RefinedShape`, `annotationCompatible`) and domain kind well-formedness to `KindCheck.lam`, adds non-empty lexicographic measure hygiene (`measureIndices ≠ []`) to `CopMutualBlockTyping`, and includes the function-reference scoping discipline (`scopeBlockExtension`, `scopeOrderedBlocks`, `ScopedProgramTyping`) excluding duplicate names and forward references.
-- source:
--   Kanstantsin Nisht, "Type-Based Termination Checking in Agda", Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, TYPES 2024. Repaired V2 formalization.

import Std

/-!
# Syntax of System F_ω^{cop, SCT} and System F_ω^c (Nisht & Abel 2024, Chapter 4 & Appendix A)

Source: Kanstantsin Nisht (supervised by Andreas Abel),
"Type-Based Termination Checking in Agda",
Master's thesis, Chalmers University of Technology and University of Gothenburg, 2024
(and K. Nisht & A. Abel, *TYPES 2024*, Copenhagen), Chapter 4 (pp. 19–30) and Appendix A (pp. I–V).

This module formalizes:
- **Section 4.1.1 (p. 20) — Polarities (`Polarity`)**:
  Variance lattice `◦ ≤ +, − ≤ ⊤` (`Polarity.le`), commutative composition `π π'` (`Polarity.comp`),
  inverse composition `π⁻¹ π'` (`Polarity.invComp`), and context polarity scaling `πΔ`, `π⁻¹Δ`.
- **Section 4.1.2 (pp. 20–22) — Sizes (`SizeVar`, `SizeMin`, `SizeExp`, `SizeCtx`)**:
  Bounded meet-semilattice of size expressions (`∞ + n` and finite meets `a^∧` of shifted size
  variables `i + n`), size increment `a + m` (`SizeExp.shift`), bound normalization `a^↑`
  (`SizeExp.boundNorm`), bounded variable lookup `Ψ ⊢ i < a` (`SizeVarBound`), well-formed size
  expressions `Ψ ⊢ a` (`SizeWf`), well-formed size contexts `⊢ Ψ` (`SizeCtxWf`), size substitutions
  `Ψ ⊢ a⃗ ⇐ Ψ'` (`SizeSubstWf`), strict and non-strict size inequality judgments `Ψ ⊢ a < b`
  (`SizeLt`) and `Ψ ⊢ a ≤ b` (`SizeLe`), and consistent size-context extension `Ψ ⊢ ∃Ψ'`
  (`SizeCtxConsistentExt`).
- **Section 4.1.3 (p. 22) — Kinds and Subkinding (`SKind`, `Kind`)**:
  Simple kinds `ι` and polarized kinds `κ ::= * | <a | πκ₁ → κ₂`, kind well-formedness `Ψ ⊢ κ`
  (`KindWf`), subkinding `Ψ ⊢ κ ≤ κ'` (`SubKind`), and polarized comparison `Ψ ⊢ O ≤^π O'`
  for sizes (`SizeLePol`) and kinds (`KindLePol`).
- **Section 4.2 (pp. 23–25) — Types, Bidirectional Kind Checking, and Subtyping**:
  Type atoms `K`, type expressions `F, A` (including sized inductive fixpoints `μ^a S` and
  coinductive fixpoints `ν^a R`), normalizing application `F @_κ G` (`normTypeApp`), bidirectional
  kind inference `Δ ⊢ F ⇒ κ` (`KindInfer`) and kind checking `Δ ⊢ F ⇐ κ` (`KindCheck`),
  context well-formedness `Δ ⊢ Δ'` (`KindingCtxWf`) and `Δ ⊢ Γ` (`TermCtxWf`), and bidirectional
  polarized subtyping `Δ ⊢ F ≤^π F' ⇒ κ` (`SubTypeInfer`), `Δ ⊢ F ≤^π F' ⇐ κ` (`SubTypeCheck`),
  and `Δ ⊢ A ≤ A'` (`SubType`).
- **Section 4.3 (p. 25) — Patterns and Copattern Spines (`Pat`, `Copat`, `PatSpine`)**:
  Pattern typing `Δ; Γ ⊢_{Δ₀} p ⇐ A` (`PatTyping`) and copattern spine typing
  `Δ; Γ | A ⊢_{Δ₀} q⃗ ⇒ C` (`SpineTyping`).
- **Section 4.4 (pp. 26–27) — Invocation Graphs and the Size-Change Termination Criterion**:
  Bipartite invocation graphs `G = (L_G, R_G, E_G : L_G × R_G ⇀ {<, ≤})` (`InvGraph`), tuple
  conformance `s⃗ ≺_G s⃗'` (`ConformsToGraph`), graph composition `G₁ ∘ G₂` (`InvGraph.comp`),
  invocation graph families `G(f, g)` (`InvGraphFamily`), transitive closure `G*(f, g)`
  (`InvGraphClosure`), and the Size-Change Termination criterion `⊢ G` (`SCTValid`).
- **Sections 4.5–4.6 (pp. 27–30) & Appendix A (pp. I–V) — Terms, Clauses, Mutual Blocks, and Programs**:
  Terms, eliminations, clauses `D = {q⃗ → t}`, declarations `f : ∀Ψ. A = D⃗`, mutual blocks `Ξ`,
  global signatures `Σ`, and programs `P = (Σ; u)` for both sized System `F_ω^{cop, SCT}` and
  unannotated System `F_ω^c` (plus measure erasure `|Ξ|` from System `F_ω^{cop}`, Section 5.5, p. 38).
-/

namespace NishtAbel2024V2

/-! ## Section 4.1.1: Polarities (p. 20) -/

/-- Variance / polarity annotations `π ∈ {◦, +, −, ⊤}` (Section 4.1, Table 1, p. 20):
- `mixed` (`◦`): mixed / invariant polarity (bottom of the information lattice)
- `pos` (`+`): covariant polarity
- `neg` (`−`): contravariant polarity
- `top` (`⊤`): constant / unused polarity (top of the information lattice). -/
inductive Polarity where
  | mixed : Polarity
  | pos : Polarity
  | neg : Polarity
  | top : Polarity
  deriving DecidableEq, Repr

namespace Polarity

/-- Lattice ordering `π ≤ π'` on polarities (Section 4.1.1, p. 20):
`◦ ≤ + ≤ ⊤` and `◦ ≤ − ≤ ⊤`, with `π ≤ π`. -/
def le : Polarity → Polarity → Bool
  | .mixed, _ => true
  | _, .top => true
  | .pos, .pos => true
  | .neg, .neg => true
  | _, _ => false

/-- Lattice join `max(π₁, π₂)` in the polarity lattice `{◦ ≤ +, − ≤ ⊤}`. -/
def join : Polarity → Polarity → Polarity
  | .mixed, π => π
  | π, .mixed => π
  | .top, _ => .top
  | _, .top => .top
  | .pos, .pos => .pos
  | .neg, .neg => .neg
  | .pos, .neg => .top
  | .neg, .pos => .top

/-- Lattice meet `min(π₁, π₂)` in the polarity lattice `{◦ ≤ +, − ≤ ⊤}`. -/
def meet : Polarity → Polarity → Polarity
  | .top, π => π
  | π, .top => π
  | .mixed, _ => .mixed
  | _, .mixed => .mixed
  | .pos, .pos => .pos
  | .neg, .neg => .neg
  | .pos, .neg => .mixed
  | .neg, .pos => .mixed

/-- Polarity negation `−π` (flips `+` and `−`, fixes `◦` and `⊤`). -/
def negPol : Polarity → Polarity
  | .mixed => .mixed
  | .pos => .neg
  | .neg => .pos
  | .top => .top

/-- Commutative composition `π π'` of polarities (Section 4.1.1, p. 20):
- `⊤ π = ⊤`
- `◦ π = ◦` for `π ≠ ⊤`
- `+ π = π`
- `− − = +`. -/
def comp : Polarity → Polarity → Polarity
  | .top, _ => .top
  | _, .top => .top
  | .mixed, _ => .mixed
  | _, .mixed => .mixed
  | .pos, π => π
  | π, .pos => π
  | .neg, .neg => .pos

/-- Inverse composition `π⁻¹ π'` of polarities (Section 4.1.1, p. 20):
- `⊤⁻¹ π' = ◦`
- `◦⁻¹ ◦ = ◦`
- `◦⁻¹ π' = ⊤` for `π' ≠ ◦`
- `+⁻¹ π' = π'`
- `−⁻¹ π' = −π'`. -/
def invComp : Polarity → Polarity → Polarity
  | .top, _ => .mixed
  | .mixed, .mixed => .mixed
  | .mixed, _ => .top
  | .pos, π' => π'
  | .neg, π' => comp .neg π'

end Polarity

/-! ## Section 4.1.2: Sizes (pp. 20–22) -/

/-- Size variable identifier `i, j ∈ SizeVar` (Table 1, p. 20). -/
abbrev SizeVar := Nat

/-- A shifted size variable `(i + n)` occurring in a minimum `a^∧` (Table 1, p. 20). -/
structure ShiftedSizeVar where
  var : SizeVar
  shift : Nat := 0
  deriving DecidableEq, Repr

/-- Non-empty formal minimum `a^∧ = (i₁ + n₁) ∧ ... ∧ (iₖ + nₖ)` of shifted size variables
(Table 1, p. 20). Represented by its head and tail so it is non-empty by construction. -/
structure SizeMin where
  head : ShiftedSizeVar
  tail : List ShiftedSizeVar := []
  deriving DecidableEq, Repr

namespace SizeMin

/-- All shifted variable summands `(i + n)` in `a^∧`. -/
def toList (m : SizeMin) : List ShiftedSizeVar :=
  m.head :: m.tail

/-- Single shifted size variable `i + n` as a `SizeMin`. -/
def single (i : SizeVar) (n : Nat := 0) : SizeMin :=
  ⟨⟨i, n⟩, []⟩

/-- Append two `SizeMin` expressions `a^∧ ∧ b^∧`. -/
def append (m₁ m₂ : SizeMin) : SizeMin :=
  ⟨m₁.head, m₁.tail ++ m₂.toList⟩

/-- Increment `(a^∧) + m` (Section 4.1.2, p. 21): adds `m` to every shifted variable in `a^∧`. -/
def shift (a : SizeMin) (m : Nat) : SizeMin :=
  ⟨⟨a.head.var, a.head.shift + m⟩, a.tail.map (fun s => ⟨s.var, s.shift + m⟩)⟩

/-- All size variables occurring in `a^∧`. -/
def vars (a : SizeMin) : List SizeVar :=
  (a.toList.map (·.var)).eraseDups

end SizeMin

/-- Size expressions `a, b ::= ∞ + n | a^∧` (Table 1, p. 20). -/
inductive SizeExp where
  | inf : Nat → SizeExp
  | meet : SizeMin → SizeExp
  deriving DecidableEq, Repr

namespace SizeExp

/-- Unshifted infinity `∞ := ∞ + 0` (p. 20). -/
def infty : SizeExp := .inf 0

/-- Single shifted size variable `i + n` as a `SizeExp`. -/
def var (i : SizeVar) (n : Nat := 0) : SizeExp :=
  .meet (SizeMin.single i n)

/-- Size increment `a + m` (Section 4.1.2, p. 21):
- `(∞ + n) + m = ∞ + (n + m)`
- `(a^∧) + m = (a^∧ + m)`. -/
def shift : SizeExp → Nat → SizeExp
  | .inf n, m => .inf (n + m)
  | .meet a, m => .meet (a.shift m)

/-- Bound normalization `a^↑` (Section 4.1.2, p. 22):
- `(∞ + n)^↑ = ∞ + 1`
- `(a^∧)^↑ = a^∧`. -/
def boundNorm : SizeExp → SizeExp
  | .inf _ => .inf 1
  | .meet a => .meet a

/-- Meet of two size expressions when both are variable meets; if either is `∞ + n`, returns the
other (supporting `∧_{i ∈ Ψ} i` in Algorithm 1, p. 58). -/
def meetExp : SizeExp → SizeExp → SizeExp
  | .meet a, .meet b => .meet (a.append b)
  | .meet a, .inf _ => .meet a
  | .inf _, .meet b => .meet b
  | .inf n, .inf m => .inf (Nat.min n m)

/-- All size variables occurring in a size expression `a`. -/
def vars : SizeExp → List SizeVar
  | .inf _ => []
  | .meet a => a.vars

/-- Substitute a single size variable `i ↦ s` inside a shifted variable `(j + n)`. -/
def substShiftedVar (i : SizeVar) (s : SizeExp) (sv : ShiftedSizeVar) : SizeExp :=
  if sv.var == i then s.shift sv.shift else .var sv.var sv.shift

/-- Substitute a mapping `σ : List (SizeVar × SizeExp)` simultaneously into a size expression `a`
(`a[a⃗ / Ψ̂]`, Section 4.1.2, p. 21). -/
def subst (σ : List (SizeVar × SizeExp)) : SizeExp → SizeExp
  | .inf n => .inf n
  | .meet m =>
      let evalOne (sv : ShiftedSizeVar) : SizeExp :=
        match σ.find? (fun p => p.1 == sv.var) with
        | some (_, s) => s.shift sv.shift
        | none => .var sv.var sv.shift
      (m.tail.map evalOne).foldl meetExp (evalOne m.head)

end SizeExp

/-- Entry `i : π(< a)` in a size context `Ψ` (Table 1, p. 20). -/
structure SizeDecl where
  var : SizeVar
  pol : Polarity := .pos
  bound : SizeExp := .infty
  deriving DecidableEq, Repr

/-- Size variable context `Ψ ::= · | Ψ, i : π(< a)` (Table 1, p. 20). -/
abbrev SizeCtx := List SizeDecl

namespace SizeCtx

/-- Domain `{i | (i : π(< a)) ∈ Ψ}` of a size context `Ψ`. -/
def dom (Ψ : SizeCtx) : List SizeVar :=
  Ψ.map (·.var)

/-- Scale polarities in `Ψ` by `π`: `π(Ψ, i : π'(< a)) = (πΨ), i : (ππ')(< a)` (p. 20). -/
def scalePol (π : Polarity) (Ψ : SizeCtx) : SizeCtx :=
  Ψ.map (fun d => { d with pol := Polarity.comp π d.pol })

/-- Inverse-scale polarities in `Ψ` by `π⁻¹`: `π⁻¹(Ψ, i : π'(< a)) = (π⁻¹Ψ), i : (π⁻¹π')(< a)` (p. 20). -/
def invScalePol (π : Polarity) (Ψ : SizeCtx) : SizeCtx :=
  Ψ.map (fun d => { d with pol := Polarity.invComp π d.pol })

end SizeCtx

/-- Bounded size variable judgment `Ψ ⊢ i < a` (Section 4.1.2, p. 21):
`(i : π(< a)) ∈ Ψ` with `π ≤ +`. -/
def SizeVarBound (Ψ : SizeCtx) (i : SizeVar) (a : SizeExp) : Prop :=
  ∃ π : Polarity, SizeDecl.mk i π a ∈ Ψ ∧ Polarity.le π .pos = true

/-- Well-formedness of a size expression `Ψ ⊢ a` (Section 4.1.2, p. 21):
- `Ψ ⊢ ∞ + n`
- `Ψ ⊢ a^∧` iff every `(i + n) ∈ a^∧` has some bound `b` with `Ψ ⊢ i < b`. -/
def SizeWf (Ψ : SizeCtx) : SizeExp → Prop
  | .inf _ => True
  | .meet a => ∀ sv ∈ a.toList, ∃ b : SizeExp, SizeVarBound Ψ sv.var b

/-- Well-formedness of a size context `⊢ Ψ` (Section 4.1.2, p. 21):
- `⊢ ·`
- if `⊢ Ψ`, `◦⁻¹Ψ ⊢ a`, and `i ∉ dom(Ψ)`, then `⊢ Ψ, i : π(< a)`. -/
inductive SizeCtxWf : SizeCtx → Prop where
  | nil : SizeCtxWf []
  | snoc {Ψ : SizeCtx} {i : SizeVar} {π : Polarity} {a : SizeExp} :
      SizeCtxWf Ψ →
      i ∉ Ψ.dom →
      SizeWf (Ψ.invScalePol .mixed) a →
      SizeCtxWf (Ψ ++ [⟨i, π, a⟩])

/-- Strict size comparison `Ψ ⊢ a < b` (Section 4.1.2, pp. 21–22), together with non-strict
comparison `Ψ ⊢ a ≤ b` defined by `Ψ ⊢ a < b + 1` (p. 22). -/
inductive SizeLt (Ψ : SizeCtx) : SizeExp → SizeExp → Prop where
  /-- `n < m ⟹ Ψ ⊢ ∞ + n < ∞ + m` (p. 21). -/
  | inf_lt_inf {n m : Nat} :
      n < m →
      SizeLt Ψ (.inf n) (.inf m)
  /-- `n < m ∧ Ψ ⊢ i < a ⟹ Ψ ⊢ i + n < i + m` (p. 21). -/
  | var_lt_var {i : SizeVar} {n m : Nat} {a : SizeExp} :
      n < m →
      SizeVarBound Ψ i a →
      SizeLt Ψ (.var i n) (.var i m)
  /-- `Ψ ⊢ i < ∞ ⟹ Ψ ⊢ i + n < ∞ + m` (p. 21: any variable bounded below limit ordinal `∞`
  remains below `∞ + m` under finite shifts `+ n`). -/
  | var_lt_inf {i : SizeVar} {n m : Nat} :
      SizeVarBound Ψ i .infty →
      SizeLt Ψ (.var i n) (.inf m)
  /-- `Ψ ⊢ i < ∞ + m ⟹ Ψ ⊢ i + n < ∞ + (m + n)` (p. 21). -/
  | var_lt_inf_add {i : SizeVar} {n m : Nat} :
      SizeVarBound Ψ i (.inf m) →
      SizeLt Ψ (.var i n) (.inf (m + n))
  /-- Transitive step through context bound: if `(i : π(< a)) ∈ Ψ` with `π ≤ +` and
  `Ψ ⊢ a + n ≤ b` (i.e., `Ψ ⊢ a + n < b + 1`), then `Ψ ⊢ i + n < b` (p. 21). -/
  | var_bound_step {i : SizeVar} {n : Nat} {a b : SizeExp} :
      SizeVarBound Ψ i a →
      SizeLt Ψ (a.shift n) (b.shift 1) →
      SizeLt Ψ (.var i n) b
  /-- Left meet rule: if `Ψ ⊢ a^∧` and `Ψ ⊢ (i + n) < b` for some `(i + n) ∈ a^∧`,
  then `Ψ ⊢ a^∧ < b` (p. 21). -/
  | meet_lt_left {a : SizeMin} {sv : ShiftedSizeVar} {b : SizeExp} :
      SizeWf Ψ (.meet a) →
      sv ∈ a.toList →
      SizeLt Ψ (.var sv.var sv.shift) b →
      SizeLt Ψ (.meet a) b
  /-- Right meet rule: if `Ψ ⊢ a < (i + n)` for all `(i + n) ∈ b^∧`,
  then `Ψ ⊢ a < b^∧` (p. 21). -/
  | lt_meet_right {a : SizeExp} {b : SizeMin} :
      (∀ sv ∈ b.toList, SizeLt Ψ a (.var sv.var sv.shift)) →
      SizeLt Ψ a (.meet b)

/-- Non-strict size comparison `Ψ ⊢ a ≤ b` defined by `Ψ ⊢ a < b + 1` (Section 4.1.2, p. 22). -/
def SizeLe (Ψ : SizeCtx) (a b : SizeExp) : Prop :=
  SizeLt Ψ a (b.shift 1)

/-- Polarized size comparison `Ψ ⊢ a ≤^π b` (Section 4.1.3, p. 22):
- `Ψ ⊢ a ≤^◦ b ⟺ Ψ ⊢ a ≤ b ∧ Ψ ⊢ b ≤ a`
- `Ψ ⊢ a ≤^+ b ⟺ Ψ ⊢ a ≤ b`
- `Ψ ⊢ a ≤^− b ⟺ Ψ ⊢ b ≤ a`
- `Ψ ⊢ a ≤^⊤ b ⟺ True`. -/
def SizeLePol (Ψ : SizeCtx) (π : Polarity) (a b : SizeExp) : Prop :=
  match π with
  | .mixed => SizeLe Ψ a b ∧ SizeLe Ψ b a
  | .pos => SizeLe Ψ a b
  | .neg => SizeLe Ψ b a
  | .top => True

/-- Well-formedness of a size substitution `Ψ ⊢ a⃗ ⇐ Ψ'` (Section 4.1.2, p. 21):
checks that `|a⃗| = |Ψ'|` and for each `(iₖ : πₖ(< bₖ))` in `Ψ'`, `Ψ ⊢ aₖ < bₖ[a⃗ / Ψ̂']`. -/
inductive SizeSubstWf (Ψ : SizeCtx) : List SizeExp → SizeCtx → Prop where
  | nil : SizeSubstWf Ψ [] []
  | snoc {as : List SizeExp} {Ψ' : SizeCtx} {a : SizeExp} {d : SizeDecl} :
      SizeSubstWf Ψ as Ψ' →
      SizeLt Ψ a (d.bound.subst (Ψ'.dom.zip as)) →
      SizeSubstWf Ψ (as ++ [a]) (Ψ' ++ [d])

/-! ## Section 4.1.3: Kinds and Subkinding (p. 22) -/

/-- Simple kinds `ι ::= * | o | ι₁ → ι₂` (Table 1, p. 20) and polarized simple kinds
`ι ::= * | π ι₁ → ι₂` (Appendix A, Table 8, p. I). -/
inductive SKind where
  | star : SKind
  | prop : SKind
  | arr : Polarity → SKind → SKind → SKind
  deriving DecidableEq, Repr

/-- Kinds with variance and bounded sizes `κ ::= * | <a | π κ₁ → κ₂` (Section 4.1, Table 1, p. 20). -/
inductive Kind where
  | star : Kind
  | lt : SizeExp → Kind
  | arr : Polarity → Kind → Kind → Kind
  deriving DecidableEq, Repr

namespace Kind

/-- Embed a simple kind `ι` into `Kind`. -/
def ofSKind : SKind → Kind
  | .star => .star
  | .prop => .star
  | .arr π ι₁ ι₂ => .arr π (ofSKind ι₁) (ofSKind ι₂)

/-- Erase size bounds from a `Kind` to obtain its underlying simple kind `|κ|`. -/
def toSKind : Kind → SKind
  | .star => .star
  | .lt _ => .star
  | .arr π κ₁ κ₂ => .arr π (toSKind κ₁) (toSKind κ₂)

end Kind

/-- Shared shape of simple and refined kinds, erasing variances and allowing
bounded-size kinds to refine a simple base kind. The existing representation
also erases the distinction between `SKind.star` and `SKind.prop`. -/
inductive BinderKindShape where
  | base
  | arrow : BinderKindShape → BinderKindShape → BinderKindShape
  deriving DecidableEq, Repr

def simpleKindShape : SKind → BinderKindShape
  | .star | .prop => .base
  | .arr _ a b => .arrow (simpleKindShape a) (simpleKindShape b)

def refinedKindShape : Kind → BinderKindShape
  | .star | .lt _ => .base
  | .arr _ a b => .arrow (refinedKindShape a) (refinedKindShape b)

/-- Refined kind shape distinguishing proper types (`*`), propositions (`o`),
bounded sizes (`< a`), and higher-kinded type operators (`ι₁ → ι₂`). -/
inductive RefinedShape where
  | type : RefinedShape
  | prop : RefinedShape
  | size : RefinedShape
  | arr : RefinedShape → RefinedShape → RefinedShape
  deriving DecidableEq, Repr

/-- Erase polarities from a simple kind `ι` while preserving `star` vs. `prop`. -/
def simpleShape : SKind → RefinedShape
  | .star => .type
  | .prop => .prop
  | .arr _ a b => .arr (simpleShape a) (simpleShape b)

/-- Erase polarities and size bounds from a refined kind `κ` while distinguishing
`.star` (`.type`) from `.lt a` (`.size`). -/
def refinedShape : Kind → RefinedShape
  | .star => .type
  | .lt _ => .size
  | .arr _ a b => .arr (refinedShape a) (refinedShape b)

/-- Compatibility between a lambda binder's syntactic simple-kind annotation `ι`
and the checked domain shape `s` (admitting `.star`-annotated size binders as well
as exact simple-shape matches). -/
def annotationCompatible (ι : SKind) (s : RefinedShape) : Prop :=
  simpleShape ι = s ∨ (ι = .star ∧ s = .size)

/-- Well-formedness of a kind `Ψ ⊢ κ` (Section 4.1.3, p. 22):
- `Ψ ⊢ *`
- `Ψ ⊢ a ⟹ Ψ ⊢ <a`
- `−Ψ ⊢ κ₁ ∧ Ψ ⊢ κ₂ ⟹ Ψ ⊢ π κ₁ → κ₂`. -/
inductive KindWf : SizeCtx → Kind → Prop where
  | star (Ψ : SizeCtx) : KindWf Ψ .star
  | lt {Ψ : SizeCtx} {a : SizeExp} :
      SizeWf Ψ a →
      KindWf Ψ (.lt a)
  | arr {Ψ : SizeCtx} {π : Polarity} {κ₁ κ₂ : Kind} :
      KindWf (Ψ.scalePol .neg) κ₁ →
      KindWf Ψ κ₂ →
      KindWf Ψ (.arr π κ₁ κ₂)

/-- Subkinding judgment `Ψ ⊢ κ ≤ κ'` (Section 4.1.3, p. 22):
- `Ψ ⊢ * ≤ *`
- `Ψ ⊢ a ≤ b ⟹ Ψ ⊢ (<a) ≤ (<b)`
- `π' ≤ π ∧ −Ψ ⊢ κ₁' ≤ κ₁ ∧ Ψ ⊢ κ₂ ≤ κ₂' ⟹ Ψ ⊢ (π κ₁ → κ₂) ≤ (π' κ₁' → κ₂')`. -/
inductive SubKind : SizeCtx → Kind → Kind → Prop where
  | star (Ψ : SizeCtx) : SubKind Ψ .star .star
  | lt {Ψ : SizeCtx} {a b : SizeExp} :
      SizeLe Ψ a b →
      SubKind Ψ (.lt a) (.lt b)
  | arr {Ψ : SizeCtx} {π π' : Polarity} {κ₁ κ₁' κ₂ κ₂' : Kind} :
      Polarity.le π' π = true →
      SubKind (Ψ.scalePol .neg) κ₁' κ₁ →
      SubKind Ψ κ₂ κ₂' →
      SubKind Ψ (.arr π κ₁ κ₂) (.arr π' κ₁' κ₂')

/-- Polarized kind comparison `Ψ ⊢ κ ≤^π κ'` (Section 4.1.3, p. 22). -/
def KindLePol (Ψ : SizeCtx) (π : Polarity) (κ κ' : Kind) : Prop :=
  match π with
  | .mixed => SubKind Ψ κ κ' ∧ SubKind Ψ κ' κ
  | .pos => SubKind Ψ κ κ'
  | .neg => SubKind Ψ κ' κ
  | .top => True

/-- Polarized maximum kind `max^π(κ, κ')` used in quantifier subtyping (Section 4.2.2, p. 24). -/
def maxKindPol (π : Polarity) (κ κ' : Kind) : Kind :=
  match π, κ, κ' with
  | .neg, .lt (.inf n), .lt (.inf m) => .lt (.inf (Nat.min n m))
  | _, .lt (.inf n), .lt (.inf m) => .lt (.inf (Nat.max n m))
  | .neg, .lt a, .lt b => .lt (SizeExp.meetExp a b)
  | _, κ₁, _ => κ₁

/-! ## Section 4.2: Types, Kinding Contexts, and Subtyping (pp. 23–25) -/

/-- Type variable identifier `X, Y, Z ∈ TyVar` (Table 2, p. 23). -/
abbrev TyVar := Nat

/-- Constructor tag `c ∈ Cons` and record field projection tag `d ∈ Proj` (Table 2, p. 23). -/
abbrev ConsName := Nat
abbrev ProjName := Nat

/-- Entry `X : π κ` in a kinding context `Δ` (Table 1, p. 20).
Size bindings `i : π(< a)` are represented both in `Δ.sizes` and as kind bindings `< a`. -/
structure TyDecl where
  var : TyVar
  pol : Polarity := .pos
  kind : Kind := .star
  deriving DecidableEq, Repr

/-- Unified kinding context `Δ` containing size declarations `sizes : SizeCtx` and type-variable
declarations `types : List TyDecl` (Table 1, p. 20 & Section 4.2, p. 23). -/
structure KindingCtx where
  sizes : SizeCtx := []
  types : List TyDecl := []
  deriving DecidableEq, Repr

namespace KindingCtx

def empty : KindingCtx := ⟨[], []⟩

/-- Scale all polarities in `Δ` by `π` (`πΔ`, Section 4.1.1, p. 20). -/
def scalePol (π : Polarity) (Δ : KindingCtx) : KindingCtx :=
  ⟨Δ.sizes.scalePol π, Δ.types.map (fun d => { d with pol := Polarity.comp π d.pol })⟩

/-- Inverse-scale all polarities in `Δ` by `π⁻¹` (`π⁻¹Δ`, Section 4.1.1, p. 20). -/
def invScalePol (π : Polarity) (Δ : KindingCtx) : KindingCtx :=
  ⟨Δ.sizes.invScalePol π, Δ.types.map (fun d => { d with pol := Polarity.invComp π d.pol })⟩

/-- Extend `Δ` with a type variable binding `X : π κ`. -/
def extType (Δ : KindingCtx) (X : TyVar) (π : Polarity) (κ : Kind) : KindingCtx :=
  match κ with
  | .lt a => ⟨Δ.sizes ++ [⟨X, π, a⟩], Δ.types ++ [⟨X, π, κ⟩]⟩
  | _ => ⟨Δ.sizes, Δ.types ++ [⟨X, π, κ⟩]⟩

/-- Extend `Δ` with a size context `Ψ`. -/
def extSizes (Δ : KindingCtx) (Ψ : SizeCtx) : KindingCtx :=
  ⟨Δ.sizes ++ Ψ, Δ.types ++ Ψ.map (fun d => ⟨d.var, d.pol, .lt d.bound⟩)⟩

/-- Extend `Δ` with a list of type/size declarations `Δ'` (`Δ, Δ'`). -/
def extDecls (Δ : KindingCtx) (Δ' : List TyDecl) : KindingCtx :=
  Δ'.foldl (fun acc d => acc.extType d.var d.pol d.kind) Δ

/-- Append two kinding contexts `Δ₁, Δ₂`. -/
def append (Δ₁ Δ₂ : KindingCtx) : KindingCtx :=
  ⟨Δ₁.sizes ++ Δ₂.sizes, Δ₁.types ++ Δ₂.types⟩

end KindingCtx

/-- Type-level atoms `K ::= a | X | 1 | × | → | ∀_κ | ∃_κ` (Table 2, p. 23). -/
inductive TyAtom where
  | size : SizeExp → TyAtom
  | var : TyVar → TyAtom
  | unit : TyAtom
  | prod : TyAtom
  | arr : TyAtom
  | all : Kind → TyAtom
  | ex : Kind → TyAtom
  deriving DecidableEq, Repr

/-- Type expressions `F, A ::= K | λX : ι. F | F F' | μ^a S | ν^a R` (Table 2, p. 23).
Inductive variant branches `S = ⟨c₁ : S_{c₁}; ...; cₙ : S_{cₙ}⟩` and coinductive record fields
`R = {d₁ : R_{d₁}; ...; dₙ : R_{dₙ}}` are represented as association lists of `(Nat × TypeExpr)`. -/
inductive TypeExpr where
  | atom : TyAtom → TypeExpr
  | lam : TyVar → SKind → TypeExpr → TypeExpr
  | app : TypeExpr → TypeExpr → TypeExpr
  | mu : SizeExp → List (Nat × TypeExpr) → TypeExpr
  | nu : SizeExp → List (Nat × TypeExpr) → TypeExpr
  deriving Repr

namespace TypeExpr

/-- Unit type `1`. -/
def unitTy : TypeExpr := .atom .unit

/-- Binary product type `A₁ × A₂`. -/
def prodTy (A₁ A₂ : TypeExpr) : TypeExpr :=
  .app (.app (.atom .prod) A₁) A₂

/-- Function arrow type `A → B`. -/
def arrTy (A B : TypeExpr) : TypeExpr :=
  .app (.app (.atom .arr) A) B

/-- Universal quantifier type `∀_κ F`. -/
def allTy (κ : Kind) (F : TypeExpr) : TypeExpr :=
  .app (.atom (.all κ)) F

/-- Existential quantifier type `∃_κ F`. -/
def exTy (κ : Kind) (F : TypeExpr) : TypeExpr :=
  .app (.atom (.ex κ)) F

/-- Bounded universal size quantification `∀(j < a). B` (`∀_{<a} (λj : *. B)`, p. 25). -/
def forallSizeLt (j : SizeVar) (a : SizeExp) (B : TypeExpr) : TypeExpr :=
  allTy (.lt a) (.lam j .star B)

/-- Bounded existential size quantification `∃(j < a). B` (`∃_{<a} (λj : *. B)`, p. 25). -/
def existsSizeLt (j : SizeVar) (a : SizeExp) (B : TypeExpr) : TypeExpr :=
  exTy (.lt a) (.lam j .star B)

/-- Iterated universal size prefix `∀Ψ. A` (Section 4.5, p. 28). -/
def forallSizes (Ψ : SizeCtx) (A : TypeExpr) : TypeExpr :=
  Ψ.foldr (fun d acc => forallSizeLt d.var d.bound acc) A

mutual

/-- Substitute a type expression `G` for type variable `X` in `F`. -/
def substTyVar (X : TyVar) (G : TypeExpr) : TypeExpr → TypeExpr
  | .atom (.var Y) => if Y == X then G else .atom (.var Y)
  | .atom K => .atom K
  | .lam Y ι body =>
      if Y == X then .lam Y ι body else .lam Y ι (substTyVar X G body)
  | .app F₁ F₂ => .app (substTyVar X G F₁) (substTyVar X G F₂)
  | .mu a S => .mu a (substTyVarBranches X G S)
  | .nu a R => .nu a (substTyVarBranches X G R)

/-- Helper: substitute `G` for `X` across a list of named branches/fields. -/
def substTyVarBranches (X : TyVar) (G : TypeExpr) :
    List (Nat × TypeExpr) → List (Nat × TypeExpr)
  | [] => []
  | (nm, F) :: rest => (nm, substTyVar X G F) :: substTyVarBranches X G rest

end

/-- Normalizing hereditary type application `F @_κ G` (Section 4.2.2, p. 24):
if `F = λX : ι. body`, substitutes `G` for `X` in `body`; otherwise forms `F G`. -/
def normApp (F G : TypeExpr) : TypeExpr :=
  match F with
  | .lam X _ body => substTyVar X G body
  | _ => .app F G

mutual

/-- Substitute size expressions `σ : List (SizeVar × SizeExp)` throughout a type `A`
(`A[a⃗ / Ψ̂]`, Section 4.5, p. 28). -/
def substSizes (σ : List (SizeVar × SizeExp)) : TypeExpr → TypeExpr
  | .atom (.size a) => .atom (.size (a.subst σ))
  | .atom (.all (.lt a)) => .atom (.all (.lt (a.subst σ)))
  | .atom (.ex (.lt a)) => .atom (.ex (.lt (a.subst σ)))
  | .atom K => .atom K
  | .lam X ι body => .lam X ι (substSizes σ body)
  | .app F₁ F₂ => .app (substSizes σ F₁) (substSizes σ F₂)
  | .mu a S => .mu (a.subst σ) (substSizesBranches σ S)
  | .nu a R => .nu (a.subst σ) (substSizesBranches σ R)

/-- Helper: substitute size expressions `σ` across a list of named branches/fields. -/
def substSizesBranches (σ : List (SizeVar × SizeExp)) :
    List (Nat × TypeExpr) → List (Nat × TypeExpr)
  | [] => []
  | (nm, F) :: rest => (nm, substSizes σ F) :: substSizesBranches σ rest

end

/-- Lookup a constructor branch `S_c` in a datatype definition `S`. -/
def lookupCons (S : List (ConsName × TypeExpr)) (c : ConsName) : Option TypeExpr :=
  (S.find? (fun p => p.1 == c)).map (·.2)

/-- Lookup a projection field `R_d` in a record definition `R`. -/
def lookupProj (R : List (ProjName × TypeExpr)) (d : ProjName) : Option TypeExpr :=
  (R.find? (fun p => p.1 == d)).map (·.2)

end TypeExpr

/-- Standard kind `◦* → *` of datatype/record functors `S` and `R` (Section 4.2.1, p. 23). -/
def functorKind : Kind :=
  .arr .mixed .star .star

mutual

/-- Kind inference judgment `Δ ⊢ F ⇒ κ` (Section 4.2.1, p. 23). -/
inductive KindInfer : KindingCtx → TypeExpr → Kind → Prop where
  | unit (Δ : KindingCtx) :
      KindInfer Δ (.atom .unit) .star
  | prod (Δ : KindingCtx) :
      KindInfer Δ (.atom .prod) (.arr .pos .star (.arr .pos .star .star))
  | arr (Δ : KindingCtx) :
      KindInfer Δ (.atom .arr) (.arr .neg .star (.arr .pos .star .star))
  | size {Δ : KindingCtx} {a : SizeExp} :
      SizeWf Δ.sizes a →
      KindInfer Δ (.atom (.size a)) (.lt (a.shift 1))
  | var {Δ : KindingCtx} {X : TyVar} {π : Polarity} {κ : Kind} :
      TyDecl.mk X π κ ∈ Δ.types →
      Polarity.le π .pos = true →
      KindInfer Δ (.atom (.var X)) κ
  | app {Δ : KindingCtx} {F G : TypeExpr} {π : Polarity} {κ κ' : Kind} :
      KindInfer Δ F (.arr π κ κ') →
      KindCheck (Δ.invScalePol π) G κ →
      KindInfer Δ (.app F G) κ'
  | all {Δ : KindingCtx} {κ : Kind} :
      KindWf (Δ.sizes.scalePol .neg) κ →
      KindInfer Δ (.atom (.all κ)) (.arr .pos (.arr .mixed κ .star) .star)
  | ex {Δ : KindingCtx} {κ : Kind} :
      KindWf Δ.sizes κ →
      KindInfer Δ (.atom (.ex κ)) (.arr .pos (.arr .mixed κ .star) .star)
  | mu {Δ : KindingCtx} {a : SizeExp} {S : List (ConsName × TypeExpr)} :
      SizeWf Δ.sizes a →
      (∀ p ∈ S, KindCheck Δ p.2 functorKind) →
      KindInfer Δ (.mu a S) .star
  | nu {Δ : KindingCtx} {a : SizeExp} {R : List (ProjName × TypeExpr)} :
      SizeWf (Δ.sizes.scalePol .neg) a →
      (∀ p ∈ R, KindCheck Δ p.2 functorKind) →
      KindInfer Δ (.nu a R) .star

/-- Kind checking judgment `Δ ⊢ F ⇐ κ` (Section 4.2.1, p. 23). -/
inductive KindCheck : KindingCtx → TypeExpr → Kind → Prop where
  | sub {Δ : KindingCtx} {F : TypeExpr} {κ κ' : Kind} :
      KindInfer Δ F κ →
      SubKind Δ.sizes κ κ' →
      KindCheck Δ F κ'
  | lam {Δ : KindingCtx} {X : TyVar} {ι : SKind} {F : TypeExpr} {π : Polarity} {κ κ' : Kind} :
      simpleKindShape ι = refinedKindShape κ →
      KindWf (Δ.sizes.invScalePol .mixed) (Kind.ofSKind ι) →
      KindWf (Δ.sizes.invScalePol .mixed) κ →
      KindCheck (Δ.extType X π κ) F κ' →
      KindCheck Δ (.lam X ι F) (.arr π κ κ')

end

/-- Relative kinding-context well-formedness `Δ ⊢ Δ'` (Section 4.2.1, p. 24). -/
inductive KindingCtxExtWf : KindingCtx → List TyDecl → Prop where
  | nil (Δ : KindingCtx) : KindingCtxExtWf Δ []
  | cons {Δ : KindingCtx} {d : TyDecl} {rest : List TyDecl} :
      KindWf (Δ.sizes.invScalePol .mixed) d.kind →
      KindingCtxExtWf (Δ.extType d.var d.pol d.kind) rest →
      KindingCtxExtWf Δ (d :: rest)

/-- Term variable identifier `x, y, z ∈ Var` (Table 2, p. 23). -/
abbrev TermVar := Nat

/-- Term typing context `Γ ::= · | Γ, x : A` (Table 2, p. 23). -/
abbrev TermCtx := List (TermVar × TypeExpr)

/-- Well-formedness of a term context `Δ ⊢ Γ` (Section 4.2.1, p. 24). -/
inductive TermCtxWf (Δ : KindingCtx) : TermCtx → Prop where
  | nil : TermCtxWf Δ []
  | snoc {Γ : TermCtx} {x : TermVar} {A : TypeExpr} :
      TermCtxWf Δ Γ →
      KindCheck Δ A .star →
      TermCtxWf Δ (Γ ++ [(x, A)])

mutual

/-- Bidirectional subtyping inference `Δ ⊢ F ≤^π F' ⇒ κ` where `π ≠ ⊤` (Section 4.2.2, p. 24). -/
inductive SubTypeInfer : KindingCtx → Polarity → TypeExpr → TypeExpr → Kind → Prop where
  | atom {Δ : KindingCtx} {π : Polarity} {K : TyAtom} {κ : Kind} :
      π ≠ .top →
      KindInfer Δ (.atom K) κ →
      SubTypeInfer Δ π (.atom K) (.atom K) κ
  | app {Δ : KindingCtx} {π π₁ : Polarity} {F F' G G' : TypeExpr} {κ₁ κ₂ : Kind} :
      π ≠ .top →
      SubTypeInfer Δ π F F' (.arr π₁ κ₁ κ₂) →
      SubTypeCheck (Δ.invScalePol π₁) (Polarity.comp π₁ π) G G' κ₁ →
      SubTypeInfer Δ π (.app F G) (.app F' G') κ₂
  | all {Δ : KindingCtx} {π : Polarity} {κ κ' : Kind} :
      π ≠ .top →
      KindLePol (Δ.sizes.scalePol .neg) (Polarity.comp .neg π) κ κ' →
      SubTypeInfer Δ π (.atom (.all κ)) (.atom (.all κ'))
        (.arr .neg (.arr .mixed (maxKindPol (Polarity.comp .neg π) κ κ') .star) .star)
  | ex {Δ : KindingCtx} {π : Polarity} {κ κ' : Kind} :
      π ≠ .top →
      KindLePol Δ.sizes π κ κ' →
      SubTypeInfer Δ π (.atom (.ex κ)) (.atom (.ex κ'))
        (.arr .pos (.arr .mixed (maxKindPol π κ κ') .star) .star)
  | mu {Δ : KindingCtx} {π : Polarity} {a a' : SizeExp}
      {S S' : List (ConsName × TypeExpr)} :
      π ≠ .top →
      SizeLePol Δ.sizes π a.boundNorm a'.boundNorm →
      S.map (·.1) = S'.map (·.1) →
      (∀ c F F', TypeExpr.lookupCons S c = some F → TypeExpr.lookupCons S' c = some F' →
        SubTypeCheck Δ π F F' functorKind) →
      SubTypeInfer Δ π (.mu a S) (.mu a' S') .star
  | nu {Δ : KindingCtx} {π : Polarity} {a a' : SizeExp}
      {R R' : List (ProjName × TypeExpr)} :
      π ≠ .top →
      SizeLePol (Δ.sizes.scalePol .neg) (Polarity.comp .neg π) a.boundNorm a'.boundNorm →
      R.map (·.1) = R'.map (·.1) →
      (∀ d F F', TypeExpr.lookupProj R d = some F → TypeExpr.lookupProj R' d = some F' →
        SubTypeCheck Δ π F F' functorKind) →
      SubTypeInfer Δ π (.nu a R) (.nu a' R') .star

/-- Bidirectional subtyping checking `Δ ⊢ F ≤^π F' ⇐ κ` (Section 4.2.2, p. 24). -/
inductive SubTypeCheck : KindingCtx → Polarity → TypeExpr → TypeExpr → Kind → Prop where
  | top (Δ : KindingCtx) (F F' : TypeExpr) (κ : Kind) :
      SubTypeCheck Δ .top F F' κ
  | star {Δ : KindingCtx} {π : Polarity} {A A' : TypeExpr} :
      SubTypeInfer Δ π A A' .star →
      SubTypeCheck Δ π A A' .star
  | arr {Δ : KindingCtx} {π π₁ : Polarity} {F F' : TypeExpr} {X : TyVar} {κ₁ κ₂ : Kind} :
      KindWf (Δ.sizes.invScalePol .mixed) κ₁ →
      SubTypeCheck (Δ.extType X π₁ κ₁) π
        (F.normApp (.atom (.var X))) (F'.normApp (.atom (.var X))) κ₂ →
      SubTypeCheck Δ π F F' (.arr π₁ κ₁ κ₂)

end

/-- Entry-point subtyping judgment `Δ ⊢ A ≤ A'` defined by `Δ ⊢ A ≤^+ A' ⇒ *` (pp. 24–25). -/
def SubType (Δ : KindingCtx) (A A' : TypeExpr) : Prop :=
  SubTypeInfer Δ .pos A A' .star

/-! ## Section 4.3: Patterns and Copattern Spines (p. 25) -/

/-- Patterns `p ::= x | () | (p₁, p₂) | c p | ^G p` (Table 3, p. 25). -/
inductive Pat where
  | var : TermVar → Pat
  | unit : Pat
  | pair : Pat → Pat → Pat
  | cons : ConsName → Pat → Pat
  | tyPack : TyVar → Pat → Pat
  deriving DecidableEq, Repr

/-- Copatterns `q ::= p | X | .d` (Table 3, p. 25). -/
inductive Copat where
  | pat : Pat → Copat
  | tyVar : TyVar → Copat
  | proj : ProjName → Copat
  deriving DecidableEq, Repr

/-- Pattern spine `q⃗ = [q₁, ..., qₙ]` (Table 3, p. 25). -/
abbrev PatSpine := List Copat

/-- Pattern typing relation `Δ; Γ ⊢_{Δ₀} p ⇐ A` (Section 4.3, p. 25). -/
inductive PatTyping : KindingCtx → List TyDecl → TermCtx → Pat → TypeExpr → Prop where
  | var (Δ₀ : KindingCtx) (x : TermVar) (A : TypeExpr) :
      PatTyping Δ₀ [] [(x, A)] (.var x) A
  | unit (Δ₀ : KindingCtx) :
      PatTyping Δ₀ [] [] .unit .unitTy
  | pair {Δ₀ : KindingCtx} {Δ₁ Δ₂ : List TyDecl} {Γ₁ Γ₂ : TermCtx}
      {p₁ p₂ : Pat} {A₁ A₂ : TypeExpr} :
      PatTyping Δ₀ Δ₁ Γ₁ p₁ A₁ →
      PatTyping Δ₀ Δ₂ Γ₂ p₂ A₂ →
      PatTyping Δ₀ (Δ₁ ++ Δ₂) (Γ₁ ++ Γ₂) (.pair p₁ p₂) (.prodTy A₁ A₂)
  | cons {Δ₀ : KindingCtx} {Δ : List TyDecl} {Γ : TermCtx}
      {c : ConsName} {p : Pat} {a : SizeExp} {S : List (ConsName × TypeExpr)}
      {Sc : TypeExpr} (j : SizeVar) :
      TypeExpr.lookupCons S c = some Sc →
      PatTyping Δ₀ Δ Γ p (.existsSizeLt j a.boundNorm (Sc.normApp (.mu (.var j) S))) →
      PatTyping Δ₀ Δ Γ (.cons c p) (.mu a S)
  | tyPack {Δ₀ : KindingCtx} {Δ : List TyDecl} {Γ : TermCtx}
      {X : TyVar} {κ : Kind} {p : Pat} {F : TypeExpr} :
      PatTyping (Δ₀.extType X .pos κ) Δ Γ p (F.normApp (.atom (.var X))) →
      PatTyping Δ₀ (⟨X, .pos, κ⟩ :: Δ) Γ (.tyPack X p) (.exTy κ F)

/-- Copattern spine typing relation `Δ; Γ | A ⊢_{Δ₀} q⃗ ⇒ C` (Section 4.3, p. 25). -/
inductive SpineTyping : KindingCtx → List TyDecl → TermCtx → TypeExpr → PatSpine → TypeExpr → Prop where
  | nil (Δ₀ : KindingCtx) (C : TypeExpr) :
      SpineTyping Δ₀ [] [] C [] C
  | pat {Δ₀ : KindingCtx} {Δ₁ Δ₂ : List TyDecl} {Γ₁ Γ₂ : TermCtx}
      {A B C : TypeExpr} {p : Pat} {qs : PatSpine} :
      PatTyping Δ₀ Δ₁ Γ₁ p A →
      SpineTyping Δ₀ Δ₂ Γ₂ B qs C →
      SpineTyping Δ₀ (Δ₁ ++ Δ₂) (Γ₁ ++ Γ₂) (.arrTy A B) (.pat p :: qs) C
  | proj {Δ₀ : KindingCtx} {Δ : List TyDecl} {Γ : TermCtx}
      {a : SizeExp} {R : List (ProjName × TypeExpr)} {d : ProjName} {Rd C : TypeExpr}
      {qs : PatSpine} (j : SizeVar) :
      TypeExpr.lookupProj R d = some Rd →
      SpineTyping Δ₀ Δ Γ (.forallSizeLt j a.boundNorm (Rd.normApp (.nu (.var j) R))) qs C →
      SpineTyping Δ₀ Δ Γ (.nu a R) (.proj d :: qs) C
  | tyVar {Δ₀ : KindingCtx} {Δ : List TyDecl} {Γ : TermCtx}
      {X : TyVar} {κ : Kind} {F C : TypeExpr} {qs : PatSpine} :
      SpineTyping (Δ₀.extType X .pos κ) Δ Γ (F.normApp (.atom (.var X))) qs C →
      SpineTyping Δ₀ (⟨X, .pos, κ⟩ :: Δ) Γ (.allTy κ F) (.tyVar X :: qs) C

/-! ## Section 4.4: Invocation Graphs and the Size-Change Termination Criterion (pp. 26–27) -/

/-- Edge label `r ∈ {<, ≤}` in an invocation graph (Section 4.4, p. 26). -/
inductive EdgeRel where
  | lt : EdgeRel
  | le : EdgeRel
  deriving DecidableEq, Repr

namespace EdgeRel

/-- Composition `r₁ ⋅ r₂` of two edge labels along a path (Section 4.4, p. 27):
`r'' = <` if `r₁ = <` or `r₂ = <`, and `≤` otherwise. -/
def seq : EdgeRel → EdgeRel → EdgeRel
  | .lt, _ => .lt
  | _, .lt => .lt
  | .le, .le => .le

/-- Choice / parallel combination `max(r₁, r₂)` when multiple paths connect `lᵢ` and `rⱼ`
(Section 7.1, p. 66: semiring `{0, 1, 2}` where `1 = ≤`, `2 = <`, and addition is `max`). -/
def combine : Option EdgeRel → Option EdgeRel → Option EdgeRel
  | some .lt, _ => some .lt
  | _, some .lt => some .lt
  | some .le, _ => some .le
  | _, some .le => some .le
  | none, none => none

end EdgeRel

/-- Bipartite oriented invocation graph `G = (L_G, R_G, E_G : L_G × R_G ⇀ {<, ≤})`
(Section 4.4, p. 26), with parts `L_G = {0, ..., leftArity - 1}` and
`R_G = {0, ..., rightArity - 1}`. -/
structure InvGraph where
  leftArity : Nat
  rightArity : Nat
  edges : List (Nat × Nat × EdgeRel)
  deriving DecidableEq, Repr

namespace InvGraph

/-- Query the best edge label `E_G(lᵢ, rⱼ) ∈ Option {<, ≤}` between left vertex `i < leftArity`
and right vertex `j < rightArity` (Section 4.4, p. 26 & Section 7.1, p. 66). -/
def edgeAt (G : InvGraph) (i j : Nat) : Option EdgeRel :=
  (G.edges.filter (fun e => e.1 == i && e.2.1 == j)).foldl
    (fun acc e => EdgeRel.combine acc (some e.2.2)) none

/-- Canonical normalized edge list on `{0, ..., leftArity - 1} × {0, ..., rightArity - 1}`. -/
def canonicalEdges (leftArity rightArity : Nat) (lookup : Nat → Nat → Option EdgeRel) :
    List (Nat × Nat × EdgeRel) :=
  (List.range leftArity).flatMap fun i =>
    (List.range rightArity).filterMap fun j =>
      (lookup i j).map fun r => (i, j, r)

/-- Normalize an invocation graph to its canonical edge representation. -/
def normalize (G : InvGraph) : InvGraph :=
  ⟨G.leftArity, G.rightArity, canonicalEdges G.leftArity G.rightArity G.edgeAt⟩

/-- Two invocation graphs with the same left/right arities are equal as partial functions
`L_G × R_G ⇀ {<, ≤}` iff their normalized forms coincide. -/
def ExtEq (G₁ G₂ : InvGraph) : Prop :=
  G₁.leftArity = G₂.leftArity ∧
  G₁.rightArity = G₂.rightArity ∧
  ∀ i < G₁.leftArity, ∀ j < G₁.rightArity, G₁.edgeAt i j = G₂.edgeAt i j

/-- Composition of invocation graphs `G₁ ∘ G₂` where `|R_{G₁}| = |L_{G₂}|` (Section 4.4, p. 27):
`L_{G₃} := L_{G₁}`, `R_{G₃} := R_{G₂}`, and `E_{G₃}(lᵢ, rⱼ) = r''` if there exists `k < |R_{G₁}|`
with `E_{G₁}(lᵢ, rₖ) = r` and `E_{G₂}(lₖ, rⱼ) = r'`, choosing `<` whenever any such `k` has
`r = <` or `r' = <`, and `≤` otherwise. -/
def comp (G₁ G₂ : InvGraph) : InvGraph :=
  let lookup (i j : Nat) : Option EdgeRel :=
    (List.range G₁.rightArity).foldl
      (fun acc k =>
        match G₁.edgeAt i k, G₂.edgeAt k j with
        | some r₁, some r₂ => EdgeRel.combine acc (some (EdgeRel.seq r₁ r₂))
        | _, _ => acc)
      none
  ⟨G₁.leftArity, G₂.rightArity, canonicalEdges G₁.leftArity G₂.rightArity lookup⟩

end InvGraph

/-- Conformance of two tuples `s⃗, s⃗' ∈ S⁺` to an invocation graph `G` (`s⃗ ≺_G s⃗'`,
Section 4.4, p. 26) with respect to strict and non-strict relations `ltRel, leRel : S → S → Prop`:
- `|s⃗| = |L_G|` and `|s⃗'| = |R_G|`
- for all `i < |L_G|` and `j < |R_G|`, `E_G(lᵢ, rⱼ) = < ⟹ ltRel sᵢ s'ⱼ`
  and `E_G(lᵢ, rⱼ) = ≤ ⟹ leRel sᵢ s'ⱼ`. -/
def ConformsToGraph {S : Type} (ltRel leRel : S → S → Prop)
    (G : InvGraph) (s s' : List S) : Prop :=
  s.length = G.leftArity ∧
  s'.length = G.rightArity ∧
  ∀ (i j : Nat) (hi : i < s.length) (hj : j < s'.length),
    (G.edgeAt i j = some .lt → ltRel (s.get ⟨i, hi⟩) (s'.get ⟨j, hj⟩)) ∧
    (G.edgeAt i j = some .le → leRel (s.get ⟨i, hi⟩) (s'.get ⟨j, hj⟩))

/-- Syntactic conformance `a⃗ ≺_G Ψ_f` in kinding context `Δ` (Section 4.5, p. 28):
the call-site size arguments `a⃗` (right part `R_G`) and caller size variables `Ψ_f` (left part `L_G`,
or vice-versa per Section 4.5 / Theorem 1, p. 34 where `β⃗ ≺_G α⃗` means `βⱼ < αᵢ` when
`E_G(lᵢ, rⱼ) = <`) satisfy the edge constraints of `G` in `Δ.sizes`. -/
def SyntacticConforms (Ψctx : SizeCtx) (G : InvGraph)
    (calleeArgs : List SizeExp) (callerParams : SizeCtx) : Prop :=
  ConformsToGraph (SizeLt Ψctx) (SizeLe Ψctx) G
    calleeArgs (callerParams.map (fun d => SizeExp.var d.var 0))

/-- Function symbol identifier `f, g ∈ Fun` (Table 4, p. 28). -/
abbrev FunName := Nat

/-- Family of invocation graphs `G(f, g)` indexed by function symbols `f, g ∈ Fun`
(Section 4.4, p. 27). -/
structure InvGraphFamily where
  arity : FunName → Nat
  graphs : FunName → FunName → List InvGraph

namespace InvGraphFamily

/-- Well-formedness of an invocation graph family `G`: every `G ∈ G(f, g)` has
`|L_G| = arity(g)` and `|R_G| = arity(f)` (so for `G₁ ∈ G(h, g)` and `G₂ ∈ G(g, f)` in
`α⃗_{i+1} ≺_{G_i} α⃗_i`, `|R_{G₁}| = arity(g) = |L_{G₂}|`, matching Lemma 1 and Theorem 1, pp. 34–35). -/
def ArityWf (𝒢 : InvGraphFamily) : Prop :=
  (∃ dom : List FunName, ∀ f g : FunName, 𝒢.graphs f g ≠ [] → f ∈ dom ∧ g ∈ dom) ∧
  ∀ f g : FunName, ∀ G ∈ 𝒢.graphs f g,
    G.leftArity = 𝒢.arity g ∧ G.rightArity = 𝒢.arity f ∧ G = G.normalize

end InvGraphFamily

/-- Inductive transitive closure `G*(f, g)` of an invocation graph family `G` under composition
(Section 4.4, p. 27):
- if `G ∈ G(f, g)`, then `G ∈ G*(f, g)`
- if `G₁ ∈ G*(h, g)` and `G₂ ∈ G*(f, h)` (so `s⃗_h ≺_{G₂} s⃗_f` and `s⃗_g ≺_{G₁} s⃗_h`, hence
  `s⃗_g ≺_{G₁ ∘ G₂} s⃗_f`), then `G₁ ∘ G₂ ∈ G*(f, g)`. -/
inductive InvGraphClosure (𝒢 : InvGraphFamily) : FunName → FunName → InvGraph → Prop where
  | base {f g : FunName} {G : InvGraph} :
      G ∈ 𝒢.graphs f g →
      InvGraphClosure 𝒢 f g G.normalize
  | comp {f h g : FunName} {G₁ G₂ : InvGraph} :
      InvGraphClosure 𝒢 h g G₁ →
      InvGraphClosure 𝒢 f h G₂ →
      InvGraphClosure 𝒢 f g (G₁.comp G₂)

/-- The Size-Change Termination criterion `⊢ G` (`SCTValid G`, Section 4.4, p. 27):
`∀ f, ∀ G ∈ G*(f, f), G = G ∘ G ⟹ ∃ k < |L_G|, E_G(lₖ, rₖ) = <`. -/
def SCTValid (𝒢 : InvGraphFamily) : Prop :=
  𝒢.ArityWf ∧
  ∀ (f : FunName) (G : InvGraph),
    InvGraphClosure 𝒢 f f G →
    G.comp G = G →
    ∃ k < G.leftArity, G.edgeAt k k = some .lt

/-! ## Sections 4.5–4.6: Terms, Clauses, Mutual Blocks, and Programs (pp. 27–30) -/

mutual

/-- Expressions / terms `r, s, t` of System `F_ω^{cop, SCT}` and System `F_ω^c`
(Table 4, p. 28 & Table 11, p. III). -/
inductive Term where
  | var : TermVar → Term
  | funRef : FunName → List SizeExp → Term
  | app : Term → Elim → Term
  | unit : Term
  | pair : Term → Term → Term
  | cons : ConsName → Option SizeExp → Term → Term
  | pack : TypeExpr → Term → Term
  | lamClauses : List Clause → Term
  | ascr : Term → TypeExpr → Term
  deriving Repr

/-- Eliminations `e ::= t | G | .d [a]` (Table 4, p. 28 & Table 11, p. III). -/
inductive Elim where
  | term : Term → Elim
  | tyArg : TypeExpr → Elim
  | proj : ProjName → Option SizeExp → Elim
  deriving Repr

/-- Definition clause `D ::= {q⃗ → t}` (Table 5, p. 29 & Table 12, p. IV). -/
inductive Clause where
  | mk : PatSpine → Term → Clause
  deriving Repr

end

namespace Term

/-- Apply a term `r` to a spine of eliminations `e⃗ = [e₁, ..., eₙ]`. -/
def appSpine (r : Term) (es : List Elim) : Term :=
  es.foldl .app r

end Term

/-- Function declaration `δ ::= f : ∀Ψ. A = D⃗` in System `F_ω^{cop, SCT}` (Table 5, p. 29).
In unannotated System `F_ω^c` (Appendix A, Table 12, p. IV), `sizeParams = []`. -/
structure FunDecl where
  name : FunName
  sizeParams : SizeCtx := []
  ty : TypeExpr
  clauses : List Clause
  deriving Repr

/-- Mutual block `Ξ ::= mutual δ⃗` (Table 5, p. 29). -/
abbrev MutualBlock := List FunDecl

/-- Global signature `Σ ::= Ξ⃗` of previously checked mutual blocks (Section 4.6, p. 30). -/
abbrev GlobalSig := List FunDecl

/-- Complete program `P ::= (Σ; u)` consisting of checked blocks `Σ` and a main term `u`
(Table 5, p. 29 & Section 4.6, p. 30). -/
structure Program where
  sig : List MutualBlock
  main : Term
  deriving Repr

namespace FunDecl

/-- Lookup a function declaration `g : ∀Ψ. A = D⃗` by name in a list of declarations. -/
def lookup (decls : List FunDecl) (g : FunName) : Option FunDecl :=
  decls.find? (fun d => d.name == g)

end FunDecl

/-- Consistent kinding-context extension check `Δ ⊢ ∃Δ'` (Section 4.1.2, p. 22 & Section 4.6, p. 29):
every size binding `(i : π(< a))` introduced in `Δ'` has a satisfiable upper bound `a`
(in particular, `a` is well-formed in `Δ, Δ'` and does not bound `i` below a variable that may be `0`). -/
def KindingCtxConsistentExt (Δ : KindingCtx) (Δ' : List TyDecl) : Prop :=
  KindingCtxExtWf Δ Δ' ∧
  ∀ d ∈ Δ', ∀ a : SizeExp, d.kind = .lt a →
    (∃ n, a = .inf n) ∨ (∃ j ∈ (Δ.extDecls Δ').sizes.dom, a = .var j 0)

/-- Typing environment bundle `Ω = (Σ; Ξ; G; f; Ψ_f)` for bidirectional expression typing in
System `F_ω^{cop, SCT}` (Section 4.5, p. 28). -/
structure TypingEnv where
  sig : GlobalSig
  block : MutualBlock
  graphs : InvGraphFamily
  caller : FunName
  callerSizes : SizeCtx

mutual

/-- Bidirectional expression typing in inference mode `Σ; Ξ; G; Ψ_f; Δ; Γ ⊢ r ⇒ C`
for System `F_ω^{cop, SCT}` (Section 4.5, pp. 28–29). -/
inductive ExprInfer (Ω : TypingEnv) : KindingCtx → TermCtx → Term → TypeExpr → Prop where
  | var {Δ : KindingCtx} {Γ : TermCtx} {x : TermVar} {A : TypeExpr} :
      (x, A) ∈ Γ →
      ExprInfer Ω Δ Γ (.var x) A
  | proj {Δ : KindingCtx} {Γ : TermCtx} {r : Term} {a : SizeExp}
      {R : List (ProjName × TypeExpr)} {d : ProjName} {Rd : TypeExpr} (j : SizeVar) :
      ExprInfer Ω Δ Γ r (.nu a R) →
      TypeExpr.lookupProj R d = some Rd →
      ExprInfer Ω Δ Γ (.app r (.proj d none))
        (.forallSizeLt j a.boundNorm (Rd.normApp (.nu (.var j) R)))
  | projSized {Δ : KindingCtx} {Γ : TermCtx} {r : Term} {a b : SizeExp}
      {R : List (ProjName × TypeExpr)} {d : ProjName} {Rd : TypeExpr} :
      ExprInfer Ω Δ Γ r (.nu a R) →
      TypeExpr.lookupProj R d = some Rd →
      SizeLt Δ.sizes b a.boundNorm →
      ExprInfer Ω Δ Γ (.app r (.proj d (some b))) (Rd.normApp (.nu b R))
  | appTerm {Δ : KindingCtx} {Γ : TermCtx} {r s : Term} {A B : TypeExpr} :
      ExprInfer Ω Δ Γ r (.arrTy A B) →
      ExprCheck Ω Δ Γ s A →
      ExprInfer Ω Δ Γ (.app r (.term s)) B
  | appTy {Δ : KindingCtx} {Γ : TermCtx} {r : Term} {κ : Kind} {F F' : TypeExpr} :
      ExprInfer Ω Δ Γ r (.allTy κ F) →
      KindCheck Δ F' κ →
      ExprInfer Ω Δ Γ (.app r (.tyArg F')) (F.normApp F')
  | ascr {Δ : KindingCtx} {Γ : TermCtx} {t : Term} {A : TypeExpr} :
      KindCheck Δ A .star →
      ExprCheck Ω Δ Γ t A →
      ExprInfer Ω Δ Γ (.ascr t A) A
  | globalFun {Δ : KindingCtx} {Γ : TermCtx} {decl : FunDecl} {as : List SizeExp} :
      decl ∈ Ω.sig →
      SizeSubstWf Δ.sizes as decl.sizeParams →
      ExprInfer Ω Δ Γ (.funRef decl.name as)
        (decl.ty.substSizes (decl.sizeParams.dom.zip as))
  | localFun {Δ : KindingCtx} {Γ : TermCtx} {decl : FunDecl} {as : List SizeExp} {G : InvGraph} :
      decl ∈ Ω.block →
      SizeSubstWf Δ.sizes as decl.sizeParams →
      G ∈ Ω.graphs.graphs Ω.caller decl.name →
      SyntacticConforms Δ.sizes G as Ω.callerSizes →
      ExprInfer Ω Δ Γ (.funRef decl.name as)
        (decl.ty.substSizes (decl.sizeParams.dom.zip as))

/-- Bidirectional expression typing in checking mode `Σ; Ξ; G; Ψ_f; Δ; Γ ⊢ r ⇐ C`
for System `F_ω^{cop, SCT}` (Section 4.5, p. 29). -/
inductive ExprCheck (Ω : TypingEnv) : KindingCtx → TermCtx → Term → TypeExpr → Prop where
  | unit (Δ : KindingCtx) (Γ : TermCtx) :
      ExprCheck Ω Δ Γ .unit .unitTy
  | pair {Δ : KindingCtx} {Γ : TermCtx} {t₁ t₂ : Term} {A₁ A₂ : TypeExpr} :
      ExprCheck Ω Δ Γ t₁ A₁ →
      ExprCheck Ω Δ Γ t₂ A₂ →
      ExprCheck Ω Δ Γ (.pair t₁ t₂) (.prodTy A₁ A₂)
  | cons {Δ : KindingCtx} {Γ : TermCtx} {c : ConsName} {t : Term}
      {a : SizeExp} {S : List (ConsName × TypeExpr)} {Sc : TypeExpr} (j : SizeVar) :
      TypeExpr.lookupCons S c = some Sc →
      ExprCheck Ω Δ Γ t (.existsSizeLt j a.boundNorm (Sc.normApp (.mu (.var j) S))) →
      ExprCheck Ω Δ Γ (.cons c none t) (.mu a S)
  | consSized {Δ : KindingCtx} {Γ : TermCtx} {c : ConsName} {b a : SizeExp} {t : Term}
      {S : List (ConsName × TypeExpr)} {Sc : TypeExpr} :
      TypeExpr.lookupCons S c = some Sc →
      SizeLt Δ.sizes b a.boundNorm →
      ExprCheck Ω Δ Γ t (Sc.normApp (.mu b S)) →
      ExprCheck Ω Δ Γ (.cons c (some b) t) (.mu a S)
  | pack {Δ : KindingCtx} {Γ : TermCtx} {F F' : TypeExpr} {κ : Kind} {t : Term} :
      KindCheck Δ F' κ →
      ExprCheck Ω Δ Γ t (F.normApp F') →
      ExprCheck Ω Δ Γ (.pack F' t) (.exTy κ F)
  | lamClauses {Δ : KindingCtx} {Γ : TermCtx} {Ds : List Clause} {A : TypeExpr} :
      (∀ D ∈ Ds, ClauseCheck Ω Δ Γ D A) →
      ExprCheck Ω Δ Γ (.lamClauses Ds) A
  | sub {Δ : KindingCtx} {Γ : TermCtx} {r : Term} {A C : TypeExpr} :
      ExprInfer Ω Δ Γ r A →
      SubType Δ A C →
      ExprCheck Ω Δ Γ r C

/-- Clause verification rule `Ω; Δ; Γ ⊢ {q⃗ → t} ⇐ A` (Section 4.6, p. 29). -/
inductive ClauseCheck (Ω : TypingEnv) : KindingCtx → TermCtx → Clause → TypeExpr → Prop where
  | mk {Δ : KindingCtx} {Γ Γ' : TermCtx} {Δ' : List TyDecl}
      {A C : TypeExpr} {qs : PatSpine} {t : Term} :
      SpineTyping Δ Δ' Γ' A qs C →
      KindingCtxConsistentExt Δ Δ' →
      ExprCheck Ω (Δ.extDecls Δ') (Γ ++ Γ') t C →
      ClauseCheck Ω Δ Γ (.mk qs t) A

end

/-- Function declaration typing `Σ; Ξ; G ⊢ f : (∀Ψ. A) = D⃗` (Section 4.6, p. 30). -/
def DeclTyping (sig : GlobalSig) (Ξ : MutualBlock) (𝒢 : InvGraphFamily) (decl : FunDecl) : Prop :=
  let Δ₀ := KindingCtx.empty.extSizes decl.sizeParams
  let Ω : TypingEnv := ⟨sig, Ξ, 𝒢, decl.name, decl.sizeParams⟩
  SizeCtxWf decl.sizeParams ∧
  KindCheck Δ₀ decl.ty .star ∧
  ∀ D ∈ decl.clauses, ClauseCheck Ω Δ₀ [] D decl.ty

/-- Mutual block typing `Σ ⊢ Ξ` via an invocation graph family `G` (Section 4.6, p. 30):
`Σ; Ξ; G ⊢ f : (∀Ψ. A) = D⃗` for all `f ∈ Ξ`, and `⊢ G`. -/
def MutualBlockTypingWith (sig : GlobalSig) (Ξ : MutualBlock) (𝒢 : InvGraphFamily) : Prop :=
  SCTValid 𝒢 ∧
  (∀ decl ∈ Ξ, 𝒢.arity decl.name = decl.sizeParams.length) ∧
  ∀ decl ∈ Ξ, DeclTyping sig Ξ 𝒢 decl

/-- Existential mutual block typing `Σ ⊢ Ξ` (Section 4.6, p. 30). -/
def MutualBlockTyping (sig : GlobalSig) (Ξ : MutualBlock) : Prop :=
  ∃ 𝒢 : InvGraphFamily, MutualBlockTypingWith sig Ξ 𝒢

/-- Global signature sequence typing `⊢ Σ` (Section 4.6, p. 30). -/
inductive SigBlocksTyping : List MutualBlock → Prop where
  | nil : SigBlocksTyping []
  | snoc {blocks : List MutualBlock} {Ξ : MutualBlock} :
      SigBlocksTyping blocks →
      MutualBlockTyping blocks.flatten Ξ →
      SigBlocksTyping (blocks ++ [Ξ])

/-- Complete program typing `⊢ P` (`⊢ (Σ; u)`, Section 4.6, p. 30). -/
def ProgramTyping (P : Program) : Prop :=
  SigBlocksTyping P.sig ∧
  ∃ A : TypeExpr,
    ExprInfer ⟨P.sig.flatten, [], ⟨fun _ => 0, fun _ _ => []⟩, 0, []⟩
      KindingCtx.empty [] P.main A

mutual

/-- Collect all function references occurring in a term `t`, including under nested clauses. -/
def scopeTermRefs : Term → List FunName
  | .var _ => []
  | .funRef f _ => [f]
  | .app r e => scopeTermRefs r ++ scopeElimRefs e
  | .unit => []
  | .pair a b => scopeTermRefs a ++ scopeTermRefs b
  | .cons _ _ t => scopeTermRefs t
  | .pack _ t => scopeTermRefs t
  | .lamClauses ds => scopeClausesRefs ds
  | .ascr t _ => scopeTermRefs t

/-- Collect all function references occurring in an elimination `e`. -/
def scopeElimRefs : Elim → List FunName
  | .term t => scopeTermRefs t
  | .tyArg _ => []
  | .proj _ _ => []

/-- Collect all function references occurring in a clause `D`. -/
def scopeClauseRefs : Clause → List FunName
  | .mk _ t => scopeTermRefs t

/-- Collect all function references occurring across a list of clauses `Ds`. -/
def scopeClausesRefs : List Clause → List FunName
  | [] => []
  | d :: ds => scopeClauseRefs d ++ scopeClausesRefs ds

end

/-- Declared function names of a signature or mutual block. -/
def scopeNames (sig : GlobalSig) : List FunName := sig.map FunDecl.name

/-- Every syntactic function reference in `decl` resolves within `allowed`. -/
def scopeDeclClosed (allowed : List FunName) (decl : FunDecl) : Prop :=
  ∀ f ∈ scopeClausesRefs decl.clauses, f ∈ allowed

/-- A flat signature has duplicate-free names and no unresolved function references. -/
def scopeSignatureClosed (sig : GlobalSig) : Prop :=
  (scopeNames sig).Nodup ∧ ∀ decl ∈ sig, scopeDeclClosed (scopeNames sig) decl

/-- Well-scoped extension of an existing closed signature `sig` by a fresh mutual block `block`
(Section 4.6, p. 30 & Section 5.4.2, p. 36). -/
def scopeBlockExtension (sig : GlobalSig) (block : MutualBlock) : Prop :=
  scopeSignatureClosed sig ∧
  (scopeNames block).Nodup ∧
  (∀ f ∈ scopeNames block, f ∉ scopeNames sig) ∧
  (∀ decl ∈ block, scopeDeclClosed (scopeNames sig ++ scopeNames block) decl)

/-- Ordered sequence of mutual blocks where each block may reference itself and earlier blocks
without name collisions or forward references. -/
inductive scopeOrderedBlocks : List MutualBlock → Prop where
  | nil : scopeOrderedBlocks []
  | snoc {prior : List MutualBlock} {block : MutualBlock} :
      scopeOrderedBlocks prior → scopeBlockExtension prior.flatten block →
      scopeOrderedBlocks (prior ++ [block])

/-- Complete program typing with ordered, closed global blocks (`scopeOrderedBlocks P.sig`). -/
def ScopedProgramTyping (P : Program) : Prop :=
  scopeOrderedBlocks P.sig ∧
  (∀ f ∈ scopeTermRefs P.main, f ∈ scopeNames P.sig.flatten) ∧
  ProgramTyping P

/-! ## Section 5.5: System F_ω^{cop} Measure Erasure `|Ξ|` (pp. 38–40) -/

/-- A declaration in Abel & Pientka's System `F_ω^{cop}` carrying an explicit lexicographic
size measure `m` (a subset/sublist of `sizeParams` of fixed length `|m|`, Section 5.5, p. 38). -/
structure CopFunDecl where
  decl : FunDecl
  measureIndices : List Nat

/-- Measure removal `|Ξ| : Ξ^{cop} → Ξ^{cop, sct}` (Section 5.5, p. 38):
strips the explicit measure annotation `m` from each declaration in a mutual block. -/
def eraseMeasures (Ξcop : List CopFunDecl) : MutualBlock :=
  Ξcop.map (·.decl)

/-- Lexicographic invocation graph `G_i` of arity `k` at position `i < k` (Section 5.5, Figure 3,
p. 39): `E_{G_i}(l_j, r_j) = ≤` for `j < i` and `E_{G_i}(l_i, r_i) = <`. -/
def lexInvGraph (measureIndices : List Nat) (paramArity : Nat) (stepIdx : Nat) : InvGraph :=
  let lookup (l r : Nat) : Option EdgeRel :=
    if l == r then
      match measureIndices.idxOf? l with
      | some pos =>
          if pos < stepIdx then some .le
          else if pos == stepIdx then some .lt
          else none
      | none => none
    else none
  ⟨paramArity, paramArity, InvGraph.canonicalEdges paramArity paramArity lookup⟩

/-- Lexicographic invocation graph family `G^{lex}` constructed in the proof of Theorem 6
(Section 5.5, p. 39): for every `f, g ∈ dom`, `G(f, g) = {G_0, ..., G_{|m|-1}}`. -/
def lexInvGraphFamily (dom : List FunName) (paramArity : Nat) (measureIndices : List Nat) :
    InvGraphFamily where
  arity := fun _ => paramArity
  graphs := fun f g =>
    if f ∈ dom ∧ g ∈ dom then
      (List.range measureIndices.length).map (lexInvGraph measureIndices paramArity)
    else []

/-- Well-typed mutual block in System `F_ω^{cop}` (Section 5.5, pp. 38–39):
all functions in `Ξcop` share a common duplicate-free measure `measureIndices` of length `m > 0`
on their size parameters, and every recursive call `g a⃗` within `f` decreases lexicographically
along `measureIndices` (i.e. conforms to one of the lexicographic graphs `G_0, ..., G_{|m|-1}`). -/
def CopMutualBlockTyping (sig : GlobalSig) (Ξcop : List CopFunDecl) : Prop :=
  let dom := (eraseMeasures Ξcop).map (·.name)
  ∃ (paramArity : Nat) (measureIndices : List Nat),
    measureIndices ≠ [] ∧
    measureIndices.Nodup ∧
    (∀ idx ∈ measureIndices, idx < paramArity) ∧
    (∀ cdecl ∈ Ξcop, cdecl.measureIndices = measureIndices ∧
      cdecl.decl.sizeParams.length = paramArity) ∧
    (∀ cdecl ∈ Ξcop,
      DeclTyping sig (eraseMeasures Ξcop)
        (lexInvGraphFamily dom paramArity measureIndices) cdecl.decl)

end NishtAbel2024V2


