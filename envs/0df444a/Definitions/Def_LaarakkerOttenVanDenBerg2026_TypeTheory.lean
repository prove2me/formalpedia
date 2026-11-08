-- Prove2me | Definitions.Def_LaarakkerOttenVanDenBerg2026_TypeTheory
-- name    : LaarakkerOttenVanDenBerg2026_TypeTheory
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T15:41:01.534049+00:00
-- url     : https://prove2.me/theorems/e364e0ec-dea6-441a-bbc0-ef74336802e5
-- title:
--   Core Type Theory with Large Sizes, Impredicative Quantifiers, Fixpoints, and Parametricity Axioms
-- statement:
--   Formalizes Section 2 (pp. 4–8) and Appendix A (pp. 20–23) of Laarakker, Otten & van den Berg (FSCD 2026): mere propositions (`IsMereProp`), contractibility (`IsContr`), half-adjoint equivalences (`IsHAEquiv`, `HAEquiv`), the core dependent type theory `SizeCoreTheory` with a Tarski universe $(U, \mathrm{El})$ closed under $\bot^U, \top^U, \mathsf{Bool}^U, \Pi^U, \Sigma^U, =^U_A$, a primitive large type $\mathsf{Size}$ with $0, {\uparrow}, \le^U, <^U$, impredicative size quantifiers $\exists i.\,A(i) : U$ (with small-motive elimination $\mathsf{ind}_\exists$ and the derived identity-motive equality principle `ex_ind_eq`) and $\forall i.\,A(i) : U$, bounded modalities $\Diamond_i A$ and $\Box_i A$, the well-founded size fixpoint operator $\mathsf{fix}$ with $\mathsf{fix}^\beta$, the canonical comparison maps (`swapPiAll`, `swapSigmaEx`, `canExPi`, `canAllSigma`, `canExLt`, `canAllLt`), and the full `ParametricSizeTheory` bundling the four parametricity equivalence axioms.
-- source:
--   Bastiaan Laarakker, Daniël Otten, and Benno van den Berg, 'Constructing (Co)inductive Types via Large Sizes', FSCD 2026 (arXiv:2602.18921), Section 2 (pp. 4–8) & Appendix A (pp. 20–23)

/-
Formalization of Section 2 and Appendix A of:
  Bastiaan Laarakker, Daniël Otten, and Benno van den Berg (FSCD 2026),
  "Constructing (Co)inductive Types via Large Sizes",
  DOI: 10.4230/LIPIcs.FSCD.2026.21 (extended version: arXiv:2602.18921v2).

This file defines:
  1. Contractibility (`IsContr`), mere propositions (`IsMereProp`), and half-adjoint
     equivalences (`IsHAEquiv`, `HAEquiv`) (Appendix A, p. 21).
     Note on identity-type scope: `El_idU` and `Equiv.toIsHAEquiv` use Lean's proof-irrelevant
     propositional equality (`Subsingleton.elim`), corresponding to an extensional / set-level
     semantic interpretation (as validated by the paper's PER / modest-set realisability model in
     Section 4 and Appendix C.4, Definition 29, p. 29).
  2. Computable tracker codes (`TrackerCode`, `encodeTracker`, `decodeTracker`, `evalTracker`)
     capturing tracked semantic functions and parametric size families in the realisability
     semantics (Section 4, pp. 13–16 & Appendix C, pp. 27–33).
  3. The core type theory with a modest Tarski universe `(U, El, realises)`, a large type `Size`
     with preorder `≤` and strict order `<`, impredicative size quantifiers `∃ i. A(i)`
     (with small-motive elimination `indEx` on parametric families) and `∀ i. A(i)` (with
     parametric introduction `lamAll`), bounded quantifiers `◇_i A` and `□_i A`, and the
     well-founded size fixpoint operator `fix` (`SizeCoreTheory`, Section 2, pp. 4–6 &
     Appendix A, pp. 20–22).
  4. The canonical quantifier-comparison maps (`swapPiAll`, `swapSigmaEx`, `canExPi`,
     `canAllSigma`, `canExLt`, `canAllLt`) and the full parametric size type theory
     (`ParametricSizeTheory`, Section 2, pp. 7–8 & Appendix A, p. 23).
-/
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Nat.Pairing

set_option linter.checkUnivs false

namespace LaarakkerOttenVanDenBerg2026

universe u v w w₁ w₂

/-! ## 1. Homotopy Type Theory Primitives (Appendix A, p. 21) -/

/-- A type `α` is a mere proposition if any two elements are propositionally equal
(used for the size preorder `i ≤ j` in Section 2, p. 5 and Appendix A, p. 22). -/
def IsMereProp (α : Type w) : Prop :=
  ∀ (x y : α), x = y

/-- Contractibility `IsContr(α) := Σ (a₀ : α), Π (a : α), a = a₀`
(Appendix A, p. 21, and Lemma 1, p. 6). -/
structure IsContr (α : Type w) : Type w where
  center : α
  contr : ∀ (a : α), a = center

/-- Transport contractibility along an equivalence `α ≃ β`. -/
def Equiv.isContr {α : Type w₁} {β : Type w₂} (e : α ≃ β) (h : IsContr α) : IsContr β where
  center := e h.center
  contr b := by
    have hb := congrArg e (h.contr (e.symm b))
    exact (e.apply_symm_apply b).symm.trans hb

/-- Half-adjoint equivalence structure `IsEquiv(f)` on a map `f : α → β`
(Appendix A, p. 21):
`Σ (g : β → α) (η : Π a, g (f a) = a) (ε : Π b, f (g b) = b), Π a, ap f (η a) = ε (f a)`. -/
structure IsHAEquiv {α : Type w₁} {β : Type w₂} (f : α → β) : Type (max w₁ w₂) where
  inv : β → α
  left_inv : ∀ (a : α), inv (f a) = a
  right_inv : ∀ (b : β), f (inv b) = b
  coh : ∀ (a : α), congrArg f (left_inv a) = right_inv (f a)

/-- Type of half-adjoint equivalences `α ≃_HA β := Σ (f : α → β), IsHAEquiv f`
(Appendix A, p. 21). -/
structure HAEquiv (α : Type w₁) (β : Type w₂) : Type (max w₁ w₂) where
  toFun : α → β
  isHAEquiv : IsHAEquiv toFun

/-- Every standard equivalence `e : α ≃ β` induces a half-adjoint equivalence
(in Lean's extensional metatheory with UIP, the 2-coherence condition holds automatically). -/
def Equiv.toIsHAEquiv {α : Type w₁} {β : Type w₂} (e : α ≃ β) : IsHAEquiv e.toFun where
  inv := e.invFun
  left_inv := e.left_inv
  right_inv := e.right_inv
  coh := fun _ => Subsingleton.elim _ _

/-- Convert a standard equivalence `α ≃ β` into a half-adjoint equivalence `HAEquiv α β`. -/
def Equiv.toHAEquiv {α : Type w₁} {β : Type w₂} (e : α ≃ β) : HAEquiv α β where
  toFun := e.toFun
  isHAEquiv := Equiv.toIsHAEquiv e

/-- Extract a standard equivalence `α ≃ β` from a half-adjoint equivalence `HAEquiv α β`. -/
def HAEquiv.toEquiv {α : Type w₁} {β : Type w₂} (e : HAEquiv α β) : α ≃ β where
  toFun := e.toFun
  invFun := e.isHAEquiv.inv
  left_inv := e.isHAEquiv.left_inv
  right_inv := e.isHAEquiv.right_inv

/-! ## 2. Computable Tracker Codes for Modest Realisability (Section 4 & Appendix C) -/

/-- Computable tracker codes representing realisers of internal functions, modal functor
actions, and well-founded size-recursor steps (Section 4, pp. 13–16 & Appendix C, pp. 27–33). -/
inductive TrackerCode : Type where
  | id : TrackerCode
  | const (c : ℕ) : TrackerCode
  | comp (d e : TrackerCode) : TrackerCode
  | fst : TrackerCode
  | snd : TrackerCode
  | pair (d e : TrackerCode) : TrackerCode
  | postComp (c : TrackerCode) : TrackerCode
  | alg (c : TrackerCode) : TrackerCode
  | coalg (c : TrackerCode) : TrackerCode
  deriving DecidableEq, Repr

/-- Encode a `TrackerCode` as a natural number via Cantor pairing. -/
def encodeTracker : TrackerCode → ℕ
  | .id => 0
  | .const c => Nat.pair 1 c + 1
  | .comp d e => Nat.pair 2 (Nat.pair (encodeTracker d) (encodeTracker e)) + 1
  | .fst => Nat.pair 3 0 + 1
  | .snd => Nat.pair 4 0 + 1
  | .pair d e => Nat.pair 5 (Nat.pair (encodeTracker d) (encodeTracker e)) + 1
  | .postComp c => Nat.pair 6 (encodeTracker c) + 1
  | .alg c => Nat.pair 7 (encodeTracker c) + 1
  | .coalg c => Nat.pair 8 (encodeTracker c) + 1

/-- Fuel-bounded decoder for `TrackerCode` (structurally recursive on `fuel`). -/
def decodeTrackerAux : ℕ → ℕ → TrackerCode
  | 0, _ => .id
  | _ + 1, 0 => .id
  | fuel + 1, m + 1 =>
    let p := Nat.unpair m
    match p.1 with
    | 1 => .const p.2
    | 2 =>
      let q := Nat.unpair p.2
      .comp (decodeTrackerAux fuel q.1) (decodeTrackerAux fuel q.2)
    | 3 => .fst
    | 4 => .snd
    | 5 =>
      let q := Nat.unpair p.2
      .pair (decodeTrackerAux fuel q.1) (decodeTrackerAux fuel q.2)
    | 6 => .postComp (decodeTrackerAux fuel p.2)
    | 7 => .alg (decodeTrackerAux fuel p.2)
    | 8 => .coalg (decodeTrackerAux fuel p.2)
    | _ => .id

/-- Decode a natural number into a `TrackerCode`. -/
def decodeTracker (n : ℕ) : TrackerCode :=
  decodeTrackerAux (n + 1) n

private theorem decodeTrackerAux_encodeTracker (c : TrackerCode) :
    ∀ (fuel : ℕ), encodeTracker c < fuel → decodeTrackerAux fuel (encodeTracker c) = c := by
  induction c with
  | id =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ f => rfl
  | const k =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ f => simp [decodeTrackerAux, encodeTracker]
  | comp d e ihd ihe =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      have hp : Nat.pair (encodeTracker d) (encodeTracker e) ≤
          Nat.pair 2 (Nat.pair (encodeTracker d) (encodeTracker e)) :=
        Nat.right_le_pair _ _
      have hd : encodeTracker d ≤ Nat.pair (encodeTracker d) (encodeTracker e) :=
        Nat.left_le_pair _ _
      have he : encodeTracker e ≤ Nat.pair (encodeTracker d) (encodeTracker e) :=
        Nat.right_le_pair _ _
      simp only [encodeTracker] at hfuel ⊢
      simp only [decodeTrackerAux, Nat.unpair_pair]
      rw [ihd f (by omega), ihe f (by omega)]
  | fst =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ f => simp [decodeTrackerAux, encodeTracker]
  | snd =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ f => simp [decodeTrackerAux, encodeTracker]
  | pair d e ihd ihe =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      have hp : Nat.pair (encodeTracker d) (encodeTracker e) ≤
          Nat.pair 5 (Nat.pair (encodeTracker d) (encodeTracker e)) :=
        Nat.right_le_pair _ _
      have hd : encodeTracker d ≤ Nat.pair (encodeTracker d) (encodeTracker e) :=
        Nat.left_le_pair _ _
      have he : encodeTracker e ≤ Nat.pair (encodeTracker d) (encodeTracker e) :=
        Nat.right_le_pair _ _
      simp only [encodeTracker] at hfuel ⊢
      simp only [decodeTrackerAux, Nat.unpair_pair]
      rw [ihd f (by omega), ihe f (by omega)]
  | postComp d ih =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      have hp : encodeTracker d ≤ Nat.pair 6 (encodeTracker d) :=
        Nat.right_le_pair _ _
      simp only [encodeTracker] at hfuel ⊢
      simp only [decodeTrackerAux, Nat.unpair_pair]
      rw [ih f (by omega)]
  | alg d ih =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      have hp : encodeTracker d ≤ Nat.pair 7 (encodeTracker d) :=
        Nat.right_le_pair _ _
      simp only [encodeTracker] at hfuel ⊢
      simp only [decodeTrackerAux, Nat.unpair_pair]
      rw [ih f (by omega)]
  | coalg d ih =>
    intro fuel hfuel
    cases fuel with
    | zero => omega
    | succ f =>
      have hp : encodeTracker d ≤ Nat.pair 8 (encodeTracker d) :=
        Nat.right_le_pair _ _
      simp only [encodeTracker] at hfuel ⊢
      simp only [decodeTrackerAux, Nat.unpair_pair]
      rw [ih f (by omega)]

@[simp]
theorem decodeTracker_encodeTracker (c : TrackerCode) :
    decodeTracker (encodeTracker c) = c :=
  decodeTrackerAux_encodeTracker c (encodeTracker c + 1) (Nat.lt_succ_self _)

/-- Tracker code for the polynomial functor action `P_{A, B} f` when `f` is tracked by `c`. -/
def polyTracker (c : TrackerCode) : TrackerCode :=
  .pair .fst (.comp (.postComp c) .snd)

/-- Evaluate a `TrackerCode` on a natural number realiser (structurally recursive on the code). -/
def evalTracker : TrackerCode → ℕ → ℕ
  | .id, n => n
  | .const c, _ => c
  | .comp d e, n => evalTracker d (evalTracker e n)
  | .fst, n => (Nat.unpair n).1
  | .snd, n => (Nat.unpair n).2
  | .pair d e, n => Nat.pair (evalTracker d n) (evalTracker e n)
  | .postComp c, e => encodeTracker (.comp c (decodeTracker e))
  | .alg c, n =>
    let p := Nat.unpair n
    evalTracker c (Nat.pair p.1
      (encodeTracker (.comp (.alg c) (decodeTracker p.2))))
  | .coalg c, n =>
    let p := Nat.unpair (evalTracker c n)
    Nat.pair p.1
      (encodeTracker (.comp (.coalg c) (decodeTracker p.2)))

/-! ## 3. Core Type Theory with Large Sizes and Fixpoints (Section 2, pp. 4–6 & Appendix A) -/

/-- `SizeCoreTheory` formalizes the core dependent type theory of Section 2 (pp. 4–6) and
Appendix A (pp. 20–22) equipped with its modest realisability structure (Section 4, pp. 13–16)
before the four parametricity axioms:
* A modest Tarski universe `(U, El, realises)` closed under `⊥^U`, `⊤^U`, `Bool^U`, tracked
  dependent products `Π^U`, dependent sums `Σ^U`, and extensional identity types `=^U`.
* A large type `Size` with `0 : Size`, `↑ : Size → Size`, and a small mere-proposition
  preorder `leU : Size → Size → U` with strict order `i < j := ↑i ≤ j`.
* Impredicative size quantifiers `exU : (Size → U) → U` (with small-motive elimination `indEx`
  on parametric branches and its computation rule `indEx_beta`) and `allU : (Size → U) → U`
  (with parametric introduction `lamAll`, elimination `appAll`, `all_beta`, `all_eta`), together
  with the bounded quantifiers `diamondBoundedU` (`∃ j < i`) and `boxBoundedU` (`∀ j < i`).
* The well-founded size fixpoint operator `fix` with propositional computation rule `fix_beta`. -/
structure SizeCoreTheory : Type (max (u + 1) (v + 1)) where
  /-- Code universe `U` of small types. -/
  U : Type u
  /-- Decoding family `El : U → Type v` mapping small type codes to their carrier types. -/
  El : U → Type v

  /-- Modest realisability relation `n ⊩_A x` on decoded small types (Section 4.1, p. 13). -/
  realises : {A : U} → ℕ → El A → Prop
  /-- Every element of a decoded small type has at least one realiser `n ∈ ℕ`. -/
  realised : ∀ {A : U} (x : El A), ∃ (n : ℕ), realises n x
  /-- Modesty: a natural number `n` realises at most one element of `El A` (Definition 13, p. 13). -/
  modest : ∀ {A : U} (n : ℕ) (x y : El A), realises n x → realises n y → x = y

  /-- Code `⊥^U` for the small empty type (Appendix A, p. 20). -/
  botU : U
  /-- Decoding equivalence `El ⊥^U ≃ Empty`. -/
  El_botU : El botU ≃ Empty

  /-- Code `⊤^U` for the small unit type (Appendix A, p. 20). -/
  topU : U
  /-- Decoding equivalence `El ⊤^U ≃ Unit`. -/
  El_topU : El topU ≃ Unit
  /-- `0` realises the unique element of `El ⊤^U` (Definition 27, p. 29). -/
  realises_topU : ∀ (x : El topU), realises 0 x

  /-- Code `Bool^U` for the small boolean type (Appendix A, p. 20). -/
  boolU : U
  /-- Decoding equivalence `El Bool^U ≃ Bool`. -/
  El_boolU : El boolU ≃ Bool

  /-- Code `Π^U` for small dependent function types (Appendix A, p. 21 & Definition 32, p. 30). -/
  piU : (A : U) → (El A → U) → U
  /-- Decoding equivalence between `El (Π^U A B)` and tracked dependent functions
  `(x : El A) → El (B x)` (Section 4.1, p. 14 & Appendix C.5, p. 30). -/
  El_piU : ∀ (A : U) (B : El A → U),
    El (piU A B) ≃
      {f : (x : El A) → El (B x) //
        ∃ (c : TrackerCode), ∀ (x : El A) (n : ℕ),
          realises n x → realises (evalTracker c n) (f x)}
  /-- Realisability characterization for `Π^U A B` (Definition 32, p. 30). -/
  realises_piU : ∀ {A : U} {B : El A → U} (g : El (piU A B)) (e : ℕ),
    realises e g ↔ ∀ (x : El A) (n : ℕ),
      realises n x → realises (evalTracker (decodeTracker e) n) ((El_piU A B g).1 x)

  /-- Code `Σ^U` for small dependent pair types (Appendix A, p. 21 & Definition 35, p. 31). -/
  sigmaU : (A : U) → (El A → U) → U
  /-- Decoding equivalence `El (Σ^U A B) ≃ ((x : El A) × El (B x))` (validating β and η). -/
  El_sigmaU : ∀ (A : U) (B : El A → U), El (sigmaU A B) ≃ ((x : El A) × El (B x))
  /-- Realisability characterization for `Σ^U A B` via Cantor pairing (Definition 35, p. 31). -/
  realises_sigmaU : ∀ {A : U} {B : El A → U} (p : El (sigmaU A B)) (n : ℕ),
    realises n p ↔
      realises (Nat.unpair n).1 (El_sigmaU A B p).1 ∧
      realises (Nat.unpair n).2 (El_sigmaU A B p).2

  /-- Code `=^U_A` for small identity types (Appendix A, p. 21 & Definition 29, p. 29). -/
  idU : (A : U) → El A → El A → U
  /-- Decoding equivalence `El (idU A x y) ≃ PLift (x = y)`. -/
  El_idU : ∀ (A : U) (x y : El A), El (idU A x y) ≃ PLift (x = y)
  /-- `0` realises every witness of `El (idU A x y)` (Definition 29, p. 29). -/
  realises_idU : ∀ {A : U} {x y : El A} (p : El (idU A x y)), realises 0 p

  /-- The primitive large type `Size` of sizes (Section 2, p. 4 & Appendix A, p. 22). -/
  Size : Type u
  /-- Minimum size `0 : Size`. -/
  zero : Size
  /-- Successor size `↑i : Size`. -/
  succ : Size → Size
  /-- Small preorder `i ≤ j : U` on sizes. -/
  leU : Size → Size → U

  /-- `le_0 : 0 ≤ i` for all `i : Size` (Section 2, p. 5). -/
  le_zero : ∀ (i : Size), El (leU zero i)
  /-- `le_suc : i ≤ ↑i` for all `i : Size` (Section 2, p. 5). -/
  le_succ : ∀ (i : Size), El (leU i (succ i))
  /-- `le_refl : i ≤ i` for all `i : Size` (Section 2, p. 5). -/
  le_refl : ∀ (i : Size), El (leU i i)
  /-- `le_trans : i ≤ j → j ≤ k → i ≤ k` (Section 2, p. 5). -/
  le_trans : ∀ {i j k : Size}, El (leU i j) → El (leU j k) → El (leU i k)
  /-- `le_eq : p =_{i ≤ j} q`, witnessing that `i ≤ j` is a mere proposition (Section 2, p. 5). -/
  le_eq : ∀ {i j : Size} (p q : El (leU i j)), p = q
  /-- `0` realises every witness of `El (leU i j)` (Appendix C.7, p. 32). -/
  realises_leU : ∀ {i j : Size} (p : El (leU i j)), realises 0 p

  /-- Impredicative existential size quantifier `∃ i. A(i) : U`
  (Section 2, p. 5, Appendix A, p. 22 & Appendix C.6, p. 30). -/
  exU : (Size → U) → U
  /-- Existential introduction `⟨s, a⟩^∃ : El (∃ i. A(i))`. -/
  pairEx : {A : Size → U} → (s : Size) → El (A s) → El (exU A)
  /-- A realiser of `a : El (A s)` also realises `⟨s, a⟩^∃ : El (∃ i. A(i))`
  (Appendix C.6, Definition 42, p. 30). -/
  realises_pairEx : ∀ {A : Size → U} (s : Size) (a : El (A s)) (n : ℕ),
    realises n a → realises n (pairEx s a)
  /-- Every realiser of `z : El (∃ i. A(i))` realises some witness `a : El (A s)` with
  `⟨s, a⟩^∃ = z` (Appendix C.6, Definition 42, p. 30). -/
  realises_exU : ∀ {A : Size → U} (z : El (exU A)) (n : ℕ),
    realises n z → ∃ (s : Size) (a : El (A s)), pairEx s a = z ∧ realises n a
  /-- Existential elimination `ind_∃` restricted to small motives `P : El (∃ i. A(i)) → U`
  and uniformly tracked (parametric) branch families `p`
  (Section 2, p. 5, Appendix A, p. 22 & Section 4.5, p. 16). -/
  indEx : {A : Size → U} → (P : El (exU A) → U) →
    (p : (i : Size) → (x : El (A i)) → El (P (pairEx i x))) →
    (∃ (c : TrackerCode), ∀ (i : Size) (x : El (A i)) (n : ℕ),
      realises n x → realises (evalTracker c n) (p i x)) →
    (z : El (exU A)) → El (P z)
  /-- Computation rule `ind_∃(⟨s, a⟩^∃, p) = p(s, a)` (Section 2, p. 5 & Appendix A, p. 22). -/
  indEx_beta : ∀ {A : Size → U} (P : El (exU A) → U)
    (p : (i : Size) → (x : El (A i)) → El (P (pairEx i x)))
    (hp : ∃ (c : TrackerCode), ∀ (i : Size) (x : El (A i)) (n : ℕ),
      realises n x → realises (evalTracker c n) (p i x))
    (s : Size) (a : El (A s)),
    indEx P p hp (pairEx s a) = p s a

  /-- Impredicative universal size quantifier `∀ i. A(i) : U`
  (Section 2, p. 6, Appendix A, p. 22 & Appendix C.6, p. 30). -/
  allU : (Size → U) → U
  /-- Universal introduction `λ^∀ i. a(i) : El (∀ i. A(i))` for parametric families `a`
  possessing a uniform realiser across all sizes `i : Size` (Section 4.5, p. 15). -/
  lamAll : {A : Size → U} → (a : (i : Size) → El (A i)) →
    (∃ (n : ℕ), ∀ (i : Size), realises n (a i)) → El (allU A)
  /-- Universal elimination `f s : El (A s)`. -/
  appAll : {A : Size → U} → El (allU A) → (i : Size) → El (A i)
  /-- Realisability characterization for `∀ i. A(i)`: `n` realises `f` iff `n` realises
  `f i` at every size `i : Size` (Appendix C.6, Definition 40, p. 30). -/
  realises_allU : ∀ {A : Size → U} (f : El (allU A)) (n : ℕ),
    realises n f ↔ ∀ (i : Size), realises n (appAll f i)
  /-- Universal β-rule `(λ^∀ i. a(i)) s = a(s)`. -/
  all_beta : ∀ {A : Size → U} (a : (i : Size) → El (A i))
    (ha : ∃ (n : ℕ), ∀ (i : Size), realises n (a i)) (s : Size),
    appAll (lamAll a ha) s = a s
  /-- Universal η-rule `λ^∀ i. (f i) = f`. -/
  all_eta : ∀ {A : Size → U} (f : El (allU A))
    (hf : ∃ (n : ℕ), ∀ (i : Size), realises n (appAll f i)),
    lamAll (fun i => appAll f i) hf = f

  /-- Bounded existential quantifier `∃ j < i. X(j, p) : U`
  (Section 2, p. 5, Section 3, p. 10 & Appendix C.7, p. 32). -/
  diamondBoundedU : (i : Size) → ((j : Size) → El (leU (succ j) i) → U) → U
  /-- Bounded existential introduction `⟨j, ⟨p, a⟩⟩^∃ : El (∃ j < i. X(j, p))`. -/
  pairDiamondB : {i : Size} → {X : (j : Size) → El (leU (succ j) i) → U} →
    (j : Size) → (p : El (leU (succ j) i)) → El (X j p) → El (diamondBoundedU i X)
  /-- A realiser of `a : El (X j p)` also realises `pairDiamondB j p a` (Appendix C.7, p. 32). -/
  realises_pairDiamondB : ∀ {i : Size} {X : (j : Size) → El (leU (succ j) i) → U}
    (j : Size) (p : El (leU (succ j) i)) (a : El (X j p)) (n : ℕ),
    realises n a → realises n (pairDiamondB j p a)
  /-- Every realiser of `z : El (diamondBoundedU i X)` realises some witness `a : El (X j p)`
  with `pairDiamondB j p a = z`. -/
  realises_diamondBoundedU : ∀ {i : Size} {X : (j : Size) → El (leU (succ j) i) → U}
    (z : El (diamondBoundedU i X)) (n : ℕ),
    realises n z → ∃ (j : Size) (p : El (leU (succ j) i)) (a : El (X j p)),
      pairDiamondB j p a = z ∧ realises n a
  /-- Bounded existential elimination into small motives `P : El (diamondBoundedU i X) → U`. -/
  indDiamondB : {i : Size} → {X : (j : Size) → El (leU (succ j) i) → U} →
    (P : El (diamondBoundedU i X) → U) →
    (f : (j : Size) → (p : El (leU (succ j) i)) → (a : El (X j p)) →
      El (P (pairDiamondB j p a))) →
    (∃ (c : TrackerCode), ∀ (j : Size) (p : El (leU (succ j) i)) (a : El (X j p)) (n : ℕ),
      realises n a → realises (evalTracker c n) (f j p a)) →
    (z : El (diamondBoundedU i X)) → El (P z)
  /-- Computation rule for `indDiamondB`. -/
  indDiamondB_beta : ∀ {i : Size} {X : (j : Size) → El (leU (succ j) i) → U}
    (P : El (diamondBoundedU i X) → U)
    (f : (j : Size) → (p : El (leU (succ j) i)) → (a : El (X j p)) →
      El (P (pairDiamondB j p a)))
    (hf : ∃ (c : TrackerCode), ∀ (j : Size) (p : El (leU (succ j) i)) (a : El (X j p)) (n : ℕ),
      realises n a → realises (evalTracker c n) (f j p a))
    (j : Size) (p : El (leU (succ j) i)) (a : El (X j p)),
    indDiamondB P f hf (pairDiamondB j p a) = f j p a

  /-- Bounded universal quantifier `∀ j < i. X(j, p) : U`
  (Section 2, p. 5, Section 3, p. 10 & Appendix C.7, p. 32). -/
  boxBoundedU : (i : Size) → ((j : Size) → El (leU (succ j) i) → U) → U
  /-- Bounded universal introduction `λ j < i. f(j, p) : El (∀ j < i. X(j, p))`. -/
  lamBoxB : {i : Size} → {X : (j : Size) → El (leU (succ j) i) → U} →
    (f : (j : Size) → (p : El (leU (succ j) i)) → El (X j p)) →
    (∃ (n : ℕ), ∀ (j : Size) (p : El (leU (succ j) i)), realises n (f j p)) →
    El (boxBoundedU i X)
  /-- Bounded universal elimination `appBoxB g j p : El (X j p)`. -/
  appBoxB : {i : Size} → {X : (j : Size) → El (leU (succ j) i) → U} →
    El (boxBoundedU i X) → (j : Size) → (p : El (leU (succ j) i)) → El (X j p)
  /-- Realisability characterization for `∀ j < i. X(j, p)` (Appendix C.7, p. 32). -/
  realises_boxBoundedU : ∀ {i : Size} {X : (j : Size) → El (leU (succ j) i) → U}
    (g : El (boxBoundedU i X)) (n : ℕ),
    realises n g ↔ ∀ (j : Size) (p : El (leU (succ j) i)), realises n (appBoxB g j p)
  /-- Bounded universal β-rule. -/
  boxB_beta : ∀ {i : Size} {X : (j : Size) → El (leU (succ j) i) → U}
    (f : (j : Size) → (p : El (leU (succ j) i)) → El (X j p))
    (hf : ∃ (n : ℕ), ∀ (j : Size) (p : El (leU (succ j) i)), realises n (f j p))
    (j : Size) (p : El (leU (succ j) i)),
    appBoxB (lamBoxB f hf) j p = f j p
  /-- Bounded universal η-rule. -/
  boxB_eta : ∀ {i : Size} {X : (j : Size) → El (leU (succ j) i) → U}
    (g : El (boxBoundedU i X))
    (hg : ∃ (n : ℕ), ∀ (j : Size) (p : El (leU (succ j) i)), realises n (appBoxB g j p)),
    lamBoxB (fun j p => appBoxB g j p) hg = g

  /-- Well-founded size fixpoint operator `fix` (Section 2, p. 6 & Appendix A, p. 22):
  given any size-indexed type family `A : Size → Type (max u v)` and a step function
  `f : ∀ i, (∀ j, ↑j ≤ i → A j) → A i`, produces `fix f : ∀ i, A i`. -/
  fix : {A : Size → Type (max u v)} →
    ((i : Size) → ((j : Size) → El (leU (succ j) i) → A j) → A i) →
    (i : Size) → A i
  /-- Propositional computation rule `fix^β` (Section 2, p. 6 & Appendix A, p. 22):
  `fix f i = f i (fun j hji => fix f j)`. -/
  fix_beta : ∀ {A : Size → Type (max u v)}
    (f : (i : Size) → ((j : Size) → El (leU (succ j) i) → A j) → A i)
    (i : Size),
    fix f i = f i (fun j _ => fix f j)

namespace SizeCoreTheory

variable (T : SizeCoreTheory.{u, v})

/-- Decoded size preorder `Le i j := El (leU i j)` (Section 2, p. 5). -/
abbrev Le (i j : T.Size) : Type v := T.El (T.leU i j)

/-- Small strict size inequality code `i < j := ↑i ≤ j : U` (Section 2, p. 5). -/
abbrev ltU (i j : T.Size) : T.U := T.leU (T.succ i) j

/-- Decoded strict size inequality `Lt i j := El (ltU i j)` (Section 2, p. 5). -/
abbrev Lt (i j : T.Size) : Type v := T.El (T.ltU i j)

/-- Non-dependent small function space `A →^U B` (Appendix A, p. 21). -/
abbrev arrU (A B : T.U) : T.U := T.piU A (fun _ => B)

/-- Non-dependent small product `A ×^U B` (Appendix A, p. 21). -/
abbrev prodU (A B : T.U) : T.U := T.sigmaU A (fun _ => B)

/-- A dependent function `f : (x : El A) → El (B x)` is tracked if some `c : TrackerCode`
maps any realiser of `x` to a realiser of `f x`. -/
abbrev IsTrackedPi {A : T.U} {B : T.El A → T.U} (f : (x : T.El A) → T.El (B x)) : Prop :=
  ∃ (c : TrackerCode), ∀ (x : T.El A) (n : ℕ),
    T.realises n x → T.realises (evalTracker c n) (f x)

/-- A non-dependent function `f : El A → El B` is tracked if it is tracked as a dependent
function into the constant family `fun _ => B`. -/
abbrev IsTracked {A B : T.U} (f : T.El A → T.El B) : Prop :=
  T.IsTrackedPi (B := fun _ => B) f

/-- A size-indexed family `a : (i : Size) → El (A i)` is parametric if some `n ∈ ℕ`
uniformly realises `a i` at all sizes `i : Size`. -/
abbrev IsParametric {A : T.Size → T.U} (a : (i : T.Size) → T.El (A i)) : Prop :=
  ∃ (n : ℕ), ∀ (i : T.Size), T.realises n (a i)

/-- A size-indexed branch family `p : (i : Size) → (x : El (A i)) → El (P (pairEx i x))`
is parametric if some `c : TrackerCode` uniformly tracks `p i` across all sizes `i : Size`. -/
abbrev IsParametricEx {A : T.Size → T.U} (P : T.El (T.exU A) → T.U)
    (p : (i : T.Size) → (x : T.El (A i)) → T.El (P (T.pairEx i x))) : Prop :=
  ∃ (c : TrackerCode), ∀ (i : T.Size) (x : T.El (A i)) (n : ℕ),
    T.realises n x → T.realises (evalTracker c n) (p i x)

/-- Transport preserves realisers across equal type codes `h : A = B`. -/
theorem realises_cast {A B : T.U} (h : A = B) (x : T.El A) (n : ℕ) :
    T.realises n (Equiv.cast (congrArg T.El h) x) ↔ T.realises n x := by
  subst h
  rfl

/-- Realiser construction for a pair `(El_sigmaU A B).invFun ⟨a, b⟩`. -/
theorem realises_sigmaMk {A : T.U} (B : T.El A → T.U)
    (a : T.El A) (b : T.El (B a)) {n₁ n₂ : ℕ}
    (ha : T.realises n₁ a) (hb : T.realises n₂ b) :
    T.realises (Nat.pair n₁ n₂) ((T.El_sigmaU A B).invFun ⟨a, b⟩) := by
  rw [T.realises_sigmaU]
  have h : T.El_sigmaU A B ((T.El_sigmaU A B).invFun ⟨a, b⟩) = ⟨a, b⟩ :=
    (T.El_sigmaU A B).right_inv ⟨a, b⟩
  rw [h]
  simp only [Nat.unpair_pair]
  exact ⟨ha, hb⟩

/-- Dependent function introduction `λ^Π x. f(x) : El (Π^U A B)` for tracked `f`. -/
def lamPi {A : T.U} {B : T.El A → T.U} (f : (x : T.El A) → T.El (B x))
    (hf : T.IsTrackedPi f) : T.El (T.piU A B) :=
  (T.El_piU A B).invFun ⟨f, hf⟩

/-- Dependent function elimination `app(f, x) : El (B x)`. -/
def appPi {A : T.U} {B : T.El A → T.U} (f : T.El (T.piU A B)) (x : T.El A) :
    T.El (B x) :=
  ((T.El_piU A B).toFun f).1 x

theorem appPi_tracked {A : T.U} {B : T.El A → T.U} (f : T.El (T.piU A B)) :
    T.IsTrackedPi (fun x => T.appPi f x) :=
  ((T.El_piU A B).toFun f).2

@[simp]
theorem pi_beta {A : T.U} {B : T.El A → T.U} (f : (x : T.El A) → T.El (B x))
    (hf : T.IsTrackedPi f) (x : T.El A) :
    T.appPi (T.lamPi f hf) x = f x :=
  congrFun (congrArg Subtype.val ((T.El_piU A B).right_inv ⟨f, hf⟩)) x

@[simp]
theorem pi_eta {A : T.U} {B : T.El A → T.U} (f : T.El (T.piU A B))
    (hf : T.IsTrackedPi (fun x => T.appPi f x) := T.appPi_tracked f) :
    T.lamPi (fun x => T.appPi f x) hf = f :=
  (T.El_piU A B).left_inv f

theorem lamPi_congr {A : T.U} {B : T.El A → T.U}
    {f₁ f₂ : (x : T.El A) → T.El (B x)} (h : f₁ = f₂)
    (hf₁ : T.IsTrackedPi f₁) (hf₂ : T.IsTrackedPi f₂) :
    T.lamPi f₁ hf₁ = T.lamPi f₂ hf₂ := by
  subst h
  rfl

theorem pi_ext {A : T.U} {B : T.El A → T.U} {f g : T.El (T.piU A B)}
    (h : ∀ x, T.appPi f x = T.appPi g x) : f = g := by
  rw [← T.pi_eta f, ← T.pi_eta g]
  exact T.lamPi_congr (funext h) _ _

theorem realises_lamPi {A : T.U} {B : T.El A → T.U}
    (f : (x : T.El A) → T.El (B x)) (hf : T.IsTrackedPi f)
    (c : TrackerCode)
    (hc : ∀ (x : T.El A) (n : ℕ), T.realises n x → T.realises (evalTracker c n) (f x)) :
    T.realises (encodeTracker c) (T.lamPi f hf) := by
  rw [T.realises_piU]
  intro x n hnx
  rw [decodeTracker_encodeTracker]
  change T.realises (evalTracker c n) (T.appPi (T.lamPi f hf) x)
  rw [T.pi_beta]
  exact hc x n hnx

theorem realises_appPi {A : T.U} {B : T.El A → T.U}
    (g : T.El (T.piU A B)) (x : T.El A) {e n : ℕ}
    (hg : T.realises e g) (hx : T.realises n x) :
    T.realises (evalTracker (decodeTracker e) n) (T.appPi g x) :=
  (T.realises_piU g e).mp hg x n hx

/-- Post-composition action on internal non-dependent functions `El (C →^U X)` by a tracked map `f`. -/
def mapArr {C X Y : T.U} (f : T.El X → T.El Y) (hf : T.IsTracked f)
    (h : T.El (T.piU C (fun _ => X))) : T.El (T.piU C (fun _ => Y)) :=
  T.lamPi (fun c => f (T.appPi h c)) (by
    rcases hf with ⟨cf, hcf⟩
    rcases T.realised h with ⟨eh, heh⟩
    refine ⟨.comp cf (decodeTracker eh), fun c n hnc => ?_⟩
    exact hcf (T.appPi h c) _ (T.realises_appPi h c heh hnc))

theorem realises_mapArr {C X Y : T.U} (f : T.El X → T.El Y) (hf : T.IsTracked f)
    (cf : TrackerCode)
    (hcf : ∀ (x : T.El X) (n : ℕ), T.realises n x → T.realises (evalTracker cf n) (f x))
    (h : T.El (T.piU C (fun _ => X))) {eh : ℕ} (heh : T.realises eh h) :
    T.realises (evalTracker (.postComp cf) eh) (T.mapArr f hf h) := by
  unfold mapArr
  exact T.realises_lamPi _ _ (.comp cf (decodeTracker eh)) (fun c n hnc =>
    hcf (T.appPi h c) _ (T.realises_appPi h c heh hnc))

@[simp]
theorem mapArr_id {C X : T.U} (h : T.El (T.piU C (fun _ => X)))
    {hid : T.IsTracked (A := X) (B := X) (fun x => x)} :
    T.mapArr (fun x => x) hid h = h :=
  T.pi_eta h _

@[simp]
theorem mapArr_comp {C X Y Z : T.U} (g : T.El Y → T.El Z) {hg : T.IsTracked g}
    (f : T.El X → T.El Y) {hf : T.IsTracked f}
    {hgf : T.IsTracked (fun x => g (f x))}
    (h : T.El (T.piU C (fun _ => X))) :
    T.mapArr (fun x => g (f x)) hgf h = T.mapArr g hg (T.mapArr f hf h) := by
  apply T.pi_ext
  intro c
  unfold mapArr
  rw [T.pi_beta, T.pi_beta, T.pi_beta]

theorem appAll_parametric {A : T.Size → T.U} (f : T.El (T.allU A)) :
    T.IsParametric (fun i => T.appAll f i) := by
  rcases T.realised f with ⟨n, hnf⟩
  exact ⟨n, (T.realises_allU f n).mp hnf⟩

theorem lamAll_congr {A : T.Size → T.U} {a₁ a₂ : (i : T.Size) → T.El (A i)}
    (h : a₁ = a₂) (ha₁ : T.IsParametric a₁) (ha₂ : T.IsParametric a₂) :
    T.lamAll a₁ ha₁ = T.lamAll a₂ ha₂ := by
  subst h
  rfl

theorem all_ext {A : T.Size → T.U} {f g : T.El (T.allU A)}
    (h : ∀ i, T.appAll f i = T.appAll g i) : f = g := by
  rw [← T.all_eta f (T.appAll_parametric f), ← T.all_eta g (T.appAll_parametric g)]
  exact T.lamAll_congr (funext h) _ _

theorem realises_lamAll {A : T.Size → T.U} (a : (i : T.Size) → T.El (A i))
    (ha : T.IsParametric a) {n : ℕ} (hn : ∀ (i : T.Size), T.realises n (a i)) :
    T.realises n (T.lamAll a ha) := by
  rw [T.realises_allU]
  intro i
  rw [T.all_beta]
  exact hn i

/-- Equivalence `El (∀ i. A i) ≃ {a : (i : Size) → El (A i) // IsParametric a}` induced by
`lamAll`, `appAll`, `all_beta`, and `all_eta`. -/
def El_allU (A : T.Size → T.U) :
    T.El (T.allU A) ≃ {a : (i : T.Size) → T.El (A i) // T.IsParametric a} where
  toFun f := ⟨T.appAll f, T.appAll_parametric f⟩
  invFun a := T.lamAll a.1 a.2
  left_inv f := T.all_eta f (T.appAll_parametric f)
  right_inv a := Subtype.ext (funext (T.all_beta a.1 a.2))

/-- Bounded existential quantifier `◇_i A := ∃ j < i. A(j) : U`
(Section 2, p. 5 & Section 3, p. 9). -/
abbrev diamondU (A : T.Size → T.U) (i : T.Size) : T.U :=
  T.diamondBoundedU i (fun j _ => A j)

/-- Bounded universal quantifier `□_i A := ∀ j < i. A(j) : U`
(Section 2, p. 5 & Section 3, p. 9). -/
abbrev boxU (A : T.Size → T.U) (i : T.Size) : T.U :=
  T.boxBoundedU i (fun j _ => A j)

/-- Introduction rule for `◇_i A`: given `j : Size`, `p : j < i`, and `a : El (A j)`,
construct `⟨j, ⟨p, a⟩⟩^∃ : El (◇_i A)`. -/
abbrev pairDiamond {A : T.Size → T.U} {i : T.Size} (j : T.Size) (p : T.Lt j i) (a : T.El (A j)) :
    T.El (T.diamondU A i) :=
  T.pairDiamondB j p a

theorem realises_pairDiamond {A : T.Size → T.U} {i : T.Size}
    (j : T.Size) (p : T.Lt j i) (a : T.El (A j)) {n : ℕ} (hna : T.realises n a) :
    T.realises n (T.pairDiamond j p a) :=
  T.realises_pairDiamondB (X := fun j _ => A j) j p a n hna

/-- Non-dependent small eliminator for `∃ i. A(i)` into any small type `C : U`. -/
def elimEx {A : T.Size → T.U} {C : T.U}
    (f : (i : T.Size) → T.El (A i) → T.El C)
    (hf : T.IsParametricEx (fun _ => C) f)
    (z : T.El (T.exU A)) : T.El C :=
  T.indEx (fun _ => C) f hf z

@[simp]
theorem elimEx_beta {A : T.Size → T.U} {C : T.U}
    (f : (i : T.Size) → T.El (A i) → T.El C)
    (hf : T.IsParametricEx (fun _ => C) f)
    (s : T.Size) (a : T.El (A s)) :
    T.elimEx f hf (T.pairEx s a) = f s a :=
  T.indEx_beta (fun _ => C) f hf s a

theorem realises_elimEx {A : T.Size → T.U} {C : T.U}
    (f : (i : T.Size) → T.El (A i) → T.El C)
    {hf : T.IsParametricEx (fun _ => C) f}
    (c : TrackerCode)
    (hc : ∀ (i : T.Size) (x : T.El (A i)) (n : ℕ),
      T.realises n x → T.realises (evalTracker c n) (f i x))
    (z : T.El (T.exU A)) {n : ℕ} (hnz : T.realises n z) :
    T.realises (evalTracker c n) (T.elimEx f hf z) := by
  rcases T.realises_exU z n hnz with ⟨s, a, rfl, hna⟩
  rw [T.elimEx_beta]
  exact hc s a n hna

/-- Equality principle for maps out of `∃ i. A(i)` into a small type `C : U`, proved by
applying `indEx` to the small identity motive `w ↦ idU C (f w) (g w)` (tracked by `.const 0`). -/
theorem ex_ind_eq {A : T.Size → T.U} {C : T.U}
    (f g : T.El (T.exU A) → T.El C)
    (h : ∀ (s : T.Size) (a : T.El (A s)), f (T.pairEx s a) = g (T.pairEx s a))
    (z : T.El (T.exU A)) : f z = g z :=
  ((T.El_idU C (f z) (g z)).toFun
    (T.indEx (fun w => T.idU C (f w) (g w))
      (fun s a => (T.El_idU C (f (T.pairEx s a)) (g (T.pairEx s a))).invFun ⟨h s a⟩)
      ⟨.const 0, fun _ _ _ _ => T.realises_idU _⟩
      z)).down

/-- Parametricity condition for bounded existential elimination `elimDiamond`. -/
abbrev IsParametricDiamond {A : T.Size → T.U} {i : T.Size} {C : T.U}
    (f : (j : T.Size) → T.Lt j i → T.El (A j) → T.El C) : Prop :=
  ∃ (c : TrackerCode), ∀ (j : T.Size) (p : T.Lt j i) (a : T.El (A j)) (n : ℕ),
    T.realises n a → T.realises (evalTracker c n) (f j p a)

/-- Non-dependent small eliminator for `◇_i A` into any small type `C : U`. -/
def elimDiamond {A : T.Size → T.U} {i : T.Size} {C : T.U}
    (f : (j : T.Size) → T.Lt j i → T.El (A j) → T.El C)
    (hf : T.IsParametricDiamond f)
    (z : T.El (T.diamondU A i)) : T.El C :=
  T.indDiamondB (fun _ => C) f hf z

@[simp]
theorem elimDiamond_beta {A : T.Size → T.U} {i : T.Size} {C : T.U}
    (f : (j : T.Size) → T.Lt j i → T.El (A j) → T.El C)
    (hf : T.IsParametricDiamond f)
    (j : T.Size) (p : T.Lt j i) (a : T.El (A j)) :
    T.elimDiamond f hf (T.pairDiamond j p a) = f j p a :=
  T.indDiamondB_beta (fun _ => C) f hf j p a

theorem realises_elimDiamond {A : T.Size → T.U} {i : T.Size} {C : T.U}
    (f : (j : T.Size) → T.Lt j i → T.El (A j) → T.El C)
    (hf : T.IsParametricDiamond f)
    (c : TrackerCode)
    (hc : ∀ (j : T.Size) (p : T.Lt j i) (a : T.El (A j)) (n : ℕ),
      T.realises n a → T.realises (evalTracker c n) (f j p a))
    (z : T.El (T.diamondU A i)) {n : ℕ} (hnz : T.realises n z) :
    T.realises (evalTracker c n) (T.elimDiamond f hf z) := by
  rcases T.realises_diamondBoundedU z n hnz with ⟨j, p, a, rfl, hna⟩
  rw [T.elimDiamond_beta]
  exact hc j p a n hna

/-- Equality principle for maps out of `◇_i A` into a small type `C : U`. -/
theorem diamond_ind_eq {A : T.Size → T.U} {i : T.Size} {C : T.U}
    (f g : T.El (T.diamondU A i) → T.El C)
    (h : ∀ (j : T.Size) (p : T.Lt j i) (a : T.El (A j)),
      f (T.pairDiamond j p a) = g (T.pairDiamond j p a))
    (z : T.El (T.diamondU A i)) : f z = g z :=
  ((T.El_idU C (f z) (g z)).toFun
    (T.indDiamondB (fun w => T.idU C (f w) (g w))
      (fun j p a => (T.El_idU C (f (T.pairDiamond j p a)) (g (T.pairDiamond j p a))).invFun ⟨h j p a⟩)
      ⟨.const 0, fun _ _ _ _ _ => T.realises_idU _⟩
      z)).down

/-- Parametricity condition for bounded universal introduction `lamBox`. -/
abbrev IsParametricBox {A : T.Size → T.U} {i : T.Size}
    (f : (j : T.Size) → T.Lt j i → T.El (A j)) : Prop :=
  ∃ (n : ℕ), ∀ (j : T.Size) (p : T.Lt j i), T.realises n (f j p)

/-- Introduction rule for `□_i A`: package a parametric bounded section
`f : ∀ j, j < i → El (A j)` into `El (□_i A)`. -/
def lamBox {A : T.Size → T.U} {i : T.Size}
    (f : (j : T.Size) → T.Lt j i → T.El (A j))
    (hf : T.IsParametricBox f) : T.El (T.boxU A i) :=
  T.lamBoxB f hf

/-- Elimination rule for `□_i A`: apply `g : El (□_i A)` to `j : Size` and `p : j < i`. -/
def appBox {A : T.Size → T.U} {i : T.Size}
    (g : T.El (T.boxU A i)) (j : T.Size) (p : T.Lt j i) : T.El (A j) :=
  T.appBoxB g j p

@[simp]
theorem appBox_lamBox {A : T.Size → T.U} {i : T.Size}
    (f : (j : T.Size) → T.Lt j i → T.El (A j))
    (hf : T.IsParametricBox f) (j : T.Size) (p : T.Lt j i) :
    T.appBox (T.lamBox f hf) j p = f j p :=
  T.boxB_beta f hf j p

theorem realises_lamBox {A : T.Size → T.U} {i : T.Size}
    (f : (j : T.Size) → T.Lt j i → T.El (A j))
    (hf : T.IsParametricBox f) {n : ℕ}
    (hn : ∀ (j : T.Size) (p : T.Lt j i), T.realises n (f j p)) :
    T.realises n (T.lamBox f hf) := by
  unfold lamBox
  rw [T.realises_boxBoundedU]
  intro j p
  rw [T.boxB_beta]
  exact hn j p

theorem realises_appBox {A : T.Size → T.U} {i : T.Size}
    (g : T.El (T.boxU A i)) (j : T.Size) (p : T.Lt j i) {e : ℕ}
    (hg : T.realises e g) :
    T.realises e (T.appBox g j p) :=
  (T.realises_boxBoundedU g e).mp hg j p

theorem appBox_parametric {A : T.Size → T.U} {i : T.Size} (g : T.El (T.boxU A i)) :
    T.IsParametricBox (fun j p => T.appBox g j p) := by
  rcases T.realised g with ⟨e, heg⟩
  exact ⟨e, fun j p => T.realises_appBox g j p heg⟩

theorem lamBox_congr {A : T.Size → T.U} {i : T.Size}
    {f₁ f₂ : (j : T.Size) → T.Lt j i → T.El (A j)}
    (h : f₁ = f₂) (hf₁ : T.IsParametricBox f₁) (hf₂ : T.IsParametricBox f₂) :
    T.lamBox f₁ hf₁ = T.lamBox f₂ hf₂ := by
  subst h
  rfl

@[simp]
theorem box_eta {A : T.Size → T.U} {i : T.Size} (g : T.El (T.boxU A i))
    (hg : T.IsParametricBox (fun j p => T.appBox g j p) := T.appBox_parametric g) :
    T.lamBox (fun j p => T.appBox g j p) hg = g :=
  T.boxB_eta g hg

theorem box_ext {A : T.Size → T.U} {i : T.Size} {g₁ g₂ : T.El (T.boxU A i)}
    (h : ∀ j p, T.appBox g₁ j p = T.appBox g₂ j p) : g₁ = g₂ := by
  rw [← T.box_eta g₁, ← T.box_eta g₂]
  exact T.lamBox_congr (funext fun j => funext fun p => h j p) _ _

/-- Equivalence between `El (□_i A)` and parametric bounded sections
`{f : (j : Size) → Lt j i → El (A j) // IsParametricBox f}`. -/
def El_boxU (A : T.Size → T.U) (i : T.Size) :
    T.El (T.boxU A i) ≃ {f : (j : T.Size) → T.Lt j i → T.El (A j) // T.IsParametricBox f} where
  toFun g := ⟨T.appBox g, T.appBox_parametric g⟩
  invFun f := T.lamBox f.1 f.2
  left_inv g := T.box_eta g
  right_inv f := Subtype.ext (funext fun j => funext fun p => T.appBox_lamBox f.1 f.2 j p)

/-- Type of fixpoint solutions for a step function
`f : (i : Size) → ((j : Size) → Lt j i → A j) → A i` (Lemma 1, p. 6):
`{h : ∀ i, A i // ∀ i, h i = f i (fun j p => h j)}`. -/
def FixpointSolution {A : T.Size → Type (max u v)}
    (f : (i : T.Size) → ((j : T.Size) → T.Lt j i → A j) → A i) :
    Type (max u v) :=
  {h : (i : T.Size) → A i // ∀ (i : T.Size), h i = f i (fun j _ => h j)}

/-! ## 4. Canonical Quantifier Maps (Section 2, pp. 7–8 & Appendix A, p. 23) -/

/-- Forward map of Proposition 2(a) (p. 7):
`Π x : A. ∀ i. B(x, i) → ∀ i. Π x : A. B(x, i)`. -/
def swapPiAll (A : T.U) (B : T.El A → T.Size → T.U) :
    T.El (T.piU A (fun x => T.allU (fun i => B x i))) →
    T.El (T.allU (fun i => T.piU A (fun x => B x i))) :=
  fun f =>
    T.lamAll (fun i =>
      T.lamPi (fun x => T.appAll (T.appPi f x) i) (by
        rcases T.realised f with ⟨e, hef⟩
        refine ⟨decodeTracker e, fun x n hnx => ?_⟩
        exact (T.realises_allU (T.appPi f x) _).mp (T.realises_appPi f x hef hnx) i)) (by
      rcases T.realised f with ⟨e, hef⟩
      refine ⟨encodeTracker (decodeTracker e), fun i => ?_⟩
      refine T.realises_lamPi _ _ (decodeTracker e) (fun x n hnx => ?_)
      exact (T.realises_allU (T.appPi f x) _).mp (T.realises_appPi f x hef hnx) i)

/-- Inverse map of Proposition 2(a) (p. 7):
`∀ i. Π x : A. B(x, i) → Π x : A. ∀ i. B(x, i)`. -/
def unswapPiAll (A : T.U) (B : T.El A → T.Size → T.U) :
    T.El (T.allU (fun i => T.piU A (fun x => B x i))) →
    T.El (T.piU A (fun x => T.allU (fun i => B x i))) :=
  fun g =>
    T.lamPi (fun x =>
      T.lamAll (fun i => T.appPi (T.appAll g i) x) (by
        rcases T.realised g with ⟨e, heg⟩
        rcases T.realised x with ⟨n, hnx⟩
        refine ⟨evalTracker (decodeTracker e) n, fun i => ?_⟩
        exact T.realises_appPi (T.appAll g i) x ((T.realises_allU g e).mp heg i) hnx)) (by
      rcases T.realised g with ⟨e, heg⟩
      refine ⟨decodeTracker e, fun x n hnx => ?_⟩
      refine T.realises_lamAll _ _ (fun i => ?_)
      exact T.realises_appPi (T.appAll g i) x ((T.realises_allU g e).mp heg i) hnx)

theorem realises_unswapPiAll (A : T.U) (B : T.El A → T.Size → T.U)
    (g : T.El (T.allU (fun i => T.piU A (fun x => B x i)))) {e : ℕ}
    (heg : T.realises e g) :
    T.realises (encodeTracker (decodeTracker e)) (T.unswapPiAll A B g) := by
  unfold unswapPiAll
  refine T.realises_lamPi _ _ (decodeTracker e) (fun x n hnx => ?_)
  refine T.realises_lamAll _ _ (fun i => ?_)
  exact T.realises_appPi (T.appAll g i) x ((T.realises_allU g e).mp heg i) hnx

/-- Forward map of Proposition 2(b) (p. 7):
`Σ x : A. ∃ i. B(x, i) → ∃ i. Σ x : A. B(x, i)` defined via `elimEx` into the small type
`∃ i. Σ x : A. B(x, i) : U`. -/
def swapSigmaEx (A : T.U) (B : T.El A → T.Size → T.U) :
    T.El (T.sigmaU A (fun x => T.exU (fun i => B x i))) →
    T.El (T.exU (fun i => T.sigmaU A (fun x => B x i))) :=
  fun p =>
    let ⟨x, z⟩ := (T.El_sigmaU A (fun x => T.exU (fun i => B x i))).toFun p
    T.elimEx (fun i b =>
      T.pairEx i ((T.El_sigmaU A (fun x => B x i)).invFun ⟨x, b⟩)) (by
        rcases T.realised x with ⟨nx, hnx⟩
        refine ⟨.pair (.const nx) .id, fun i b n hnb => ?_⟩
        exact T.realises_pairEx i _ _
          (T.realises_sigmaMk (fun x => B x i) x b hnx hnb)) z

theorem realises_swapSigmaEx (A : T.U) (B : T.El A → T.Size → T.U)
    (p : T.El (T.sigmaU A (fun x => T.exU (fun i => B x i)))) {n : ℕ}
    (hnp : T.realises n p) :
    T.realises n (T.swapSigmaEx A B p) := by
  unfold swapSigmaEx
  rcases (T.realises_sigmaU p n).mp hnp with ⟨hn1, hn2⟩
  rw [← Nat.pair_unpair n]
  exact T.realises_elimEx
    (fun i b => T.pairEx i ((T.El_sigmaU A (fun x => B x i)).invFun
      ⟨(T.El_sigmaU A (fun x => T.exU (fun i => B x i)) p).1, b⟩))
    (.pair (.const (Nat.unpair n).1) .id)
    (fun i b m hmb => T.realises_pairEx i _ _
      (T.realises_sigmaMk (fun x => B x i) _ b hn1 hmb))
    (T.El_sigmaU A (fun x => T.exU (fun i => B x i)) p).2 hn2

/-- Inverse map of Proposition 2(b) (p. 7):
`∃ i. Σ x : A. B(x, i) → Σ x : A. ∃ i. B(x, i)` defined via `elimEx` into the small type
`Σ x : A. ∃ i. B(x, i) : U`. -/
def unswapSigmaEx (A : T.U) (B : T.El A → T.Size → T.U) :
    T.El (T.exU (fun i => T.sigmaU A (fun x => B x i))) →
    T.El (T.sigmaU A (fun x => T.exU (fun i => B x i))) :=
  T.elimEx (fun i pair =>
    let ⟨x, b⟩ := (T.El_sigmaU A (fun x => B x i)).toFun pair
    (T.El_sigmaU A (fun x => T.exU (fun i => B x i))).invFun ⟨x, T.pairEx i b⟩) (by
      refine ⟨.id, fun i pair n hnp => ?_⟩
      rcases (T.realises_sigmaU pair n).mp hnp with ⟨hn1, hn2⟩
      have h := T.realises_sigmaMk (fun x => T.exU (fun i => B x i))
        (T.El_sigmaU A (fun x => B x i) pair).1
        (T.pairEx i (T.El_sigmaU A (fun x => B x i) pair).2)
        hn1 (T.realises_pairEx i _ _ hn2)
      simpa [evalTracker] using h)

/-- First canonical parametricity map (Section 2, p. 7 & Appendix A, p. 23):
`(∃ i. Π x : A. ∃ j < i. B(x, j)) → (Π x : A. ∃ i. B(x, i))`. -/
def canExPi (A : T.U) (B : T.El A → T.Size → T.U) :
    T.El (T.exU (fun i => T.piU A (fun x => T.diamondU (B x) i))) →
    T.El (T.piU A (fun x => T.exU (B x))) :=
  T.elimEx (fun _ f =>
    T.lamPi (fun x =>
      T.elimDiamond (fun j _ b => T.pairEx j b)
        ⟨.id, fun j _ b _ hnb => T.realises_pairEx j b _ hnb⟩
        (T.appPi f x)) (by
      rcases T.realised f with ⟨ef, hef⟩
      refine ⟨decodeTracker ef, fun x n hnx => ?_⟩
      have hfx := T.realises_appPi f x hef hnx
      exact T.realises_elimDiamond (fun j _ b => T.pairEx j b) _ .id
        (fun j _ b _ hnb => T.realises_pairEx j b _ hnb) (T.appPi f x) hfx)) (by
    refine ⟨.postComp .id, fun i f ef hef => ?_⟩
    refine T.realises_lamPi _ _ (.comp .id (decodeTracker ef)) (fun x n hnx => ?_)
    have hfx := T.realises_appPi f x hef hnx
    exact T.realises_elimDiamond (fun j _ b => T.pairEx j b) _ .id
      (fun j _ b _ hnb => T.realises_pairEx j b _ hnb) (T.appPi f x) hfx)

/-- Second canonical parametricity map (Section 2, p. 7 & Appendix A, p. 23):
`(Σ x : A. ∀ i. B(x, i)) → (∀ i. Σ x : A. B(x, i))`. -/
def canAllSigma (A : T.U) (B : T.El A → T.Size → T.U) :
    T.El (T.sigmaU A (fun x => T.allU (B x))) →
    T.El (T.allU (fun i => T.sigmaU A (fun x => B x i))) :=
  fun p =>
    let ⟨x, f⟩ := (T.El_sigmaU A (fun x => T.allU (B x))).toFun p
    T.lamAll (fun i =>
      (T.El_sigmaU A (fun x => B x i)).invFun ⟨x, T.appAll f i⟩) (by
        rcases T.realised x with ⟨nx, hnx⟩
        rcases T.realised f with ⟨nf, hnf⟩
        refine ⟨Nat.pair nx nf, fun i => ?_⟩
        exact T.realises_sigmaMk (fun x => B x i) x (T.appAll f i) hnx
          ((T.realises_allU f nf).mp hnf i))

/-- Third canonical parametricity map (Section 2, p. 7 & Appendix A, p. 23):
`(∃ i. ∃ j < i. C(j)) → (∃ i. C(i))`. -/
def canExLt (C : T.Size → T.U) :
    T.El (T.exU (fun i => T.diamondU C i)) →
    T.El (T.exU C) :=
  T.elimEx (fun _ d =>
    T.elimDiamond (fun j _ c => T.pairEx j c)
      ⟨.id, fun j _ c _ hnc => T.realises_pairEx j c _ hnc⟩ d) (by
    refine ⟨.id, fun i d n hnd => ?_⟩
    exact T.realises_elimDiamond (fun j _ c => T.pairEx j c) _ .id
      (fun j _ c _ hnc => T.realises_pairEx j c _ hnc) d hnd)

/-- Fourth canonical parametricity map (Section 2, p. 7 & Appendix A, p. 23):
`(∀ i. C(i)) → (∀ i. ∀ j < i. C(j))`. -/
def canAllLt (C : T.Size → T.U) :
    T.El (T.allU C) →
    T.El (T.allU (fun i => T.boxU C i)) :=
  fun f => T.lamAll (fun _ =>
    T.lamBox (fun j _ => T.appAll f j) (by
      rcases T.realised f with ⟨nf, hnf⟩
      exact ⟨nf, fun j _ => (T.realises_allU f nf).mp hnf j⟩)) (by
    rcases T.realised f with ⟨nf, hnf⟩
    refine ⟨nf, fun _ => ?_⟩
    exact T.realises_lamBox _ _ (fun j _ => (T.realises_allU f nf).mp hnf j))

theorem canAllLt_tracked (C : T.Size → T.U) :
    T.IsTracked (T.canAllLt C) := by
  refine ⟨.id, fun f nf hnf => ?_⟩
  unfold canAllLt
  refine T.realises_lamAll _ _ (fun _ => ?_)
  exact T.realises_lamBox _ _ (fun j _ => (T.realises_allU f nf).mp hnf j)

/-- Canonical map `∃ i. A → A` for a size-independent small type `A : U`
(Proposition 3, p. 8). -/
def constExToEl (A : T.U) : T.El (T.exU (fun _ => A)) → T.El A :=
  T.elimEx (fun _ a => a) ⟨.id, fun _ _ _ hna => hna⟩

/-- Canonical map `A → ∀ i. A` for a size-independent small type `A : U`
(Proposition 3, p. 8). -/
def elToConstAll (A : T.U) : T.El A → T.El (T.allU (fun _ => A)) :=
  fun a => T.lamAll (fun _ => a) (by
    rcases T.realised a with ⟨n, hna⟩
    exact ⟨n, fun _ => hna⟩)

end SizeCoreTheory

/-- `ParametricSizeTheory` extends `SizeCoreTheory` with the four parametricity equivalence
axioms of Section 2.3 (p. 7) and Appendix A (p. 23) together with the uniform realiser
tracking of their inverses (Section 4.5, pp. 15–16 & Appendix C.9, pp. 34–35):
1. `∃` parametric over `Π` (`param_ex_pi`): `canExPi A B` is a half-adjoint equivalence.
2. `∀` parametric over `Σ` (`param_all_sigma`): `canAllSigma A B` is a half-adjoint equivalence.
3. `∃` parametric over `<` (`param_ex_lt`): `canExLt C` is a half-adjoint equivalence.
4. `∀` parametric over `<` (`param_all_lt`): `canAllLt C` is a half-adjoint equivalence. -/
structure ParametricSizeTheory : Type (max (u + 1) (v + 1)) extends SizeCoreTheory.{u, v} where
  /-- Axiom 1 (`∃` parametric over `Π`, p. 7):
  `(∃ i. Π x : A. ∃ j < i. B(x, j)) ≃ (Π x : A. ∃ i. B(x, i))`. -/
  param_ex_pi : ∀ (A : U) (B : El A → Size → U),
    IsHAEquiv (toSizeCoreTheory.canExPi A B)
  /-- Uniform tracker `.id` for `(param_ex_pi A B).inv`. -/
  param_ex_pi_tracked : ∀ (A : U) (B : El A → Size → U)
    (g : El (piU A (fun x => exU (B x)))) (n : ℕ),
    realises n g → realises n ((param_ex_pi A B).inv g)
  /-- Axiom 2 (`∀` parametric over `Σ`, p. 7):
  `(Σ x : A. ∀ i. B(x, i)) ≃ (∀ i. Σ x : A. B(x, i))`. -/
  param_all_sigma : ∀ (A : U) (B : El A → Size → U),
    IsHAEquiv (toSizeCoreTheory.canAllSigma A B)
  /-- Uniform tracker `.id` for `(param_all_sigma A B).inv`. -/
  param_all_sigma_tracked : ∀ (A : U) (B : El A → Size → U)
    (w : El (allU (fun i => sigmaU A (fun x => B x i)))) (n : ℕ),
    realises n w → realises n ((param_all_sigma A B).inv w)
  /-- Axiom 3 (`∃` parametric over `<`, p. 7):
  `(∃ i. ∃ j < i. C(j)) ≃ (∃ i. C(i))`. -/
  param_ex_lt : ∀ (C : Size → U),
    IsHAEquiv (toSizeCoreTheory.canExLt C)
  /-- Uniform tracker `.id` for `(param_ex_lt C).inv`. -/
  param_ex_lt_tracked : ∀ (C : Size → U) (z : El (exU C)) (n : ℕ),
    realises n z → realises n ((param_ex_lt C).inv z)
  /-- Axiom 4 (`∀` parametric over `<`, p. 7):
  `(∀ i. C(i)) ≃ (∀ i. ∀ j < i. C(j))`. -/
  param_all_lt : ∀ (C : Size → U),
    IsHAEquiv (toSizeCoreTheory.canAllLt C)
  /-- Uniform tracker `.id` for `(param_all_lt C).inv`. -/
  param_all_lt_tracked : ∀ (C : Size → U) (w : El (allU (fun i => toSizeCoreTheory.boxU C i))) (n : ℕ),
    realises n w → realises n ((param_all_lt C).inv w)

end LaarakkerOttenVanDenBerg2026


