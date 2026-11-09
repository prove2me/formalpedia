-- Prove2me | Definitions.Def_ThreeColorFloodIt_FixedHeight_grammar
-- name    : ThreeColorFloodIt_FixedHeight_grammar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:36.222336+00:00
-- url     : https://prove2.me/theorems/ffd7af02-1fac-41fc-b77d-c064dba40cfb
-- title:
--   Charged elementary pushdown rules, finite frames and finite grammar witnesses
-- statement:
--   An elementary rule replaces the top symbol by zero, one or two symbols, with a nonnegative integer charge. The four symbols are three colors and a bottom marker; a replacement $BC$ has $B$ on top. Frame runs rewrite only above a fixed untouched suffix, exposing it only at termination.
--
--   The grammar uses finite inductive derivations for pop, one-symbol and two-symbol replacements. Its value is
--   $$D[p,A,q]=\inf\{d:\text{a finite frame-removing run of cost }d\text{ exists}\}.$$
--   An absent run has value infinity. The capped grammar retains only derivations whose every subtree costs at most $M$. Circular zero-cost equations cannot construct a derivation. A macro compiler introduces private phase controls and expands pops, pushes and charges into elementary rules; the final bottom pop enters the accepting control directly. These definitions support exact optimization and witness recovery.
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 15 (PDF 16), §4.5, Eqs. (3)–(5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf

import Mathlib

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

abbrev StackSymbol := Option (Fin 3)

structure StackRule (Q : Type) where
  source : Q
  top : StackSymbol
  target : Q
  replacement : List StackSymbol
  cost : ℕ

def Elementary {Q : Type} (r : StackRule Q) : Prop := r.replacement.length ≤ 2

abbrev WeightedPDS (Q : Type) := Set (StackRule Q)

/-- Frame execution always rewrites a nonempty word ABOVE the fixed suffix.
The suffix is exposed only at termination; it is never read or changed. -/
inductive FrameRun {Q : Type} (S : WeightedPDS Q) (suffix : List StackSymbol) :
    Q → List StackSymbol → Q → ℕ → Prop
  | done (q) : FrameRun S suffix q [] q 0
  | step (r : StackRule Q) (tail : List StackSymbol) (q : Q) (d : ℕ)
      (rule : r ∈ S) (rest : FrameRun S suffix r.target (r.replacement ++ tail) q d) :
      FrameRun S suffix r.source (r.top :: tail) q (r.cost + d)

/-- Finite derivation trees for exactly equations (3), (4), (5); B is above C. -/
inductive Derivation {Q : Type} (S : WeightedPDS Q) :
    Q → StackSymbol → Q → ℕ → Prop
  | pop (r : StackRule Q) (hr : r ∈ S) (h : r.replacement = []) :
      Derivation S r.source r.top r.target r.cost
  | one (r : StackRule Q) (B : StackSymbol) (q : Q) (d : ℕ)
      (hr : r ∈ S) (h : r.replacement = [B])
      (child : Derivation S r.target B q d) :
      Derivation S r.source r.top q (r.cost + d)
  | two (r : StackRule Q) (B C : StackSymbol) (t q : Q) (d e : ℕ)
      (hr : r ∈ S) (h : r.replacement = [B, C])
      (left : Derivation S r.target B t d) (right : Derivation S t C q e) :
      Derivation S r.source r.top q (r.cost + d + e)

inductive CappedDerivation {Q : Type} (S : WeightedPDS Q) (M : ℕ) :
    Q → StackSymbol → Q → ℕ → Prop
  | pop (r : StackRule Q) (hr : r ∈ S) (h : r.replacement = []) (cap : r.cost ≤ M) :
      CappedDerivation S M r.source r.top r.target r.cost
  | one (r : StackRule Q) (B : StackSymbol) (q : Q) (d : ℕ)
      (hr : r ∈ S) (h : r.replacement = [B])
      (child : CappedDerivation S M r.target B q d) (cap : r.cost + d ≤ M) :
      CappedDerivation S M r.source r.top q (r.cost + d)
  | two (r : StackRule Q) (B C : StackSymbol) (t q : Q) (d e : ℕ)
      (hr : r ∈ S) (h : r.replacement = [B, C])
      (left : CappedDerivation S M r.target B t d)
      (right : CappedDerivation S M t C q e) (cap : r.cost + d + e ≤ M) :
      CappedDerivation S M r.source r.top q (r.cost + d + e)

noncomputable def frameValue {Q : Type} (S : WeightedPDS Q)
    (p : Q) (A : StackSymbol) (q : Q) : WithTop ℕ :=
  sInf {v | ∃ d, FrameRun S [] p [A] q d ∧ v = (d : WithTop ℕ)}

/-- A macro compiles to a sequence of charged elementary operations. -/
inductive StackAction where
  | pop (a : StackSymbol)
  | push (a : StackSymbol)
  | charge (d : ℕ)

structure MacroRule (Q : Type) where
  source : Q
  actions : List StackAction
  target : Q

inductive ExpandedControl {Q : Type} (macros : Set (MacroRule Q)) where
  | base (q : Q)
  | phase (r : {r // r ∈ macros}) (position : Fin (r.val.actions.length + 1))

/-- Macro choice enters a private phase. Each operation inspects/replaces only
the top symbol; pushes replace A by [B,A]. End phases return to base control. -/
def expandMacros {Q : Type} (macros : Set (MacroRule Q)) :
    WeightedPDS (ExpandedControl macros) :=
  {r | (∃ (m : {m // m ∈ macros}) (A : StackSymbol),
        r = ⟨.base m.val.source, A, .phase m 0, [A], 0⟩) ∨
    (∃ (m : {m // m ∈ macros}) (A : StackSymbol),
        r = ⟨.phase m (Fin.last m.val.actions.length), A, .base m.val.target, [A], 0⟩) ∨
    (∃ (m : {m // m ∈ macros}) (i : Fin m.val.actions.length) (A : StackSymbol),
      (∃ B, m.val.actions.get i = .pop B ∧
        r = ⟨.phase m i.castSucc, B, .phase m i.succ, [], 0⟩) ∨
      (∃ B, m.val.actions.get i = .push B ∧
        r = ⟨.phase m i.castSucc, A, .phase m i.succ, [B, A], 0⟩) ∨
      (∃ d, m.val.actions.get i = .charge d ∧
        r = ⟨.phase m i.castSucc, A, .phase m i.succ, [A], d⟩)) ∨
    (∃ (m : {m // m ∈ macros}) (i : Fin m.val.actions.length),
      i.val + 1 = m.val.actions.length ∧ m.val.actions.get i = .pop none ∧
        r = ⟨.phase m i.castSucc, none, .base m.val.target, [], 0⟩)}

end ThreeColorFloodIt.FixedHeight


