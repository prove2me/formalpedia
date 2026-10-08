-- Prove2me | Definitions.Def_MFOTLMon_Monitor_Syntax
-- name    : MFOTLMon_Monitor_Syntax
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T03:33:57.274978+00:00
-- url     : https://prove2.me/theorems/dcd68e6a-e52a-47d7-9c45-290c409dbbcc
-- title:
--   Definitions 2.1–2.2 and §2.2, pp. 15:4–15:6 — MFOTL formulas, temporal structures over ℕ, satisfaction, free variables, tsub, bounded formulas, φ^(D̄,τ̄,i)
-- statement:
--   This file sets up the syntax and semantics of **metric first-order temporal logic** (MFOTL).
--
--   **Signatures and intervals.** A signature $S=(C,R,\iota)$ consists of a finite set $C$ of constant symbols, a finite set $R$ of predicates and an arity map $\iota:R\to\mathbb N$; there are no function symbols. Variables are the natural numbers, and a term is a variable or a constant. An interval is a nonempty set $[b,b')=\{a\in\mathbb N\mid b\le a<b'\}$ with $b\in\mathbb N$, $b'\in\mathbb N\cup\{\infty\}$ and $b<b'$.
--
--   **Formulas** (Definition 2.1). They are built from equalities $t\approx t'$ and atoms $r(t_1,\dots,t_{\iota(r)})$ by $\neg\varphi$, $\varphi\vee\psi$, $\exists x.\,\varphi$ and the temporal operators $\bullet_I\varphi$ (previous), $\circ_I\varphi$ (next), $\varphi\,\mathsf S_I\,\psi$ (since) and $\varphi\,\mathsf U_I\,\psi$ (until), for every interval $I$. The connectives $\wedge$, $\to$, $\forall$, $\blacklozenge_I$, $\blacksquare_I$, $\lozenge_I$, $\square_I$ and $\mathit{true}:=\exists x.\,x\approx x$ are abbreviations.
--
--   **Temporal structures.** Following the restrictions of §3.1, the domain is $\mathbb N$. A temporal structure $(\bar{\mathcal D},\bar\tau)$ assigns to each time point $i\in\mathbb N$ and predicate $r$ a relation $r^{\mathcal D_i}\subseteq\mathbb N^{\iota(r)}$, to each constant a rigid value $c^{\bar{\mathcal D}}\in\mathbb N$, and to each time point a time stamp $\tau_i\in\mathbb N$, where $\tau_0\le\tau_1\le\cdots$ and for every $\tau\in\mathbb N$ some $\tau_i>\tau$.
--
--   **Satisfaction** (Definition 2.2). For a valuation $v:\mathbb N\to\mathbb N$ and a time point $i$, the relation $(\bar{\mathcal D},\bar\tau,v,i)\models\varphi$ is defined as usual on the first-order connectives, and
--   $$
--   \begin{aligned}
--   (\bar{\mathcal D},\bar\tau,v,i)\models\bullet_I\psi &\iff i>0,\ \tau_i-\tau_{i-1}\in I,\ (\bar{\mathcal D},\bar\tau,v,i-1)\models\psi,\\
--   (\bar{\mathcal D},\bar\tau,v,i)\models\circ_I\psi &\iff \tau_{i+1}-\tau_i\in I,\ (\bar{\mathcal D},\bar\tau,v,i+1)\models\psi,\\
--   (\bar{\mathcal D},\bar\tau,v,i)\models\psi\,\mathsf S_I\,\psi' &\iff \exists j\le i:\ \tau_i-\tau_j\in I,\ (\dots,j)\models\psi',\ (\dots,k)\models\psi \text{ for all } j<k\le i,\\
--   (\bar{\mathcal D},\bar\tau,v,i)\models\psi\,\mathsf U_I\,\psi' &\iff \exists j\ge i:\ \tau_j-\tau_i\in I,\ (\dots,j)\models\psi',\ (\dots,k)\models\psi \text{ for all } i\le k<j.
--   \end{aligned}
--   $$
--
--   **Terminology** (§2.2). $\mathit{free}(\varphi)$ is the set of free variables; the vector $\bar x=(x_1,\dots,x_n)$ of free variables lists them in increasing order. The **satisfying set** at time point $i$ is
--   $$
--   \varphi^{(\bar{\mathcal D},\bar\tau,i)}=\{\bar d\in\mathbb N^n\mid (\bar{\mathcal D},\bar\tau,v[\bar x\mapsto\bar d],i)\models\varphi \text{ for some valuation } v\}.
--   $$
--   $\mathit{tsub}(\varphi)$ is the set of top-level temporal subformulas ($\mathit{tsub}(\neg\psi)=\mathit{tsub}(\exists x.\psi)=\mathit{tsub}(\psi)$, $\mathit{tsub}(\psi\vee\psi')=\mathit{tsub}(\psi)\cup\mathit{tsub}(\psi')$, $\{\varphi\}$ for temporal $\varphi$, $\emptyset$ for atoms), $\mathit{dsub}(\varphi)$ the set of direct subformulas. A formula is **bounded** if the interval of every $\mathsf U_I$ in it is finite. Two further predicates on a formula $\Phi$ express the paper's two "without loss of generality" assumptions: every temporal subformula occurs only once in $\Phi$ (§3.6), and the two direct subformulas of every $\mathsf S_I$ and $\mathsf U_I$ subformula of $\Phi$ have the same free variables (§3.4).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** The domain is fixed to $\mathbb N$, as §3.1 assumes ($|\bar{\mathcal D}|=\mathbb N$); constant domains and rigid constants then hold by construction. Tuples are lists of natural numbers (an $r^{\mathcal D_i}$ contains only lists of length $\iota(r)$); `satSet` lists tuples in the order of the sorted free variables. Interval upper bounds live in $\mathbb N_\infty$. Since $\bar\tau$ is monotone, the natural-number differences $\tau_i-\tau_j$ ($j\le i$) are exact. Sets of subformulas are represented as lists; the temporal subformulas of $\Phi$ are listed with multiplicity, so "occurs only once" is `List.Nodup`.
-- source:
--   Basin, Klaedtke, Müller, Zălinescu, Monitoring metric first-order temporal properties, J. ACM 62(2), Article 15 (2015), pp. 15:4–15:6, Definitions 2.1, 2.2 and §2.2; §3.1 (p. 15:8) for the domain ℕ; WLOG assumptions of §3.4 (p. 15:10) and §3.6 (p. 15:15)

import Mathlib

namespace MFOTLMon.Monitor

/-- A signature `S = (C, R, ι)` (§2.1, p. 15:4): a finite set `C` of constant symbols, a finite set
`R` of predicates, and the arity function `ι : R → ℕ`. There are no function symbols. -/
structure Signature where
  C : Type
  R : Type
  arity : R → ℕ
  [finC : Fintype C]
  [finR : Fintype R]

attribute [instance] Signature.finC Signature.finR

variable {S : Signature}

/-- Terms `t ∈ V ∪ C`: the variables are `V = ℕ` (`Sum.inl x`), the constants are `C` (`Sum.inr c`). -/
abbrev Term (S : Signature) := ℕ ⊕ S.C

/-- A nonempty interval `[lo, hi) = {a ∈ ℕ | lo ≤ a < hi}` with `lo ∈ ℕ`, `hi ∈ ℕ ∪ {∞}` and
`lo < hi` (the set `𝕀` of §2.1, p. 15:4). -/
structure Interval where
  lo : ℕ
  hi : ℕ∞
  lo_lt_hi : (lo : ℕ∞) < hi

/-- Membership `t ∈ [lo, hi)`. -/
def Interval.Mem (I : Interval) (t : ℕ) : Prop := I.lo ≤ t ∧ (t : ℕ∞) < I.hi

/-- MFOTL formulas over the signature `S` (Definition 2.1, p. 15:4). -/
inductive Formula (S : Signature) where
  /-- `t ≈ t'` -/
  | eq : Term S → Term S → Formula S
  /-- `r(t₁, …, t_{ι(r)})` -/
  | pred : (r : S.R) → (Fin (S.arity r) → Term S) → Formula S
  /-- `¬φ` -/
  | neg : Formula S → Formula S
  /-- `φ ∨ ψ` -/
  | or : Formula S → Formula S → Formula S
  /-- `∃x. φ` -/
  | ex : ℕ → Formula S → Formula S
  /-- `●_I φ` (previous) -/
  | prev : Interval → Formula S → Formula S
  /-- `○_I φ` (next) -/
  | next : Interval → Formula S → Formula S
  /-- `φ S_I ψ` (since) -/
  | since : Interval → Formula S → Formula S → Formula S
  /-- `φ U_I ψ` (until) -/
  | until : Interval → Formula S → Formula S → Formula S

namespace Formula

/-- `true := ∃x. x ≈ x` (§2.2, p. 15:6), with `x` the variable `0`. -/
def tt : Formula S := .ex 0 (.eq (.inl 0) (.inl 0))
/-- `φ ∧ ψ := ¬(¬φ ∨ ¬ψ)` -/
def and (φ ψ : Formula S) : Formula S := .neg (.or (.neg φ) (.neg ψ))
/-- `φ → ψ := ¬φ ∨ ψ` -/
def imp (φ ψ : Formula S) : Formula S := .or (.neg φ) ψ
/-- `∀x. φ := ¬∃x. ¬φ` -/
def all (x : ℕ) (φ : Formula S) : Formula S := .neg (.ex x (.neg φ))
/-- `◆_I φ := true S_I φ` -/
def once (I : Interval) (φ : Formula S) : Formula S := .since I tt φ
/-- `■_I φ := ¬◆_I ¬φ` -/
def hist (I : Interval) (φ : Formula S) : Formula S := .neg (once I (.neg φ))
/-- `◇_I φ := true U_I φ` -/
def eventually (I : Interval) (φ : Formula S) : Formula S := .until I tt φ
/-- `□_I φ := ¬◇_I ¬φ` -/
def always (I : Interval) (φ : Formula S) : Formula S := .neg (eventually I (.neg φ))

/-- Number of constructors, used to order subformulas (a proper subformula is strictly smaller). -/
def size : Formula S → ℕ
  | .eq _ _ => 1
  | .pred _ _ => 1
  | .neg φ => size φ + 1
  | .or φ ψ => size φ + size ψ + 1
  | .ex _ φ => size φ + 1
  | .prev _ φ => size φ + 1
  | .next _ φ => size φ + 1
  | .since _ φ ψ => size φ + size ψ + 1
  | .until _ φ ψ => size φ + size ψ + 1

/-- A formula is temporal if its main connective is a temporal operator. -/
def isTemporal : Formula S → Bool
  | .prev _ _ => true
  | .next _ _ => true
  | .since _ _ _ => true
  | .until _ _ _ => true
  | _ => false

end Formula

/-- A temporal structure `(D̄, τ̄)` over `S` with domain `|D̄| = ℕ` (§2.1, p. 15:4, specialized as in
§3.1, p. 15:8): `rel i r = r^{Dᵢ} ⊆ ℕ^{ι(r)}` (tuples as lists of length `ι(r)`), rigid constants
`const c = c^{D̄}`, and time stamps `τ` that are monotone and make progress. -/
structure TempStruct (S : Signature) where
  rel : ℕ → S.R → Set (List ℕ)
  rel_arity : ∀ i r l, l ∈ rel i r → l.length = S.arity r
  const : S.C → ℕ
  τ : ℕ → ℕ
  mono : Monotone τ
  progress : ∀ t : ℕ, ∃ i, t < τ i

/-- Value of a term under a valuation `v` (and the constants' interpretation `const`). -/
def evalTerm (const : S.C → ℕ) (v : ℕ → ℕ) : Term S → ℕ
  | .inl x => v x
  | .inr c => const c

/-- The satisfaction relation `(D̄, τ̄, v, i) ⊨ φ` (Definition 2.2, p. 15:5). -/
def Sat (D : TempStruct S) : Formula S → (ℕ → ℕ) → ℕ → Prop
  | .eq t t', v, _ => evalTerm D.const v t = evalTerm D.const v t'
  | .pred r ts, v, i => List.ofFn (fun k => evalTerm D.const v (ts k)) ∈ D.rel i r
  | .neg ψ, v, i => ¬ Sat D ψ v i
  | .or ψ ψ', v, i => Sat D ψ v i ∨ Sat D ψ' v i
  | .ex x ψ, v, i => ∃ d : ℕ, Sat D ψ (Function.update v x d) i
  | .prev I ψ, v, i => 0 < i ∧ I.Mem (D.τ i - D.τ (i - 1)) ∧ Sat D ψ v (i - 1)
  | .next I ψ, v, i => I.Mem (D.τ (i + 1) - D.τ i) ∧ Sat D ψ v (i + 1)
  | .since I ψ ψ', v, i =>
      ∃ j, j ≤ i ∧ I.Mem (D.τ i - D.τ j) ∧ Sat D ψ' v j ∧ ∀ k, j < k → k ≤ i → Sat D ψ v k
  | .until I ψ ψ', v, i =>
      ∃ j, i ≤ j ∧ I.Mem (D.τ j - D.τ i) ∧ Sat D ψ' v j ∧ ∀ k, i ≤ k → k < j → Sat D ψ v k

/-- Variables of a term. -/
def termVars : Term S → Finset ℕ
  | .inl x => {x}
  | .inr _ => ∅

/-- The free variables `free(φ)` (§2.2, p. 15:5). -/
def free : Formula S → Finset ℕ
  | .eq t t' => termVars t ∪ termVars t'
  | .pred _ ts => Finset.univ.biUnion fun k => termVars (ts k)
  | .neg ψ => free ψ
  | .or ψ ψ' => free ψ ∪ free ψ'
  | .ex x ψ => (free ψ).erase x
  | .prev _ ψ => free ψ
  | .next _ ψ => free ψ
  | .since _ ψ ψ' => free ψ ∪ free ψ'
  | .until _ ψ ψ' => free ψ ∪ free ψ'

/-- The fixed vector `x̄ = (x₁, …, xₙ)` of free variables of `φ`: `free(φ)` sorted increasingly. -/
def freeList (φ : Formula S) : List ℕ := (free φ).sort (· ≤ ·)

/-- `v[x̄ ↦ d̄]`: the valuation mapping `xs[k]` to `ds[k]` and every other variable to `v`'s value. -/
def assign (v : ℕ → ℕ) (xs ds : List ℕ) : ℕ → ℕ :=
  fun y => if y ∈ xs then ds.getD (xs.idxOf y) 0 else v y

/-- The satisfying set `φ^{(D̄,τ̄,i)} = {d̄ ∈ ℕⁿ | (D̄, τ̄, v[x̄ ↦ d̄], i) ⊨ φ for some v}` (§2.2,
p. 15:6), with `x̄ = freeList φ` and tuples as lists of length `n = |free(φ)|`. -/
def satSet (D : TempStruct S) (φ : Formula S) (i : ℕ) : Set (List ℕ) :=
  {ds | ds.length = (freeList φ).length ∧ ∃ v : ℕ → ℕ, Sat D φ (assign v (freeList φ) ds) i}

/-- The top-level temporal subformulas `tsub(φ)` (§2.2, p. 15:5), as a list. -/
def tsub : Formula S → List (Formula S)
  | .eq _ _ => []
  | .pred _ _ => []
  | .neg ψ => tsub ψ
  | .or ψ ψ' => tsub ψ ++ tsub ψ'
  | .ex _ ψ => tsub ψ
  | .prev I ψ => [.prev I ψ]
  | .next I ψ => [.next I ψ]
  | .since I ψ ψ' => [.since I ψ ψ']
  | .until I ψ ψ' => [.until I ψ ψ']

/-- The direct subformulas `dsub(φ)` (§2.2, p. 15:6), as a list. -/
def dsub : Formula S → List (Formula S)
  | .eq _ _ => []
  | .pred _ _ => []
  | .neg ψ => [ψ]
  | .ex _ ψ => [ψ]
  | .prev _ ψ => [ψ]
  | .next _ ψ => [ψ]
  | .or ψ ψ' => [ψ, ψ']
  | .since _ ψ ψ' => [ψ, ψ']
  | .until _ ψ ψ' => [ψ, ψ']

/-- All subformula occurrences of `φ` (including `φ`), in preorder. -/
def subformulas : Formula S → List (Formula S)
  | .eq t t' => [.eq t t']
  | .pred r ts => [.pred r ts]
  | .neg ψ => .neg ψ :: subformulas ψ
  | .or ψ ψ' => .or ψ ψ' :: (subformulas ψ ++ subformulas ψ')
  | .ex x ψ => .ex x ψ :: subformulas ψ
  | .prev I ψ => .prev I ψ :: subformulas ψ
  | .next I ψ => .next I ψ :: subformulas ψ
  | .since I ψ ψ' => .since I ψ ψ' :: (subformulas ψ ++ subformulas ψ')
  | .until I ψ ψ' => .until I ψ ψ' :: (subformulas ψ ++ subformulas ψ')

/-- The temporal subformula occurrences of `Φ`. -/
def tempSubs (Φ : Formula S) : List (Formula S) := (subformulas Φ).filter Formula.isTemporal

/-- `φ` is bounded: the interval of every `U_I` occurring in `φ` is finite (§2.2, p. 15:5). -/
def Bounded : Formula S → Prop
  | .eq _ _ => True
  | .pred _ _ => True
  | .neg ψ => Bounded ψ
  | .or ψ ψ' => Bounded ψ ∧ Bounded ψ'
  | .ex _ ψ => Bounded ψ
  | .prev _ ψ => Bounded ψ
  | .next _ ψ => Bounded ψ
  | .since _ ψ ψ' => Bounded ψ ∧ Bounded ψ'
  | .until I ψ ψ' => I.hi ≠ ⊤ ∧ Bounded ψ ∧ Bounded ψ'

/-- Each temporal subformula occurs only once in `Φ` (the WLOG assumption of §3.6, p. 15:15). -/
def TemporalSubformulasOnce (Φ : Formula S) : Prop := (tempSubs Φ).Nodup

/-- The two direct subformulas of every `S_I` and `U_I` subformula have the same free variables (the
WLOG assumption of §3.4, p. 15:10). -/
def DirectFreeAligned : Formula S → Prop
  | .eq _ _ => True
  | .pred _ _ => True
  | .neg ψ => DirectFreeAligned ψ
  | .or ψ ψ' => DirectFreeAligned ψ ∧ DirectFreeAligned ψ'
  | .ex _ ψ => DirectFreeAligned ψ
  | .prev _ ψ => DirectFreeAligned ψ
  | .next _ ψ => DirectFreeAligned ψ
  | .since _ ψ ψ' => free ψ = free ψ' ∧ DirectFreeAligned ψ ∧ DirectFreeAligned ψ'
  | .until _ ψ ψ' => free ψ = free ψ' ∧ DirectFreeAligned ψ ∧ DirectFreeAligned ψ'

end MFOTLMon.Monitor


