-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_Repair
-- name    : KSATSingleFlip_Connect_Repair
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:07:18.907193+00:00
-- url     : https://prove2.me/theorems/4565afa5-7507-4288-ab89-9f32eeea7ea8
-- title:
--   Repairs, Repair (Algorithm 3), FindPath (Algorithm 4) and the counts NoTree, ForcingLink, MultiLink
-- statement:
--   $\Phi^+$ is a clause list, $\Phi_0\subseteq\Phi^+$ a set $I_0$ of its positions.
--
--   * Definition 7.3 (p. 53): $(U,y)$ is an $(x,W)$-repair (`IsRepair`) if $U\supseteq W$, $y\in\Omega_{\Phi^+}$, $y = x$ off $U$, and for every sub-formula $\Psi\subseteq\Phi^+$ and $\sigma\in\Omega_\Psi$ agreeing with $x$ off $U$ there is a satisfying path in $\Omega_\Psi$ from $\sigma$ to $y$ of length $d_H(\sigma,y)$. Good (`IsGoodRepair`): $|U|\le \frac{1}{2\rho}|W| + \frac{\rho^2 n}{8}$.
--   * Definition 7.10: a pair matching on positions $J$ (`IsPairMatching`): two-element $M_C\subseteq\mathrm{vbl}(C)$, pairwise disjoint; $V(M)$ = `matchedVars`.
--   * Algorithm 3 (pp. 60–61). State `RState`: $U$, the retained trees $F$ with associated clauses, the pair matching $(J,M)$; $A$, $V(F)$, assigned, pending ($\neg$assigned and $\mathrm{sat}_x(C)\subseteq U$), and the output (line 14: flip $V(F)$, make both literals on each $M_C$ true). `RStep`: one while-iteration on a pending clause $C$: if a small ($\le(\ln k)^6$ variables) complete forcing tree of $\Phi_0$ under $x$ rooted in $\mathrm{vbl}(C)$ avoids $U$, retain one (tree repair); otherwise extend the pair matching to $J\cup\{C\}$ keeping all matched variables matched (Augment; `Fail` iff no pair matching on $J\cup\{C\}$ exists), add $V(M)$ to $U$, drop retained trees meeting $V(M)$. The paper resolves the choices (which pending clause, which tree, which shortest augmenting paths) by fixed lexicographic rules (p. 60); `RStep` allows every resolution, so the paper's deterministic run is one of the runs. `RepairRun … s r i`: a run with $i$ loop iterations returning $r$ (`none` = Fail); `RepairReach`: partial runs. `repairCost n |Φ⁺| i` $= (i+2)(n+|\Phi^+|)$: the declared cost model — one preprocessing pass, one pass per iteration (clause scan, tree enumeration at $O_k(1)$ per root, at most two BFS), one output pass, each charged $n+|\Phi^+|$.
--   * Algorithm 4 (p. 65): `greedyWalk` flips the least $u$ with $z(u)\ne t(u)$ and $z\oplus u\in\Omega_\Phi$ (fuel $n$); `findPath Φ y y' t` concatenates the walk from $y$ to $t$ with the reversed walk from $y'$ to $t$ (shared endpoint $t$ once). `findPathCost` $= (\text{length}+2)(n+|\Phi|) + n\cdot(\text{number of assignments written})$: one clause scan per flip plus writing the path.
--   * §7.3 counts (p. 62) for fixed $x,\Phi_0,\Phi^+$: $C_{\mathrm{force}}$ = clauses of $\Phi_0$ with one $x$-true literal, $C_{\mathrm{multi}}$ = clauses of $\Phi^+$ with at least two; `NoTree k Φ⁺ I₀ x B`, `ForcingLink`, `MultiLink` exactly as on p. 62; `RepairBounds` = bounds (i)–(iii) of Lemma 7.11; `omittedWeak` = $\{C\in\Phi^+\setminus\Phi_0 : |\mathrm{sat}_x(C)|\le1\}$.
-- source:
--   Wang, Yin, Yu, Zhang (2026), Single-Variable Connectivity in Random k-SAT, arXiv:2611.05981 (held version, SHA-256 1821a501…58b80f5), Definition 7.3 (printed p. 53, PDF 55), §7.3 Definition 7.10, Algorithm 3 and p. 62 (PDF 62–64), Algorithm 4 (p. 65, PDF 67)

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_Model
import Definitions.Def_KSATSingleFlip_Connect_FactorGraph

noncomputable section

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-! # Repairs, Repair (Algorithm 3), FindPath (Algorithm 4) and the small-set counts

Wang, Yin, Yu, Zhang (2026), arXiv:2611.05981: Definition 7.3 (printed p. 53), §7.3
(pp. 60–62: Definition 7.10, Algorithm 3, the counts `NoTree`, `ForcingLink`, `MultiLink`),
§7.4 (p. 65, Algorithm 4).

`Φ⁺` is a clause list; the sub-formula `Φ₀ ⊆ Φ⁺` is the set `I₀` of its positions. Clauses are
handled by position, so identical copies are distinct clauses. -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `(U, y)` is an `(x, W)`-repair for `Φ⁺` (Definition 7.3): `U ⊇ W`, `y ∈ Ω_{Φ⁺}`, `y = x` off
`U`, and for every sub-formula `Ψ ⊆ Φ⁺` (positions `I`) and every `σ ∈ Ω_Ψ` agreeing with `x`
outside `U` there is a satisfying path in `Ω_Ψ` from `σ` to `y` of length `d_H(σ, y)`. -/
def IsRepair (Φp : GFormula V) (x : V → Bool) (W U : Finset V) (y : V → Bool) : Prop :=
  W ⊆ U ∧ y ∈ sols Φp ∧ (∀ u, u ∉ U → y u = x u) ∧
    ∀ (I : Finset (Fin Φp.length)) (σ : V → Bool), σ ∈ sols (subF Φp I) →
      (∀ u, u ∉ U → σ u = x u) →
        ∃ p, IsSatPath (subF Φp I) p σ y ∧ pathLength p = hamming σ y

/-- A good repair (Definition 7.3, printed p. 53): `|U| ≤ |W|/(2ρ) + ρ² n/8`. -/
def IsGoodRepair {n : ℕ} (k : ℕ) (Φp : GFormula (Fin n)) (x : Fin n → Bool) (W U : Finset (Fin n))
    (y : Fin n → Bool) : Prop :=
  IsRepair Φp x W U y ∧ (U.card : ℝ) ≤ W.card / (2 * rho k) + rho k ^ 2 * n / 8

/-- A pair matching (Definition 7.10) on the clause positions `J`: each `M c` (`c ∈ J`) is a
two-element subset of `vbl(c)`, and these sets are pairwise disjoint. -/
def IsPairMatching (Φp : GFormula V) (J : Finset (Fin Φp.length)) (M : Fin Φp.length → Finset V) :
    Prop :=
  (∀ c ∈ J, M c ⊆ vbl (Φp.get c) ∧ (M c).card = 2) ∧
    ∀ c ∈ J, ∀ c' ∈ J, c ≠ c' → Disjoint (M c) (M c')

/-- The matched variable set `V(M)`. -/
def matchedVars (Φp : GFormula V) (J : Finset (Fin Φp.length)) (M : Fin Φp.length → Finset V) :
    Finset V :=
  J.biUnion M

/-- A small complete forcing tree for Repair: a forcing tree of `Φ₀ = Φ⁺_{I₀}` under `x`, complete
in `Φ₀`, with at most `(ln k)^6` variables. -/
def IsSmallTree (k : ℕ) (Φp : GFormula V) (I0 : Finset (Fin Φp.length)) (x : V → Bool)
    (T : ForcingTree Φp x) : Prop :=
  T.CompleteIn I0 ∧ (T.size : ℝ) ≤ Real.log k ^ 6

/-- A state of Repair: the repair set `U`, the retained trees `F` (each with its associated clause),
and the pair matching `(J, M)`. -/
structure RState (Φp : GFormula V) (x : V → Bool) where
  U : Finset V
  F : List (ForcingTree Φp x × Fin Φp.length)
  J : Finset (Fin Φp.length)
  M : Fin Φp.length → Finset V

namespace RState

variable {Φp : GFormula V} {x : V → Bool}

/-- `A`: the clauses of the retained trees and their associated clauses. -/
def A (s : RState Φp x) : Finset (Fin Φp.length) :=
  (s.F.map fun p => insert p.2 p.1.cls).foldr (· ∪ ·) ∅

/-- `V(F)`: the variables of the retained trees. -/
def VF (s : RState Φp x) : Finset V := (s.F.map fun p => p.1.vars).foldr (· ∪ ·) ∅

/-- A clause is assigned if it belongs to `A ∪ J`. -/
def Assigned (s : RState Φp x) (c : Fin Φp.length) : Prop := c ∈ s.A ∨ c ∈ s.J

/-- A clause the while-loop of Algorithm 3 may process: unassigned, with `sat_x(C) ⊆ U`. -/
def Pending (s : RState Φp x) (c : Fin Φp.length) : Prop :=
  ¬ s.Assigned c ∧ satSet x (Φp.get c) ⊆ s.U

/-- The output assignment (line 14): `x` with every retained-tree variable flipped and, for each
`C ∈ J`, both variables of `M_C` set to make their literals in `C` true. -/
def output (s : RState Φp x) : V → Bool := fun u =>
  if u ∈ s.VF then !x u
  else if h : ∃ c ∈ s.J, u ∈ s.M c then ((Φp.get (Classical.choose h)) u).getD (x u)
  else x u

end RState

/-- The initial state (lines 1–2): `U = W`, nothing retained, the empty pair matching. -/
def RState.init (Φp : GFormula V) (x : V → Bool) (W : Finset V) : RState Φp x :=
  ⟨W, [], ∅, fun _ => ∅⟩

/-- One iteration of the while-loop of Algorithm 3 (lines 3–13), from `s` processing the pending
clause `c`; `none` is `Fail`. If some small complete forcing tree rooted in `vbl(c)` avoids `U` it
is retained (tree repair); otherwise `Augment` extends the pair matching to `J ∪ {c}` keeping every
matched variable matched (or fails when no pair matching on `J ∪ {c}` exists), `V(M)` joins `U`,
and every retained tree meeting `V(M)` is dropped. The source resolves the choices (which pending
clause, which tree, which augmenting paths) by fixed lexicographic rules (p. 60); this relation
allows every resolution. -/
def RStep (k : ℕ) (Φp : GFormula V) (I0 : Finset (Fin Φp.length)) (x : V → Bool)
    (s : RState Φp x) (c : Fin Φp.length) (s' : Option (RState Φp x)) : Prop :=
  s.Pending c ∧
  ((∃ T : ForcingTree Φp x, IsSmallTree k Φp I0 x T ∧ T.root ∈ vbl (Φp.get c) ∧
      Disjoint T.vars s.U ∧ s' = some ⟨s.U ∪ T.vars, s.F ++ [(T, c)], s.J, s.M⟩) ∨
   ((¬ ∃ T : ForcingTree Φp x, IsSmallTree k Φp I0 x T ∧ T.root ∈ vbl (Φp.get c) ∧
      Disjoint T.vars s.U) ∧
    ((∃ M' : Fin Φp.length → Finset V, IsPairMatching Φp (insert c s.J) M' ∧
        matchedVars Φp s.J s.M ⊆ matchedVars Φp (insert c s.J) M' ∧
        s' = some ⟨s.U ∪ matchedVars Φp (insert c s.J) M',
          s.F.filter (fun p => Disjoint p.1.vars (matchedVars Φp (insert c s.J) M')),
          insert c s.J, M'⟩) ∨
     ((¬ ∃ M' : Fin Φp.length → Finset V, IsPairMatching Φp (insert c s.J) M') ∧ s' = none))))

/-- `RepairRun k Φ⁺ I₀ x s r i`: a run of Algorithm 3 from the state `s` that performs `i`
iterations of the while-loop and returns `r` (`some (U, y)`, or `none` for `Fail`). -/
inductive RepairRun (k : ℕ) (Φp : GFormula V) (I0 : Finset (Fin Φp.length)) (x : V → Bool) :
    RState Φp x → Option (Finset V × (V → Bool)) → ℕ → Prop
  | done (s : RState Φp x) : (∀ c, ¬ s.Pending c) → RepairRun k Φp I0 x s (some (s.U, s.output)) 0
  | fail (s : RState Φp x) (c : Fin Φp.length) : RStep k Φp I0 x s c none →
      RepairRun k Φp I0 x s none 1
  | step (s s' : RState Φp x) (c : Fin Φp.length) (r : Option (Finset V × (V → Bool))) (i : ℕ) :
      RStep k Φp I0 x s c (some s') → RepairRun k Φp I0 x s' r i → RepairRun k Φp I0 x s r (i + 1)

/-- `RepairReach k Φ⁺ I₀ x s s' i`: `i` successful iterations lead from `s` to `s'`. -/
inductive RepairReach (k : ℕ) (Φp : GFormula V) (I0 : Finset (Fin Φp.length)) (x : V → Bool) :
    RState Φp x → RState Φp x → ℕ → Prop
  | refl (s : RState Φp x) : RepairReach k Φp I0 x s s 0
  | step (s s' s'' : RState Φp x) (c : Fin Φp.length) (i : ℕ) :
      RStep k Φp I0 x s c (some s') → RepairReach k Φp I0 x s' s'' i →
        RepairReach k Φp I0 x s s'' (i + 1)

/-- The declared cost of a run of Repair with `i` loop iterations: one clause-order and forcing-list
pass (radix sorting, §7.3 p. 62), `i` iterations each charged one scan of the variables and
clauses (pending-clause scan, tree enumeration at `O_k(1)` per root, at most two breadth-first
searches, tree removal), and the output pass; each pass costs `n + |Φ⁺|` units. -/
def repairCost (n numClauses i : ℕ) : ℕ := (i + 2) * (n + numClauses)

/-! ## FindPath (Algorithm 4) -/

/-- The greedy walk of Algorithm 4 (lines 2–4) from `z` to `t` in `Ω_Φ`: repeatedly flip the least
`u` with `z(u) ≠ t(u)` and `z ⊕ u ∈ Ω_Φ`; `none` if it gets stuck or runs out of `fuel` steps. -/
def greedyWalk {n : ℕ} (Φ : GFormula (Fin n)) (t : Fin n → Bool) :
    ℕ → (Fin n → Bool) → Option (List (Fin n → Bool))
  | 0, z => if z = t then some [z] else none
  | fuel + 1, z =>
    if z = t then some [z] else
      let cand := Finset.univ.filter fun u => z u ≠ t u ∧ FSat (flip z u) Φ
      if h : cand.Nonempty then (greedyWalk Φ t fuel (flip z (cand.min' h))).map (z :: ·)
      else none

/-- `FindPath(y, y′, t)` (Algorithm 4): the greedy walk from `y` to `t` followed by the reversal of
the greedy walk from `y′` to `t` (the shared endpoint `t` listed once). Each walk is given `n`
steps, the most a walk that only flips disagreeing coordinates can take. -/
def findPath {n : ℕ} (Φ : GFormula (Fin n)) (y y' t : Fin n → Bool) : Option (List (Fin n → Bool)) :=
  match greedyWalk Φ t n y, greedyWalk Φ t n y' with
  | some g1, some g2 => some (g1 ++ g2.reverse.tail)
  | _, _ => none

/-- The declared cost of FindPath: each greedy flip is charged one clause scan (`n + |Φ|` units:
"scanning the clauses identifies all forced variables", p. 66), plus `n` units per assignment
written in the output path. -/
def findPathCost (n numClauses : ℕ) (p : List (Fin n → Bool)) : ℕ :=
  (pathLength p + 2) * (n + numClauses) + n * p.length

/-! ## The counts of §7.3 (p. 62) for fixed `x`, `Φ₀ = Φ⁺_{I₀}` and `Φ⁺` -/

/-- `C_force`: the positions in `Φ₀` of clauses with exactly one `x`-true literal. -/
def Cforce (Φp : GFormula V) (I0 : Finset (Fin Φp.length)) (x : V → Bool) : Finset (Fin Φp.length) :=
  I0.filter fun c => (satSet x (Φp.get c)).card = 1

/-- `C_multi`: the positions in `Φ⁺` of clauses with at least two `x`-true literals. -/
def Cmulti (Φp : GFormula V) (x : V → Bool) : Finset (Fin Φp.length) :=
  Finset.univ.filter fun c => 2 ≤ (satSet x (Φp.get c)).card

/-- `C` has an `x`-false literal on the variable `u`. -/
def FalseLitOn (x : V → Bool) (C : GClause V) (u : V) : Prop := C u = some (!x u)

/-- `NoTree(B)`: clauses `C ∈ C_force ∪ C_multi` with `sat_x(C) ⊆ B` such that no small complete
forcing tree in `Φ₀` under `x`, rooted at a variable whose literal in `C` is false, avoids `B`. -/
def NoTree (k : ℕ) (Φp : GFormula V) (I0 : Finset (Fin Φp.length)) (x : V → Bool) (B : Finset V) :
    ℕ :=
  ((Cforce Φp I0 x ∪ Cmulti Φp x).filter fun c => satSet x (Φp.get c) ⊆ B ∧
    ¬ ∃ u, FalseLitOn x (Φp.get c) u ∧ HasSmallCFT Φp I0 x u (Real.log k ^ 6) B).card

/-- `ForcingLink(U)`: clauses in `C_force` whose forced variable lies in `U` and which have an
`x`-false literal on a variable in `U`. -/
def ForcingLink (Φp : GFormula V) (I0 : Finset (Fin Φp.length)) (x : V → Bool) (U : Finset V) : ℕ :=
  ((Cforce Φp I0 x).filter fun c => satSet x (Φp.get c) ⊆ U ∧
    ∃ u ∈ U, FalseLitOn x (Φp.get c) u).card

/-- `MultiLink(U)`: clauses `C ∈ C_multi` with `sat_x(C) ⊆ U` and an `x`-false literal on a
variable in `U`. -/
def MultiLink (Φp : GFormula V) (x : V → Bool) (U : Finset V) : ℕ :=
  ((Cmulti Φp x).filter fun c => satSet x (Φp.get c) ⊆ U ∧
    ∃ u ∈ U, FalseLitOn x (Φp.get c) u).card

/-- The three bounds (i)–(iii) of Lemma 7.11 for `(Φ⁺, Φ₀, x)`. -/
def RepairBounds {n : ℕ} (k : ℕ) (Φp : GFormula (Fin n)) (I0 : Finset (Fin Φp.length))
    (x : Fin n → Bool) : Prop :=
  (∀ B : Finset (Fin n), (B.card : ℝ) ≤ rho k * n →
      (NoTree k Φp I0 x B : ℝ) < max (rho k ^ 4 * n) (B.card / (1024 * Real.log k ^ 20))) ∧
  (∀ B : Finset (Fin n), rho k ^ 4 * n ≤ B.card → B.card ≤ ⌈2 * rho k * n⌉₊ →
      (((Cforce Φp I0 x).filter fun c => satSet x (Φp.get c) ⊆ B).card : ℝ) ≤
        Real.log k ^ 8 * B.card) ∧
  (∀ U : Finset (Fin n), rho k ^ 4 * n ≤ U.card → (U.card : ℝ) ≤ rho k * n →
      (ForcingLink Φp I0 x U : ℝ) + 2 * MultiLink Φp x U < (1 + 1 / (4 * Real.log k ^ 6)) * U.card)

/-- `D = {C ∈ Φ⁺ ∖ Φ₀ : |sat_x(C)| ≤ 1}`: the omitted clauses with at most one `x`-true literal. -/
def omittedWeak (Φp : GFormula V) (I0 : Finset (Fin Φp.length)) (x : V → Bool) :
    Finset (Fin Φp.length) :=
  (Finset.univ \ I0).filter fun c => (satSet x (Φp.get c)).card ≤ 1

end KSATSingleFlip.Connect


