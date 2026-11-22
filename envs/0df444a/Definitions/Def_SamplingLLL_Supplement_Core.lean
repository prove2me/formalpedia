-- Prove2me | Definitions.Def_SamplingLLL_Supplement_Core
-- name    : SamplingLLL_Supplement_Core
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:53:10.265477+00:00
-- url     : https://prove2.me/theorems/c1ebd303-9562-4cbc-b59a-1ea2d00563ba
-- title:
--   Sparse-core decomposition: blocks, (D1)–(D3), syntactic codes and the connection sum $T_i(F;L)$ of (D4)
-- statement:
--   Let $F$ be a formula of $m$ labelled clauses on $n$ Boolean variables and let $U$ be a set of variables, $W=V(F)\setminus U$. $F_U$ is the set of clauses meeting $U$ and $C_{\mathrm{res}}$ the rest. A **cross clause** meets both $U$ and $W$. The **blocks** $B_1,\dots,B_{s_B}$ are the connected components of $U$ joined by clauses entirely contained in $U$. For a block $B$: $P_B$ is its set of cross clauses, $h_B=|P_B|$, $S_B=\sum_{v\in B}\deg_F(v)$. Put $N_0=n+m+2$ and $L_0=\max\{2,\lceil\log_2(128m)\rceil\}$.
--
--   **Hypotheses.**
--
--   1. (D1) Every cross clause contains exactly one variable of $U$; every variable of $W$ occurs in at most $\Delta$ clauses of $F$.
--   2. (D2) For every block, $|B|+S_B\le a_{\mathrm{blk}}\log N_0$, and the clauses internal to the block can be matched to distinct variables of the block, each matched variable belonging to its clause.
--   3. (D3) Delete the variable of $U$ from each cross clause and keep the clauses of $C_{\mathrm{res}}$; join two residual scopes when they share a remaining variable. For every nonempty connected family $T$ of at most $L_s=\max\{2,\lfloor\delta n\rfloor\}$ residual scopes, $|\mathrm{vbl}_W(T)|\ge(k-3)|T|$; and $L_s\ge L_0$.
--
--   **Syntactic codes (F.3.1).** A code of cost $K$ rooted at a cross clause is a plane tree on $K$ clause-occurrence vertices rooted at that clause, one of three colours on each edge, an old-root vertex with one of its corners, and a traversal instruction on each edge: either "stay at this clause" or a pair (one of $k$ positions, one of $\Delta$ clones), which moves to the clause containing that clone of the variable at that position. A vertex has as many corners as incident half-edges, and the isolated vertex one; for $K=1$ there is no rooting metadata. Reading a code in the formula visits clauses; a missing position or clone index stops the traversal of the affected edge. $J(\gamma)$ is the set of blocks of the cross clauses visited, including the root block. $G_B$ contains every code of cost $1\le K<L$ rooted at a cross clause of $B$.
--
--   **The connection sum (62).** With $p=2^{-k+3}$ and $\zeta=(1-4p)^{-1}$,
--   $$
--   T_i(F;L)=\sum_{R\ni B_i}2^{|R|}\,\zeta^{\sum_{B\in R}h_B}\sum_{(A_B)\in\Lambda_i(R)}\ \prod_{B\in R}\ \prod_{\gamma\in A_B}2p^{K_\gamma},
--   $$
--   where $\Lambda_i(R)$ selects a subset $A_B\subseteq G_B$ at each $B\in R$ such that $J(\gamma)\subseteq R$ for every selected code and every block of $R$ is reachable from $B_i$ by repeatedly following a selected code from its root block to a block it encounters. Condition (D4) is $\max_i T_i(F;L_0)\le N_0^\beta$.
--
--   These are the hypotheses of Theorem F.6; they depend only on the scopes and on $U$, not on the literal signs.
--
--   **Formalization Note** Blocks are finite sets of variables. Positions are the remaining variables of a clause and clones the clauses containing a variable, both in increasing index order; the paper notes that the sum does not depend on this numbering. The (vertex, corner) pair of a code is an index below $\max\{1,2(K-1)\}$, the number of such pairs. All sums in $T_i$ are finite sums. $\log$ in (D2) is the natural logarithm. In (D3), $k-3$ is a natural-number subtraction; Theorem F.6 assumes $k\ge4$.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Appendix F.2, pp.49–50 ((55), (D1)–(D3), (56)); F.3.1, pp.52–53 (codes, Lemma F.4); F.4, pp.53–54 ((62)); (D4), p.55

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_cnfData

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

/-! # The sparse-core decomposition of Appendix F.2–F.4 and its hypotheses (D1)–(D4)

Source: Achlioptas, *Counting and Sampling by Local Repair*, STOC 2027 submission (manuscript sha256
7a943167…), Appendix F.2 (pp.49–50), F.3.1 (pp.52–53), F.4 (pp.53–54). -/

/-- A plane forest with decorated edges: the ordered children of a vertex of a syntactic code (F.3.1, p.52).
`cons col ins sub rest` is a first child, joined to its parent by an edge of colour `col` carrying the
traversal instruction `ins`, with its own children `sub`, followed by the later children `rest`. An
instruction is `none` ("stay at this clause") or `some (j, i)`: position `j` of the current clause and clone
`i` of the variable at that position. There are `1 + kΔ = d` instructions per edge. -/
inductive Forest (k Δ : ℕ) : Type
  | nil : Forest k Δ
  | cons (col : Fin 3) (ins : Option (Fin k × Fin Δ)) (sub rest : Forest k Δ) : Forest k Δ

namespace Forest

variable {k Δ : ℕ}

/-- The number of vertices of the forest. -/
def size : Forest k Δ → ℕ
  | nil => 0
  | cons _ _ sub rest => 1 + sub.size + rest.size

/-- The `1 + kΔ` edge instructions. -/
def instrs (k Δ : ℕ) : List (Option (Fin k × Fin Δ)) :=
  none :: (List.finRange k).flatMap fun j => (List.finRange Δ).map fun i => some (j, i)

/-- Every forest with at most `s` vertices. -/
def upTo (k Δ : ℕ) : ℕ → List (Forest k Δ)
  | 0 => [nil]
  | s + 1 => nil :: (List.finRange 3).flatMap fun col => (instrs k Δ).flatMap fun ins =>
      (upTo k Δ s).flatMap fun a => (upTo k Δ s).flatMap fun b =>
        if a.size + b.size ≤ s then [cons col ins a b] else []

end Forest

/-- A syntactic code (F.3.1, p.52): a plane tree on `K = tree.size + 1` clause-occurrence vertices rooted at
the specified occurrence of the clause `root` (the forest `tree` is the ordered list of the root's
children), a colour among three and a traversal instruction on every edge, and an old-root vertex with one
of its corners, recorded as the index `corner` among the corners of the tree. A vertex has as many corners
as incident half-edges and the isolated vertex has one, so a tree on `K ≥ 2` vertices has `2(K − 1)`
(vertex, corner) pairs; for `K = 1` the sole code has no rooting metadata (Lemma F.4), which is the single
index `0`. -/
structure Code (k Δ m : ℕ) where
  /-- The root clause, a cross clause of the block the code is rooted at. -/
  root : Fin m
  /-- The children of the root, with the decorations of all edges. -/
  tree : Forest k Δ
  /-- The old-root vertex and corner, as an index below `max 1 (2 (K − 1))`. -/
  corner : ℕ

/-- The cost `K` of a code: its number of clause-occurrence vertices. -/
def Code.cost {k Δ m : ℕ} (γ : Code k Δ m) : ℕ := γ.tree.size + 1

/-- A formula's clause scopes with a selected set `U` of variables to remove (F.2, p.49): `m` labelled
clauses on `n` Boolean variables, `W = V(F) ∖ U`. Literal signs are not part of the decomposition. -/
structure Core (n m : ℕ) where
  /-- The scope of each clause. -/
  scope : Fin m → Finset (Fin n)
  /-- The removed variables `U`. -/
  U : Finset (Fin n)

namespace Core

variable {n m : ℕ} (F : Core n m)

/-- `deg_F(v)`: the number of clauses containing `v`. -/
def deg (v : Fin n) : ℕ := (Finset.univ.filter fun c => v ∈ F.scope c).card

/-- A cross clause meets both `U` and `W` (p.49). -/
def cross (c : Fin m) : Prop := (F.scope c ∩ F.U).Nonempty ∧ ¬ F.scope c ⊆ F.U

instance : DecidablePred F.cross := fun c => by unfold cross; infer_instance

/-- Two variables of `U` lie in a common clause entirely contained in `U`. -/
def link (u v : Fin n) : Prop :=
  u ∈ F.U ∧ v ∈ F.U ∧ ∃ c, F.scope c ⊆ F.U ∧ u ∈ F.scope c ∧ v ∈ F.scope c

/-- The block of `u ∈ U`: its connected component among the variables of `U`, joined by clauses entirely
contained in `U` (p.49). An isolated variable of `U` forms a singleton block. -/
noncomputable def blockOf (u : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => Relation.ReflTransGen F.link u v

/-- The blocks `B_1, …, B_{s_B}`. -/
noncomputable def blocks : Finset (Finset (Fin n)) := by
  classical
  exact F.U.image F.blockOf

/-- `P_B`: the cross clauses of the block `B`. -/
def crossOf (B : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun c => F.cross c ∧ (F.scope c ∩ B).Nonempty

/-- `h_B = |P_B|`. -/
def h (B : Finset (Fin n)) : ℕ := (F.crossOf B).card

/-- `S_B = Σ_{v∈B} deg_F(v)`. -/
def S (B : Finset (Fin n)) : ℕ := ∑ v ∈ B, F.deg v

/-- `N₀ = n + m + 2`. -/
def N0 (_F : Core n m) : ℕ := n + m + 2

/-- `L₀ = max{2, ⌈log₂(128 m)⌉}` (p.50). -/
def L0 (_F : Core n m) : ℕ := max 2 (Nat.clog 2 (128 * m))

/-- The residual scope of a clause: its variables outside `U` (D3, p.49). It is empty exactly for the
clauses internal to `U`, which are not residual clauses. -/
def res (c : Fin m) : Finset (Fin n) := F.scope c \ F.U

/-- Two residual scopes are joined when they share a remaining variable (D3). -/
def resG : SimpleGraph (Fin m) where
  Adj a b := a ≠ b ∧ (F.res a ∩ F.res b).Nonempty
  symm := ⟨fun a b hab => ⟨hab.1.symm, by rw [Finset.inter_comm]; exact hab.2⟩⟩
  loopless := ⟨fun a hab => hab.1 rfl⟩

/-- (D1), p.49: every cross clause contains exactly one variable of `U`, and every variable of `W` occurs in
at most `Δ` clauses of the original formula. -/
def D1 (Δ : ℕ) : Prop :=
  (∀ c, F.cross c → (F.scope c ∩ F.U).card = 1) ∧ ∀ v, v ∉ F.U → F.deg v ≤ Δ

/-- (D2), p.49: for every block, `|B| + S_B ≤ a_blk log N₀` (natural logarithm), and the internal clauses of
the block can be matched to distinct variables of the block, each matched variable belonging to its
matched clause. -/
def D2 (ablk : ℝ) : Prop :=
  ∀ B ∈ F.blocks, ((B.card + F.S B : ℕ) : ℝ) ≤ ablk * Real.log (F.N0 : ℝ) ∧
    ∃ f : Fin m → Fin n, (∀ c, F.scope c ⊆ B → f c ∈ F.scope c) ∧
      ∀ c c', F.scope c ⊆ B → F.scope c' ⊆ B → f c = f c' → c = c'

/-- (D3), pp.49–50: for every nonempty connected family `T` of at most `L_s = max{2, ⌊δn⌋}` residual scopes,
`|vbl_W(T)| ≥ (k − 3)|T|` (56); and `L_s ≥ L₀`. -/
def D3 (k : ℕ) (δ : ℝ) : Prop :=
  (∀ T : Finset (Fin m), T.card ≤ max 2 ⌊δ * (n : ℝ)⌋₊ → (∀ c ∈ T, ¬ F.scope c ⊆ F.U) →
      (F.resG.induce (T : Set (Fin m))).Connected → (k - 3) * T.card ≤ (T.biUnion F.res).card) ∧
    F.L0 ≤ max 2 ⌊δ * (n : ℝ)⌋₊

/-- Follow one traversal instruction from the clause `cur` (F.3.1, p.52): `none` stays; `some (j, i)` takes
the `j`-th remaining variable of `cur` and moves to the `i`-th clause containing it (its `i`-th clone), both
in increasing index order. A missing position or clone index is an invalid instruction (`none`). -/
def step {k Δ : ℕ} (cur : Fin m) : Option (Fin k × Fin Δ) → Option (Fin m)
  | none => some cur
  | some (j, i) =>
    match ((F.res cur).sort (· ≤ ·))[(j : ℕ)]? with
    | none => none
    | some w => ((Finset.univ.filter fun c => w ∈ F.scope c).sort (· ≤ ·))[(i : ℕ)]?

/-- The clauses visited below a vertex standing at the clause `cur`, reading its children in order. An
invalid instruction stops the traversal of the affected edge and of everything below it (p.53). -/
def visit {k Δ : ℕ} : Forest k Δ → Fin m → Finset (Fin m)
  | Forest.nil, _ => ∅
  | Forest.cons _ ins sub rest, cur =>
    (match F.step cur ins with
      | none => ∅
      | some c => insert c (visit sub c)) ∪ visit rest cur

/-- `J(γ)`: the core blocks encountered when the code is read in the formula, including its root block
(F.4, p.53): the blocks of the cross clauses among the visited clauses. -/
noncomputable def J {k Δ : ℕ} (γ : Code k Δ m) : Finset (Finset (Fin n)) :=
  F.blocks.filter fun B => ∃ c ∈ insert γ.root (F.visit γ.tree γ.root), c ∈ F.crossOf B

/-- `G_B` for the cutoff `L`: every syntactic code of cost `1 ≤ K < L` rooted at one of the `h_B` cross
clauses of `B` (F.4, p.53). -/
noncomputable def codes (k Δ L : ℕ) (B : Finset (Fin n)) : Finset (Code k Δ m) := by
  classical
  exact (F.crossOf B ×ˢ ((Forest.upTo k Δ (L - 2)).toFinset.filter fun t => t.size + 1 < L)).biUnion
    fun at_ => (Finset.range (max 1 (2 * at_.2.size))).image fun j => ⟨at_.1, at_.2, j⟩

/-- The connection sum `T_i(F; L)` of (62), p.54, for the block `B_i = Bi`, with `p = 2^{−k+3}` and
`ζ = (1 − 4p)^{-1}`:
`Σ_{R ∋ B_i} 2^{|R|} ζ^{Σ_{B∈R} h_B} Σ_{(A_B) ∈ Λ_i(R)} ∏_{B∈R} ∏_{γ∈A_B} 2 p^{K_γ}`,
where `Λ_i(R)` selects a subset `A_B ⊆ G_B` at each `B ∈ R` with `J(γ) ⊆ R` for every selected code and with
every block of `R` reachable from `B_i` by repeatedly following a selected code from its root block to a
block it encounters. All sums are finite sums over `Finset`s. -/
noncomputable def T (k Δ L : ℕ) (Bi : Finset (Fin n)) : ℚ := by
  classical
  exact ∑ R ∈ F.blocks.powerset.filter (fun R => Bi ∈ R),
    (2 : ℚ) ^ R.card * ((1 - 4 * p0k k)⁻¹) ^ (∑ B ∈ R, F.h B) *
      ∑ A ∈ (Fintype.piFinset fun B : Finset (Fin n) =>
            if B ∈ R then (F.codes k Δ L B).powerset else {∅}).filter
          (fun A => (∀ B ∈ R, ∀ γ ∈ A B, F.J γ ⊆ R) ∧
            ∀ B ∈ R, Relation.ReflTransGen (fun X Y => ∃ γ ∈ A X, Y ∈ F.J γ) Bi B),
        ∏ B ∈ R, ∏ γ ∈ A B, 2 * p0k k ^ γ.cost

/-- (D4), p.55: `max_{1≤i≤s_B} T_i(F; L₀) ≤ N₀^β`; vacuous when there is no block. -/
def D4 (k Δ β : ℕ) : Prop := ∀ B ∈ F.blocks, F.T k Δ F.L0 B ≤ (F.N0 : ℚ) ^ β

end Core

end SamplingLLL.Supplement


