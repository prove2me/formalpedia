-- Prove2me | Definitions.Def_RestrictedAssignment_Svensson_extendSchedule
-- name    : RestrictedAssignment_Svensson_extendSchedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:26:22.421696+00:00
-- url     : https://prove2.me/theorems/150e7a65-a9fa-41c3-9b9d-6d7d8b330abf
-- title:
--   Algorithm 2 (ExtendSchedule): partial schedules, blockers, potential moves, values, and the dual solution $(y^*, z^*)$
-- statement:
--   This file defines the local search procedure of Section 4 of Svensson's paper and the objects its analysis uses, for an instance $(J, M, p, \Gamma)$ of restricted assignment. Throughout, $R = 16/17$.
--
--   1. **Job classes** (Definition 4.2). A job $j$ is *big* if $p_j \ge 11/17$, *medium* if $9/17 < p_j < 11/17$, *small* if $p_j \le 9/17$; a big job is *huge* if $p_j \ge 14/17$ and *large* otherwise. $J_B$, $J_M$ are the big and medium jobs.
--   2. **Partial schedules** (Definition 3.2). A partial schedule is $\sigma : J \to M \cup \{\mathrm{TBD}\}$. It is *valid* if every job placed on a machine is placed on a machine of $\Gamma(j)$, every machine is assigned at most one big job, and $p(\sigma^{-1}(i)) \le 1 + R$ for every machine $i$.
--   3. **Moves and blockers** (Definitions 3.3, 3.4). A move is a pair $(j,i)$ with $i \in \Gamma_\sigma(j) = \Gamma(j) \setminus \{\sigma(j)\}$. A blocker $B$ has a job set $J(B)$, a machine $M(B)$ (or $\bot$), and a type: small, big or medium. The tree $T$ is recorded by its blockers $B_0, B_1, \dots, B_t$ in the order they were added. $J(T)$, $M(T)$, $M_S(T)$, $M_B(T)$, $M_M(T)$ are the jobs of $T$, the machines of $T$, and the machines of small, big and medium blockers. $S = \{ j \text{ small} : \Gamma_\sigma(j) \subseteq M_S(T)\}$, $S_i = \sigma^{-1}(i) \cap S$ and $M_i = J_M \cap \sigma^{-1}(i)$.
--   4. **Potential moves** (p. 12, Definitions 4.3, 4.4), for $j \in J(T)$: a *small move* if $j$ is small and $i \notin M_S(T)$, or $j$ is medium with $i \notin M(T)$, or large with $i \notin M_B(T) \cup M_S(T)$, and $i$ is not assigned a big job; *medium/large-to-big* under the same conditions on medium and large jobs when $i$ is assigned a big job; for huge $j$ and $i \notin M(T)$: *huge-to-small* if no big job is on $i$ and $p(j) + p(S_i \cup M_i) \le 1+R$, *huge-to-big* if a big job is on $i$ and $p(j) + p(S_i \cup M_i) \le 1+R$, *huge-to-medium* if $p(j) + p(S_i) \le 1+R < p(j) + p(S_i \cup M_i)$. A potential move is *valid* if $\sigma(j) \leftarrow i$ gives a valid schedule.
--   5. **Values** (Definition 4.5), with $L_i = \sigma^{-1}(i)$, in $\mathbb R^2$ ordered lexicographically:
--   $$
--   \mathrm{Val}(j,i) = \begin{cases} (0,0) & \text{valid},\\ (p(j),\, p(L_i)) & \text{small move},\\ (2,0) & \text{medium/large-to-big},\\ (3,\, p(L_i)) & \text{huge-to-small},\\ (4,0) & \text{huge-to-big},\\ (5,\, |L_i \cap J_M|) & \text{huge-to-medium}. \end{cases}
--   $$
--   6. **Algorithm 2** (p. 14). Starting from a partial schedule $\sigma_0$ and a job $j_{\mathrm{new}}$, $T$ is initialized with the small root blocker $J(B_0) = \{j_{\mathrm{new}}\}$, $M(B_0) = \bot$. While $\sigma(j_{\mathrm{new}})$ is TBD, the algorithm chooses a potential move $(j,i)$ of minimum value (any one, if several), lets $B$ be the blocker with $j \in J(B)$, and: if the move is valid, sets $\sigma(j) \leftarrow i$ and removes $B$ and all blockers added after $B$; if it is a small or huge-to-small move, adds a small blocker with machine $i$ and jobs $\sigma^{-1}(i) \setminus J(T)$; if it is a medium/large-to-big or huge-to-big move, adds a big blocker with machine $i$ and the big job on $i$; otherwise (huge-to-medium) adds a medium blocker with machine $i$ and jobs $\sigma^{-1}(i) \cap J_M$. A state is *reachable* if it arises from the initial state after finitely many iterations.
--   7. **The dual solution** (proof of Lemma 4.6, p. 15):
--   $$
--   z^*_j = \begin{cases} 11/17 & j \in J(T) \text{ big},\\ 9/17 & j \in J(T) \text{ medium},\\ p_j & j \in J(T) \cup S \text{ small},\\ 0 & \text{otherwise}, \end{cases} \qquad y^*_i = \begin{cases} 1 & i \in M_S(T),\\ \sum_{j \in \sigma^{-1}(i)} z^*_j & \text{otherwise.} \end{cases}
--   $$
--
--   These definitions are the substrate for the analysis of Algorithm 2: validity is preserved, a potential move exists whenever [C-LP] is feasible (via $(y^*, z^*)$), and the algorithm terminates.
--
--   **Formalization Note** A partial schedule is `σ : J → Option M` (`none` = TBD); a state is `AlgState` (schedule and list of blockers in insertion order; parent pointers of the tree are not recorded since no step depends on them). `Step Γ p jnew s s'` is one iteration of the while loop as a relation: the minimum-value rule is a hypothesis on the chosen pair, so ties are resolved nondeterministically. The index `k` of the blocker containing $j$ is existentially quantified (on reachable states it is unique). The big blocker of line 12 has job set $\sigma^{-1}(i) \cap J_B$, which is $\{j_B\}$ in a valid schedule. `Reachable Γ p σ0 jnew s` is the reflexive–transitive closure of `Step` from `initState σ0 jnew`. `moveVal` has type `Lex (ℝ × ℝ)`.
-- source:
--   Svensson, Santa Claus Schedules Jobs on Unrelated Machines, arXiv:1011.1168v2, pp. 4-6 (Defs. 3.2-3.5), p. 11 (R = 16/17), pp. 12-14 (Defs. 4.2-4.5, Algorithm 2), p. 15 (S, S_i, and (y*, z*) in the proof of Lemma 4.6)

import Mathlib

namespace RestrictedAssignment.Svensson

open Finset Classical

variable {J M : Type} [Fintype J] [Fintype M] [DecidableEq J] [DecidableEq M]

/-- Svensson, arXiv:1011.1168v2, p. 11: "Throughout this section we let R = 16/17." -/
noncomputable def R : ℝ := 16 / 17

/-! ### Job classes (Definition 4.2, p. 12) -/

/-- Definition 4.2: `j` is big if `p_j ≥ 11/17`. -/
def IsBig (p : J → ℝ) (j : J) : Prop := 11 / 17 ≤ p j

/-- Definition 4.2: `j` is medium if `11/17 > p_j > 9/17`. -/
def IsMedium (p : J → ℝ) (j : J) : Prop := 9 / 17 < p j ∧ p j < 11 / 17

/-- Definition 4.2: `j` is small if `p_j ≤ 9/17`. -/
def IsSmall (p : J → ℝ) (j : J) : Prop := p j ≤ 9 / 17

/-- Definition 4.2: a big job is huge if `p_j ≥ 14/17`. -/
def IsHuge (p : J → ℝ) (j : J) : Prop := 14 / 17 ≤ p j

/-- Definition 4.2: a big job that is not huge is large (`11/17 ≤ p_j < 14/17`). -/
def IsLarge (p : J → ℝ) (j : J) : Prop := 11 / 17 ≤ p j ∧ p j < 14 / 17

/-! ### Partial schedules (Definition 3.2, p. 4; recalled on p. 11 with R = 16/17) -/

/-- A partial schedule `σ : J → M ∪ {TBD}`; `none` is TBD. `pload p σ i = p(σ⁻¹(i))`. -/
noncomputable def pload (p : J → ℝ) (σ : J → Option M) (i : M) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => σ j = some i), p j

/-- Definition 3.2 (p. 4), recalled on p. 11: a partial schedule is valid if each machine is
assigned at most one big job and `p(σ⁻¹(i)) ≤ 1 + R`. The first clause, `σ(j) ∈ Γ(j)`, is the
model's implicit requirement (`p_{ij} = ∞` for `i ∉ Γ(j)`, p. 1–2). -/
def Valid (Γ : J → Finset M) (p : J → ℝ) (σ : J → Option M) : Prop :=
  (∀ j i, σ j = some i → i ∈ Γ j) ∧
  ∀ i, (Finset.univ.filter (fun j => σ j = some i ∧ IsBig p j)).card ≤ 1 ∧ pload p σ i ≤ 1 + R

/-! ### Blockers and the tree of blockers (Definition 3.4, pp. 5–6, 12) -/

/-- The kind bit of a blocker: small, big (p. 6) or medium (p. 12). -/
inductive BlockerKind
  | small
  | big
  | medium
  deriving DecidableEq

/-- Definition 3.4: a blocker `B` has a job set `J(B)`, a machine `M(B)` (`none` = ⊥), and the
bit recording whether it is a small, big or medium blocker. -/
structure Blocker (J M : Type) where
  jobs : Finset J
  machine : Option M
  kind : BlockerKind

/-- A state of Algorithm 2: the partial schedule `σ` and the blockers `B₀, B₁, …, B_t` of the
tree `T`, listed in the order in which they were added (the "linear structure", p. 5). The parent
pointers of the tree are not recorded: nothing in Algorithm 2 depends on them. -/
structure AlgState (J M : Type) where
  σ : J → Option M
  T : List (Blocker J M)

variable (Γ : J → Finset M) (p : J → ℝ)

/-- `j ∈ J(T)`. -/
def InJT (s : AlgState J M) (j : J) : Prop := ∃ B ∈ s.T, j ∈ B.jobs

/-- `i ∈ M(T)`. -/
def InMT (s : AlgState J M) (i : M) : Prop := ∃ B ∈ s.T, B.machine = some i

/-- `i ∈ M_S(T)`: `i` is the machine of a small blocker. -/
def InMS (s : AlgState J M) (i : M) : Prop :=
  ∃ B ∈ s.T, B.kind = BlockerKind.small ∧ B.machine = some i

/-- `i ∈ M_B(T)`: `i` is the machine of a big blocker. -/
def InMB (s : AlgState J M) (i : M) : Prop :=
  ∃ B ∈ s.T, B.kind = BlockerKind.big ∧ B.machine = some i

/-- `i ∈ M_M(T)`: `i` is the machine of a medium blocker. -/
def InMM (s : AlgState J M) (i : M) : Prop :=
  ∃ B ∈ s.T, B.kind = BlockerKind.medium ∧ B.machine = some i

/-- Definition 3.3 (p. 5): `i ∈ Γ_σ(j) = Γ(j) \ {σ(j)}`, i.e. `(j, i)` is a move. -/
def IsMove (s : AlgState J M) (j : J) (i : M) : Prop := i ∈ Γ j ∧ s.σ j ≠ some i

/-- p. 15: `S = S(T) = {j ∈ J : j is small with Γ_σ(j) ⊆ M_S(T)}`. -/
def InS (s : AlgState J M) (j : J) : Prop :=
  IsSmall p j ∧ ∀ i, IsMove Γ s j i → InMS s i

/-- Definition 4.4: `S_i = {j ∈ σ⁻¹(i) : j is small with Γ_σ(j) ⊆ M_S(T)}`. -/
noncomputable def Si (s : AlgState J M) (i : M) : Finset J :=
  Finset.univ.filter (fun j => s.σ j = some i ∧ InS Γ p s j)

/-- Definition 4.4: `M_i = J_M ∩ σ⁻¹(i)`, the medium jobs assigned to `i`. -/
noncomputable def Mi (s : AlgState J M) (i : M) : Finset J :=
  Finset.univ.filter (fun j => s.σ j = some i ∧ IsMedium p j)

/-- `i` is assigned a big job. -/
def HasBig (s : AlgState J M) (i : M) : Prop := ∃ j, s.σ j = some i ∧ IsBig p j

/-! ### Potential moves (p. 12, Definitions 4.3 and 4.4) -/

/-- The types of potential moves of Section 4. -/
inductive MoveType
  | small
  | medLargeToBig
  | hugeToSmall
  | hugeToBig
  | hugeToMedium
  deriving DecidableEq

/-- `(j, i)` is a potential move of type `t` with respect to the state `s`:
* small (p. 12): `j ∈ J(T)` small and `i ∉ M_S(T)`;
* small / medium/large-to-big (Definition 4.3): `j ∈ J(T)` medium with `i ∉ M(T)`, or large
  with `i ∉ M_B(T) ∪ M_S(T)`; small if `i` is not assigned a big job, medium/large-to-big if it is;
* huge-to-small / huge-to-big / huge-to-medium (Definition 4.4): `j ∈ J(T)` huge, `i ∉ M(T)`, and
  respectively: no big job on `i` and `p(j) + p(S_i ∪ M_i) ≤ 1 + R`; a big job on `i` and
  `p(j) + p(S_i ∪ M_i) ≤ 1 + R`; `p(j) + p(S_i) ≤ 1 + R` and `p(j) + p(S_i ∪ M_i) > 1 + R`. -/
def IsPotentialMoveOf (s : AlgState J M) (j : J) (i : M) : MoveType → Prop
  | .small => InJT s j ∧ IsMove Γ s j i ∧
      ((IsSmall p j ∧ ¬ InMS s i) ∨
       (IsMedium p j ∧ ¬ InMT s i ∧ ¬ HasBig p s i) ∨
       (IsLarge p j ∧ ¬ InMB s i ∧ ¬ InMS s i ∧ ¬ HasBig p s i))
  | .medLargeToBig => InJT s j ∧ IsMove Γ s j i ∧
      ((IsMedium p j ∧ ¬ InMT s i) ∨ (IsLarge p j ∧ ¬ InMB s i ∧ ¬ InMS s i)) ∧ HasBig p s i
  | .hugeToSmall => InJT s j ∧ IsMove Γ s j i ∧ IsHuge p j ∧ ¬ InMT s i ∧ ¬ HasBig p s i ∧
      p j + ∑ k ∈ Si Γ p s i ∪ Mi p s i, p k ≤ 1 + R
  | .hugeToBig => InJT s j ∧ IsMove Γ s j i ∧ IsHuge p j ∧ ¬ InMT s i ∧ HasBig p s i ∧
      p j + ∑ k ∈ Si Γ p s i ∪ Mi p s i, p k ≤ 1 + R
  | .hugeToMedium => InJT s j ∧ IsMove Γ s j i ∧ IsHuge p j ∧ ¬ InMT s i ∧
      p j + ∑ k ∈ Si Γ p s i, p k ≤ 1 + R ∧ 1 + R < p j + ∑ k ∈ Si Γ p s i ∪ Mi p s i, p k

/-- `(j, i)` is a potential move (of some type). -/
def IsPotentialMove (s : AlgState J M) (j : J) (i : M) : Prop :=
  ∃ t, IsPotentialMoveOf Γ p s j i t

/-- Definition 3.5 (p. 6), p. 12: a potential move `(j, i)` is valid if the update `σ(j) ← i`
results in a valid schedule. -/
def IsValidMove (s : AlgState J M) (j : J) (i : M) : Prop :=
  IsPotentialMove Γ p s j i ∧ Valid Γ p (Function.update s.σ j (some i))

/-! ### Values of moves (Definition 4.5, p. 14) -/

/-- Definition 4.5, with `L_i = σ⁻¹(i)`: the value of a potential move `(j, i)` in `ℝ × ℝ`,
ordered lexicographically: `(0, 0)` if valid, `(p(j), p(L_i))` if a small move, `(2, 0)` if
medium/large-to-big, `(3, p(L_i))` if huge-to-small, `(4, 0)` if huge-to-big,
`(5, |L_i ∩ J_M|)` if huge-to-medium. (The potential move types are mutually exclusive; the last
branch is only reached by pairs that are not potential moves, whose value is never used.) -/
noncomputable def moveVal (s : AlgState J M) (j : J) (i : M) : Lex (ℝ × ℝ) :=
  if IsValidMove Γ p s j i then toLex (0, 0)
  else if IsPotentialMoveOf Γ p s j i .small then toLex (p j, pload p s.σ i)
  else if IsPotentialMoveOf Γ p s j i .medLargeToBig then toLex (2, 0)
  else if IsPotentialMoveOf Γ p s j i .hugeToSmall then toLex (3, pload p s.σ i)
  else if IsPotentialMoveOf Γ p s j i .hugeToBig then toLex (4, 0)
  else if IsPotentialMoveOf Γ p s j i .hugeToMedium then toLex (5, ((Mi p s i).card : ℝ))
  else toLex (0, 0)

/-! ### Algorithm 2, ExtendSchedule(σ, j_new) (p. 14) -/

/-- The union `J(T)` as a finite set. -/
noncomputable def jobsT (s : AlgState J M) : Finset J :=
  Finset.univ.filter (fun j => InJT s j)

/-- One iteration of the while loop of Algorithm 2 (lines 2–15), as a relation between states.
`Step s s'` holds iff `σ(j_new)` is TBD in `s` (line 2), and for some potential move `(j, i)` of
minimum lexicographic value among all potential moves in `s` (line 3; ties are broken
arbitrarily) and some blocker `B = T[k]` with `j ∈ J(B)` (line 4), `s'` is obtained by
* line 5–7, if `(j, i)` is valid: `σ(j) ← i`, and `B` and all blockers added after `B` removed;
* line 8–9, if a potential small or huge-to-small move: a small blocker with machine `i` and jobs
  `σ⁻¹(i) \ J(T)` appended;
* line 10–12, if a potential medium/large-to-big or huge-to-big move: a big blocker with machine
  `i` and job set `σ⁻¹(i) ∩ J_B` (the big job `j_B` with `σ(j_B) = i`) appended;
* line 13–14, otherwise (huge-to-medium): a medium blocker with machine `i` and jobs
  `σ⁻¹(i) ∩ J_M` appended. -/
def Step (jnew : J) (s s' : AlgState J M) : Prop :=
  s.σ jnew = none ∧
  ∃ j i, IsPotentialMove Γ p s j i ∧
    (∀ j' i', IsPotentialMove Γ p s j' i' → moveVal Γ p s j i ≤ moveVal Γ p s j' i') ∧
    ∃ k, ∃ hk : k < s.T.length, j ∈ (s.T.get ⟨k, hk⟩).jobs ∧
      s' =
        if IsValidMove Γ p s j i then
          ⟨Function.update s.σ j (some i), s.T.take k⟩
        else if IsPotentialMoveOf Γ p s j i .small ∨ IsPotentialMoveOf Γ p s j i .hugeToSmall then
          ⟨s.σ, s.T ++ [⟨Finset.univ.filter (fun j' => s.σ j' = some i) \ jobsT s,
            some i, BlockerKind.small⟩]⟩
        else if IsPotentialMoveOf Γ p s j i .medLargeToBig ∨
            IsPotentialMoveOf Γ p s j i .hugeToBig then
          ⟨s.σ, s.T ++ [⟨Finset.univ.filter (fun j' => s.σ j' = some i ∧ IsBig p j'),
            some i, BlockerKind.big⟩]⟩
        else
          ⟨s.σ, s.T ++ [⟨Finset.univ.filter (fun j' => s.σ j' = some i ∧ IsMedium p j'),
            some i, BlockerKind.medium⟩]⟩

/-- Line 1 of Algorithm 2: the tree `T` initialized with the special small root blocker
`J(B) = {j_new}`, `M(B) = ⊥`, and the given partial schedule `σ₀`. -/
def initState (σ0 : J → Option M) (jnew : J) : AlgState J M :=
  ⟨σ0, [⟨{jnew}, none, BlockerKind.small⟩]⟩

/-- `s` is a state reached by Algorithm 2 started on `(σ₀, j_new)` after finitely many
iterations. -/
def Reachable (σ0 : J → Option M) (jnew : J) (s : AlgState J M) : Prop :=
  Relation.ReflTransGen (Step Γ p jnew) (initState σ0 jnew) s

/-! ### The dual solution of the proof of Lemma 4.6 (p. 15) -/

/-- `z*_j = 11/17` if `j ∈ J(T)` is big, `9/17` if `j ∈ J(T)` is medium, `p_j` if
`j ∈ J(T) ∪ S` is small, `0` otherwise. -/
noncomputable def zStar (s : AlgState J M) (j : J) : ℝ :=
  if InJT s j ∧ IsBig p j then 11 / 17
  else if InJT s j ∧ IsMedium p j then 9 / 17
  else if (InJT s j ∨ InS Γ p s j) ∧ IsSmall p j then p j
  else 0

/-- `y*_i = 1` if `i ∈ M_S(T)`, and `∑_{j ∈ σ⁻¹(i)} z*_j` otherwise. -/
noncomputable def yStar (s : AlgState J M) (i : M) : ℝ :=
  if InMS s i then 1
  else ∑ j ∈ Finset.univ.filter (fun j => s.σ j = some i), zStar Γ p s j

end RestrictedAssignment.Svensson


