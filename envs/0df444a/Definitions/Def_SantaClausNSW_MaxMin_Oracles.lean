-- Prove2me | Definitions.Def_SantaClausNSW_MaxMin_Oracles
-- name    : SantaClausNSW_MaxMin_Oracles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T20:35:20.755048+00:00
-- url     : https://prove2.me/theorems/2974ecec-72d0-4c63-95ef-ca43b7cef5d4
-- title:
--   Value, demand, restricted demand and budgeted-routine oracle ports, instance encodings and output decoding
-- statement:
--   A set of items $S$ is written as its indicator list $(1_{j\in S})_{j<m}$ and agent $i$ as the number $i$. An oracle is a fixed answer function; each predicate says that it answers every well-formed question of its kind correctly and leaves other questions unconstrained.
--
--   - **Value oracle**: the question $(i,1_S)$ is answered $[v_i(S)]$.
--   - **Demand oracle**: the question $(i,p_1,\dots,p_m)$ with nonnegative rational prices is answered $1_D$ for a set $D$ maximizing $v_i(D)-\sum_{j\in D}p_j$ over all sets (ties broken in any way).
--   - **Restricted demand oracle**: the question $(i,1_R,p)$ is answered $1_D$ with $D\subseteq R$ maximizing the same objective over subsets of $R$.
--   - **Budgeted routine with factor $\beta$** (Lemma A.1): the question $(1,i,c_1,\dots,c_m,B,t)$ with $c\ge0$, $B\ge0$, $t>0$ is answered $1_D$ with $c(D)\le B$ and $v_i(D)\ge\beta t$ whenever some set within the budget has value at least $t$; the question $(0,i,1_S)$ is an exact value query.
--
--   An oracle instance is given by the input $n,m,\sigma$ and has size $n+m+\sigma$; an explicit input list has size $n+m$ plus its encoding length. An additive instance is the table $(v_{ij})$ of nonnegative rationals, with $v_i(S)=\sum_{j\in S}v_{ij}$. Outputs are decoded totally: the allocation from the first $m$ entries (entry $j=i+1$ gives item $j$ to agent $i$), selected configurations from the following indicator blocks, and an explicit configuration solution from a flag, the target $T$, the number $K$ of triples and the triples $(i,y_{i,S},1_S)$.
--
--   The guarantee $\mathrm{MMApprox}(v,\rho,A)$ says $\min_i v_i(Y_i)\le\rho\cdot\min_i v_i(A_i)$ for every allocation $Y$, i.e. $\mathrm{OPT}_{MM}\le\rho\cdot\min_iv_i(A_i)$. `SolOutcome` says that an output either reports $T_{LP}=0$ (and $T_{LP}=0$ holds) or is a well-formed list of at most $K$ triples forming a configuration solution with objective value $T>\gamma\,T_{LP}$.
--
--   **Formalization Note.** Every list decodes to an allocation, so no output is excluded; a malformed configuration-solution output fails `SolWellFormed`.
-- source:
--   Chen, Feng, Hu, Li, Zhang, Santa Claus and Weighted Nash Social Welfare with Subadditive Valuations, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 10 §2; p. 59 Lemma A.1; p. 62 App. B; p. 67 App. E.1

import Mathlib
import Definitions.Def_SantaClausNSW_MaxMin_Valuations
import Definitions.Def_SantaClausNSW_MaxMin_Machine

namespace SantaClausNSW.MaxMin

/-!
# Oracle ports, input encodings and output decoding

Chen, Feng, Hu, Li, Zhang, *Santa Claus and Weighted Nash Social Welfare with Subadditive
Valuations*, arXiv:2611.05229 (held version, sha256 98a235d3…), p. 10 §2 (value, demand and
restricted demand queries), p. 59 Lemma A.1 (budgeted routine), p. 67 App. E.1.

An oracle is a fixed answer function (`Oracle`); each predicate below says that it answers every
well-formed question of its kind correctly, and leaves every other question unconstrained. A set
`S ⊆ M` is written as its indicator list of length `m` (`encSet`); agent `i` as the number `i`.
-/

/-- The indicator list `(1_{j ∈ S})_{j < m}` of a set of items. -/
def encSet {m : ℕ} (S : Finset (Fin m)) : List ℚ :=
  List.ofFn (fun j : Fin m => if j ∈ S then 1 else 0)

/-- The set of items `j < m` whose entry at position `off + j` of `l` equals `1`. -/
def decSetAt (m : ℕ) (l : List ℚ) (off : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun j : Fin m => l.getD (off + (j : ℕ)) 0 = 1)

/-- The allocation written by the first `m` entries of `l`: entry `j` equal to `i + 1` gives item
`j` to agent `i`; any other entry leaves `j` unassigned. Every list decodes to an allocation. -/
def decAlloc (n m : ℕ) (l : List ℚ) : Fin n → Finset (Fin m) :=
  fun i => Finset.univ.filter (fun j : Fin m => l.getD (j : ℕ) 0 = ((i : ℕ) : ℚ) + 1)

/-- The configurations written after the first `m` entries of `l`: agent `i`'s set is the
indicator block at positions `m + i·m, …, m + i·m + m − 1`. -/
def decConfigs (n m : ℕ) (l : List ℚ) : Fin n → Finset (Fin m) :=
  fun i => decSetAt m l (m + (i : ℕ) * m)

/-- A correct value oracle for `(v_i)`: the question `i, 1_S` is answered `[v_i(S)]`. -/
def IsValueOracle {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (O : Oracle) : Prop :=
  ∀ (i : Fin n) (S : Finset (Fin m)), ∃ r : ℚ,
    O (((i : ℕ) : ℚ) :: encSet S) = [r] ∧ (r : ℝ) = v i S

/-- `D` is a demand set of `v` at prices `p` among the subsets of `R`:
`v(D) − p(D) ≥ v(T) − p(T)` for every `T ⊆ R`, and `D ⊆ R`. -/
def IsDemandSet {m : ℕ} (v : Finset (Fin m) → ℝ) (p : Fin m → ℚ) (R D : Finset (Fin m)) :
    Prop :=
  D ⊆ R ∧ ∀ T ⊆ R, v T - ∑ j ∈ T, (p j : ℝ) ≤ v D - ∑ j ∈ D, (p j : ℝ)

/-- A correct (ordinary) demand oracle for `(v_i)`: the question `i, p_1, …, p_m` with
nonnegative rational prices is answered `1_D` for a set `D` maximizing `v_i(D) − ∑_{j ∈ D} p_j`
over all of `M`; ties are broken in any way, fixed by the oracle function. -/
def IsDemandOracle {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (O : Oracle) : Prop :=
  ∀ (i : Fin n) (p : Fin m → ℚ), (∀ j, 0 ≤ p j) →
    ∃ D : Finset (Fin m), O (((i : ℕ) : ℚ) :: List.ofFn p) = encSet D ∧
      IsDemandSet (v i) p Finset.univ D

/-- A correct restricted demand oracle for `(v_i)`: the question `i, 1_R, p_1, …, p_m` with
nonnegative rational prices is answered `1_D` for a set `D ⊆ R` maximizing
`v_i(D) − ∑_{j ∈ D} p_j` over the subsets of `R`. -/
def IsRestrictedDemandOracle {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (O : Oracle) : Prop :=
  ∀ (i : Fin n) (R : Finset (Fin m)) (p : Fin m → ℚ), (∀ j, 0 ≤ p j) →
    ∃ D : Finset (Fin m), O (((i : ℕ) : ℚ) :: (encSet R ++ List.ofFn p)) = encSet D ∧
      IsDemandSet (v i) p R D

/-- The two ports of Lemma A.1 (p. 59) on one oracle, for a fixed `β`:
* `0, i, 1_S` is the exact value query, answered `[v_i(S)]`;
* `1, i, c_1, …, c_m, B, t` with costs `c ≥ 0`, budget `B ≥ 0` and target `t > 0` is the
  budgeted routine: it is answered `1_D` with `c(D) ≤ B`, and `v_i(D) ≥ β t` whenever some set
  `S` with `c(S) ≤ B` has `v_i(S) ≥ t`. -/
def IsBudgetedOracle {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (β : ℚ) (O : Oracle) : Prop :=
  (∀ (i : Fin n) (S : Finset (Fin m)), ∃ r : ℚ,
    O (0 :: ((i : ℕ) : ℚ) :: encSet S) = [r] ∧ (r : ℝ) = v i S) ∧
  (∀ (i : Fin n) (c : Fin m → ℚ) (B t : ℚ), (∀ j, 0 ≤ c j) → 0 ≤ B → 0 < t →
    ∃ D : Finset (Fin m), O (1 :: ((i : ℕ) : ℚ) :: (List.ofFn c ++ [B, t])) = encSet D ∧
      ∑ j ∈ D, c j ≤ B ∧
      ((∃ S : Finset (Fin m), ∑ j ∈ S, c j ≤ B ∧ (t : ℝ) ≤ v i S) → ((β * t : ℚ) : ℝ) ≤ v i D))

/-- The input of an oracle instance (parts (ii), (iii) of Theorem 1.1): the numbers `n, m, σ`. -/
def oracleInput (n m σ : ℕ) : List ℚ := [(n : ℚ), (m : ℚ), (σ : ℚ)]

/-- The size of an oracle instance: `n + m + σ` (the valuations enter only through σ, App. E.1). -/
def oracleSize (n m σ : ℕ) : ℕ := n + m + σ

/-- The size of an instance given by an explicit input list: `n + m` plus its encoding length. -/
def explicitSize (n m : ℕ) (input : List ℚ) : ℕ := n + m + listBits input

/-- The input of an additive instance (part (i)): `n, m` and the table `(v_{ij})` row by row. -/
def tableInput {n m : ℕ} (V : Fin n → Fin m → ℚ) : List ℚ :=
  [(n : ℚ), (m : ℚ)] ++ (List.finRange n).flatMap (fun i => List.ofFn (V i))

/-- The additive valuations of a table: `v_i(S) = ∑_{j ∈ S} v_{ij}`. -/
def tableValuation {n m : ℕ} (V : Fin n → Fin m → ℚ) : Fin n → Finset (Fin m) → ℝ :=
  fun i S => ∑ j ∈ S, (V i j : ℝ)

/-- The max-min guarantee with ratio `ρ` for the output allocation `A`:
`min_i v_i(Y_i) ≤ ρ · min_i v_i(A_i)` for every allocation `Y` (equivalently
`OPT_MM ≤ ρ · min_i v_i(A_i)`). -/
def MMApprox {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (ρ : ℝ) (A : Fin n → Finset (Fin m)) :
    Prop :=
  ∀ Y : Fin n → Finset (Fin m), IsAllocation Y → mmValue v Y ≤ ρ * mmValue v A

/-! ## Explicit configuration solutions as outputs (Lemma 3.4, Lemma A.1) -/

/-- The output format of an explicit configuration solution: entry `0` is a flag (`0` = "`T_LP = 0`
detected", `1` = a solution follows); entry `1` is the target `T`; entry `2` the number `K` of
triples; triple `r < K` occupies the `m + 2` entries from `3 + r(m + 2)`: the agent, the mass
`y_{i,S}` and the indicator of `S`. -/
def solFlag (l : List ℚ) : ℚ := l.getD 0 0

/-- The target `T` of an output solution. -/
def solTarget (l : List ℚ) : ℚ := l.getD 1 0

/-- The number of triples of an output solution. -/
def solCount (l : List ℚ) : ℕ := (⌊l.getD 2 0⌋).toNat

/-- Agent entry of triple `r`. -/
def solAgent (m : ℕ) (l : List ℚ) (r : ℕ) : ℚ := l.getD (3 + r * (m + 2)) 0

/-- Mass entry of triple `r`. -/
def solMassEntry (m : ℕ) (l : List ℚ) (r : ℕ) : ℚ := l.getD (3 + r * (m + 2) + 1) 0

/-- Configuration of triple `r`. -/
def solSet (m : ℕ) (l : List ℚ) (r : ℕ) : Finset (Fin m) := decSetAt m l (3 + r * (m + 2) + 2)

/-- Every triple names an agent `i < n` and writes its set with entries in `{0, 1}`. -/
def SolWellFormed (n m : ℕ) (l : List ℚ) : Prop :=
  ∀ r < solCount l, (∃ i : Fin n, solAgent m l r = ((i : ℕ) : ℚ)) ∧
    ∀ j : Fin m, l.getD (3 + r * (m + 2) + 2 + (j : ℕ)) 0 = 0 ∨
      l.getD (3 + r * (m + 2) + 2 + (j : ℕ)) 0 = 1

/-- The masses `y_{i,S}` listed by an output solution (repeated pairs add up). -/
def solMass (n m : ℕ) (l : List ℚ) : Fin n → Finset (Fin m) → ℝ :=
  fun i S => ∑ r ∈ Finset.range (solCount l),
    if solAgent m l r = ((i : ℕ) : ℚ) ∧ solSet m l r = S then (solMassEntry m l r : ℝ) else 0

/-- The outcome required of Lemmas 3.4 and A.1 on the output `l`, with support bound `K` and
target factor `γ`: either the flag `0` and `T_LP = 0`, or the flag `1`, a well-formed list of at
most `K` triples forming a configuration solution with objective value `T`, and `T > γ · T_LP`. -/
def SolOutcome {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (γ : ℝ) (K : ℕ) (l : List ℚ) : Prop :=
  (solFlag l = 0 ∧ TLP v = 0) ∨
  (solFlag l = 1 ∧ SolWellFormed n m l ∧ solCount l ≤ K ∧
    IsConfigSolutionAt v (solMass n m l) (solTarget l : ℝ) ∧ γ * TLP v < (solTarget l : ℝ))

end SantaClausNSW.MaxMin


