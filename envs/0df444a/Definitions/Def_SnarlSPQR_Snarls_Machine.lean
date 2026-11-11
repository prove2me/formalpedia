-- Prove2me | Definitions.Def_SnarlSPQR_Snarls_Machine
-- name    : SnarlSPQR_Snarls_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:29:17.907326+00:00
-- url     : https://prove2.me/theorems/6d642c2c-2608-4cc7-ab64-b54688804a1b
-- title:
--   The deterministic word RAM, the edge-list input of a bidirected graph and the output layout of a snarl representation
-- statement:
--   The paper names no machine model. Its algorithmic claim is read on the published integer RAM `CongruencyTU` (unit cost per instruction, input block $R[0]=|I|$, $R[i+1]=I[i]$, output $R[1..R[0]]$ at halting) with three restrictions.
--
--   - **Deterministic.** The program contains no coin and no oracle instruction.
--   - **Logarithmic words.** One width constant $w$, fixed with the program, bounds the bit length of every register at every step by $w\,(1+\log_2(2+|V(G)|+|E(G)|))$.
--   - **Time.** Time is the cost counter at halting.
--
--   **Input.** A bidirected graph on the vertices $0,\dots,n-1$ is given by its edges $\{u_1a_1,v_1b_1\},\dots,\{u_ma_m,v_mb_m\}$, each listed once, in either orientation and in any order, as
--   $$[n,m,u_1,a_1,v_1,b_1,\dots,u_m,a_m,v_m,b_m],$$
--   with sign code $+\mapsto1$, $-\mapsto0$.
--
--   **Output.** The output is $[k,|T_1|,T_1,\dots,|T_k|,T_k,\ell,S_1,\dots,S_\ell]$. A vertex-side $v\alpha$ is written as $v,\mathrm{code}(\alpha)$, and each pair $S_j$ as four integers.
--
--   **Representation of all snarls** (Theorem 2) has four parts:
--   - every $T_i$ lists distinct vertex-sides of $G$;
--   - any two distinct elements of a $T_i$ form a snarl;
--   - every $S_j$ is a snarl;
--   - every snarl of $G$ is a pair of distinct elements of some $T_i$ or equals some $S_j$ as an unordered pair.
--
--   **Formalization Note.** `Deterministic`, `WordBounded` and `HaltsWithin` follow the published `MinDegST_AddOne_Machine` pattern but are restated here, because that module's encodings are for simple graphs. A halted state is fixed, so the output read at any halting step is the output of the first halting step.
-- source:
--   Sena, Politov, Moumard, Cairo, Rizzi, Cáceres, Schmidt, Harviainen, Tomescu, Identifying bubble-like subgraphs in linear-time via a unified SPQR-tree framework, arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), p. 12, Theorem 2; pp. 41–42 (proof of Theorem 2); machine model chosen for this mission

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_SnarlSPQR_Snarls_Snarl

open Classical

namespace SnarlSPQR.Snarls

/-!
# The machine, the input encoding of a bidirected graph, and the output representation
(Theorem 2, p. 12; proof pp. 41–42)

Sena et al., arXiv:2604.08071 (copy of 2026-11-03, sha256 40a9dca1…), Theorem 2 (p. 12, restated
p. 41) and its running-time proof (pp. 41–42). The paper names no machine model; this module fixes
one, shared by the goal.

**Machine.** A program of the published integer RAM `CongruencyTU.Program`
(`Def_CongruencyTU_Machine`: unit cost per instruction, input block `R[0] = |I|, R[i+1] = I[i]`,
output block `R[1], …, R[R[0]]` at halting), run without coins and without oracle, that is
**deterministic** (it contains no `coin` and no `query` instruction) and has **logarithmic
words**: one width constant `width`, fixed with the program, bounds the bit length of every
register at every step by `width · (1 + log₂(2 + scale))`, with `scale = |V(G)| + |E(G)|`.
Without the word bound unit-cost arithmetic on unbounded integers would trivialize running
times. Time is the cost counter at halting. (The pattern of the published
`MinDegST_AddOne_Machine`, copied here because that module's encodings are for `SimpleGraph`.)

**Input.** A bidirected graph on the vertices `0, …, n − 1` (`Fin n`), given by a list of its
edges, each edge listed exactly once, in either orientation, in any order:
`[n, m, u₁, a₁, v₁, b₁, …, u_m, a_m, v_m, b_m]` for the edges `{u_i a_i, v_i b_i}`, with the sign
code `+ ↦ 1`, `− ↦ 0`.

**Output.** Lists `T₁, …, T_k` of vertex-sides and pairs `S₁, …, S_ℓ` of vertex-sides, written
`[k, |T₁|, T₁…, …, |T_k|, T_k…, ℓ, S₁…, …, S_ℓ…]`, a vertex-side `vα` as the two integers
`v, code(α)` and a pair as four integers.

**Representation** (Theorem 2): each `T_i` lists vertex-sides of `G`, each once, and any two
distinct vertex-sides of a `T_i` form a snarl of `G`; each `S_j` is a snarl of `G`; and every snarl
of `G` is a pair of distinct vertex-sides of some `T_i` or equals some `S_j` (the representation
is of the set of *all* snarls). The size bounds are stated in the goal.
-/

/-- A deterministic program: no coin instruction and no oracle query. -/
def Deterministic (P : CongruencyTU.Program) : Prop :=
  (∀ d, CongruencyTU.Instr.coin d ∉ P) ∧ ∀ a, CongruencyTU.Instr.query a ∉ P

/-- Logarithmic words: on input `I`, at every step every register of the run of `P` (no coins,
no oracle) has bit length at most `width · (1 + log₂(2 + scale))`. -/
def WordBounded (P : CongruencyTU.Program) (I : List ℤ) (width scale : ℕ) : Prop :=
  ∀ t j, Nat.size ((CongruencyTU.run P CongruencyTU.noOracle CongruencyTU.noCoins I t).reg j).natAbs
    ≤ width * (1 + Nat.log2 (2 + scale))

/-- On input `I` the run of `P` (no coins, no oracle) halts with accumulated cost at most `B`,
and its output at halting satisfies `Good`. (A halted state is fixed, so the output is that of
the first halting step.) -/
def HaltsWithin (P : CongruencyTU.Program) (I : List ℤ) (B : ℕ) (Good : List ℤ → Prop) : Prop :=
  ∃ t, CongruencyTU.isHalted P (CongruencyTU.run P CongruencyTU.noOracle CongruencyTU.noCoins I t)
      = true ∧
    (CongruencyTU.run P CongruencyTU.noOracle CongruencyTU.noCoins I t).cost ≤ B ∧
    Good (CongruencyTU.outputOf (CongruencyTU.run P CongruencyTU.noOracle CongruencyTU.noCoins I t))

/-- The sign code: `+ ↦ 1`, `− ↦ 0`. -/
def signCode : Sign → ℤ
  | .pos => 1
  | .neg => 0

variable {n : ℕ}

/-- A vertex-side `vα` as the two integers `[v, code(α)]`. -/
def encSide (p : Fin n × Sign) : List ℤ := [(p.1.val : ℤ), signCode p.2]

/-- `l` lists the edges of `G`, each exactly once, each in either orientation. -/
def IsEdgeListOf (G : BiGraph (Fin n)) (l : List ((Fin n × Sign) × (Fin n × Sign))) : Prop :=
  (l.map fun p => s(p.1, p.2)).Nodup ∧ ∀ e, e ∈ G.edges ↔ ∃ p ∈ l, s(p.1, p.2) = e

/-- The input `[n, m, u₁, a₁, v₁, b₁, …]` for the edge list `l` of a graph on `Fin n`. -/
def encInput (n : ℕ) (l : List ((Fin n × Sign) × (Fin n × Sign))) : List ℤ :=
  [(n : ℤ), (l.length : ℤ)] ++ l.flatMap fun p => encSide p.1 ++ encSide p.2

/-- The output layout `[k, |T₁|, T₁…, …, |T_k|, T_k…, ℓ, S₁…, …, S_ℓ…]`. -/
def encRep (Ts : List (List (Fin n × Sign))) (Ss : List ((Fin n × Sign) × (Fin n × Sign))) :
    List ℤ :=
  [(Ts.length : ℤ)] ++ Ts.flatMap (fun T => (T.length : ℤ) :: T.flatMap encSide) ++
    [(Ss.length : ℤ)] ++ Ss.flatMap fun p => encSide p.1 ++ encSide p.2

/-- `(Ts, Ss)` is a representation of the set of all snarls of `G` (Theorem 2, items 1–2 and
completeness): every `T_i` lists vertex-sides of `G` without repetition and any two distinct
elements of a `T_i` form a snarl; every `S_j` is a snarl; every snarl is a pair of distinct
elements of some `T_i` or equals some `S_j` (as an unordered pair). -/
def IsSnarlRep (G : BiGraph (Fin n)) (Ts : List (List (Fin n × Sign)))
    (Ss : List ((Fin n × Sign) × (Fin n × Sign))) : Prop :=
  (∀ T ∈ Ts, T.Nodup ∧ ∀ a ∈ T, a ∈ G.sides) ∧
    (∀ T ∈ Ts, ∀ a ∈ T, ∀ b ∈ T, a ≠ b → G.Snarl a b) ∧
    (∀ p ∈ Ss, G.Snarl p.1 p.2) ∧
    ∀ a b, G.Snarl a b →
      (∃ T ∈ Ts, a ∈ T ∧ b ∈ T ∧ a ≠ b) ∨ ∃ p ∈ Ss, s(p.1, p.2) = s(a, b)

end SnarlSPQR.Snarls


