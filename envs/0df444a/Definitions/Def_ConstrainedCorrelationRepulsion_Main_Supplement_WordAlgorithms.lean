-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Supplement_WordAlgorithms
-- name    : ConstrainedCorrelationRepulsion_Main_Supplement_WordAlgorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:04:39.045812+00:00
-- url     : https://prove2.me/theorems/68cd1732-04fa-40b2-9e83-7a642c1268da
-- title:
--   Costed graph algorithms and the exact transfer resources
-- statement:
--   The finite register programs and machine executions are the published ones. The word-mode instruction subset contains natural arithmetic, memory access, graph-bit queries, comparisons, jumps and halting; fair coins are also available. There is no real arithmetic or optimization primitive. Input queries expose only the graph and its cluster-deletion constraints. Output deletion bits occupy the upper triangle of an $n$ by $n$ matrix, while output vertex-cover bits occupy $n$ words. Every supported terminal state must encode a legal solution satisfying the pointwise approximation ratio. The interpreter charges every executed instruction; matrix/output reads are charged explicitly as well.
--
--   An at-most-$N$ time envelope $f$ means the same program solves every graph with $n\le N$ vertices within some budget $B\le f(N)$. No monotonicity or polynomial growth of $f$ is assumed. The transfer coefficient is
--
--   $$k=\left\lceil\frac{c}{2(c-1)}\right\rceil,\qquad c'=k+1.$$
--
--   For an endpoint $v$ of the chosen input edge, the constructed call graph is explicitly $\overline{G-v}\vee K_{kn^2}$. The integer $k$ can be compiled into the finite program for fixed $c$. This permitted rounding has the same lower bound on $t$ and the same $c'$ as the proof's $t=\lceil cn^2/[2(c-1)]\rceil$.
--
--   These are ordinary adjacency-matrix word-operation semantics for the sharp bounds, rather than the bit-cost convention used for Theorem 1.5. Polynomial bit simulation of the graph construction and extraction must be supplied inside the Cook reductions proving Theorem 1.2; this definition grants no such simulation for arbitrary word programs.
--
--   Differences from the source:
--   - encoding: graph algorithms and their usual worst-case time → finite costed register executions with an at-most-size envelope; reason: all calls and outputs are charged and arbitrary envelopes need not be monotone.
-- source:
--   Yixin Cao, Ying Xu, STOC 2027 submission #869 (October 2026), Theorem 1.3 and proof, printed pp.2, 36–37 (PDF pp.3, 37–38)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Supplement_Graphs
import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Algorithm

namespace ConstrainedCorrelationRepulsion.Main.Supplement

open Classical

/-- Word programs use the published finite register syntax. Only natural
word arithmetic, memory, graph-bit reads and comparisons are available. Real registers only
hold graph bits, casts of natural words or fair-coin parameters. There is no real arithmetic, optimizer,
free callback or subroutine instruction with an uncharged runtime. -/
def WordInstruction : Instruction → Prop
  | .natConst _ _ | .natAdd _ _ _ | .natSub _ _ _ | .natMul _ _ _ |
    .natDiv _ _ _ | .natMod _ _ _ | .natLoad _ _ | .natStore _ _ |
    .query _ _ _ _ | .cast _ _ | .branchNat _ _ _ _ | .branchReal _ _ _ _ |
    .jump _ | .halt | .bernoulli _ _ => True
  | .ratConst _ q => q = 0 ∨ q = 1 ∨ q = 1/2
  | _ => False

def WordProgram (code : Program) : Prop := ∀ i ∈ code, WordInstruction i

/-- Graph-only input; no solution or timing information is in the oracle. -/
noncomputable def graphOracle {n : ℕ} (G : Graph n) : ℕ → ℕ → ℕ → ℝ :=
  inputOracle (deletionInstance G)

/-- Deletion output is the upper triangular part of an n-by-n bit matrix at addresses
n*u+v. Requiring IsDeletionSet separately rules out additions and illegal pairs. -/
noncomputable def decodeDeletion {n : ℕ} (s : MachineState) : Finset (Sym2 (Fin n)) :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter fun e =>
    e.1 < e.2 ∧ s.natMem (n*e.1.val+e.2.val) ≠ 0).image fun e => s(e.1,e.2)

noncomputable def decodeCover {n : ℕ} (s : MachineState) : Finset (Fin n) :=
  Finset.univ.filter (fun v => s.natMem v.val ≠ 0)

/-- Unit-cost word execution, with input and output matrix accesses charged. The arithmetic
is the ordinary word-operation convention of §7. Polynomial bit simulation of the actual
reduction (which manipulates polynomially bounded graph indices) belongs to the Cook
reductions in the hardness theorem; it is not presumed from this predicate. -/
def DeletionRun {n : ℕ} (code : Program) (G : Graph n) (c : ℝ) (B : ℕ) : Prop :=
  WordProgram code ∧ n*n+n+1 ≤ B ∧
  BoundedRun false code (graphOracle G) (initialState n) (B-(n*n+n)) ∧
  ∀ s ∈ (machineRun false code (graphOracle G) (initialState n) (B-(n*n+n))).support,
    IsDeletionSet G (decodeDeletion s) ∧
    ((decodeDeletion (n:=n) s).card : ℝ) ≤ c * (deletionOPT G : ℝ)

def CoverRun {n : ℕ} (code : Program) (G : Graph n) (c : ℝ) (B : ℕ) : Prop :=
  WordProgram code ∧ n+1 ≤ B ∧
  BoundedRun false code (graphOracle G) (initialState n) (B-n) ∧
  ∀ s ∈ (machineRun false code (graphOracle G) (initialState n) (B-n)).support,
    G.IsVertexCover (↑(decodeCover (n:=n) s) : Set (Fin n)) ∧
    ((decodeCover (n:=n) s).card : ℝ) ≤ c * (tau G : ℝ)

/-- f is an at-most-N envelope, so no monotonicity of the supplied function is assumed. -/
def DeletionAlgorithm (code : Program) (c : ℝ) (f : ℕ → ℕ) : Prop :=
  ∀ N n, n ≤ N → ∀ G : Graph n, ∃ B ≤ f N, DeletionRun code G c B

noncomputable def blowupCoefficient (c : ℝ) : ℕ := ⌈c / (2*(c-1))⌉₊ + 1

/-- The two graph calls in the proof: remove one edge endpoint, complement, join.
The integer k is compiled once for the fixed c; no real c is read at runtime. -/
noncomputable def endpointJoin {n : ℕ} (G : Graph (n+1)) (v : Fin (n+1))
    (k : ℕ) : Graph (n + k*(n+1)^2) :=
  joinClique ((G.comap v.succAbove)ᶜ) (k*(n+1)^2)

end ConstrainedCorrelationRepulsion.Main.Supplement


