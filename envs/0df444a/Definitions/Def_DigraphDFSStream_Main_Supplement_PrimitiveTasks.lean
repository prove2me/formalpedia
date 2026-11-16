-- Prove2me | Definitions.Def_DigraphDFSStream_Main_Supplement_PrimitiveTasks
-- name    : DigraphDFSStream_Main_Supplement_PrimitiveTasks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T12:56:07.652849+00:00
-- url     : https://prove2.me/theorems/b858d1f0-fb41-456d-bcbe-5bf6e3702074
-- title:
--   Reachability, directed path and SCC streaming tasks
-- statement:
--   The primitive tasks run the published streaming program with charged task parameters. On a graph with $m$ labelled vertices, single-source reachability returns precisely the vertices reachable from its source, including the source. Directed path construction returns a nonempty simple directed path with the specified first and last vertices whenever the last vertex is reachable from the first. There is no correctness obligation for a path query with unreachable target. SCC decomposition returns the full partition into strongly connected components; no topological order is needed by the SCC tests in §4.
--
--   Fix an ambient scale $n\ge1$, a vertex factor $A$, pass budget $p(n)$, bit budget $b(n)$ and reliability exponent $D$. The primitive package requires uniform programs such that, on every stream with $m\le An$ labels,
--   $$\text{passes}\le p(n),\qquad\text{charged bits}\le b(n),\qquad\Pr(\text{correct output})\ge1-(n+2)^{-D}.$$
--   The ambient scale and query vertices are supplied in the charged header. Resource bounds and termination hold on every tape; the measurable success event is calculated from that program's actual execution. Reversed and induced streams and virtual source/sink graphs must be simulated by the eventual calling program with their costs charged.
--
--   The reachability/path package and the SCC package are separate. Section 4's resource lemmas assume both, whereas Theorem 1.2 assumes only reachability and path construction. Constants $A,D$ are chosen before the pass and bit functions and every graph. The statement's existential choice of $D$ leaves the full amplification and adaptive-call error budget as proof obligations, rather than assuming that primitive calls succeed.
-- source:
--   Prantar Ghosh, Amirhossein Janfaza, STOC 2027 submission #1648 (October 2026), §2, Facts 2.3–2.6, printed p.5 (PDF p.6); §4 standing assumptions, printed pp.11–12 (PDF pp.12–13); Theorem 1.2 proof, printed p.18 (PDF p.19)

import Definitions.Def_DigraphDFSStream_Main_GraphSemantics
import Definitions.Def_DigraphDFSStream_Main_Supplement_ParameterizedStreaming

set_option autoImplicit false

namespace DigraphDFSStream.Main.Supplement

def ReachOutput {m : ℕ} (E : Finset (Fin m × Fin m)) (s : Fin m)
    (out : List Bool) : Prop :=
  ∃ xs : List (Fin m), xs.Nodup ∧ out = vertexCode xs ∧
    ∀ v : Fin m, v ∈ xs ↔ Reach E Finset.univ s v

def PathOutput {m : ℕ} (E : Finset (Fin m × Fin m)) (s t : Fin m)
    (out : List Bool) : Prop :=
  Reach E Finset.univ s t → ∃ xs : List (Fin m), out = vertexCode xs ∧
    SimplePath E Finset.univ xs ∧ xs.head? = some s ∧ xs.getLast? = some t

/-- Unordered SCC decomposition suffices for every SCC test in Section 4. -/
def SCCOutput {m : ℕ} (E : Finset (Fin m × Fin m)) (out : List Bool) : Prop :=
  ∃ cs : List (List (Fin m)), out = familyCode cs ∧
    (∀ xs ∈ cs, xs.Nodup ∧ IsSCC E Finset.univ xs.toFinset) ∧
    (cs.map List.toFinset).Pairwise Disjoint ∧ cs.flatten.toFinset = Finset.univ

/-- p(n) bounds queries on all graphs with at most A*n labels, including a virtual source or
sink. n is the ambient confidence/space scale, supplied in the charged header. These are
actual programs, not free graph oracles. Reliability is unconditional over their own coins. -/
def ReachPathPrimitives (A : ℕ) (p b : ℕ → ℕ) (D : ℕ) : Prop :=
  ∃ R T : StreamProgram, ∀ (n m : ℕ), 1 ≤ n → m ≤ A * n →
    ∀ (input : List (Fin m × Fin m)) (s t : Fin m),
      ParameterBounds R input (natCode n ++ natCode s.val) (b n) (p n) ∧
      ParameterReliable R input (natCode n ++ natCode s.val)
        (ReachOutput input.toFinset s) ((n + 2 : ℝ) ^ (-(D : ℝ))) ∧
      ParameterBounds T input (natCode n ++ natCode s.val ++ natCode t.val) (b n) (p n) ∧
      ParameterReliable T input (natCode n ++ natCode s.val ++ natCode t.val)
        (PathOutput input.toFinset s t) ((n + 2 : ℝ) ^ (-(D : ℝ)))

def SCCPrimitive (A : ℕ) (p b : ℕ → ℕ) (D : ℕ) : Prop :=
  ∃ S : StreamProgram, ∀ (n m : ℕ), 1 ≤ n → m ≤ A * n →
    ∀ input : List (Fin m × Fin m),
      ParameterBounds S input (natCode n) (b n) (p n) ∧
      ParameterReliable S input (natCode n) (SCCOutput input.toFinset)
        ((n + 2 : ℝ) ^ (-(D : ℝ)))

def SectionPrimitives (A : ℕ) (p b : ℕ → ℕ) (D : ℕ) : Prop :=
  ReachPathPrimitives A p b D ∧ SCCPrimitive A p b D

end DigraphDFSStream.Main.Supplement


