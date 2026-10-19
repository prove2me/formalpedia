-- Prove2me | Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces
-- name    : OAI_Combinatorics_Hamiltonian_Traces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:50:25.49951+00:00
-- url     : https://prove2.me/theorems/8cb092a0-34c8-4d29-8db6-5db1376fd8e6
-- title:
--   Branch sets and middle cores of arcs in a plane embedding
-- statement:
--   **Setting.** Let $G$ be a simple graph on a vertex set $V$. A plane embedding of $G$ consists of pairwise distinct points $p_v\in\mathbb{R}^2$ and, for every ordered pair $(v,w)$ of adjacent vertices, an injective continuous arc $\gamma_{vw}:[0,1]\to\mathbb{R}^2$ with $\gamma_{vw}(0)=p_v$ and $\gamma_{vw}(1)=p_w$, such that $\gamma_{wv}(t)=\gamma_{vw}(1-t)$, an arc passes through a vertex point only at its own endpoints, and interior points of arcs of different edges never coincide. A *dart* is an ordered pair $d=(v,w)$ of adjacent vertices, with first vertex $v$ and second vertex $w$.
--
--   1. **Curve of a dart.** For $d=(v,w)$, $\gamma_d=\gamma_{vw}$; it starts at $p_v$ and ends at $p_w$.
--   2. **Two parameters.** The points $\tfrac13$ and $\tfrac23$ of the unit interval.
--   3. **Traces.** For $a,b\in[0,1]$, the trace of $d$ on $[a,b]$ is $\gamma_d([a,b])=\{\gamma_d(t): a\le t\le b\}\subseteq\mathbb{R}^2$ (empty if $a>b$).
--   4. **Branch set of a vertex.**
--   $$
--   \operatorname{br}(v)=\{p_v\}\ \cup\bigcup_{d=(v,w)}\gamma_d\bigl([0,\tfrac13]\bigr),
--   $$
--   the union being over all darts starting at $v$: the point $p_v$ together with the first third of every arc leaving it.
--   5. **Core of a dart.** $\operatorname{core}(d)=\gamma_d\bigl([\tfrac13,\tfrac23]\bigr)$, the middle third of the arc. Because $\gamma_{wv}(t)=\gamma_{vw}(1-t)$, a dart and its reverse have the same core.
--
--   These are compact connected pieces of the drawing (for finite $V$). Branch sets of distinct vertices are disjoint, cores of darts on different edges are disjoint, a branch set is disjoint from the core of every dart not incident to its vertex, and the core of $d=(v,w)$ meets both $\operatorname{br}(v)$ and $\operatorname{br}(w)$. Since finitely many compact sets that are disjoint in prescribed pairs have uniformly thick disjoint neighbourhoods, these sets can be replaced by the lattice cells of a fine square grid, which is how the drawing yields disjoint lattice corridors.
--
--   **Formalization Note** Darts are Mathlib's `G.Dart` and arcs are `Path`s parametrised by `unitInterval`; `curve`, `trace`, `branch` and `core` are the Lean names, `curve_zero` and `curve_one` are the endpoint simp lemmas, and `third`, `twoThirds` are the elements $1/3$ and $2/3$ of `unitInterval`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Hamiltonian/Traces.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Traces.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BarnetteHamiltonian mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing

namespace OAI

/-! Compact connected arc traces and uniform positive thickenings. -/

namespace Barnette.PlaneEmbedding

noncomputable section

variable {V : Type*} {G : SimpleGraph V} (E : PlaneEmbedding G)

def curve (d : G.Dart) : Path (E.point d.fst) (E.point d.snd) :=
  E.arc d.fst d.snd d.adj

@[simp] theorem curve_zero (d : G.Dart) : E.curve d 0 = E.point d.fst :=
  (E.curve d).source

@[simp] theorem curve_one (d : G.Dart) : E.curve d 1 = E.point d.snd :=
  (E.curve d).target

 def third : unitInterval := ⟨1 / 3, by norm_num⟩
 def twoThirds : unitInterval := ⟨2 / 3, by norm_num⟩

def trace (d : G.Dart) (a b : unitInterval) : Set (ℝ × ℝ) :=
  (E.curve d) '' Set.Icc a b

def branch (v : V) : Set (ℝ × ℝ) :=
  {E.point v} ∪ ⋃ d : {d : G.Dart // d.fst = v}, E.trace d.val 0 third

def core (d : G.Dart) : Set (ℝ × ℝ) := E.trace d third twoThirds

end
end Barnette.PlaneEmbedding

end OAI


