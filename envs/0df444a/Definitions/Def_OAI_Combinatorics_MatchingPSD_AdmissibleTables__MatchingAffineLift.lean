-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_AdmissibleTables__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:39:35.960346+00:00
-- url     : https://prove2.me/theorems/a1cb32eb-b340-4b21-9d37-194e0f4e8a2b
-- title:
--   Colour-preserving bijections, typed edge sets and the three-block vertex set
-- statement:
--   This file contains the combinatorial objects used to realise prescribed numbers of edges between three colour classes by an explicit perfect matching.
--
--   The *histogram* of a map $f:X\to K$ on a finite set $X$ is $h_f(k)=|f^{-1}(k)|$, and $\mathcal V_h=\{0,\dots,h-1\}\times\{\mathrm{false},\mathrm{true}\}$ denotes the standard vertex set with $2h$ elements.
--
--   1. **Colour-preserving bijection.** Let $A,B$ be finite sets, $K$ a set with decidable equality, and $f:A\to K$, $g:B\to K$ maps with $h_f=h_g$. A bijection $A\to B$ is obtained by choosing, for every $k\in K$, a bijection between the equally large colour classes $f^{-1}(k)$ and $g^{-1}(k)$ and assembling these; it carries every colour class of $f$ onto the colour class of $g$ of the same colour.
--   2. **Edge types.** The six types of an edge whose endpoints have colours in $\{0,1,2\}$ are enumerated as
--   $$
--   \tau_0=(0,0),\quad \tau_1=(0,1),\quad \tau_2=(0,2),\quad \tau_3=(1,1),\quad \tau_4=(1,2),\quad \tau_5=(2,2).
--   $$
--   3. **Typed edges and their endpoint colouring.** For $E=(E_0,\dots,E_5)\in\mathbb{N}^6$, the set of typed edges is $\mathcal E_E=\bigsqcup_{t=0}^{5}\{t\}\times\{0,\dots,E_t-1\}$, i.e. $E_t$ edges of type $\tau_t$. Each edge $e$ has the two endpoints $(e,\mathrm{false})$ and $(e,\mathrm{true})$; if $e$ has type $\tau_t=(a,b)$, the endpoint $(e,\mathrm{false})$ gets colour $a$ and $(e,\mathrm{true})$ gets colour $b$.
--   4. **Endpoint sizes.** The numbers of endpoints of colours $0,1,2$ are recorded by
--   $$
--   \nu(E)=\bigl(2E_0+E_1+E_2,\ \ E_1+2E_3+E_4,\ \ E_2+E_4+2E_5\bigr).
--   $$
--   5. **Three-block vertex set.** For $s\in\mathbb{N}$, $\mathcal T_s=(A_s\sqcup B_s)\sqcup C_s$ with $A_s,B_s$ two copies of $\{0,\dots,2s\}$ (each of odd size $2s+1$) and $C_s=\{0,\dots,s-1\}\times\{\mathrm{false},\mathrm{true}\}$ (of size $2s$). It is coloured by giving $A_s$, $B_s$, $C_s$ the colours $0$, $1$, $2$. It has $|\mathcal T_s|=2(3s+1)$ elements, and a fixed (non-canonical) bijection $\mathcal T_s\to\mathcal V_{3s+1}$ is chosen from this cardinality equality.
--
--   Matching the two endpoints of each typed edge gives a perfect matching of $\mathcal E_E\times\{\mathrm{false},\mathrm{true}\}$ with exactly $E_1$, $E_2$, $E_4$ edges between the colour classes $0$–$1$, $0$–$2$, $1$–$2$. Whenever $\nu(E)$ is the histogram of a colouring of another finite set, the colour-preserving bijection of item 1 transports this matching there. Applied to $\mathcal T_s$, whose colour histogram is $(2s+1,2s+1,2s)$, this produces matchings of the three-block vertex set with prescribed numbers of edges between the blocks.
--
--   **Formalization Note** The Lean names are `colorEquiv` (noncomputable, assembled from `Equiv.sigmaFiberEquiv` and `Fintype.equivOfCardEq` on each fibre), `typePair`, `TypedEdges E` (a sigma type), `edgeColor`, `endpointSizes`, `TripleVertices s`, `tripleColor` and `tripleEquiv`; `triple_card` is the cardinality lemma. The histogram is `histogram f k = Fintype.card {a // f a = k}`, and `Vertices h` is `Fin h × Bool`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/AdmissibleTables.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/AdmissibleTables.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingAffineLift mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry__MatchingAffineLift

namespace OAI

universe u_1 u_2 u_3 u_4

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section ColorTransport
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [Fintype A] [Fintype B] [Fintype C] [DecidableEq C]
noncomputable def colorEquiv (f : A → C) (g : B → C) (h : histogram f = histogram g) : A ≃ B :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight (fun c => Fintype.equivOfCardEq (congrFun h c))).trans
      (Equiv.sigmaFiberEquiv g))

end ColorTransport

def typePair : Fin 6 → Fin 3 × Fin 3 := ![(0,0),(0,1),(0,2),(1,1),(1,2),(2,2)]
abbrev TypedEdges (E : Fin 6 → ℕ) := (t : Fin 6) × Fin (E t)
def edgeColor (E : Fin 6 → ℕ) : TypedEdges E × Bool → Fin 3 :=
  fun v => if v.2 then (typePair v.1.1).2 else (typePair v.1.1).1

def endpointSizes (E : Fin 6 → ℕ) : Fin 3 → ℕ :=
  ![2*E 0+E 1+E 2, E 1+2*E 3+E 4, E 2+E 4+2*E 5]

abbrev TripleVertices (s : ℕ) := (Fin (2*s+1) ⊕ Fin (2*s+1)) ⊕ (Fin s × Bool)
def tripleColor {s : ℕ} : TripleVertices s → Fin 3 :=
  Sum.elim (Sum.elim (fun _ => 0) (fun _ => 1)) (fun _ => 2)

lemma triple_card (s : ℕ) : Fintype.card (TripleVertices s) = 2*(3*s+1) := by
  simp only [TripleVertices, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod,
    Fintype.card_bool]
  omega

noncomputable def tripleEquiv (s : ℕ) : TripleVertices s ≃ Vertices (3*s+1) :=
  Fintype.equivOfCardEq (by
    change Fintype.card (TripleVertices s) = Fintype.card (Fin (3*s+1) × Bool)
    rw [triple_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega)

end MatchingSmoothing

end OAI


