-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_GlobalGeometry__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:38:44.103009+00:00
-- url     : https://prove2.me/theorems/59758f8f-7907-48c2-96df-5e8ca048a084
-- title:
--   Three-colour cross vectors and the local-to-global extension of pairings
-- statement:
--   This file sets up the colour classes and the gluing maps that embed a local matching problem on three blocks into a global vertex set made of two blocks and many cells.
--
--   **Notation.** A *pairing* of a set $X$ is a permutation $M$ of $X$ with $M(M(a))=a$ and $M(a)\neq a$ for every $a\in X$, that is, a perfect matching of $X$ in which every $a$ is matched to its partner $M(a)$. For pairings $M$ of $X$ and $N$ of $Y$, $M\oplus N$ is the pairing of $X\sqcup Y$ acting as $M$ on $X$ and as $N$ on $Y$; for pairings $(N_j)_{j\in J}$ of a set $C$, the cellwise pairing $\mathrm{cw}(N)$ of $J\times C$ is $(j,c)\mapsto(j,N_j(c))$; for a bijection $e:X\to Y$, $e_*M=e\circ M\circ e^{-1}$. For a finite set $V$, a colouring $z:V\to\{0,1,2\}$ and colours $c_1,c_2$, $T_{c_1c_2}(z,M)$ is the number of $v\in V$ with $z(v)=c_1$ and $z(M(v))=c_2$; for $c_1\neq c_2$ it is the number of edges of $M$ between colour class $c_1$ and colour class $c_2$.
--
--   1. **Block colourings.** For sets $A,B,C$, the colouring of $A\sqcup B$ gives $A$ colour $0$ and $B$ colour $1$; the colouring $\kappa$ of $(A\sqcup B)\sqcup C$ gives $A$, $B$, $C$ the colours $0$, $1$, $2$.
--   2. **Cross vector.** For a finite set $V$, $z:V\to\{0,1,2\}$ and a pairing $M$ of $V$,
--   $$
--   x(z,M)=\bigl(T_{01}(z,M),\ T_{02}(z,M),\ T_{12}(z,M)\bigr)\in\mathbb{R}^3 .
--   $$
--   For $z=\kappa$ it records the numbers of $A$–$B$, $A$–$C$ and $B$–$C$ edges of $M$.
--   3. **Cross vectors of split pairings.** For finite $A,B,C$, a pairing $M$ of $A\sqcup B$ and a pairing $N$ of $C$, $x(\kappa,M\oplus N)=(e_{AB}(M),0,0)$, where $e_{AB}(M)$ is the number of $A$–$B$ edges of $M$ (the coordinate $T_{01}$ for the colouring of $A\sqcup B$). Conversely, a pairing of $(A\sqcup B)\sqcup C$ whose second and third cross coordinates vanish (no $A$–$C$ and no $B$–$C$ edges) maps $A\sqcup B$ into itself.
--   4. **Star fibre.** For finite $A,B,C$ and $\xi\in\mathbb{R}$, $(M,N)\mapsto M\oplus N$ is a bijection from $\{M \text{ pairing of } A\sqcup B:\ e_{AB}(M)=\xi\}\times\{N\text{ pairing of } C\}$ onto $\{M\text{ pairing of }(A\sqcup B)\sqcup C:\ x(\kappa,M)=(\xi,0,0)\}$.
--   5. **Inserting a cell.** Let $D$, $C$, $I$ be sets and $i\in I$. The bijection $C\sqcup(\{j\in I: j\neq i\}\times C)\to I\times C$ sends $c\mapsto(i,c)$ and $(j,c)\mapsto(j,c)$; together with the associativity of disjoint unions it yields a bijection $\sigma_i:(D\sqcup C)\sqcup(\{j\neq i\}\times C)\to D\sqcup(I\times C)$.
--   6. **Local extension.** For a pairing $M$ of $D\sqcup C$ and pairings $N=(N_j)_{j\neq i}$ of $C$,
--   $$
--   \operatorname{ext}_i(M,N)=(\sigma_i)_*\bigl(M\oplus\mathrm{cw}(N)\bigr),
--   $$
--   the pairing of $D\sqcup(I\times C)$ that matches $D\cup(\{i\}\times C)$ according to $M$ (with $C$ placed as the cell $i$) and matches every other cell $\{j\}\times C$ internally by $N_j$.
--   7. **Local lift of permutations.** For a permutation $p$ of $D\sqcup C$, $\operatorname{lift}_i(p)=\sigma_i\circ(p\sqcup\mathrm{id})\circ\sigma_i^{-1}$ is the permutation of $D\sqcup(I\times C)$ that acts as $p$ on $D\cup(\{i\}\times C)$ and fixes all other cells pointwise.
--
--   In the lower-bound argument $D=A\sqcup B$ consists of two odd blocks and $I\times C$ of many even cells. A global matching is assembled from a local matching of $A\cup B\cup(\text{cell } i)$ and internal matchings of the other cells, and the cross vector of the local part determines how many matching edges cross the cuts of interest. The star fibre describes the local matchings whose only edges between different blocks are $A$–$B$ edges.
--
--   **Formalization Note** The Lean names are `abColor`, `threeColor`, `crossVector`, `starFiberEquiv`, `insertCellEquiv`, `localSplitEquiv`, `extendLocal` and `liftLocal`; item 3 consists of the lemmas `crossVector_sum` and `threeColor_closed`. The cross vector is `crossVector z M i = crossCoordinate z i M = tableCoordinate z (crossPair i) M` with `crossPair = ((0,1),(0,2),(1,2))`, real-valued. Items 5 to 7 assume decidable equality on $I$ and no finiteness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/GlobalGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/GlobalGeometry.lean by skeleton subtraction
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

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace MatchingSmoothing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

section ThreeCellGeometry
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [Fintype A] [Fintype B] [Fintype C]

def abColor : A ⊕ B → Fin 3 := Sum.elim (fun _ => 0) (fun _ => 1)
def threeColor : (A ⊕ B) ⊕ C → Fin 3 := Sum.elim abColor (fun _ => 2)
noncomputable def crossVector {V : Type u_4} [Fintype V] (z : V → Fin 3)
    (M : Pairing V) : Fin 3 → ℝ := fun i => crossCoordinate z i M

lemma crossVector_sum (M : Pairing (A ⊕ B)) (N : Pairing C) :
    crossVector threeColor (Pairing.sum M N) = ![tableCoordinate abColor (0,1) M,0,0] := by
  have h02 : tableCoordinate (abColor : A ⊕ B → Fin 3) (0,2) M = 0 := by
    apply (tableCoordinate_eq_zero_iff _ _ _).mpr
    intro v hv
    have hh := hv.2
    cases he : M.1 v <;> simp [he, abColor] at hh
  have h12 : tableCoordinate (abColor : A ⊕ B → Fin 3) (1,2) M = 0 := by
    apply (tableCoordinate_eq_zero_iff _ _ _).mpr
    intro v hv
    have hh := hv.2
    cases he : M.1 v <;> simp [he, abColor] at hh
  funext i
  fin_cases i <;>
    simp [crossVector, crossCoordinate, crossPair, threeColor,
      tableCoordinate_sum, tableCoordinate_constant, h02, h12]

lemma threeColor_closed (M : Pairing ((A ⊕ B) ⊕ C))
    (h1 : crossCoordinate threeColor 1 M = 0) (h2 : crossCoordinate threeColor 2 M = 0) :
    ∀ a : A ⊕ B, ∃ a' : A ⊕ B, M.1 (.inl a) = .inl a' := by
  have h1' := (tableCoordinate_eq_zero_iff _ _ _).mp h1
  have h2' := (tableCoordinate_eq_zero_iff _ _ _).mp h2
  intro a
  cases hm : M.1 (.inl a) with
  | inl a' => exact ⟨a',rfl⟩
  | inr c =>
    cases a with
    | inl a => exact False.elim (h1' (.inl (.inl a)) ⟨rfl, by rw [hm]; rfl⟩)
    | inr b => exact False.elim (h2' (.inl (.inr b)) ⟨rfl, by rw [hm]; rfl⟩)

noncomputable def starFiberEquiv (x : ℝ) :
    {M : Pairing (A ⊕ B) // tableCoordinate abColor (0,1) M = x} × Pairing C ≃
      {M : Pairing ((A ⊕ B) ⊕ C) // crossVector threeColor M = ![x,0,0]} :=
  Pairing.sumFiberEquiv _ _
    (fun M N => by rw [crossVector_sum]; simp)
    (fun M hM => threeColor_closed M
      (by have := congrFun hM 1; exact this)
      (by have := congrFun hM 2; exact this))

end ThreeCellGeometry

section GlobalExtension
variable {D : Type u_5} {C : Type u_6} {I : Type u_7} [DecidableEq I]

def insertCellEquiv (i : I) : C ⊕ ({j : I // j ≠ i} × C) ≃ I × C where
  toFun v := v.elim (fun c => (i,c)) (fun jc => (jc.1.1,jc.2))
  invFun v := if h : v.1 = i then .inl v.2 else .inr (⟨v.1,h⟩,v.2)
  left_inv v := by
    cases v with
    | inl c => simp
    | inr jc => simp [jc.1.2]
  right_inv v := by
    rcases v with ⟨j,c⟩
    by_cases h : j = i <;> simp_all

def localSplitEquiv (i : I) : (D ⊕ C) ⊕ ({j : I // j ≠ i} × C) ≃ D ⊕ (I × C) :=
  (Equiv.sumAssoc D C _).trans (Equiv.sumCongr (Equiv.refl D) (insertCellEquiv i))

def extendLocal (i : I) (M : Pairing (D ⊕ C)) (N : {j : I // j ≠ i} → Pairing C) :
    Pairing (D ⊕ (I × C)) :=
  Pairing.transport (localSplitEquiv i) (Pairing.sum M (Pairing.cellwise N))

def liftLocal (i : I) (p : Equiv.Perm (D ⊕ C)) : Equiv.Perm (D ⊕ (I × C)) :=
  (localSplitEquiv i).symm.trans
    ((Equiv.sumCongr p (Equiv.refl _)).trans (localSplitEquiv i))

end GlobalExtension
end MatchingSmoothing

end OAI


