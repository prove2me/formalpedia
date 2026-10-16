-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints
-- name    : OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T16:13:18.381833+00:00
-- url     : https://prove2.me/theorems/9f6a240c-7c23-487b-b7ff-a731373a9170
-- title:
--   Vector assignment and endpoint monomials of the first transfer
-- statement:
--   Let $V$ be a complex vector space, $S(V)$ its symmetric algebra over $\mathbb{C}$, $\mathrm{Sym}^nV\subseteq S(V)$ the $\mathbb{C}$-span of all products of $n$ vectors, and $[u_0,\dots,u_{n-1}]\in\mathrm{Sym}^nV$ such a product; write $u^n=[u,\dots,u]$, and for $p\in\mathrm{Sym}^rV$, $q\in\mathrm{Sym}^mV$ let $p\cdot q\in\mathrm{Sym}^{r+m}V$ be their product in $S(V)$. Fix $r,m\in\mathbb{N}$, the block labels $\mathsf{x},\mathsf{t},\mathsf{y}_0,\dots,\mathsf{y}_{m-1}$, and for $k\in\mathbb{N}$ the stage-$k$ labelling $\lambda_k$ of the slots $(i,j)$, $0\le i\le r$, $0\le j<r+m$: in row $0$, $\lambda_k(0,j)=\mathsf{y}_j$ if $j<k$ and $j<m$, and $\mathsf{t}$ otherwise; in rows $i\ge 1$, $\lambda_k(i,j)=\mathsf{x}$ if $j<r$ and $\mathsf{y}_{j-r}$ otherwise.
--
--   1. **Vector assignment.** For $x,t\in V$ and $y=(y_0,\dots,y_{m-1})\in V^m$, the map $\phi=\phi_{x,t,y}$ from labels to vectors with $\phi(\mathsf{x})=x$, $\phi(\mathsf{t})=t$ and $\phi(\mathsf{y}_j)=y_j$, with one evaluation lemma for each case.
--   2. **Endpoint monomials.** Let $M_k(i)=\bigl[\phi(\lambda_k(i,0)),\dots,\phi(\lambda_k(i,r+m-1))\bigr]\in\mathrm{Sym}^{r+m}V$ be the monomial read off row $i$ at stage $k$. Then
--   $$
--   M_0(0)=t^{r+m},\qquad M_k(i)=x^r\cdot[y_0,\dots,y_{m-1}]\quad(1\le i\le r,\ k\in\mathbb{N}),\qquad M_m(0)=t^r\cdot[y_0,\dots,y_{m-1}].
--   $$
--
--   For a multilinear form $T$ on $(\mathrm{Sym}^{r+m}V)^{r+1}$ these identities evaluate the two ends of the first transfer chain: with $Y=[y_0,\dots,y_{m-1}]$, the flattening of $T$ evaluated on the grid $(\phi(\lambda_k(i,j)))_{i,j}$ equals $T(t^{r+m},x^r\cdot Y,\dots,x^r\cdot Y)$ for $k=0$ and $T(t^r\cdot Y,x^r\cdot Y,\dots,x^r\cdot Y)$ for $k=m$. This is how vanishing at stage $m$ is converted into vanishing with the common product $Y$ removed from the first argument.
--
--   **Formalization Note** The vector assignment is `firstVectors x t y`, defined by cases on `FirstBlock m`; the products $x^r\cdot Y$ and $t^r\cdot Y$ use the graded multiplication `symPowMul r m`, and the rows $i\ge 1$ appear as `i.succ` with `i : Fin r`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/TransferEndpoints.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/TransferEndpoints.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem346
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {κ : Type v} [Fintype κ]

/-- Assign vector values to the three kinds of blocks in the first transfer. -/
def firstVectors {m : ℕ} (x t : V) (y : Fin m → V) : FirstBlock m → V
  | none => x
  | some none => t
  | some (some j) => y j

omit [AddCommGroup V] [Module ℂ V] in
@[simp] theorem firstVectors_x {m : ℕ} (x t : V) (y : Fin m → V) :
    firstVectors x t y none = x := rfl
omit [AddCommGroup V] [Module ℂ V] in
@[simp] theorem firstVectors_t {m : ℕ} (x t : V) (y : Fin m → V) :
    firstVectors x t y (some none) = t := rfl
omit [AddCommGroup V] [Module ℂ V] in
@[simp] theorem firstVectors_y {m : ℕ} (x t : V) (y : Fin m → V) (j : Fin m) :
    firstVectors x t y (some (some j)) = y j := rfl

@[simp] theorem firstLabel_initial_monomial (r m : ℕ) (x t : V) (y : Fin m → V) :
    symMonomial (r+m) V (fun j => firstVectors x t y (firstLabel r m 0 (0,j))) =
      symMonomial (r+m) V (fun _ => t) := by
  simp

@[simp] theorem firstLabel_other_monomial (r m k : ℕ) (x t : V)
    (y : Fin m → V) (i : Fin r) :
    symMonomial (r+m) V (fun j => firstVectors x t y (firstLabel r m k (i.succ,j))) =
      symPowMul r m (symMonomial r V (fun _ => x)) (symMonomial m V y) := by
  rw [symPowMul_symMonomial]
  congr 1
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro j
    simp [Fin.append]
  · intro j
    simp [Fin.append]

@[simp] theorem firstLabel_final_monomial (r m : ℕ) (x t : V) (y : Fin m → V) :
    symMonomial (r+m) V (fun j => firstVectors x t y (firstLabel r m m (0,j))) =
      symPowMul r m (symMonomial r V (fun _ => t)) (symMonomial m V y) := by
  apply Subtype.ext
  change (∏ j : Fin (r+m), SymmetricAlgebra.ι ℂ V
      (firstVectors x t y (firstLabel r m m (0,j)))) =
    (∏ _ : Fin r, SymmetricAlgebra.ι ℂ V t) * ∏ j : Fin m, SymmetricAlgebra.ι ℂ V (y j)
  rw [← (finCongr (Nat.add_comm m r)).prod_comp
    (fun j : Fin (r+m) => SymmetricAlgebra.ι ℂ V
      (firstVectors x t y (firstLabel r m m (0,j))))]
  rw [Fin.prod_univ_add]
  have hleft : (∏ j : Fin m, SymmetricAlgebra.ι ℂ V
      (firstVectors x t y (firstLabel r m m
        (0, (finCongr (Nat.add_comm m r)) (Fin.castAdd r j))))) =
      ∏ j : Fin m, SymmetricAlgebra.ι ℂ V (y j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp [firstLabel]
  have hright : (∏ j : Fin r, SymmetricAlgebra.ι ℂ V
      (firstVectors x t y (firstLabel r m m
        (0, (finCongr (Nat.add_comm m r)) (Fin.natAdd m j))))) =
      ∏ _ : Fin r, SymmetricAlgebra.ι ℂ V t := by
    apply Finset.prod_congr rfl
    intro j _
    simp [firstLabel]
  rw [hleft, hright, mul_comm]

end Problem346

end

end OAI


