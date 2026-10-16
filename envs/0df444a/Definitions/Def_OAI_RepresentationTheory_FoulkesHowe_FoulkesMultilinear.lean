-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
-- name    : OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:37:55.061985+00:00
-- url     : https://prove2.me/theorems/5367ddb5-4360-432f-adb5-008e3ae3e436
-- title:
--   The Foulkes–Howe averaging formula as a multilinear map in its grid entries
-- statement:
--   Let $V$ be a complex vector space and $S(V)$ its symmetric algebra over $\mathbb{C}$. For $n\in\mathbb{N}$, $\mathrm{Sym}^nV$ denotes the $\mathbb{C}$-linear span inside $S(V)$ of all products $u_0u_1\cdots u_{n-1}$ of $n$ vectors of $V$, and for $u_0,\dots,u_{n-1}\in V$ we write $[u_0,\dots,u_{n-1}]\in\mathrm{Sym}^nV$ for this product. Applying the same construction to the vector space $\mathrm{Sym}^bV$ gives $\mathrm{Sym}^a(\mathrm{Sym}^bV)$. A grid is a family $v=(v_{j,i})$ of vectors of $V$ indexed by rows $0\le j<b$ and columns $0\le i<a$, and $S_a$ is the symmetric group on the column positions $\{0,\dots,a-1\}$.
--
--   The module defines the following objects.
--
--   1. **Monomial map.** For every $n$, the multilinear map $V^n\to\mathrm{Sym}^nV$, $(u_0,\dots,u_{n-1})\mapsto[u_0,\dots,u_{n-1}]$.
--   2. **Grid reindexing.** For a $b$-tuple $\sigma=(\sigma_0,\dots,\sigma_{b-1})$ of permutations in $S_a$, the bijection from the pairs $(i,j)$ with $i<a$, $j<b$ to the pairs $(j,i')$ with $j<b$, $i'<a$ given by $(i,j)\mapsto(j,\sigma_j(i))$, with inverse $(j,i')\mapsto(\sigma_j^{-1}(i'),j)$.
--   3. **One summand.** For such a $\sigma$, the map sending a grid $v$ to
--   $$
--   \Phi_\sigma(v)=\bigl[\,w^\sigma_0,\dots,w^\sigma_{a-1}\,\bigr]\in\mathrm{Sym}^a(\mathrm{Sym}^bV),\qquad w^\sigma_i=\bigl[v_{0,\sigma_0(i)},v_{1,\sigma_1(i)},\dots,v_{b-1,\sigma_{b-1}(i)}\bigr]\in\mathrm{Sym}^bV,
--   $$
--   so the $i$-th inner monomial collects, from every row $j$, the entry in column $\sigma_j(i)$. It is regarded as a multilinear map in the $ab$ entries of the grid, one vector argument per entry.
--   4. **The averaged map.** The multilinear map in the $ab$ grid entries
--   $$
--   \Phi(v)=\frac{1}{(a!)^{b}}\sum_{(\sigma_0,\dots,\sigma_{b-1})\in S_a^{\,b}}\Phi_\sigma(v).
--   $$
--   The accompanying identity states that $\Phi(v)$ is exactly the Foulkes–Howe formula $F(v)$, which is defined by the same averaged expression with the grid written as a function of the row and the column. That formula is the value that the canonical map $\mathrm{Sym}^b(\mathrm{Sym}^aV)\to\mathrm{Sym}^a(\mathrm{Sym}^bV)$ is required to take on the monomial $\bigl[[v_{0,0},\dots,v_{0,a-1}],\dots,[v_{b-1,0},\dots,v_{b-1,a-1}]\bigr]$ whose inner factors are the rows of $v$.
--
--   Packaging $F$ as a multilinear map makes its linearity in each individual vector entry directly available. Restricting it to the entries of a single row then shows that the formula depends linearly on that row, which is the input needed to construct the canonical Foulkes–Howe map.
--
--   **Formalization Note** The grid is a function on `Fin b × Fin a`. The summands `foulkesSummandMultilinear` are obtained from the bundled monomial map `monomialMultilinearAux` by composing outer and inner monomial maps and reindexing along `foulkesIndexEquiv`; `foulkesMultilinear_apply` identifies `foulkesMultilinear a b V` with `foulkesFormula a b V` after currying the grid. The prefactor is the complex inverse of $(a!)^b$, which is nonzero.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/FoulkesMultilinear.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/FoulkesMultilinear.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped BigOperators
universe u

namespace Problem346

 def monomialMultilinearAux (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :
    MultilinearMap ℂ (fun _ : Fin n => V) (SymPow n V) :=
  ((MultilinearMap.mkPiAlgebra ℂ (Fin n) (SymmetricAlgebra ℂ V)).compLinearMap
    (fun _ => SymmetricAlgebra.ι ℂ V)).codRestrict (symPowSubmodule n V)
      (fun v => Submodule.subset_span (Set.mem_range_self v))

/-- Reindex the slots in a transposed grid, allowing an independent permutation
in each original row. -/
def foulkesIndexEquiv (a b : ℕ) (σ : Fin b → Equiv.Perm (Fin a)) :
    (Σ _ : Fin a, Fin b) ≃ (Fin b × Fin a) where
  toFun p := (p.2, σ p.2 p.1)
  invFun p := ⟨(σ p.1).symm p.2, p.1⟩
  left_inv p := by cases p; simp
  right_inv p := by cases p; simp

/-- A summand of the Foulkes--Howe formula, viewed as a multilinear map in
all entries of the input grid. -/
def foulkesSummandMultilinear (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (σ : Fin b → Equiv.Perm (Fin a)) :
    MultilinearMap ℂ (fun _ : Fin b × Fin a => V) (SymPow a (SymPow b V)) :=
  ((monomialMultilinearAux a (SymPow b V)).compMultilinearMap
      (fun _ => monomialMultilinearAux b V)).domDomCongr (foulkesIndexEquiv a b σ)

@[simp] theorem foulkesSummandMultilinear_apply (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (σ : Fin b → Equiv.Perm (Fin a))
    (v : Fin b × Fin a → V) :
    foulkesSummandMultilinear a b V σ v =
      symMonomial a (SymPow b V)
        (fun i => symMonomial b V (fun j => v (j, σ j i))) := rfl

/-- The canonical Foulkes--Howe expression is multilinear in its `a * b`
individual vector arguments. -/
def foulkesMultilinear (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :
    MultilinearMap ℂ (fun _ : Fin b × Fin a => V) (SymPow a (SymPow b V)) := by
  classical
  exact ((a.factorial : ℂ) ^ b)⁻¹ •
    ∑ σ : Fin b → Equiv.Perm (Fin a), foulkesSummandMultilinear a b V σ

@[simp] theorem foulkesMultilinear_apply (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin b × Fin a → V) :
    foulkesMultilinear a b V v = foulkesFormula a b V (fun j i => v (j, i)) := by
  classical
  simp [foulkesMultilinear, foulkesFormula]

end Problem346

end

end OAI


