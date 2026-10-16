-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
-- name    : OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:46:04.761731+00:00
-- url     : https://prove2.me/theorems/b026a1fc-c46a-47aa-b47b-2534982ef258
-- title:
--   The lower-arity product form $T(t^{r+m}, x^r Q_1, \dots, x^r Q_r)$
-- statement:
--   Let $V$ be a complex vector space, $S(V)$ its symmetric algebra over $\mathbb{C}$, and $\mathrm{Sym}^nV\subseteq S(V)$ the $\mathbb{C}$-span of all products of $n$ vectors of $V$. For $u\in V$ write $u^n=u\cdots u\in\mathrm{Sym}^nV$ for its $n$-th power, and for $p\in\mathrm{Sym}^rV$, $Q\in\mathrm{Sym}^mV$ write $p\cdot Q\in\mathrm{Sym}^{r+m}V$ for their product in $S(V)$. A form of arity $a$ on $\mathrm{Sym}^bV$ is a $\mathbb{C}$-multilinear map $T\colon(\mathrm{Sym}^bV)^a\to\mathbb{C}$; no symmetry is required.
--
--   Given natural numbers $r,m$, a form $T$ of arity $r+1$ on $\mathrm{Sym}^{r+m}V$, and vectors $x,t\in V$, the module defines the form $T_{x,t}$ of arity $r$ on $\mathrm{Sym}^mV$ by
--   $$
--   T_{x,t}(Q_1,\dots,Q_r)=T\bigl(t^{r+m},\ x^r\cdot Q_1,\ \dots,\ x^r\cdot Q_r\bigr),\qquad Q_1,\dots,Q_r\in\mathrm{Sym}^mV.
--   $$
--   It is multilinear because each map $Q\mapsto x^r\cdot Q$ is linear; a lemma records the displayed value formula.
--
--   The construction lowers the arity from $r+1$ to $r$ and the degree from $r+m$ to $m$. It is the bridge of the stabilization induction for symmetric forms $T$ satisfying $T(Y,\dots,Y)=0$ for every product $Y$ of vectors: information about a form of arity $r+1$ on $\mathrm{Sym}^{r+m}V$ is passed to the forms $T_{x,t}$, to which the induction hypothesis on the arity applies, and vanishing of all $T_{x,t}$ is then transferred back to $T$.
--
--   **Formalization Note** The form type `SymmetricMultilinearForm (r+1) (r+m) V` is an abbreviation for all multilinear maps; symmetry is a separate predicate. `lowerProductForm r m T x t` curries $T$ in its first argument at $t^{r+m}$ and precomposes each remaining argument with the linear map `symPowMul r m` applied to $x^r$; the distinguished argument is placed first using `Fin.cons`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/VanishingInduction.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/VanishingInduction.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
universe u
namespace Problem346

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

/-- The lower-arity form used in the stabilization induction. -/
def lowerProductForm (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (x t : V) :
    SymmetricMultilinearForm r m V :=
  (T.curryLeft (symMonomial (r+m) V (fun _ => t))).compLinearMap
    (fun _ => symPowMul r m (symMonomial r V (fun _ => x)))

@[simp] theorem lowerProductForm_apply (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (x t : V)
    (Q : Fin r → SymPow m V) :
    lowerProductForm r m T x t Q =
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun i => symPowMul r m (symMonomial r V (fun _ => x)) (Q i))) := rfl

end Problem346

end

end OAI


