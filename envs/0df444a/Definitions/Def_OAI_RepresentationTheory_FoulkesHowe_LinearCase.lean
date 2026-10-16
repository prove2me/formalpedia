-- Prove2me | Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
-- name    : OAI_RepresentationTheory_FoulkesHowe_LinearCase
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T15:15:07.695+00:00
-- url     : https://prove2.me/theorems/0176e54f-d04e-43ac-a4d6-01b595704978
-- title:
--   The Foulkes formula for $a=1$ is a single product
-- statement:
--   Let $V$ be a complex vector space and $S(V)$ its symmetric algebra over $\mathbb{C}$. For $n\in\mathbb{N}$ let $\mathrm{Sym}^n V\subseteq S(V)$ be the linear span of the products $[v_0,\dots,v_{n-1}]=v_0v_1\cdots v_{n-1}$ of $n$ vectors of $V$; applying the same construction to the vector space $\mathrm{Sym}^b V$ gives $\mathrm{Sym}^a(\mathrm{Sym}^b V)$, whose products are written $[x_0,\dots,x_{a-1}]$ with $x_i\in\mathrm{Sym}^b V$. For $a,b\in\mathbb{N}$ and an array $v=(v_{j,i})$ of vectors of $V$ with $b$ rows $j\in\{0,\dots,b-1\}$ and $a$ columns $i\in\{0,\dots,a-1\}$, the *Foulkes formula* is the element
--   $$F_{a,b}(v)=\frac{1}{(a!)^b}\sum_{(\sigma_0,\dots,\sigma_{b-1})\in S_a^{\,b}}\Bigl[\,[v_{0,\sigma_0(0)},\dots,v_{b-1,\sigma_{b-1}(0)}],\ \dots,\ [v_{0,\sigma_0(a-1)},\dots,v_{b-1,\sigma_{b-1}(a-1)}]\,\Bigr]\in\mathrm{Sym}^a(\mathrm{Sym}^b V),$$
--   where $S_a$ is the symmetric group on $\{0,\dots,a-1\}$: the $i$-th inner product collects one entry from each row, the entry of row $j$ being taken from column $\sigma_j(i)$.
--
--   The file records the case of a single column: for every $b\in\mathbb{N}$ and every array $v$ with $b$ rows and one column,
--   $$F_{1,b}(v)=\Bigl[\,[v_{0,0},v_{1,0},\dots,v_{b-1,0}]\,\Bigr]\in\mathrm{Sym}^1(\mathrm{Sym}^b V).$$
--
--   A linear map $\mu:\mathrm{Sym}^b(\mathrm{Sym}^a V)\to\mathrm{Sym}^a(\mathrm{Sym}^b V)$ satisfies the Foulkes condition when $\mu\bigl([[v_{0,0},\dots,v_{0,a-1}],\dots,[v_{b-1,0},\dots,v_{b-1,a-1}]]\bigr)=F_{a,b}(v)$ for every array $v$. For $a=1$ the identity above makes this condition explicit: $\mu$ must send $[[v_{0,0}],\dots,[v_{b-1,0}]]$ to $[[v_{0,0},\dots,v_{b-1,0}]]$.
--
--   **Formalization Note** The array is a function `v : Fin b → Fin 1 → V`, and the theorem `foulkesFormula_one` is a simp lemma rewriting `foulkesFormula 1 b V v` to the displayed one-factor product.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/LinearCase.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/LinearCase.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FoulkesHowe mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality

namespace OAI

noncomputable section
open scoped BigOperators
universe u
namespace Problem346

@[simp] theorem foulkesFormula_one (b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] (v : Fin b → Fin 1 → V) :
    foulkesFormula 1 b V v =
      symMonomial 1 (SymPow b V) (fun _ => symMonomial b V (fun j => v j 0)) := by
  classical
  simp [foulkesFormula, Fin.eq_zero]

end Problem346

end

end OAI


