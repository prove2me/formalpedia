-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
-- name    : OAI_NumberTheory_ShortEgyptian_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:14:53.306987+00:00
-- url     : https://prove2.me/theorems/b3242776-2c7a-40f9-ab5d-72058c895922
-- title:
--   Unit-fraction sums of lists, and the quotient and residue of the greedy step
-- statement:
--   This file fixes the elementary arithmetic objects behind Egyptian fraction expansions. A list $\mathbf n=(n_1,\dots,n_k)$ of natural numbers is a finite sequence in which order and repetitions are allowed, and all sums of reciprocals are computed in $\mathbb{Q}$.
--
--   1. **Unit-fraction sum.** For a list $\mathbf n=(n_1,\dots,n_k)$,
--
--      $$\Sigma(\mathbf n)=\sum_{i=1}^{k}\frac{1}{n_i}\in\mathbb{Q},$$
--
--      so the empty list has sum $0$. The file records the rules $\Sigma(\varnothing)=0$, $\Sigma(n,n_1,\dots,n_k)=\frac1n+\Sigma(n_1,\dots,n_k)$, and $\Sigma(\mathbf m\,\mathbf n)=\Sigma(\mathbf m)+\Sigma(\mathbf n)$ for the concatenation $\mathbf m\,\mathbf n$ of two lists.
--
--   2. **Unit-sum representation.** A list $\mathbf n$ represents a rational number $x$ if every entry satisfies $n_i\ge 2$ and $\Sigma(\mathbf n)=x$. Unlike an Egyptian fraction expansion in the strict sense, the entries need not be increasing or distinct.
--
--   3. **Greedy quotient.** For $v,u\in\mathbb{N}$,
--
--      $$z(v,u)=\Bigl\lceil \frac{v}{u}\Bigr\rceil,$$
--
--      which for $u\ge 1$ is the least natural number $z$ with $v\le uz$.
--
--   4. **Residue.** For $v,u,z\in\mathbb{N}$, $\operatorname{res}(v,u,z)=\max(uz-v,\,0)$, that is, $uz-v$ truncated at $0$.
--
--   For a fraction $u/v$ with $0<u<v$, the number $1/z$ with $z=z(v,u)$ is the largest unit fraction not exceeding $u/v$, and with $r=\operatorname{res}(v,u,z)$ one has
--
--   $$\frac{u}{v}=\frac1z+\frac{r}{vz},\qquad 0\le r<u .$$
--
--   Iterating this step is the classical greedy (Fibonacci–Sylvester) algorithm. In the surrounding development the quotient–residue pair drives both the existence of expansions and the residue-descent argument for short expansions, in which the numerator $u$ is replaced by the smaller residue $r$ (and the denominator by $vz$) at each step; unit-sum representations are the objects these arguments produce.
--
--   **Formalization Note** The Lean names are `unitSum`, `IsUnitSum`, `quotient` and `residue`, with the simp lemmas `unitSum_nil`, `unitSum_cons` and `unitSum_append`. The quotient is the natural-number ceiling `Nat.ceil` of the rational number v/u; since Lean's division by zero gives 0, the quotient with u = 0 equals 0. The residue uses truncated natural-number subtraction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/Basic.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/Basic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ShortEgyptianFractions mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ShortEgyptianFractions

namespace OAI

namespace ShortEgyptian

def unitSum (ns : List ℕ) : ℚ :=
  (ns.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum

def IsUnitSum (x : ℚ) (ns : List ℕ) : Prop :=
  (∀ n ∈ ns, 2 ≤ n) ∧ unitSum ns = x

noncomputable def quotient (v u : ℕ) : ℕ := ⌈(v : ℚ) / (u : ℚ)⌉₊

def residue (v u z : ℕ) : ℕ := u * z - v

@[simp] theorem unitSum_nil : unitSum [] = 0 := rfl

@[simp] theorem unitSum_cons (n : ℕ) (ns : List ℕ) :
    unitSum (n :: ns) = (1 : ℚ) / n + unitSum ns := rfl

@[simp] theorem unitSum_append (xs ys : List ℕ) :
    unitSum (xs ++ ys) = unitSum xs + unitSum ys := by
  simp [unitSum]

end ShortEgyptian

end OAI


