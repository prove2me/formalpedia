-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
-- name    : OAI_Analysis_DirectCrouzeix_Resolvent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:23:47.115513+00:00
-- url     : https://prove2.me/theorems/b93743c4-df60-4771-be29-a9e4738c9d27
-- title:
--   The quadratic form $u\mapsto\langle u,Au\rangle$ of a complex square matrix
-- statement:
--   Let $n\in\mathbb{N}$, let $A$ be a complex $n\times n$ matrix acting on $\mathbb{C}^{n}$ by matrix–vector multiplication, and equip $\mathbb{C}^{n}$ with its standard inner product $\langle u,v\rangle=\sum_{i=1}^{n}\overline{u_i}\,v_i$, which is conjugate-linear in the first argument and linear in the second. For a vector $u\in\mathbb{C}^{n}$ of arbitrary length the module defines the value of the quadratic form of $A$ at $u$:
--
--   $$
--   q_A(u)=\langle u,Au\rangle=\sum_{i=1}^{n}\sum_{j=1}^{n}\overline{u_i}\,A_{ij}\,u_j=u^{*}Au\in\mathbb{C}.
--   $$
--
--   The numerical range of $A$ is precisely the set of values of this form on unit vectors, $W(A)=\{q_A(u):u\in\mathbb{C}^{n},\ \|u\|=1\}$. The form is linear in $A$, satisfies $q_{A^{*}}(u)=\overline{q_A(u)}$ and $q_A(\lambda u)=|\lambda|^{2}q_A(u)$ for $\lambda\in\mathbb{C}$, and $q_{I}(u)=\|u\|^{2}$. These rules are what one uses to show that a Hermitian matrix whose quadratic form has nonnegative real part on all unit vectors is positive semidefinite, and from there the resolvent positivity statement of this development: if $z\notin W(A)$ and $\eta\in\mathbb{C}$ satisfies $\operatorname{Re}\big(\overline{\eta}\,(z-w)\big)\ge0$ for every $w\in W(A)$, then $\eta(zI-A)^{-1}+\big(\eta(zI-A)^{-1}\big)^{*}$ is positive semidefinite.
--
--   **Formalization Note** `quadratic A u` is `inner ℂ u (Matrix.toEuclideanCLM A u)` for `A : Matrix (Fin n) (Fin n) ℂ` and `u : EuclideanSpace ℂ (Fin n)`; Mathlib's inner product is conjugate-linear in its first argument, matching the convention above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/Resolvent.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/Resolvent.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

def quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) : ℂ :=
  inner ℂ u (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A u)

end DirectCrouzeix

end

end OAI


