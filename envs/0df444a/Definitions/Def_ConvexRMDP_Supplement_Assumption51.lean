-- Prove2me | Definitions.Def_ConvexRMDP_Supplement_Assumption51
-- name    : ConvexRMDP_Supplement_Assumption51
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:52:04.825703+00:00
-- url     : https://prove2.me/theorems/48c90dc6-11e2-516c-ba7a-e294db578a26
-- title:
--   Assumption 5.1: $\mathcal U_{sa}=\{p\in\Delta(S)\mid g_{sa,i}(p)\le0\}$ with Slater (corrected: Slater point feasible, in relint dom)
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP, $m \in \mathbb N$, and for each $(s,a)$ let $g_{sa,1}, \dots, g_{sa,m} : \mathbb R^{\mathcal S} \to \mathbb R \cup \{+\infty\}$. **Assumption 5.1** holds when
--
--   1. every $g_{sa,i}$ is proper, closed and convex;
--   2. $\mathcal U_{sa} = \{p \in \Delta(\mathcal S) : g_{sa,i}(p) \le 0 \text{ for all } i\}$ for every $(s,a)$;
--   3. (**Slater's condition**) for every $(s,a)$ there is a point $p$ in the relative interior of $\Delta(\mathcal S)$ which lies in the relative interior of $\operatorname{dom}(g_{sa,i})$ for every $i$, satisfies $g_{sa,i}(p) \le 0$ for every affine $g_{sa,i}$, and satisfies $g_{sa,i}(p) < 0$ for every $g_{sa,i}$ that is not affine.
--
--   Under this assumption the inner minimization over $\mathcal U_{sa}$ in the convex program (4.7) can be replaced by its conic dual (Proposition 5.1, Theorem 5.1).
--
--   **Correction.** The paper's Slater condition requires only a point $p \in \operatorname{relint}\Delta(\mathcal S)$ with $g_{sa,i}(p) < 0$ for the non-affine $g_{sa,i}$; the point need not satisfy the affine constraints nor lie in $\operatorname{relint}\operatorname{dom}(g_{sa,i})$. Then the dual maximum of Proposition 5.1 can fail to be attained. For $\mathcal S=\{1,2,3\}$, put $u=p_1-p_2$, $v=p_3-1/3$, $g_1(p)=u^2-v$ and $g_2(p)=v$. The feasible set in the simplex is the singleton $(1/3,1/3,1/3)$, while $(1/4,1/4,1/2)$ satisfies the printed strict condition for the non-affine $g_1$ but violates the affine constraint. For $x_1>1$, $x_2=x_3=1$, an attained dual optimum would give KKT multipliers at the singleton; this is impossible because the objective has a nonzero derivative in the $u$ direction while both active constraint gradients have zero $u$ component. The proof cites Boyd–Vandenberghe §5.2.3, whose refined Slater condition is the one stated in item 3.
--
--   **Formalization Note** sa-rectangularity is built into the published structure `ConvexRMDP.RMDP`. The relative interior is Mathlib's `intrinsicInterior`; "affine" means $g = \varphi$ for an affine map $\varphi : \mathbb R^{\mathcal S} \to \mathbb R$. The number $m$ and the functions $g$ are parameters of each theorem.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, §5, Assumption 5.1, p.15; Slater condition corrected after Boyd & Vandenberghe (2004) §5.2.3, cited in the proof on p.16

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP
import Definitions.Def_AubinLipschitz_effDom
import Definitions.Def_TensorAHPE_IsProperClosedConvex

namespace ConvexRMDP

namespace Supplement

variable {S A : Type*} [Fintype S] [Fintype A]

/-- **Assumption 5.1, with Slater's condition corrected** (Grand-Clément & Petrik,
arXiv:2209.10187v2, p.15). The sa-rectangular uncertainty set is described by `m` constraints: for every
`(s,a)` there are proper closed convex `g_{sa,1}, …, g_{sa,m} : ℝ^S → ℝ ∪ {+∞}` with
`𝒰_{sa} = {p ∈ Δ(S) | g_{sa,i}(p) ≤ 0, ∀ i}`, and Slater's condition holds: there is `p` in the relative
interior of `Δ(S)` with `g_{sa,i}(p) < 0` for every `i` such that `g_{sa,i}` is not affine.

**Correction.** As printed, the Slater point need not satisfy the affine constraints nor lie in the
relative interior of `dom(g_{sa,i})`; the dual maximum in Proposition 5.1 can then fail to be attained.
The paper's proof cites Boyd–Vandenberghe §5.2.3, whose refined Slater condition is used here: the
point `p` (in `relint Δ(S)`, as printed) also lies in `relint dom(g_{sa,i})` for every `i` and satisfies
the affine constraints `g_{sa,i}(p) ≤ 0`.

**Formalization Note.** sa-rectangularity is built into `RMDP` (sets indexed by `(s,a)`). `relint` is
Mathlib's `intrinsicInterior`. "Affine" means `g = ↑φ` for an affine map `φ : ℝ^S → ℝ`. The number `m`
and the functions `g` are parameters; the paper's "there exists `m`, `g`" is recovered by quantifying
over them in each theorem. -/
def Assumption51 (M : RMDP S A) (m : ℕ) (g : S → A → Fin m → (S → ℝ) → EReal) : Prop :=
  (∀ s a i, TensorAHPE.IsProperClosedConvex (g s a i)) ∧
    (∀ s a, M.U s a = {p | p ∈ stdSimplex ℝ S ∧ ∀ i, g s a i p ≤ 0}) ∧
    (∀ s a, ∃ p ∈ intrinsicInterior ℝ (stdSimplex ℝ S),
      (∀ i, p ∈ intrinsicInterior ℝ (AubinLipschitz.effDom (g s a i))) ∧
      ∀ i, ((∃ φ : (S → ℝ) →ᵃ[ℝ] ℝ, ∀ q, g s a i q = ((φ q : ℝ) : EReal)) → g s a i p ≤ 0) ∧
        ((¬ ∃ φ : (S → ℝ) →ᵃ[ℝ] ℝ, ∀ q, g s a i q = ((φ q : ℝ) : EReal)) → g s a i p < 0))

end Supplement

end ConvexRMDP


