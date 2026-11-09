-- Prove2me | Definitions.Def_CSPSubsample_extender
-- name    : CSPSubsample_extender
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:27:56.021201+00:00
-- url     : https://prove2.me/theorems/fefdfc62-652c-4b80-b83a-b9078a0800d5
-- title:
--   Tie-breaking rule, deterministic extender $D_{\mathcal S}$, the family $\Psi(\mathcal S)$, and the best-response sequence $\phi^{(t)}$
-- statement:
--   Let $\mathcal S=(S_t)_{t\in[T]}$ with $S_t\subseteq V\setminus V_t$. A **seed** is $\bar\sigma=(\sigma_t)_{t\in[T]}\in\times_{t}[q]^{S_t}$. The **deterministic extender** assigns to every variable $i$ with block $t=b(i)$
--   $$
--   D_{\mathcal S}(\bar\sigma)_i\in\arg\max_{a\in[q]}\mathrm{val}^{\mathrm{bal}}_{\{i\}\cup S_t}\big((i\to a)\otimes\sigma_t\big),\tag{6}
--   $$
--   ties being broken by a fixed rule, and $\Psi(\mathcal S)=\{D_{\mathcal S}(\bar\sigma):\bar\sigma\text{ a seed}\}$.
--
--   For $U\subseteq[n]$ and a starting assignment $\phi^{(0)}$ (in the paper, an optimal balanced assignment on $U$), the **best-response sequence** $\phi^{(1)},\dots,\phi^{(T)}$ is
--   $$
--   \phi^{(t)}_i=\begin{cases}\phi^{(t-1)}_i & i\in U_{-t},\\ \in\arg\max_{a\in[q]}\mathrm{val}^{\mathrm{bal}}_{\{i\}\cup S_t}\big((i\to a)\otimes\phi^{(t-1)}|_{S_t}\big) & i\in U_t,\end{cases}\tag{7}
--   $$
--   with ties broken by the same rule as in (6), and the seed $\tilde\sigma=(\phi^{(t-1)}|_{S_t})_{t\in[T]}$.
--
--   $\Psi(\mathcal S)$ has at most $q^{\sum_t|S_t|}$ members and is the small family of the structure lemma.
--
--   **Formalization Note** The tie-breaking rule is any function choosing a maximizer of each objective; it may depend on the variable. A seed is a map $[T]\to[q]^n$ of which only $\sigma_t$ on $S_t$ is read. In Lean, step $t+1$ of the sequence updates the variables of $U$ in block index $t$ (paper block $t+1$), and variables outside $U$ keep their initial value.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), §5.2–5.3, eqs. (6) and (7), pp.13–14 (PDF pp.15–16); Claim 5.2, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_CSPSubsample_Instance
import Definitions.Def_CSPSubsample_valbal

set_option autoImplicit false

namespace CSPSubsample

/-- A **tie-breaking rule**: for each variable `i` and each objective `g : [q] → ℝ`, `tb i g` is a
maximizer of `g` (the "arbitrary but deterministic" choice in `arg max` of eqs. (6) and (7) of
arXiv:2608.00203 (PDF sha256 fd9ae011…), p.14 = PDF p.16).

**Formalization Note** The rule may depend on the variable `i` and on the objective; the same
rule is used in (6) (`extender`) and in (7) (`phiSeq`), which is the paper's "ties are broken
consistently with Equation (6)". -/
def IsArgmaxRule {n q : ℕ} (tb : Fin n → (Fin q → ℝ) → Fin q) : Prop :=
  ∀ (i : Fin n) (g : Fin q → ℝ) (a : Fin q), g a ≤ g (tb i g)

/-- The best response of variable `i` (block `t = b(i)`) to the assignment `ψ` on the seed set
`S_t`: `tb`'s choice in `arg max_{a ∈ [q]} val^bal_{{i} ∪ S_t}((i → a) ⊗ ψ|_{S_t})`
(arXiv:2608.00203 (PDF sha256 fd9ae011…), eqs. (6) and (7), p.14 = PDF p.16). -/
noncomputable def bestResp {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T)
    (S : Fin T → Finset (Fin n)) (tb : Fin n → (Fin q → ℝ) → Fin q) (i : Fin n)
    (ψ : Fin n → Fin q) : Fin q :=
  tb i fun a => valbal I b (insert i (S (b i))) (Function.update ψ i a)

/-- The **deterministic extender** `D_S(σ̄)`: for a seed `σ̄ = (σ_t)_{t ∈ [T]}`, each variable `i`
with block `t = b(i)` gets `D_S(σ̄)_i ∈ arg max_{a ∈ [q]} val^bal_{{i} ∪ S_t}((i → a) ⊗ σ_t)`
(arXiv:2608.00203 (PDF sha256 fd9ae011…), eq. (6), p.14 = PDF p.16).

**Formalization Note** A seed is `σ : Fin T → Fin n → Fin q`; only `σ t` on `S t` is read, so
seeds are the paper's `⨉_t [q]^{S_t}` up to the unread coordinates. -/
noncomputable def extender {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T)
    (S : Fin T → Finset (Fin n)) (tb : Fin n → (Fin q → ℝ) → Fin q)
    (σ : Fin T → Fin n → Fin q) : Fin n → Fin q :=
  fun i => bestResp I b S tb i (σ (b i))

/-- `Ψ(S) = {D_S(σ̄) : σ̄ a seed}`, one assignment for each seed (arXiv:2608.00203 (PDF sha256
fd9ae011…), §5.2, pp.13–14 = PDF pp.15–16). -/
noncomputable def Psi {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T)
    (S : Fin T → Finset (Fin n)) (tb : Fin n → (Fin q → ℝ) → Fin q) :
    Finset (Fin n → Fin q) :=
  Finset.univ.image (extender I b S tb)

/-- The best-response sequence `ϕ^{(0)}, ϕ^{(1)}, …, ϕ^{(T)}` of eq. (7) (arXiv:2608.00203 (PDF
sha256 fd9ae011…), p.14 = PDF p.16): `ϕ^{(0)} = ϕ0` and `ϕ^{(t)}` updates the variables of
`U_t` to the best response to `ϕ^{(t−1)}|_{S_t}`, keeping every other variable.

**Formalization Note** `phiSeq … ϕ0 t` is `ϕ^{(t)}`; step `t + 1` updates the variables `i ∈ U`
with `b i = t` (Lean block index `t` = paper block `t + 1`). Assignments are total; variables
outside `U` keep their value of `ϕ0`. The paper starts at a maximizer `ϕ*` of `val^bal_U`; that
hypothesis is placed on the statements that use it. -/
noncomputable def phiSeq {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T)
    (U : Finset (Fin n)) (S : Fin T → Finset (Fin n)) (tb : Fin n → (Fin q → ℝ) → Fin q)
    (ϕ0 : Fin n → Fin q) : ℕ → Fin n → Fin q
  | 0 => ϕ0
  | t + 1 => fun i =>
      if i ∈ U ∧ (b i).val = t then bestResp I b S tb i (phiSeq I b U S tb ϕ0 t)
      else phiSeq I b U S tb ϕ0 t i

/-- The seed `σ̃ = (ϕ^{(t−1)}|_{S_t})_{t ∈ [T]}` of Claim 5.2 (arXiv:2608.00203 (PDF sha256
fd9ae011…), p.14 = PDF p.16): Lean block `t` (paper block `t + 1`) gets `ϕ^{(t)}`. -/
noncomputable def seedOf {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T)
    (U : Finset (Fin n)) (S : Fin T → Finset (Fin n)) (tb : Fin n → (Fin q → ℝ) → Fin q)
    (ϕ0 : Fin n → Fin q) : Fin T → Fin n → Fin q :=
  fun t => phiSeq I b U S tb ϕ0 t.val

end CSPSubsample


