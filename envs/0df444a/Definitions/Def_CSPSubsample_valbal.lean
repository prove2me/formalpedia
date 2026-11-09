-- Prove2me | Definitions.Def_CSPSubsample_valbal
-- name    : CSPSubsample_valbal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:22:14.00852+00:00
-- url     : https://prove2.me/theorems/dde357ac-b583-4e7a-9c03-0e6a99146f19
-- title:
--   Blocks, balanced constraints $M(U)$, $M_i(U)$, the balanced value $\mathrm{val}^{\mathrm{bal}}_U$, $\mathrm{OPT}^{\mathrm{bal}}$, and $H_{i,U}(a,\psi)$
-- statement:
--   Partition the variables $[n]$ into $T$ disjoint blocks $V_1,\dots,V_T$, and let $b(i)\in[T]$ be the block of variable $i$. For $U\subseteq[n]$ let $U_t=U\cap V_t$ and $U_{-t}=U\setminus U_t$. A tuple is **balanced** if its variables lie in distinct blocks:
--   $$
--   M=\{(i_1,\dots,i_k)\in W: b(i_j)\neq b(i_{j'})\ \forall j\neq j'\in[k]\},\quad M(U)=M\cap U^k,\quad M_i(U)=\{w\in M(U): i\in w\}.
--   $$
--   The **balanced value** and **balanced optimum** on $U$, the maximum over a family $\Phi\subseteq[q]^n$, and the **contribution of variable $i$** are
--   $$
--   \mathrm{val}^{\mathrm{bal}}_U(\phi)=\frac1{|U|^k}\sum_{w\in M(U)}P_w(\phi|_w),\qquad \mathrm{OPT}^{\mathrm{bal}}(U)=\max_{\phi\in[q]^U}\mathrm{val}^{\mathrm{bal}}_U(\phi),\qquad \mathrm{OPT}^{\mathrm{bal}}_\Phi(U)=\max_{\phi\in\Phi}\mathrm{val}^{\mathrm{bal}}_U(\phi),
--   $$
--   $$
--   H_{i,U}(a,\psi)=\sum_{w\in M_i(\{i\}\cup U)}P_w\big((i\to a)\otimes\psi|_{w\setminus\{i\}}\big),
--   $$
--   where $(i\to a)\otimes\psi$ assigns $a$ to $i$ and follows $\psi$ elsewhere.
--
--   Dropping the unbalanced constraints makes the value separable over the variables of one block, which is what the extender of §5.2 exploits.
--
--   **Formalization Note** The block map $b:[n]\to[T]$ is an arbitrary function (the paper's blocks have size "approximately $n/T$"); $V_t=\{i:b(i)=t\}$. Blocks are `Fin T` (paper block $t$ is Lean index $t-1$). Assignments are total; each quantity reads only the variables of its set. The normalizer is the power $|U|^k$.
-- source:
--   Bernasconi, Castiglioni, Celli, Farina, Malavolta, A Subsampling Theorem for Constraint Satisfaction Problems with Large Arity, arXiv:2608.00203 (PDF sha256 fd9ae01113266fee273c46c14c8a1a39f36a958dba3fc276cd74bf4c3daff445), §5.1, pp.12–13 (PDF pp.14–15); OPT^bal_Φ, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_CSPSubsample_Instance
import Definitions.Def_CSPSubsample_valOn

set_option autoImplicit false

namespace CSPSubsample

/-- `U_t = U ∩ V_t`, the variables of `U` in block `t`, where the blocks `V_t = {i : b(i) = t}`
are given by a block map `b : [n] → [T]` (arXiv:2608.00203 (PDF sha256 fd9ae011…), §5.1,
pp.12–13 = PDF pp.14–15).

**Formalization Note** The block map `b` is arbitrary (the paper's blocks have size
"approximately n/T"; every statement using `b` is stated for every partition). Blocks are
`Fin T`, paper block `t` is Lean index `t − 1`. `V_t` itself is `blockPart b univ t`. -/
def blockPart {n T : ℕ} (b : Fin n → Fin T) (U : Finset (Fin n)) (t : Fin T) : Finset (Fin n) :=
  U.filter fun i => b i = t

/-- `U_{−t} = U ∖ U_t`, the variables of `U` in all blocks other than `t` (arXiv:2608.00203
(PDF sha256 fd9ae011…), p.13 = PDF p.15). -/
def blockCompl {n T : ℕ} (b : Fin n → Fin T) (U : Finset (Fin n)) (t : Fin T) :
    Finset (Fin n) :=
  U.filter fun i => b i ≠ t

/-- `M(U) = M ∩ U^k`, the **balanced** constraints supported on `U`, where
`M = {(i_1, …, i_k) ∈ W : b(i_j) ≠ b(i_{j'}) ∀ j ≠ j'}` (arXiv:2608.00203 (PDF sha256 fd9ae011…),
§5.1, p.12 = PDF p.14). Balanced means `b ∘ w` injective. -/
noncomputable def balancedOn {n k T : ℕ} (b : Fin n → Fin T) (U : Finset (Fin n)) : Finset (Fin k ↪ Fin n) :=
  Finset.univ.filter fun w => Function.Injective (b ∘ w) ∧ ∀ j, w j ∈ U

/-- `M_i(U) = {w ∈ M(U) : i ∈ w}`, the balanced constraints in `U` whose scope contains `i`
(arXiv:2608.00203 (PDF sha256 fd9ae011…), p.12 = PDF p.14). -/
noncomputable def balancedThrough {n k T : ℕ} (b : Fin n → Fin T) (U : Finset (Fin n)) (i : Fin n) :
    Finset (Fin k ↪ Fin n) :=
  (balancedOn b U).filter fun w => ∃ j, w j = i

/-- `∑_{w ∈ M(U)} P_w(ϕ|_w)`, the unnormalized balanced value on `U`. -/
noncomputable def sumBal {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T)
    (U : Finset (Fin n)) (ϕ : Fin n → Fin q) : ℝ :=
  ∑ w ∈ balancedOn b U, I.P w (ϕ ∘ w)

/-- The **balanced CSP value** `val^bal_U(ϕ) = (1/|U|^k) ∑_{w ∈ M(U)} P_w(ϕ|_w)`
(arXiv:2608.00203 (PDF sha256 fd9ae011…), p.13 = PDF p.15).

**Formalization Note** `ϕ` is a total assignment; only its values on `U` are read (the paper's
`ϕ ∈ [q]^U`). The normalizer is the power `|U|^k`. -/
noncomputable def valbal {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T)
    (U : Finset (Fin n)) (ϕ : Fin n → Fin q) : ℝ :=
  sumBal I b U ϕ / (U.card : ℝ) ^ k

/-- `OPT^bal(U) = max_{ϕ ∈ [q]^U} val^bal_U(ϕ)` (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.13 =
PDF p.15).

**Formalization Note** `⨆` over the finite type of total assignments (attained when nonempty). -/
noncomputable def OPTbal {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T)
    (U : Finset (Fin n)) : ℝ :=
  ⨆ ϕ : Fin n → Fin q, valbal I b U ϕ

/-- `OPT^bal_Φ(U) = max_{ϕ ∈ Φ} val^bal_U(ϕ)` for a family `Φ ⊆ [q]^n` (arXiv:2608.00203 (PDF
sha256 fd9ae011…), p.18 = PDF p.20). See `maxOver` for the empty family. -/
noncomputable def OPTbalPhi {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T)
    (Φ : Finset (Fin n → Fin q)) (U : Finset (Fin n)) : ℝ :=
  maxOver Φ (valbal I b U)

/-- `H_{i,U}(a, ψ) = ∑_{w ∈ M_i({i} ∪ U)} P_w((i → a) ⊗ ψ|_{w∖{i}})`, the total contribution of
the balanced constraints containing `i` and otherwise supported on `U`, when `i` is assigned `a`
and the other variables follow `ψ` (arXiv:2608.00203 (PDF sha256 fd9ae011…), p.13 = PDF p.15).

**Formalization Note** `(i → a) ⊗ ψ` is `Function.update ψ i a` with `ψ` total; only the values
of `ψ` on `U` are read. -/
noncomputable def Hval {n k q T : ℕ} (I : Instance n k q) (b : Fin n → Fin T) (i : Fin n)
    (U : Finset (Fin n)) (a : Fin q) (ψ : Fin n → Fin q) : ℝ :=
  ∑ w ∈ balancedThrough b (insert i U) i, I.P w (Function.update ψ i a ∘ w)

end CSPSubsample


