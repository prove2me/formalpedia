-- Prove2me | Definitions.Def_MultiCollQ_Supplement_bucketCollRel
-- name    : MultiCollQ_Supplement_bucketCollRel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:58:49.596379+00:00
-- url     : https://prove2.me/theorems/acf8d1dd-5471-4460-895d-5024b3f8a497
-- title:
--   Bucket multi-collision relation and real success probability of a forward permutation algorithm
-- statement:
--   Let $Q_c=b^{-1}(c)$ be public buckets partitioning $[N]$ and $\pi$ a permutation of $[N]$. An output $g$ consisting of $\ell$ groups $g_1,\dots,g_\ell$ of $r$ inputs each is **correct** for $\pi$ when
--
--   1. the $r$ inputs of each group are distinct,
--   2. the images $\pi(g_i(a))$ of the inputs of group $i$ all lie in one bucket, and
--   3. images of different groups lie in different buckets,
--
--   that is, $g$ lists $r$ distinct preimages in each of $\ell$ distinct buckets.
--
--   For a forward permutation-query algorithm $A$ run with $T$ real swap queries $P_\pi|x,w\rangle=|x\rangle\otimes S_{\pi(x)}|w\rangle$, the **real success probability** for a predicate $R$ on outputs is the probability that measuring the final state $\psi_{\pi,T}$ in the computational basis and applying the output map gives an output satisfying $R$:
--
--   $$
--   p_\pi=\sum_{c:\ R(\mathrm{out}(c))}|\psi_{\pi,T}(c)|^2 .
--   $$
--
--   These objects state the upper bound of Theorem 4.8.
--
--   **Formalization Note** Outputs are maps $\mathrm{Fin}\,\ell\to\mathrm{Fin}\,r\to\mathrm{Fin}\,N$; the algorithms and their runs are those of the base mission's `MultiCollQ.FwdAlg`.
-- source:
--   Peng, Hou, Dong, Quantum multi-collision lower bounds for arbitrary bounded types, manuscript (Oct. 2026; STOC 2027 submission, sha256 e20a0870b16226a4c1b2ff8ccbc19ad9605f91268e96586242ff551b9f17fdf1), Theorem 4.8, p.44; §2.3, p.12

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_MultiCollQ_FwdAlg

namespace MultiCollQ.Supplement

open CompPermOracle

/-- The relation "`g` lists `r` distinct preimages under `π` in each of `ℓ` distinct buckets" for a
permutation `π` of `[N]` and public buckets `b : [N] → [h]` (Peng, Hou, Dong, *Quantum
multi-collision lower bounds for arbitrary bounded types*, manuscript (Oct. 2026), Theorem 4.8,
p.44: "finds `r` distinct preimages in each of `ℓ` distinct buckets").

**Formalization Note.** An output is `g : Fin ℓ → Fin r → Fin N`, the `ℓ` groups of `r` inputs. The
three conjuncts: the inputs of a group are distinct; the images under `π` of a group lie in one
bucket `Q_c = b⁻¹(c)`; images of different groups lie in different buckets. -/
def bucketCollRel {N h : ℕ} (r ℓ : ℕ) (b : Fin N → Fin h) (π : Equiv.Perm (Fin N))
    (g : Fin ℓ → Fin r → Fin N) : Prop :=
  (∀ i, Function.Injective (g i)) ∧ (∀ i a a', b (π (g i a)) = b (π (g i a'))) ∧
    ∀ i i', i ≠ i' → ∀ a a', b (π (g i a)) ≠ b (π (g i' a'))

/-- The real success probability of a forward permutation-query algorithm `A` against `π` after
`T` queries: the accessible registers of `A.realState π T` are measured in the computational basis
and the output map `out` is applied to the outcome; the value is the probability that the output
satisfies `R` (Peng, Hou, Dong, manuscript (Oct. 2026), §2.3, p.12; Theorem 4.8, p.44).

**Formalization Note.** `Σ_{c : R (out c)} |ψ(c)|²` with `ψ = A.realState π T`, a unit vector. -/
noncomputable def realSuccessProb {N : ℕ} {Wk : Type} [Fintype Wk] [DecidableEq Wk] {Y : Type}
    (A : FwdAlg N Wk) (π : Equiv.Perm (Fin N)) (T : ℕ) (out : FAcc N Wk → Y) (R : Y → Prop) : ℝ := by
  classical
  exact ∑ c ∈ Finset.univ.filter (fun c => R (out c)), ‖A.realState π T c‖ ^ 2

end MultiCollQ.Supplement


