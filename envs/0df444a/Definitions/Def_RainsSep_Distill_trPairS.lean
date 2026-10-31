-- Prove2me | Definitions.Def_RainsSep_Distill_trPairS
-- name    : RainsSep_Distill_trPairS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:32.836993+00:00
-- url     : https://prove2.me/theorems/8ea661fe-a5fd-4bac-9d18-5096d647a454
-- title:
--   $\mathrm{Tr}(\mathrm{Tr}_S X\cdot\mathrm{Tr}_S Y)$ over qubits of $V$ and $W$
-- statement:
--   Let $V$ be an $n$-qubit register, $W=\mathbb C^K$, and $X,Y$ operators on $V\otimes W$. Let $S$ be a set of subsystems: qubits of $V$, and possibly $W$ itself (the paper's index $0$). Write $\mathrm{Tr}_S$ for the partial trace over the subsystems in $S$. This definition is the number
--
--   $$
--   \mathrm{Tr}\big(\mathrm{Tr}_S(X)\,\mathrm{Tr}_S(Y)\big)=\sum X_{(r,s),(r',s)}\,Y_{(r',t),(r,t)},
--   $$
--
--   the sum over basis labels $r,r'$ of the subsystems outside $S$ and $s,t$ of the subsystems in $S$.
--
--   **Formalization Note** The sum is written over all index quadruples $x,x',y,y'$ with $x,x'$ agreeing on $S$, $y,y'$ agreeing on $S$, and $x,y'$ and $x',y$ agreeing off $S$; this is the same sum. $W$ is encoded by the label `none`, qubit $k$ by `some k`.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Eq. (23), p. 2 (definition of Tr_S)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace RainsSep.Distill

open Classical in
/-- **`Tr(Tr_S X · Tr_S Y)`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Eq. (23), p. 2: "where Tr_S(ρ) is the partial trace of ρ with respects to the qubits of V
indexed by S, as well as W if 0 ∈ S."

For operators `X, Y` on `V ⊗ W` (`V` an `n`-qubit register, `W = ℂ^K`) and a set `S` of
subsystems (`some k` = qubit `k` of `V`, `none` = `W`, the paper's index `0`), this is
`Tr(Tr_S X · Tr_S Y)`, written out as the sum of `X_{x x'} Y_{y y'}` over the index tuples with
`x, x'` agreeing on `S`, `y, y'` agreeing on `S`, `x, y'` agreeing off `S`, and `x', y`
agreeing off `S`.

**Formalization Note.** Writing `x = (r, s)`, `x' = (r', s)`, `y = (r', t)`, `y' = (r, t)` with
`r, r'` on the complement of `S` and `s, t` on `S`, the sum is
`Σ X_{(r,s),(r',s)} Y_{(r',t),(r,t)} = Tr(Tr_S X · Tr_S Y)`. -/
noncomputable def trPairS {n K : ℕ} (S : Finset (Option (Fin n)))
    (X Y : Matrix (QAlgorithms.Qubits n × Fin K) (QAlgorithms.Qubits n × Fin K) ℂ) : ℂ :=
  let agree : Finset (Option (Fin n)) → QAlgorithms.Qubits n × Fin K →
      QAlgorithms.Qubits n × Fin K → Prop :=
    fun T x y => (∀ k : Fin n, some k ∈ T → x.1 k = y.1 k) ∧ (none ∈ T → x.2 = y.2)
  ∑ x, ∑ x', ∑ y, ∑ y',
    if agree S x x' ∧ agree S y y' ∧ agree Sᶜ x y' ∧ agree Sᶜ x' y then X x x' * Y y y' else 0

end RainsSep.Distill


