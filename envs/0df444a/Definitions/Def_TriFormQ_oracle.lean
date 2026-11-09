-- Prove2me | Definitions.Def_TriFormQ_oracle
-- name    : TriFormQ_oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:22.091737+00:00
-- url     : https://prove2.me/theorems/5679429b-727b-4f30-8917-ad636115bdb8
-- title:
--   Evaluation oracle function $(x,y,z)\mapsto f(x,y,z)$
-- statement:
--   For a trilinear form $f$ on $\mathbb F_q^n$ (coefficient tensor $\theta$), the **evaluation oracle** acts on computational basis states by
--
--   $$O_f:\ |x\rangle|y\rangle|z\rangle|b\rangle\ \mapsto\ |x\rangle|y\rangle|z\rangle|b+f(x,y,z)\rangle ,\qquad x,y,z\in\mathbb F_q^n,\ b\in\mathbb F_q .$$
--
--   This definition is the function $(x,y,z)\mapsto f(x,y,z)$ that the oracle evaluates. An adaptive quantum query algorithm with this oracle function queries the platform's standard oracle built from it, which is exactly $O_f$ with addition in $\mathbb F_q$.
--
--   **Formalization Note** The oracle matrix is `QAlgorithms.xorOracle (oracle θ)` (the permutation matrix of $(p,b)\mapsto(p,b+g(p))$ over the additive group of $\mathbb F_q$). The work register that the paper omits "for simplicity of presentation" is the workspace of the platform's query algorithms, on which the oracle acts as the identity.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), §1, p.2 (PDF p.5)

import Definitions.Def_TriFormQ_TriForm_eval

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), §1, p.2 (PDF p.5): "A quantum
oracle query for f is defined by its action on computational basis states as follows:
Of : |x⟩|y⟩|z⟩|b⟩ ↦ |x⟩|y⟩|z⟩|f(x, y, z) + b⟩". The function `(x, y, z) ↦ f(x, y, z)` that the
oracle evaluates.

**Formalization Note.** An adaptive algorithm (`AdaptiveAlg.outProb`, `AdaptiveAlg.maxQueries`)
with oracle function `oracle θ` queries the platform's standard oracle
`QAlgorithms.xorOracle (oracle θ)`, the permutation matrix of `((x, y, z), b) ↦ ((x, y, z),
b + f(x, y, z))` over the additive group of `F`, i.e. `O_f`. The work register the paper omits
"for simplicity of presentation" is the workspace of `QAlgorithms.QueryAlg`, on which the oracle
acts as the identity. -/
def oracle {F : Type} [Field F] {n : ℕ} (θ : TriForm F n) : Vec F n × Vec F n × Vec F n → F :=
  fun p => TriForm.eval θ p.1 p.2.1 p.2.2

end TriFormQ


