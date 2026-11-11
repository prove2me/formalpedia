-- Prove2me | Definitions.Def_UnitalMIP_pauliFold
-- name    : UnitalMIP_pauliFold
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:39:30.820393+00:00
-- url     : https://prove2.me/theorems/219c3748-b38e-4a08-89e5-85f997444947
-- title:
--   Pauli folding $\Phi_{h,r}(P_\alpha)=\chi_r(\alpha)P_{H\alpha}$
-- statement:
--   For a hash $h:[n]\to[D]$ and $\alpha\in(\mathbb F_2^2)^n$ set $(H\alpha)_j=\sum_{i:h(i)=j}\alpha_i$. For signs $r\in(\mathbb F_2^2)^n$ set $\chi_r(\alpha)=(-1)^{\sum_i(r_{i,1}\alpha_{i,1}+r_{i,2}\alpha_{i,2})}$. **Pauli folding** is the linear map from $n$-qubit to $D$-qubit operators with
--
--   $$
--   \Phi_{h,r}(P_\alpha)=\chi_r(\alpha)\,P_{H\alpha},\qquad\text{so}\qquad \Phi_{h,r}(F)=\sum_\alpha \hat F(\alpha)\,\chi_r(\alpha)\,P_{H\alpha}.
--   $$
--
--   It is the dimension-reduction map that compresses low-degree block approximants from $n$ to $D$ qubits.
--
--   **Formalization Note** The linear extension is written through the Pauli expansion; the seed $(h,r)$ is an arbitrary map `Fin n → Fin D` and signs.
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), (25)–(26), p.27

import Mathlib
import Definitions.Def_UnitalMIP_pauliString

open scoped Matrix

namespace UnitalMIP

/-- The folded label `(Hα)_j := ∑_{i : h(i) = j} α_i ∈ 𝔽₂²` of `α ∈ (𝔽₂²)ⁿ` under a hash
`h : [n] → [D]` (arXiv:2609.39318, version of 2026-11-03, sha256 56ebc59e…, (25), p.27). -/
def foldLabel {n D : ℕ} (h : Fin n → Fin D) (α : Fin n → Fin 2 × Fin 2) : Fin D → Fin 2 × Fin 2 :=
  fun j => ∑ i ∈ Finset.univ.filter (fun i => h i = j), α i

/-- The sign `χ_r(α) := (−1)^{∑_i (r_{i,1} α_{i,1} + r_{i,2} α_{i,2})}` (arXiv:2609.39318, (26),
p.27). -/
def foldSign {n : ℕ} (r α : Fin n → Fin 2 × Fin 2) : ℂ :=
  (-1 : ℂ) ^ (∑ i, ((r i).1.val * (α i).1.val + (r i).2.val * (α i).2.val))

/-- **Pauli folding** `Φ_{h,r}` (arXiv:2609.39318, version of 2026-11-03, (26), p.27): the linear map
from operators on `n` qubits to operators on `D` qubits with `Φ_{h,r}(P_α) := χ_r(α) P_{Hα}`,
extended linearly through the Pauli expansion `F = ∑_α F̂(α) P_α`.

**Formalization Note** The linear extension is written out: `Φ_{h,r}(F) = ∑_α F̂(α) χ_r(α) P_{Hα}`,
with `F̂(α) = τ_{2^n}(P_α† F)` (`pauliCoeff`). The seed `(h, r)` is an arbitrary pair of a map
`Fin n → Fin D` and signs `r ∈ (𝔽₂²)ⁿ`; the source draws it at random, and Theorem 3.4 asserts the
existence of one good deterministic seed. -/
noncomputable def pauliFold {n D : ℕ} (h : Fin n → Fin D) (r : Fin n → Fin 2 × Fin 2)
    (F : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) : Matrix (Fin D → Fin 2) (Fin D → Fin 2) ℂ :=
  ∑ α : Fin n → Fin 2 × Fin 2, (pauliCoeff F α * foldSign r α) • pauliString (foldLabel h α)

end UnitalMIP


