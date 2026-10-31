-- Prove2me | Definitions.Def_MayersBC_bcjlProb
-- name    : MayersBC_bcjlProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:41.436519+00:00
-- url     : https://prove2.me/theorems/163c2436-ab20-4559-85a9-06d9ec7980cb
-- title:
--   Honest commitment distribution $p(\theta, c \mid b)$
-- statement:
--   Let $C \subseteq \{0,1\}^n$ be a linear code and $r \in \{0,1\}^n$. To commit honestly to the bit $b$, Alice chooses $\theta \in \{+,\times\}^n$ uniformly at random and $c$ uniformly from the coset $\{c \in C : c \odot r = b\}$, where $c \odot r = \sum_i c_i r_i \bmod 2$. Hence
--
--   $$
--   p(\theta, c \mid b) = \begin{cases} \dfrac{2^{-n}}{\big|\{c' \in C : c' \odot r = b\}\big|} & \text{if } c \in C \text{ and } c \odot r = b,\\[2mm] 0 & \text{otherwise.}\end{cases}
--   $$
--
--   This is the probability that Alice, having $b$ in mind, prepares $|c\rangle_\theta$.
--
--   **Formalization Note** $C$ is any $\mathbb Z/2$-linear subspace of $(\mathbb Z/2)^n$; the "required properties" of the code in the protocol are not used anywhere in the analysis and are not imposed. If no codeword satisfies $c \odot r = b$ the function is identically $0$ (the set for $b = 0$ always contains $c = 0$).
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section b, pp.3–4 (COMMIT step 3; p(θ, c|b) on p.4)

import Mathlib
import Definitions.Def_MayersBC_Opening

namespace MayersBC

open Classical in
/-- Mayers, arXiv:quant-ph/9603015v3, section b, pp.3–4: `p(θ, c | b)`, the probability that
Alice, committing honestly to `b`, prepares `|c⟩_θ`. Step 3 of COMMIT: `θ` is uniform on
`{+, ×}^n` and `c` is uniform on `{c ∈ C | c ⊙ r = b}`, so
`p(θ, c | b) = 2^{-n} / |{c' ∈ C | c' ⊙ r = b}|` for `c` in that set, and `0` otherwise.

**Formalization Note.** The linear code `C` is any `ZMod 2`-submodule of `(ZMod 2)^n` (the
"required properties" of step 1 are never used); `c ⊙ r` is the dot product over `ZMod 2`.
Membership is decided classically. If the set is empty (no codeword has `c ⊙ r = b`), the value
is identically `0`; the set for `b = 0` always contains `c = 0`. -/
noncomputable def bcjlProb {n : ℕ} (C : Submodule (ZMod 2) (Fin n → ZMod 2))
    (r : Fin n → ZMod 2) (b : ZMod 2) : Opening n → ℝ :=
  fun w => if w.2 ∈ C ∧ w.2 ⬝ᵥ r = b then
    (1 / 2 ^ n) / ((Finset.univ.filter fun c : Fin n → ZMod 2 => c ∈ C ∧ c ⬝ᵥ r = b).card : ℝ)
  else 0

end MayersBC


