-- Prove2me | Definitions.Def_LaconicBarrier_Supplement_StrongLocal
-- name    : LaconicBarrier_Supplement_StrongLocal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:32:52.077684+00:00
-- url     : https://prove2.me/theorems/dbc8e0b9-5c9a-4813-b941-7e5aaaf3869d
-- title:
--   Strong local correctness of a multiprover protocol
-- statement:
--   Let $\mathcal R$ be an NP relation with language $L$. A multiprover protocol with specified honest provers $P_1, \dots, P_{k'}$ has **strong local correctness** with error $\epsilon_c$ if, for every yes-instance with statement $x \in L$ and every tuple $(w_1, \dots, w_{k'})$ with $(x, w_j) \in \mathcal R$ for all $j$,
--   $$
--   \Pr\bigl[\langle P_1(w_1), \dots, P_{k'}(w_{k'}), V \rangle(x) = 1\bigr] \ge 1 - \epsilon_c .
--   $$
--   Here $P_j(w_j)$ is prover $j$ holding witness $w_j$. Its replies depend only on $x$, $w_j$, its own question and independent private coins. The honest algorithms are fixed before the witnesses are chosen, there is no shared randomness, and the witnesses may differ.
--
--   This strengthens the completeness of Definition 4.32: completeness only asks for some accepted provers, while strong local correctness asks that honest provers with arbitrary, possibly different valid witnesses are accepted.
--
--   **Formalization Note** One honest algorithm $H(x, w, q; \rho)$ serves every prover index. The witness tuple is a function on prover indices, of which those below $k'$ must be valid.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 8.1, p.50

import Mathlib
import Definitions.Def_LaconicBarrier_Supplement_MIPVerifier

namespace LaconicBarrier.Supplement

/-- **Strong local correctness** (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower
Bounds for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), Definition
8.1, p.50): the protocol with the specified honest provers has strong local correctness with error
`ϵ_c` on the yes-instances if, for every `i ∈ yes` with statement `x = inst i` and every tuple
`(w₁, …, w_{k′})` of witnesses with `(x, w_j) ∈ R` for all `j`, the verifier accepts the honest
provers `P_j(w_j)` with probability at least `1 − ϵ_c(i)`. Honest prover `j` answers a question `q`
with `H(x, w_j, q; ρ)` for independent private coins `ρ` (`hc x w q` of them): its reply depends
only on `x`, its own witness and its own question ("The honest algorithms are fixed before the
witnesses are chosen, with no joint preprocessing or shared randomness. The witnesses may differ").

**Formalization Note** One honest algorithm `H` serves every prover index; the witness tuple is a
function `ws` on prover indices, of which those below `k′(i)` must be valid. -/
def MIPVerifier.StrongLocal {I : Type} (V : MIPVerifier I) (yes : Set I) (inst : I → List Bool)
    (Rel : List Bool → List Bool → Prop) (kP ℓP : I → ℕ)
    (hc : List Bool → List Bool → List Bool → ℕ)
    (H : (x w q : List Bool) → (Fin (hc x w q) → Bool) → List Bool) (εc : I → ℝ) : Prop :=
  ∀ i ∈ yes, ∀ ws : ℕ → List Bool, (∀ j < kP i, Rel (inst i) (ws j)) →
    1 - εc i ≤ V.accProb i (kP i) (ℓP i)
      (fun j q => (PMF.uniformOfFintype (Fin (hc (inst i) (ws j) q) → Bool)).map
        (H (inst i) (ws j) q))

end LaconicBarrier.Supplement


