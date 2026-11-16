-- Prove2me | Definitions.Def_CompPermOracle_Supplement_keyedState
-- name    : CompPermOracle_Supplement_keyedState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:48:07.401142+00:00
-- url     : https://prove2.me/theorems/3a31c95a-3bfb-40f7-a106-65dba1e70d30
-- title:
--   Success probabilities with an output map, and the ideal-cipher run
-- statement:
--   Let $\mathcal A$ be a quantum algorithm with forward and inverse swap-oracle access (a published `Alg`), run for $q$ queries. After the last query its accessible registers are measured in the computational basis and an output map turns the outcome $c$ into the algorithm's output $\mathrm{out}(c)$. For a success event $S$, the success probability in the random permutation model is
--   $$
--   \Pr[S]=\frac1{N!}\sum_{\varphi\in S_N}\ \sum_{c:\ S(\mathrm{out}(c),\varphi)}\big\|\psi_q^{\varphi}(c)\big\|^2,
--   $$
--   where $\psi_q^\varphi$ is the algorithm's state after $q$ queries to $\tilde O_\varphi,\tilde O_{\varphi^{-1}}$.
--
--   In the **ideal cipher model** with a finite key space $\mathcal K$, the oracle is a family $\Phi=(\varphi_k)_{k\in\mathcal K}$ of independent uniform permutations, and the algorithm has quantum access to $(k,x)\mapsto\varphi_k(x)$ and $(k,y)\mapsto\varphi_k^{-1}(y)$, including superpositions over keys. A query under key $k$ applies $\tilde O_{\varphi_k}$ or $\tilde O_{\varphi_k^{-1}}$ to the input and answer registers, controlled on the key register, and acts only on the permutation indexed by $k$. The success probability is $(N!)^{-|\mathcal K|}\sum_\Phi\sum_{c:\,S(\mathrm{out}(c),\Phi)}\|\psi_q^{\Phi}(c)\|^2$.
--
--   These experiments define the probabilities $p$, $p_{\mathrm{pre}}$ and $p_{\mathrm{col}}$ of Theorems 5.3, 5.5 and 5.6.
--
--   **Formalization Note** A keyed algorithm is a published `Alg N (K × W)` whose workspace starts with an accessible key register, so its unitaries can prepare and change keys coherently; the oracle registers are not accessible. The `accept` field of `Alg` is unused in these experiments. The source measures the purification; by Remark 3.3 (published as `CompPermOracle.remark_3_3`) this is the same probability as the classically sampled experiment defined here.
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), §3.2, p.6 (ideal cipher); §5 opening and Lemma 5.1, p.27 (query model, probability p); Remark 3.3, p.6

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_Alg

namespace CompPermOracle.Supplement

open CompPermOracle

variable {N : ℕ}

open Classical in
/-- The success probability of a `q`-query algorithm with an output map in the random permutation
model (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), §5, p.27):
`(N!)⁻¹ ∑_φ ∑_{c : S(out c, φ)} ‖realState A φ q c‖²`.

**Formalization Note.** The algorithm is the published `CompPermOracle.Alg` (forward and inverse
swap queries, coherently controlled on a direction bit, as §5 requires: "All query counts in this
section refer to the swap oracles"); its `accept` field is unused here. After `q` queries the
accessible registers are measured in the computational basis and the output map `out` turns the
outcome `c` into the algorithm's output. `S o φ` is the success event for output `o` against `φ`.
The source measures the purification; by Remark 3.3 (published as `CompPermOracle.remark_3_3`) this
is the same number as this classically sampled experiment. -/
noncomputable def realSuccess {W : Type} [Fintype W] [DecidableEq W] {Out : Type}
    (A : Alg N W) (q : ℕ) (out : Acc N W → Out) (S : Out → Equiv.Perm (Fin N) → Prop) : ℝ :=
  ((N.factorial : ℝ))⁻¹ *
    ∑ φ : Equiv.Perm (Fin N), ∑ c : Acc N W, if S (out c) φ then ‖realState A φ q c‖ ^ 2 else 0

/-- One query to an ideal cipher `Φ = (φ_k)_{k ∈ 𝒦}` (arXiv:2609.28469, §3.2, p.6): on the basis
state `(d, x, a, (k, w))` it applies `Õ_{φ_k}` (direction `d = false`) or `Õ_{φ_k⁻¹}` (`d = true`)
to (input, answer), controlled on the key `k`, and leaves the key and the workspace untouched.

**Formalization Note.** A keyed algorithm is a published `Alg N (K × W)` whose workspace starts
with a key register `K`. The key register is accessible, so the algorithm chooses keys and may query
superpositions of keys; a query under key `k` acts only on the permutation indexed by `k`. -/
noncomputable def keyedStep {K W : Type} [Fintype K] [DecidableEq K] [Fintype W] [DecidableEq W]
    (Φ : K → Equiv.Perm (Fin N)) (ψ : Hil (Acc N (K × W))) : Hil (Acc N (K × W)) :=
  WithLp.toLp 2 fun c =>
    (if c.1 then swapOracleInv (Φ c.2.2.2.1) else swapOracle (Φ c.2.2.2.1))
      (WithLp.toLp 2 fun p : Fin N × Ans N => ψ (c.1, p.1, p.2, c.2.2.2)) (c.2.1, c.2.2.1)

/-- The state of a keyed algorithm against the ideal cipher `Φ` after `j` queries, each followed by
the algorithm's unitary. -/
noncomputable def keyedState {K W : Type} [Fintype K] [DecidableEq K] [Fintype W] [DecidableEq W]
    (A : Alg N (K × W)) (Φ : K → Equiv.Perm (Fin N)) : ℕ → Hil (Acc N (K × W))
  | 0 => A.init
  | j + 1 => A.Uop j (keyedStep Φ (keyedState A Φ j))

open Classical in
/-- The success probability of a `q`-query keyed algorithm with an output map in the ideal cipher
model (arXiv:2609.28469, §3.2, p.6: the `φ_k` are independent and uniform):
`((N!)^{|𝒦|})⁻¹ ∑_Φ ∑_{c : S(out c, Φ)} ‖keyedState A Φ q c‖²`. -/
noncomputable def keyedSuccess {K W : Type} [Fintype K] [DecidableEq K] [Fintype W]
    [DecidableEq W] {Out : Type} (A : Alg N (K × W)) (q : ℕ) (out : Acc N (K × W) → Out)
    (S : Out → (K → Equiv.Perm (Fin N)) → Prop) : ℝ :=
  (((N.factorial : ℝ)) ^ Fintype.card K)⁻¹ *
    ∑ Φ : K → Equiv.Perm (Fin N), ∑ c : Acc N (K × W),
      if S (out c) Φ then ‖keyedState A Φ q c‖ ^ 2 else 0

end CompPermOracle.Supplement


