-- Prove2me | Definitions.Def_WeldedPath_Supplement_pWt
-- name    : WeldedPath_Supplement_pWt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:14:55.065624+00:00
-- url     : https://prove2.me/theorems/88f03393-0dc0-40a7-8382-e2a9d7e103bf
-- title:
--   The standard-oracle success probability $p_{\mathrm{wt}}$ of Algorithm 3.9
-- statement:
--   A **candidate path** is a list $x_{\mathrm{path}}=(z_0,\alpha_1,z_1,\dots,\alpha_m,z_m)$ with $z_0=0$, pairwise distinct labels $z_i\in[0,M]$, colors $\alpha_i$ and $m\ge n$. **Algorithm 3.9** samples $\sigma=(\sigma_{\mathrm{label}},\sigma_{\mathrm{edge}})\sim D_{\mathrm{prod}}$, runs a $q$-query algorithm $A$ with the welded trees oracle $O^{(wt)}_\sigma$, reads $x_{\mathrm{path}}$ off the final measurement, rejects it unless it is a candidate path, and then:
--
--   1. if $m\le 2q+1$: rejects unless $F^{(wt)}_\sigma(z_{i-1},\alpha_i)=z_i$ for every $i\in[m]$, and accepts iff exactly two of the three colors $\alpha$ give an answer $F^{(wt)}_\sigma(z_m,\alpha)\neq z_m$;
--   2. if $m>2q+1$: accepts iff for every $i\in[2q+1]$ at least one color $\alpha$ gives $F^{(wt)}_\sigma(z_i,\alpha)\neq z_i$.
--
--   $p_{\mathrm{wt}}$ is the probability that Algorithm 3.9 accepts, over $\sigma$ and the measurement. It is at least the probability that $A$ outputs an entrance–exit path under $D_{\mathrm{prod}}$.
--
--   **Formalization Note** The output map sends a measurement outcome to the list of steps $(\alpha_i,z_i)$, as in the published `successProb`; $D_{\mathrm{prod}}$ is the uniform average over the published `prodSupport`. The verifier's queries are evaluations of $F^{(wt)}_\sigma$. Step 1 counts colors, not distinct neighbours (footnote 2 of the source).
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), candidate path, p.22; Algorithm 3.9 and footnote 2, p.23

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_successProb

namespace WeldedPath

namespace Supplement

open QAlgorithms WeldedInstance

variable {n : ℕ}

/-- The welded trees oracle's answer `F^{(wt)}_σ(z, α)` (26) at a number `z`, as a number: the
published `F` for `z ∈ [0, M]`, and `z` itself for `z > M` (never used: the verifier only queries
labels of a candidate path, which lie in `[0, M]`) (Carolan, Childs, Coudron, Gilani,
Miloschewsky, Podder, arXiv:2611.05912 (sha256 b31400a0…), p.17). -/
noncomputable def Fnat (l : ℕ) (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) (z : ℕ) (α : Fin 3) : ℕ :=
  if h : z < labelBound n + 1 then (G.F l σ ⟨z, h⟩ α).1 else z

/-- The labels `z_0 = 0, z_1, …, z_m` of an output list of steps `(α_1, z_1), …, (α_m, z_m)`, each
`z_i` read as the number its `(2n+1)`-bit string encodes. -/
def pathLabels (out : List (Fin 3 × Qubits (2 * n + 1))) : List ℕ :=
  0 :: out.map fun s => bitsToNat s.2

/-- `x_path = (z_0, α_1, z_1, …, α_m, z_m)` is a candidate path (arXiv:2611.05912
(sha256 b31400a0…), p.22): `z_0 = 0`, the labels `z_i ∈ [0, M]` are pairwise distinct, and
`m ≥ n`. -/
def IsCandidatePath (out : List (Fin 3 × Qubits (2 * n + 1))) : Prop :=
  (∀ s ∈ out, bitsToNat s.2 ≤ labelBound n) ∧ (pathLabels out).Nodup ∧ n ≤ out.length

/-- Acceptance in Algorithm 3.9 (arXiv:2611.05912 (sha256 b31400a0…), p.23) for the oracle
`O^{(wt)}_σ`, after `A` made `q` queries and output the candidate `x_path` of length `m`:
1. reject unless `x_path` is a candidate path (step 2);
2. if `m ≤ 2q + 1` (step 3): accept iff `F^{(wt)}_σ(z_{i−1}, α_i) = z_i` for every `i ∈ [m]`
   (3a) and exactly two of the three colors `α ∈ C` have `F^{(wt)}_σ(z_m, α) ≠ z_m` (3b);
3. if `m > 2q + 1` (step 4): accept iff for every `i ∈ [2q + 1]` some color `α ∈ C` has
   `F^{(wt)}_σ(z_i, α) ≠ z_i`.

**Formalization Note.** Querying `O^{(wt)}_σ` at `(z, α)` with the answer register `0` returns
`F^{(wt)}_σ(z, α)`, so the verifier's queries are evaluations of `F`. Step 3b counts answers
(colors), not distinct neighbours (footnote 2, p.23). -/
def Accepts39 (l : ℕ) (G : WeldedInstance n) (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    (q : ℕ) (out : List (Fin 3 × Qubits (2 * n + 1))) : Prop :=
  let zs := pathLabels out
  let m := out.length
  IsCandidatePath out ∧
    (m ≤ 2 * q + 1 →
      (∀ i, i < m → Fnat l G σ (zs.getD i 0) ((out.getD i (0, 0)).1) = zs.getD (i + 1) 0) ∧
      (Finset.univ.filter fun α : Fin 3 => Fnat l G σ (zs.getD m 0) α ≠ zs.getD m 0).card = 2) ∧
    (2 * q + 1 < m →
      ∀ i, 1 ≤ i → i ≤ 2 * q + 1 → ∃ α : Fin 3, Fnat l G σ (zs.getD i 0) α ≠ zs.getD i 0)

/-- The success probability `p_wt` of Algorithm 3.9 (Standard Oracle Pathfinding;
arXiv:2611.05912 (sha256 b31400a0…), p.23): sample `σ = (σ_label, σ_edge) ∼ D_prod`, run the
`q`-query algorithm `A` with `O^{(wt)}_σ`, read the candidate path off the final measurement with
the output map `out`, and verify it as in `Accepts39`.

**Formalization Note.** `D_prod` is the uniform distribution on the published `prodSupport`;
the probability is the published `probOver` (average over `σ` of the probability of the event
under the final computational-basis measurement of `A` with the oracle `xorOracle (oracleFn σ)`).
The output map `out` sends a measurement outcome to the list of steps `(α_i, z_i)`, as in the
published `successProb`. The verifier's queries are classical given `σ`. -/
noncomputable def pWt (l : ℕ) (G : WeldedInstance n) {W : Type*} [Fintype W] [DecidableEq W]
    {q : ℕ} (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q)
    (out : ((Qubits (2 * n + 1) × Fin 3) × Qubits (2 * n + 1)) × W →
      List (Fin 3 × Qubits (2 * n + 1))) : ℝ :=
  G.probOver l (G.prodSupport l) A fun σ z => Accepts39 l G σ q (out z)

end Supplement

end WeldedPath


