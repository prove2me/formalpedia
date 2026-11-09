-- Prove2me | Definitions.Def_WeldedPath_oracleFn
-- name    : WeldedPath_oracleFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:10:09.922514+00:00
-- url     : https://prove2.me/theorems/5ecfddcd-c893-4cd2-ad8e-5c1ddf4ca115
-- title:
--   The welded trees oracle $O^{(wt)}_\sigma$ and its answer function $F^{(wt)}_\sigma$
-- statement:
--   Let $M=2^{2n}$. Vertices are hidden behind a random labeling $\sigma_{\mathrm{label}}$, a permutation of $[0,M]$ with $\sigma_{\mathrm{label}}(0)=0$. For $\sigma=(\sigma_{\mathrm{label}},\sigma_{\mathrm{edge}})$, a label $x\in[0,M]$ and a color $\alpha$,
--   $$
--   F^{(wt)}_\sigma(x,\alpha)=\sigma_{\mathrm{label}}\big(\mathrm{Nb}_{\sigma_{\mathrm{edge}}}(\sigma_{\mathrm{label}}^{-1}(x),\alpha)\big),\qquad O^{(wt)}_\sigma|x,\alpha,y\rangle=|x,\alpha,y\oplus F^{(wt)}_\sigma(x,\alpha)\rangle,
--   $$
--   where the label and answer registers hold strings of $2n+1$ bits. For $x>M$ the oracle acts as the identity.
--
--   This is the only access an algorithm has to the graph: it learns labels of neighbors, never structural indices.
--
--   **Formalization Note** A $(2n+1)$-bit string encodes its binary value, most significant bit first (`QAlgorithms.bitsToNat`, `natToBits`). The oracle is `QAlgorithms.xorOracle` of the answer function, which returns the bits of $F^{(wt)}_\sigma(x,\alpha)$ when the queried string encodes $x\le M$ and $0$ otherwise.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), pp.16–17, (26)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_Nb

namespace WeldedPath

/-- `M = 2^{2n}`; the labels are `[0, M]` (arXiv:2611.05912 (sha256 b31400a0…), p.16). -/
def labelBound (n : ℕ) : ℕ := 2 ^ (2 * n)

/-- The label set `[0, M]`, as `Fin (M + 1)`. -/
abbrev Label (n : ℕ) := Fin (labelBound n + 1)

/-- The exit index `2^{n+1} − 1` as an element of `[0, M]`. -/
def exitLabelIdx (n : ℕ) : Label n :=
  ⟨exitIdx n, by
    unfold exitIdx labelBound
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; norm_num
    · have h1 : 2 ^ (n + 1) ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 0 < 2 ^ (n + 1) := Nat.two_pow_pos _
      omega⟩

namespace WeldedInstance

variable {n : ℕ}

/-- The welded trees oracle function `F^{(wt)}_σ(x, α) = σ_label(Nb_{σ_edge}(σ_label^{-1}(x), α))`
(26) (arXiv:2611.05912 (sha256 b31400a0…), p.17), for `σ = (σ_label, σ_edge)` and a label
`x ∈ [0, M]`.

**Formalization Note.** `σ_label` is a permutation of `[0, M]` (`Fin (M + 1)`); the support
condition `σ_label(0) = 0` is imposed by the distributions (`prodSupport`). `Nb` returns `v` or a
structural index, both at most `M` for `n ≥ 2`; the fallback `x` covers `n ≤ 1` only. -/
noncomputable def F (l : ℕ) (G : WeldedInstance n) (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    (x : Label n) (α : Fin 3) : Label n :=
  if h : G.Nb l σ.2 (σ.1.symm x).1 α < labelBound n + 1 then σ.1 ⟨_, h⟩ else x

/-- The answer function of the XOR oracle `O^{(wt)}_σ|x, α, y⟩ = |x, α, y ⊕ F^{(wt)}_σ(x, α)⟩`
(arXiv:2611.05912 (sha256 b31400a0…), p.17), on `(2n+1)`-bit registers: the answer is the bit
string of `F^{(wt)}_σ(x, α)` when the queried string encodes `x ≤ M`, and `0` (the oracle acts as
the identity) when it encodes `x > M`.

**Formalization Note.** A string `b` encodes the number `bitsToNat b` (most significant bit
first), and `natToBits (2n+1)` is the inverse encoding; `[0, M]` with `M = 2^{2n}` fits in
`2n + 1` bits. The color register holds `α ∈ Fin 3`. -/
noncomputable def oracleFn (l : ℕ) (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) :
    QAlgorithms.Qubits (2 * n + 1) × Fin 3 → QAlgorithms.Qubits (2 * n + 1) :=
  fun x =>
    if h : QAlgorithms.bitsToNat x.1 < labelBound n + 1 then
      QAlgorithms.natToBits (2 * n + 1) (G.F l σ ⟨_, h⟩ x.2).1
    else 0

end WeldedInstance

end WeldedPath


