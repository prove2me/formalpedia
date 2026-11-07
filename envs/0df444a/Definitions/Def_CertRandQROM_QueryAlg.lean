-- Prove2me | Definitions.Def_CertRandQROM_QueryAlg
-- name    : CertRandQROM_QueryAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:18.061427+00:00
-- url     : https://prove2.me/theorems/ab5f11f6-772a-4f9c-8fc4-9dc2417cfd82
-- title:
--   Quantum query algorithm with a phase oracle, and its states $|\psi^h_j\rangle$
-- statement:
--   A **quantum query algorithm** $\mathcal A$ making $Q$ queries acts on registers $R=(R_Q,R_A)$: a query register $R_Q$ with orthonormal basis $\{|u\rangle : u\in U\}$ ($U$ is the oracle's input set, $[n]\times\Sigma$ in the paper) and a work register $R_A$ with basis indexed by a finite set $W$. It consists of
--
--   1. an initial unit vector $|\psi_0\rangle\in\mathbb C^{U\times W}$;
--   2. unitaries $U_1,\dots,U_Q$ on $\mathbb C^{U\times W}$;
--   3. a final measurement with outcomes in a finite set $O$, given by a POVM $\{M_o\}_{o\in O}$ ($M_o\succeq 0$, $\sum_o M_o = I$).
--
--   For an oracle $h:U\to\{0,1\}$ the **phase oracle** is $O_h|u\rangle|a\rangle=(-1)^{h(u)}|u\rangle|a\rangle$, and the states of the run are
--
--   $$
--   |\psi^h_0\rangle=|\psi_0\rangle,\qquad |\psi^h_{j}\rangle=U_{j}\,O_h\,|\psi^h_{j-1}\rangle\quad(1\le j\le Q).
--   $$
--
--   This is the model of all statements of the mission: the adversary is any such algorithm, with a work register of any finite dimension.
--
--   **Formalization Note** The query register is exactly $U$ (no idle sector), so the whole register is submitted at every query as in §3.2. `unitary j` is $U_{j+1}$ and `state h j` is $|\psi^h_j\rangle$; for $j\ge Q$ the state stays $|\psi^h_Q\rangle$. A POVM covers the paper's general measurement $M$ (projective measurements included). The inputs $(1^\lambda,1^{h_\infty})$ are absorbed into the initial state. Oracle value $1$ is `true`.
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), §3.2 Query-Bounded Algorithms, pp.14–15 (PDF pp.16–17); phase oracle as in the proof of Lemma 3.4, p.16

import Mathlib

open scoped ComplexOrder

namespace CertRandQROM

/-- **A quantum query algorithm making `Q` queries to a phase oracle** (Coladangelo, Khurana,
Mutreja, Roberts, Slote, Tal, *Unconditional Certified Randomness without Structure*,
arXiv:2608.31112 (sha256 b75095a2…), §3.2 "Query-Bounded Algorithms", pp.14–15).

The algorithm acts on registers `R = (R_Q, R_A)`: the query register `R_Q` with orthonormal
basis indexed by the oracle's input set `U` (in the paper `U = [n] × Σ`), and a work register
`R_A` with basis indexed by `W`. It is given by

1. an initial pure state `|ψ₀⟩` (`init`, a unit vector of `ℂ^{U × W}`);
2. unitaries `U_1, …, U_Q` (`unitary j` is the paper's `U_{j+1}`);
3. a final measurement `M` with outcomes in `O`, given as a POVM (`meas o` positive
   semidefinite, `Σ_o meas o = 1`).

**Formalization Note** The query register is exactly `U`: there is no idle (non-querying)
sector, as in §3.2, where the whole register `R_Q` is submitted at every query. The paper's
measurement `M` is general; a POVM covers projective measurements. The inputs `(1^λ, 1^{h∞})`
are absorbed into `init` (statements take one algorithm per security parameter). `W` is any
finite type, so the work register is unbounded across a family. -/
structure QueryAlg (U W O : Type) [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    [Fintype O] (Q : ℕ) where
  /-- The initial state `|ψ₀⟩` on `R = (R_Q, R_A)`. -/
  init : EuclideanSpace ℂ (U × W)
  /-- `|ψ₀⟩` is a unit vector. -/
  init_norm : ‖init‖ = 1
  /-- `unitary j` is the unitary `U_{j+1}` applied after the `(j+1)`-th query (0-based `j`). -/
  unitary : Fin Q → (EuclideanSpace ℂ (U × W) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (U × W))
  /-- The POVM element of outcome `o` of the final measurement `M`. -/
  meas : O → Matrix (U × W) (U × W) ℂ
  /-- Every POVM element is positive semidefinite. -/
  meas_psd : ∀ o, (meas o).PosSemidef
  /-- The POVM elements sum to the identity. -/
  meas_sum : ∑ o, meas o = 1

/-- The phase oracle `O_h` of `h : U → {0,1}` on `R = (R_Q, R_A)`:
`O_h |u⟩|a⟩ = (−1)^{h(u)} |u⟩|a⟩` (§3.2 p.15 "phase oracle"; proof of Lemma 3.4, p.16).
`true` is the oracle value `1`. -/
noncomputable def phaseOracle {U W : Type} (h : U → Bool) (ψ : EuclideanSpace ℂ (U × W)) :
    EuclideanSpace ℂ (U × W) :=
  WithLp.toLp 2 fun p => (if h p.1 then -1 else 1) * ψ p

/-- The state `|ψ_j^h⟩` of the algorithm `A` with oracle `h` after `j` queries (§3.2, p.15):
`|ψ_0^h⟩ = |ψ₀⟩` and `|ψ_{j+1}^h⟩ = U_{j+1} O_h |ψ_j^h⟩` for `j < Q`. For `j ≥ Q` the state
stays `|ψ_Q^h⟩` (no further queries). -/
noncomputable def QueryAlg.state {U W O : Type} [Fintype U] [DecidableEq U] [Fintype W]
    [DecidableEq W] [Fintype O] {Q : ℕ} (A : QueryAlg U W O Q) (h : U → Bool) :
    ℕ → EuclideanSpace ℂ (U × W)
  | 0 => A.init
  | j + 1 => if hj : j < Q then A.unitary ⟨j, hj⟩ (phaseOracle h (A.state h j)) else A.state h j

end CertRandQROM


