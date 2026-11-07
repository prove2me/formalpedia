-- Prove2me | Definitions.Def_PathRecording_adversary
-- name    : PathRecording_adversary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:09:39.890008+00:00
-- url     : https://prove2.me/theorems/682fbbb8-83ba-455e-b346-cf086c1374a4
-- title:
--   Adversary runs against $Q_\rho$, against $Q^{\mathrm{Path}}_\rho$ and against a fixed $\rho(g)$, and their reduced states
-- statement:
--   A $t$-query adversary has a query register $A=V=\mathbb C^N$, a workspace $B$ (any finite set of basis states), unitaries $A_1,\dots,A_t$ on $A\otimes B$ and a start state $\psi\in A\otimes B$. After $t$ queries to a purified oracle $\mathcal O$ the joint state is
--   $$\mathcal O\,A_t\,\mathcal O\,A_{t-1}\cdots\mathcal O\,A_1\,(\psi\otimes|\emptyset\rangle_R),\qquad(3.1)$$
--   in three semantics:
--
--   1. **uncompressed**: $R=L^2(G)$, start $\psi\otimes|1\rangle$, $\mathcal O=Q_\rho\otimes I_B$;
--   2. **path recording**: $R=\mathrm{Path}_i$ after $i$ queries, start $\psi\otimes|\emptyset\rangle$ ($\mathrm{Path}_0=\mathbb C$), and the $i$-th query applies $Q^{\mathrm{Path}}_{\rho,i}$ built from a family of Schur–Weyl data;
--   3. **fixed $g$**: no register $R$, $\mathcal O=\rho(g)\otimes I_B$.
--
--   The **reduced state** $\mathrm{tr}_R|\varphi\rangle\langle\varphi|$ on $A\otimes B$ has entries $\int_G\varphi_k(g)\overline{\varphi_{k'}(g)}\,dg$ (uncompressed) and $\sum_p\varphi(k,p)\overline{\varphi(k',p)}$ (path). The **Haar average** of the fixed-$g$ runs is $\mathbb E_{g\sim\mu}|A^{\rho(g)}\psi\rangle\langle A^{\rho(g)}\psi|$.
--
--   **Formalization Note** The unitaries are a sequence `A : ℕ → U(N·|B|)` with `A i` the paper's $A_{i+1}$; a $t$-query run reads only the first $t$, and any list extends to such a sequence. The start state $\psi$ is arbitrary (Theorem 5.3: "for all input states"), not only $|0\rangle$.
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Definition 3.5, Eq. (3.1) and footnote 37, pp.31–32; §4.1, p.47; Definition 5.1, p.62; Theorem 5.3, p.63; Theorem 1.5(3), p.12

import Mathlib
import Definitions.Def_PathRecording_fourier
import Definitions.Def_PathRecording_pathOracle

set_option autoImplicit false

namespace PathRecording

/-!
# Purified oracle adversaries run against `Q_ρ`, against `Q^{Path}_ρ`, and against a fixed `ρ(g)`

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Definition 3.5, pp.31–32: a `t`-query adversary is a list of unitaries
`(A₁, …, A_t)` on the query register `A` and a workspace `B`; the purified oracle `𝒪` acts on `A` and
a hidden register `R`, and after `t` queries the state is
`tr_R[(∏_{i=1}^t 𝒪_{AR} · A_{i,AB}) (|0⟩_{AB} ⊗ |∅⟩_R)]` (3.1), with `∏_{i=1}^t X_i := X_t ⋯ X_1`
(footnote 37). Theorem 5.3 (p.63) takes "every t-query quantum algorithm A whose query register is V"
and "all input states |ψ⟩"; Theorem 1.5(3) (p.12) compares with running the algorithm against
`ρ(g)` for a Haar-random `g`.

**Formalization Note.**
* The query register is `V = ℂᴺ`, the workspace any finite type `B`; `A ⊗ B` has basis
  `Fin N × B`. The adversary is a sequence `A : ℕ → U(ℂ^{N·|B|})`, where `A i` is the paper's
  `A_{i+1}`; a run of `t` queries reads only `A 0, …, A (t-1)` (any list `(A₁,…,A_t)` extends to a
  sequence). The start state is an arbitrary `ψ ∈ ℂ^{Fin N × B}` (not only `|0⟩`).
* Order (3.1): the `i`-th step applies `A_i` and then the oracle; the run ends with an oracle call.
* Uncompressed semantics: `R = L²(G)`, start `ψ ⊗ |1⟩`, oracle `Q_ρ ⊗ I_B`; the state is a function
  `Fin N × B → L²(G)`.
* Path semantics: `R = Path_i` after `i` queries, start `ψ ⊗ |∅⟩` (`Path_0 = ℂ`, as `Fin 0 → Fin N`
  has one element), and the `i`-th query applies `Q^{Path}_{ρ,i}`, built from the Schur–Weyl data at
  `i − 1` and `i` of a family `S`.
* Fixed `g`: the oracle is the unitary `ρ(g) ⊗ I_B`, no recording register.
* Reduced states on `A ⊗ B` (`tr_R |φ⟩⟨φ|`): entry `(k, k')` is `⟪φ_{k'}, φ_k⟫_{L²} = ∫ φ_k \overline{φ_{k'}}`
  for the uncompressed state and `Σ_p φ(k,p) \overline{φ(k',p)}` for the path state; the Haar average
  of the fixed-`g` density matrices is `∫ φ_g(k) \overline{φ_g(k')} dμ(g)`.
-/

open Matrix MeasureTheory Kronecker
open scoped ENNReal InnerProductSpace

variable {G : Type*} [Group G] [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] (μ : Measure G) [IsFiniteMeasure μ] {N : ℕ}

variable (B : Type) [Fintype B] [DecidableEq B]

/-- A local operator `U` on `A ⊗ B` applied to a state of `A ⊗ B ⊗ L²(G)`. -/
noncomputable def localApply (U : Matrix (Fin N × B) (Fin N × B) ℂ)
    (φ : Fin N × B → Lp ℂ 2 μ) : Fin N × B → Lp ℂ 2 μ :=
  fun k => ∑ j, U k j • φ j

/-- The uncompressed oracle `Q_ρ ⊗ I_B` on `A ⊗ B ⊗ L²(G)` (Eq. (4.1), p.47). -/
noncomputable def oracleAB (ρ : UnitaryRep G N) (φ : Fin N × B → Lp ℂ 2 μ) :
    Fin N × B → Lp ℂ 2 μ :=
  fun k => ∑ x, (entryLinf μ ρ k.1 x • φ (x, k.2) : Lp ℂ 2 μ)

/-- The state of `A ⊗ B ⊗ L²(G)` after `i` queries to `Q_ρ`, started from `ψ ⊗ |1⟩`
(Definition 3.5, Eq. (3.1), p.32; §4.1, p.47). -/
noncomputable def uncompressedRun (ρ : UnitaryRep G N)
    (A : ℕ → Matrix.unitaryGroup (Fin N × B) ℂ) (ψ : Fin N × B → ℂ) :
    ℕ → (Fin N × B → Lp ℂ 2 μ)
  | 0 => fun k => ψ k • oneLp μ
  | i + 1 => oracleAB μ B ρ (localApply μ B (A i : Matrix (Fin N × B) (Fin N × B) ℂ)
      (uncompressedRun ρ A ψ i))

/-- The state of `A ⊗ B ⊗ Path_i` after `i` queries to the path recording oracle, started from
`ψ ⊗ |∅⟩`; the `(i+1)`-st query applies `Q^{Path}_{ρ,i+1}` (Definition 5.1, p.62; Eq. (3.1)). -/
noncomputable def pathRun {ρ : UnitaryRep G N} (S : (t : ℕ) → SchurWeylData ρ t)
    (A : ℕ → Matrix.unitaryGroup (Fin N × B) ℂ) (ψ : Fin N × B → ℂ) :
    (i : ℕ) → (Fin N × B) × PathIdx N i → ℂ
  | 0 => fun q => ψ q.1
  | i + 1 => fun q => ∑ x : Fin N, ∑ p : PathIdx N i,
      pathOracle (S i) (S (i + 1)) (q.1.1, q.2) (x, p) *
        ∑ k : Fin N × B, (A i : Matrix (Fin N × B) (Fin N × B) ℂ) (x, q.1.2) k *
          pathRun S A ψ i (k, p)

/-- The state of `A ⊗ B` after `i` queries to the fixed unitary `ρ(g) ⊗ I_B`, started from `ψ`. -/
noncomputable def fixedRun (ρ : UnitaryRep G N) (g : G)
    (A : ℕ → Matrix.unitaryGroup (Fin N × B) ℂ) (ψ : Fin N × B → ℂ) : ℕ → (Fin N × B → ℂ)
  | 0 => ψ
  | i + 1 => (ρ.mat g ⊗ₖ (1 : Matrix B B ℂ)) *ᵥ
      ((A i : Matrix (Fin N × B) (Fin N × B) ℂ) *ᵥ fixedRun ρ g A ψ i)

/-- The reduced state `tr_R |φ⟩⟨φ|` on `A ⊗ B` of a state of `A ⊗ B ⊗ L²(G)`:
entry `(k, k')` is `⟪φ_{k'}, φ_k⟫ = ∫_G φ_k(g) \overline{φ_{k'}(g)} dg`. -/
noncomputable def reducedUnc (φ : Fin N × B → Lp ℂ 2 μ) : Matrix (Fin N × B) (Fin N × B) ℂ :=
  Matrix.of fun k k' => ⟪φ k', φ k⟫_ℂ

/-- The reduced state `tr_R |χ⟩⟨χ|` on `A ⊗ B` of a state of `A ⊗ B ⊗ Path_i`:
entry `(k, k')` is `Σ_p χ(k, p) \overline{χ(k', p)}`. -/
noncomputable def reducedPath {i : ℕ} (χ : (Fin N × B) × PathIdx N i → ℂ) :
    Matrix (Fin N × B) (Fin N × B) ℂ :=
  Matrix.of fun k k' => ∑ p, χ (k, p) * star (χ (k', p))

/-- The Haar-averaged density matrix `E_{g∼μ} |A^{ρ(g)}ψ⟩⟨A^{ρ(g)}ψ|` after `t` queries
(Theorem 1.5(3), p.12). -/
noncomputable def haarAverage (ρ : UnitaryRep G N) (A : ℕ → Matrix.unitaryGroup (Fin N × B) ℂ)
    (ψ : Fin N × B → ℂ) (t : ℕ) : Matrix (Fin N × B) (Fin N × B) ℂ :=
  Matrix.of fun k k' => ∫ g, fixedRun B ρ g A ψ t k * star (fixedRun B ρ g A ψ t k') ∂μ

end PathRecording


