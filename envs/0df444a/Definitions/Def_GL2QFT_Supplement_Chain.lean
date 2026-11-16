-- Prove2me | Definitions.Def_GL2QFT_Supplement_Chain
-- name    : GL2QFT_Supplement_Chain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:35:28.153184+00:00
-- url     : https://prove2.me/theorems/94bbf0f4-58dc-4434-85ce-80432413068c
-- title:
--   Bratteli paths and the recursive chain transform $Q_m$ of (44)
-- statement:
--   For a chain of subgroups $\{e\}=G_1<G_2<\dots<G_n=G$ (levels $k=0,\dots,N$, the paper's $m=k+1$):
--
--   1. The **Bratteli paths** $P(\mu)$ (§3.3): a path to $\mu$ at level $k+1$ is an edge $\lambda\to\mu$ with $\lambda\in N^-(\mu)$ followed by a path to $\lambda$; a path to a level-$0$ node is the root. These are the labels $P:\lambda\to\mu$ of the Gelfand–Tsetlin basis (Corollary B.7).
--   2. The **chain transform** of Theorem 3.7, eq. (44):
--   $$Q_1=\mathfrak F_{G_1},\qquad Q_m=(U^m_{\rm Ind}\otimes I)\,(I_{\mathbb C[T_m]}\otimes Q_{m-1})\,\mathrm{Enc}_m ,$$
--   with the codomain of $Q_m$ written in the basis $|\mu,Q,R^*\rangle$, $Q,R\in P(\mu)$, through the identification of Lemma 3.5 at each level.
--
--   **Formalization Note** $U^m_{\rm Ind}\otimes I$ and $\mathrm{Enc}_m$ are the published `UIndTensorI` and `Enc` for $G_{m-1}\le G_m$ with the transversal $T_m$; the subgroups are subgroups of the ambient $G$.
-- source:
--   Bruinsma, Posta, Stokvis, Grinko, Ozols, Quantum Fourier transform toolbox, arXiv:2608.28573 (held version, sha256 ecd45073…), §3.3 p.21, Theorem 3.7 eq. (44) p.22 (PDF pp.22–23)

import Definitions.Def_GL2QFT_InductionTransform

noncomputable section

open Classical

namespace GL2QFT

namespace Supplement

namespace Chain

open Induction

/-! Levels are numbered `k = 0, 1, …, N`; level `k` is the paper's level `m = k + 1`, so the chain
`{e} = G_1 < G_2 < ⋯ < G_n = G` of §3.3 is `grp 0 < grp 1 < ⋯ < grp N` with `n = N + 1`. -/

variable {G : Type} [Group G] [Fintype G] (grp : ℕ → Subgroup G) (Λ : ℕ → Type) [∀ k, Fintype (Λ k)]
  (Nm : ∀ k, Λ (k + 1) → Finset (Λ k))

/-- arXiv:2608.28573 (held version, sha256 ecd45073…), §3.3, p.21 (PDF p.22): the set `P(μ)` of
directed paths `P^(1) → P^(2) → ⋯ → P^(m) = μ` in the Bratteli diagram from the root to the node `μ`
at level `k` (an edge `λ → μ` exactly when `λ ∈ N⁻(μ)`). A path to `μ` at level `k + 1` is an edge
`λ → μ` (`λ ∈ N⁻(μ)`) followed by a path to `λ`; this is the labelling `P : λ → μ` of
Definition 3.1 with `P ∈ P(λ)` (Corollary B.7). -/
def Paths : (k : ℕ) → Λ k → Type
  | 0, _ => Unit
  | k + 1, μ => Σ l : (Nm k μ), Paths k l.1

instance instFintypePaths : ∀ (k : ℕ) (μ : Λ k), Fintype (Paths Λ Nm k μ)
  | 0, _ => inferInstanceAs (Fintype Unit)
  | k + 1, μ =>
      letI : ∀ l : Nm k μ, Fintype (Paths Λ Nm k l.1) := fun l => instFintypePaths k l.1
      inferInstanceAs (Fintype (Σ l : (Nm k μ), Paths Λ Nm k l.1))

instance instDecEqPaths : ∀ (k : ℕ) (μ : Λ k), DecidableEq (Paths Λ Nm k μ) :=
  fun _ _ => Classical.decEq _

/-- The subgroup `G_{m−1} = grp k` of `G_m = grp (k+1)`, as a subgroup of `grp (k+1)`. -/
abbrev lowerSub (k : ℕ) : Subgroup (grp (k + 1)) := (grp k).subgroupOf (grp (k + 1))

/-- An element of `grp k ∩ grp (k+1)` (as a subgroup of `grp (k+1)`) viewed as an element of
`grp k`. -/
def toLower (k : ℕ) (h : lowerSub grp k) : grp k := ⟨((h : grp (k + 1)) : G), h.2⟩

variable (R : ∀ k (μ : Λ k), grp k → Matrix (Paths Λ Nm k μ) (Paths Λ Nm k μ) ℂ)
  (T : ∀ k, Set (grp (k + 1)))

/-- arXiv:2608.28573, Theorem 3.7, eq. (44), p.22 (PDF p.23): the recursively defined maps
`Q_1 = F_{G_1}` and `Q_m = (U^m_Ind ⊗ I)(I_{ℂ[T_m]} ⊗ Q_{m−1}) Enc_m`, `2 ≤ m ≤ n`, with the codomain
of `Q_m` written in the basis `|μ, Q, R*⟩`, `Q, R ∈ P(μ)`, through the identification of Lemma 3.5
(`|λ, Q : λ̃ → μ, R*⟩ ≡ |μ, Q : λ̃ → μ, (R : λ → μ)*⟩`).

**Formalization Note** Level `k` is the paper's `m = k + 1`. `U^m_Ind` is the base mission's
`UIndTensorI` for `grp k ≤ grp (k+1)` with the transversal `T k`; `Enc_m` is `Enc`; the columns of
`Q_{m−1}` (elements of `grp k`) are re-indexed as elements of `grp k` inside `grp (k+1)`. -/
def chainQ : (k : ℕ) → Matrix (Σ μ : Λ k, Paths Λ Nm k μ × Paths Λ Nm k μ) (grp k) ℂ
  | 0 => fourierMatrix (R 0)
  | k + 1 =>
      ((UIndTensorI (T k) (Paths Λ Nm k) (Nm k) (R (k + 1)) *
          Matrix.kronecker (1 : Matrix (T k) (T k) ℂ)
            ((chainQ k).submatrix id (toLower grp k))) *
        Enc (lowerSub grp k) (T k)).submatrix (ident (Paths Λ Nm k) (Nm k)) id

end Chain

end Supplement

end GL2QFT


