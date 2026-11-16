-- Prove2me | Definitions.Def_AgnosticTNS_Supplement_groupState
-- name    : AgnosticTNS_Supplement_groupState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:39:53.657288+00:00
-- url     : https://prove2.me/theorems/a150c154-64ba-49de-86df-9000b30acc22
-- title:
--   Grouped and padded state $|\psi\rangle_{\hat{\mathcal X}}$
-- statement:
--   Given a partition $\hat{\mathcal X}=\{\hat X_t\}_{t\in V(\hat T)}$ of $[n]$ and a vector $|\psi\rangle\in(\mathbb C^d)^{\otimes n}$, group the qudits of each bag into one physical subsystem using the canonical identification
--   $$
--   \bigotimes_{v\in[n]}\mathbb C^d \cong \bigotimes_{t\in V(\hat T)} (\mathbb C^d)^{\otimes|\hat X_t|},
--   $$
--   and pad each grouped space to dimension $d^k$. The result $|\psi\rangle_{\hat{\mathcal X}}$ is a vector on $m$ sites of dimension $d^k$.
--
--   **Formalization Note** The vertices of a bag are listed in increasing order and a local configuration is sent to its base-$d$ number in $\{0,\dots,d^{|\hat X_t|}-1\}\subseteq\{0,\dots,d^k-1\}$; padding entries get amplitude $0$. Any fixed bag-local injective identification gives an equivalent statement.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 6.14, Eqs. (6.31)–(6.32), p.56

import Mathlib

namespace AgnosticTNS.Supplement

/-- **The grouped and padded state** `|ψ⟩_X̂`, Eqs. (6.31)–(6.32), Theorem 6.14, p.56 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)):
under the canonical identification `⊗_{v ∈ [n]} ℂ^d ≅ ⊗_{t} (ℂ^d)^{⊗|X̂_t|}`, after padding each grouped
local space to dimension `d^k`.

**Formalization Note** The vertices of a bag are listed in increasing order and `x|_{X̂_t}` is sent to
its base-`d` number `Σ_{v ∈ X̂_t} x_v d^{rank of v in X̂_t} ∈ [d^{|X̂_t|}] ⊆ [d^k]` (when `|X̂_t| ≤ k`).
`|ψ⟩_X̂(y) = ψ(x)` when `y` is the image of `x`, and `0` on the padding. Any fixed bag-local injective
identification gives an equivalent statement (`S_{d^k}(T̂, ·)` is invariant under local isometries on
physical legs). -/
noncomputable def groupState {n m : ℕ} (d k : ℕ) (Xhat : Fin m → Finset (Fin n))
    (ψ : (Fin n → Fin d) → ℂ) : (Fin m → Fin (d ^ k)) → ℂ := by
  classical
  exact fun y => ∑ x : Fin n → Fin d,
    if ∀ t, (y t : ℕ) = ∑ v ∈ Xhat t, (x v : ℕ) * d ^ ((Xhat t).filter (· < v)).card then ψ x else 0

end AgnosticTNS.Supplement


