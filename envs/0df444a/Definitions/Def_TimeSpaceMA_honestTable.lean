-- Prove2me | Definitions.Def_TimeSpaceMA_honestTable
-- name    : TimeSpaceMA_honestTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:58:10.634805+00:00
-- url     : https://prove2.me/theorems/10ccd27d-9d3a-4e37-b888-13deb46c7bd6
-- title:
--   Honest tables $R_j$ and their sources $Z_j$
-- statement:
--   For $h\in[q]^j$ and $\alpha\in[L]^{m-j}$, write $\sigma(h)\alpha:=(\sigma(h_1),\dots,\sigma(h_j),\alpha_1,\dots,\alpha_{m-j})$. For a word $Y$ on $[L]^m$ and a bilinear form $\Phi$, the **honest table** of level $j$ is
--   $$R_j(\alpha,\beta):=\sum_{h\in[q]^j}\Phi\bigl(Y(\sigma(h)\alpha),Y(\sigma(h)\beta)\bigr).$$
--   Its **source** is $Z_j(\alpha',\beta')=\sum_{h\in[q]^j}\Phi(y_{h\alpha'},y_{h\beta'})$.
--
--   **Formalization Note** Levels are indexed by the number $n=m-j$ of remaining axes.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), Definition 3.16, p.14; Lemma 3.17(a), p.14

import Definitions.Def_TimeSpaceMA_tensorEncode

namespace TimeSpaceMA

variable {m : ℕ}

/-- `σ(h)α`: the tuple `h` on the first `m − n` positions and `α` on the last `n`; p.14. -/
def prefixed {n : ℕ} {X : Type*} (hn : n ≤ m) (h : Fin (m - n) → X) (α : Fin n → X) : Fin m → X :=
  fun i => if hi : i.val < m - n then h ⟨i.val, hi⟩ else α ⟨i.val - (m - n), by omega⟩

/-- The honest table of level `j = m − n` on `α, β ∈ [L]^n` (Williams, Xi, STOC 2027 submission,
manuscript sha256 184c2f95…, Definition 3.16, p.14):
`R_j(α, β) := Σ_{h ∈ [q]^j} Φ(Y(σ(h)α), Y(σ(h)β))`.

**Formalization Note** The level is indexed by the number `n = m − j` of remaining axes, so that the
trace identity needs no cast between `Fin (m − j)` and `Fin (m − (j − 1))`. -/
def honestTable {q L : ℕ} {V : Type*} [AddCommGroup V] (σ : Fin q → Fin L)
    (Y : (Fin m → Fin L) → V) (Φ : V →ₗ[ℤ] V →ₗ[ℤ] ℤ) (n : ℕ) (hn : n ≤ m)
    (α β : Fin n → Fin L) : ℤ :=
  ∑ h : Fin (m - n) → Fin q, Φ (Y (prefixed hn (σ ∘ h) α)) (Y (prefixed hn (σ ∘ h) β))

/-- The source `Z_j(α′, β′) = Σ_{h ∈ [q]^j} Φ(y_{hα′}, y_{hβ′})` of the honest table; Lemma 3.17(a),
p.14. Same indexing: `n = m − j`. -/
def honestSource {q : ℕ} {V : Type*} [AddCommGroup V] (y : (Fin m → Fin q) → V)
    (Φ : V →ₗ[ℤ] V →ₗ[ℤ] ℤ) (n : ℕ) (hn : n ≤ m) (α' β' : Fin n → Fin q) : ℤ :=
  ∑ h : Fin (m - n) → Fin q, Φ (y (prefixed hn h α')) (y (prefixed hn h β'))

end TimeSpaceMA


