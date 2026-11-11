-- Prove2me | Definitions.Def_LindbladShallow_extendPriv
-- name    : LindbladShallow_extendPriv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:10:27.88624+00:00
-- url     : https://prove2.me/theorems/e78d108a-f33c-4f87-905a-4c13aee292e2
-- title:
--   Extension of an operator on public ⊕ one private space by the identity on the other private spaces
-- statement:
--   Let $\mathcal H$ be a public space and $\mathcal L_1,\dots,\mathcal L_L$ mutually orthogonal private spaces. An operator $S_j$ on $\mathcal H\oplus\mathcal L_j$ is extended to $\mathcal H\oplus\bigoplus_k\mathcal L_k$ by acting as $S_j$ on $\mathcal H\oplus\mathcal L_j$ and as the identity on every $\mathcal L_k$, $k\ne j$.
--
--   This is the extension used in Lemma 4.2 (sequential composition of transducers).
-- source:
--   Shen, Wu, Yuan, Zhang, Shallow Quantum Circuits for Geometrically Local Lindblad Dynamics, arXiv:2610.05362 (held version, sha256 8f4637ef…), Lemma 4.2, p.26

import Mathlib

open scoped Matrix

namespace LindbladShallow

/-- Extension of an operator `S_j` on `ℋ ⊕ 𝓛_j` to `ℋ ⊕ ⨁_k 𝓛_k` by the identity on all other
private spaces `𝓛_k`, `k ≠ j` (arXiv:2610.05362, held version sha256 8f4637ef…, Lemma 4.2,
p.26). The private spaces are the summands of a sigma type, hence mutually orthogonal. -/
def extendPriv {ι : Type*} {L : ℕ} {κ : Fin L → Type*} [∀ k, DecidableEq (κ k)] (j : Fin L)
    (S : Matrix (ι ⊕ κ j) (ι ⊕ κ j) ℂ) : Matrix (ι ⊕ Σ k, κ k) (ι ⊕ Σ k, κ k) ℂ :=
  fun p q =>
    match p, q with
    | .inl a, .inl b => S (.inl a) (.inl b)
    | .inl a, .inr ⟨k, y⟩ => if h : k = j then S (.inl a) (.inr (h ▸ y)) else 0
    | .inr ⟨k, x⟩, .inl b => if h : k = j then S (.inr (h ▸ x)) (.inl b) else 0
    | .inr ⟨k, x⟩, .inr ⟨k', y⟩ =>
      if h : k = j ∧ k' = j then S (.inr (h.1 ▸ x)) (.inr (h.2 ▸ y))
      else if k = j ∨ k' = j then 0
      else if h' : k = k' then (if h' ▸ x = y then 1 else 0) else 0

end LindbladShallow


