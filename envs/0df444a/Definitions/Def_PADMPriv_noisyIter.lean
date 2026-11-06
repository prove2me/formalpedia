-- Prove2me | Definitions.Def_PADMPriv_noisyIter
-- name    : PADMPriv_noisyIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:36.950999+00:00
-- url     : https://prove2.me/theorems/c4772fdc-bddc-4f19-8f8e-623b1c0f6184
-- title:
--   Noisy iteration $\tilde u_{(k)}=T_k(\tilde u_{(k-1)})+w_{(k)}$
-- statement:
--   Given operators $T_1,\dots,T_n:\mathbb R^m\to\mathbb R^m$, an initial point $u_0$ and noise vectors $w_{(1)},\dots,w_{(n)}$, the **noisy iteration** is
--   $$
--   \tilde u_{(0)} = u_0,\qquad \tilde u_{(k)} = T_k(\tilde u_{(k-1)}) + w_{(k)},\quad k=1,\dots,n.
--   $$
--   It is the scheme of Lemma A6 (privacy amplification by iteration) and, with $T_k = T_{f_k}$ and $w_{(k)} = z_{(k)}/2$, the private PADM update (20).
--
--   **Formalization Note** Operators and noise vectors are indexed by $\{0,\dots,n-1\}$; steps beyond $n$ repeat the last iterate and are never used.
-- source:
--   Li–Lai–Weng, Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization, STOC 2027 submission (manuscript sha256 d58edbe0…0f3d), Lemma A6, p.24; Eq. (20), p.8

import Mathlib

namespace PADMPriv

/-- The noisy iteration `ũ₍₀₎ = u₀`, `ũ₍ₖ₎ = T_k(ũ₍ₖ₋₁₎) + w₍ₖ₎` (`k = 1, …, n`) of
Li–Lai–Weng, *Exact Feasibility and Privacy Amplification for Linearly Constrained Optimization*, STOC 2027 submission manuscript (sha256 d58edbe0…0f3d), Lemma A6, p.24, and of the private PADM update (20), p.8.

**Formalization Note** The operators and the noise vectors are `Fin n`-indexed: step `k + 1`
of the paper uses `T ⟨k, _⟩` and `w ⟨k, _⟩`. Steps beyond `n` repeat the last iterate (junk,
never used). -/
noncomputable def noisyIter {m n : ℕ}
    (T : Fin n → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (u₀ : EuclideanSpace ℝ (Fin m)) (w : Fin n → EuclideanSpace ℝ (Fin m)) :
    ℕ → EuclideanSpace ℝ (Fin m)
  | 0 => u₀
  | k + 1 => if h : k < n then T ⟨k, h⟩ (noisyIter T u₀ w k) + w ⟨k, h⟩ else noisyIter T u₀ w k

end PADMPriv


