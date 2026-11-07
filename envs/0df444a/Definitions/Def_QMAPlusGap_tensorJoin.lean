-- Prove2me | Definitions.Def_QMAPlusGap_tensorJoin
-- name    : QMAPlusGap_tensorJoin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:37.627461+00:00
-- url     : https://prove2.me/theorems/facdcfa2-8452-4884-8ebb-fe0f65129768
-- title:
--   Tensor product $X\otimes Y$ on $n_1+n_2$ registers
-- statement:
--   For an operator $X$ on $\mathcal H^{\otimes n_1}$ and $Y$ on $\mathcal H^{\otimes n_2}$, the operator $X\otimes Y$ on $\mathcal H^{\otimes(n_1+n_2)}$ acts as $X$ on the first $n_1$ registers and as $Y$ on the last $n_2$:
--   $$
--   \langle a\,a'|X\otimes Y|b\,b'\rangle=\langle a|X|b\rangle\langle a'|Y|b'\rangle .
--   $$
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 11 (9), p.20; Proposition 9 (5), p.15

import Mathlib

set_option autoImplicit false

namespace QMAPlusGap

/-- The **tensor product `X ⊗ Y`** of an operator `X` on `n₁` registers and `Y` on `n₂` registers, as an
operator on `n₁ + n₂` registers (`X` on the first `n₁`), Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 11 (9), p.20 and Proposition 9 (5), p.15
(`ρ_N^{(1)} ⊗ ρ_N^{(2)}` on `2N` registers). -/
def tensorJoin {ι : Type} {n₁ n₂ : ℕ} (X : Matrix (Fin n₁ → ι) (Fin n₁ → ι) ℂ)
    (Y : Matrix (Fin n₂ → ι) (Fin n₂ → ι) ℂ) : Matrix (Fin (n₁ + n₂) → ι) (Fin (n₁ + n₂) → ι) ℂ :=
  Matrix.of fun a b =>
    X (fun i => a (Fin.castAdd n₂ i)) (fun i => b (Fin.castAdd n₂ i)) *
      Y (fun i => a (Fin.natAdd n₁ i)) (fun i => b (Fin.natAdd n₁ i))

end QMAPlusGap


