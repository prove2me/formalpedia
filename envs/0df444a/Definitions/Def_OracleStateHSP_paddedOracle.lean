-- Prove2me | Definitions.Def_OracleStateHSP_paddedOracle
-- name    : OracleStateHSP_paddedOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:29:54.447001+00:00
-- url     : https://prove2.me/theorems/e898ee13-d5dd-42ef-a48b-eacb8640131d
-- title:
--   Padded Simon oracle $O_{\tilde f}$ (eq. (52))
-- statement:
--   For $f : V \to V$ let $\tilde f : G = K \oplus V \to V$, $\tilde f(k, v) = f(v)$. The **Padded Simon oracle** is the unitary
--   $$
--   O_{\tilde f}\, |k\rangle_r |v\rangle_m |b\rangle_m = |k\rangle_r |v\rangle_m |b + f(v)\rangle_m ,
--   $$
--   the permutation matrix of $((k, v), b) \mapsto ((k, v), b + f(v))$. At $r = 0$ it is Simon's oracle $O_f|x\rangle|b\rangle = |x\rangle|b + f(x)\rangle$ of §4.2.1.
--
--   **Formalization Note** It is the published standard XOR oracle `QAlgorithms.xorOracle` of $\tilde f$. $G = \mathbb Z_2^n$ is encoded as $\mathbb Z_2^r \times \mathbb Z_2^m$ with $n = r + m$.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 4.8, eq. (52), p.37

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OracleStateHSP_V
import Definitions.Def_OracleStateHSP_K

namespace OracleStateHSP

/-- The Padded Simon oracle `O_f̃` (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Definition 4.8, eq. (52), p.37): for `f̃(k, v) = f(v)`
on `G = K ⊕ V`, `O_f̃ |k⟩_r |v⟩_m |b⟩_m = |k⟩_r |v⟩_m |b + f(v)⟩_m`. It is the standard XOR oracle
`QAlgorithms.xorOracle` of `f̃`, the permutation matrix of `((k, v), b) ↦ ((k, v), b + f(v))`.
At `r = 0` it is Simon's oracle `O_f` (p.36) up to the trivial factor `Z_2^0`.

**Formalization Note.** `Z_2^n` is encoded as `Z_2^r × Z_2^m` with `n = r + m`. -/
noncomputable def paddedOracle (r : ℕ) {m : ℕ} (f : V m → V m) :
    Matrix ((K r × V m) × V m) ((K r × V m) × V m) ℂ :=
  QAlgorithms.xorOracle (fun g : K r × V m => f g.2)

end OracleStateHSP


