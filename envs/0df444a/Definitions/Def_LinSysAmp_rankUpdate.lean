-- Prove2me | Definitions.Def_LinSysAmp_rankUpdate
-- name    : LinSysAmp_rankUpdate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:36.588189+00:00
-- url     : https://prove2.me/theorems/8abdeb8c-ee48-4695-87aa-dc06c05327d6
-- title:
--   Invertible updates of rank $k$: the distribution, $e_k$ and the operator $K_k$
-- statement:
--   Let $1\le k\le n$. An **invertible update of rank $k$** is sampled as follows: draw $U,V$ uniformly and independently from $F^{n\times k}$; if $\det(I_k+V^\top U)\ne0$ output $R=I_n+UV^\top$, and otherwise output $\bot$.
--
--   1. $e_k$ is the probability of outputting $\bot$. It depends on $n$, $k$ and $F$ only.
--   2. $K_k$ is the Markov operator on $\mathrm{GL}_n(F)$ moving from $M$ to $RM$, where $R$ is an invertible update of rank $k$ conditioned on $R\ne\bot$:
--   $$
--   K_k(M,M')=\frac{\Pr[R\ne\bot\ \text{and}\ RM=M']}{1-e_k}.
--   $$
--
--   These are the objects that re-randomize the matrix of a linear system at low cost, since $RM=M+U(V^\top M)$.
--
--   **Formalization Note** $\bot$ is `none`. The objects are defined for all $n,k$, and the statements about them assume $1\le k\le n$. The division is Lean's, with $x/0=0$, but $1-e_k>1/4$ in the stated range (Lemma 4.5, item 2), so $K_k$ is the printed conditional probability there.
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Definition 4.4, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_LinSysAmp_lineqSuccess

set_option autoImplicit false

open Matrix

namespace LinSysAmp

/-!
# Invertible updates of rank `k` (Definition 4.4)

G. Couteau, N. Melissaris, T. Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and
Fine-Grained Cryptography*, arXiv:2611.04680 (version held, sha256 af7a90ac…), Definition 4.4, p.18
(PDF p.20): "Let 1 ≤ k ≤ n. An invertible update of rank k is sampled as follows. Sample
U, V ← F_q^{n×k}. If det(I_k + V⊤U) ≠ 0, output R = I_n + UV⊤, and otherwise output ⊥. We denote by
e_k the probability of outputting ⊥, and by K_k the Markov operator on GL_n(F_q) which moves from M to
RM, where R is an invertible update of rank k conditioned on R ≠ ⊥."

**Formalization Note.** `⊥` is `none`. The objects are defined for all `n, k`; the statements about
them assume `1 ≤ k ≤ n`, as Definition 4.4 does. `e_k` has no `M` argument (it depends on `U, V`
only). `K_k(M, M') = Pr[R ≠ ⊥ ∧ RM = M'] / (1 − e_k)` is the **conditioned** kernel on
`GL_n(F) = InvMat n F`; the division is Lean's (`x / 0 = 0`), and `1 − e_k > 0` for `1 ≤ k`
(Lemma 4.5(2)), so it is the printed conditional probability in the stated range.
-/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- An invertible update of rank `k`: `U, V` uniform in `F^{n×k}`; output `some (I + UV⊤)` if
`det(I_k + V⊤U) ≠ 0`, else `none` (`⊥`).
(arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 4.4, p.18 (PDF p.20).) -/
noncomputable def updateDist (n k : ℕ) (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    PMF (Option (Matrix (Fin n) (Fin n) F)) :=
  (PMF.uniformOfFintype (Matrix (Fin n) (Fin k) F)).bind fun U =>
    (PMF.uniformOfFintype (Matrix (Fin n) (Fin k) F)).bind fun V =>
      PMF.pure (if (1 + Vᵀ * U).det ≠ 0 then some (1 + U * Vᵀ) else none)

/-- `e_k`: the probability that an invertible update of rank `k` outputs `⊥`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 4.4, p.18 (PDF p.20).) -/
noncomputable def ek (n k : ℕ) (F : Type*) [Field F] [Fintype F] [DecidableEq F] : ℝ :=
  (updateDist n k F none).toReal

/-- The Markov operator `K_k` on `GL_n(F)`: `K_k(M, M') = Pr[R ≠ ⊥ ∧ RM = M'] / (1 − e_k)`.
(arXiv:2611.04680, version held, sha256 af7a90ac…, Definition 4.4, p.18 (PDF p.20).) -/
noncomputable def Kk (n k : ℕ) (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (M M' : InvMat n F) : ℝ :=
  (((updateDist n k F).map fun o => o.map fun R => R * M.1) (some M'.1)).toReal / (1 - ek n k F)

end LinSysAmp


