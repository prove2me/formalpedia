-- Prove2me | Definitions.Def_ShamirLLR_evalTuples
-- name    : ShamirLLR_evalTuples
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:25:56.367218+00:00
-- url     : https://prove2.me/theorems/60bc277e-320f-485f-9eb2-343cde464aec
-- title:
--   Evaluation tuples $\mathcal A_{p,m}$ and the average $\mathbb E_a$
-- statement:
--   Let $p$ be a prime and $m\ge 1$. The set of **evaluation tuples** is
--   $$
--   \mathcal A_{p,m}=\{(a_1,\dots,a_m)\in(\mathbb F_p^{*})^m:\ a_i\neq a_j\text{ whenever } i\neq j\},
--   $$
--   the ordered $m$-tuples of distinct nonzero public evaluation places of Shamir sharing. It carries the uniform distribution, and $\mathbb E_a\,\varphi(a)=|\mathcal A_{p,m}|^{-1}\sum_{a\in\mathcal A_{p,m}}\varphi(a)$ denotes the average over it.
--
--   Every bound of the mission averages a worst-case insecurity over the public places with this average.
--
--   **Formalization Note** $\mathbb F_p$ is `ZMod p` and a tuple is a function `Fin m → ZMod p`. The average is $0$ when $\mathcal A_{p,m}$ is empty ($m>p-1$); every statement using it forces $p>m$.
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), p.2 and §6.1, p.39 (PDF pp.3, 40)

import Mathlib

set_option autoImplicit false

namespace ShamirLLR

/-- The set `A_{p,m}` of ordered `m`-tuples of distinct nonzero evaluation places in `𝔽_p`.

Source: J. Hwang, H. K. Maji, I. D. Shkredov, X. Ye, *Local Leakage Resilience of
Multiplication-friendly Shamir Secret Sharing*, manuscript of 2 Nov 2026 (held version, sha256
fcd6871f…), p.2 ("Averages over a use uniform ordered tuples of m distinct nonzero field
elements") and §6.1, p.39: `A_{p,m} = {(a₁, …, a_m) ∈ (𝔽_p^*)^m : a_i ≠ a_j whenever i ≠ j}`.

**Formalization Note.** `𝔽_p` is `ZMod p`; a tuple is a function `Fin m → ZMod p`. -/
def evalTuples (p m : ℕ) [NeZero p] : Finset (Fin m → ZMod p) :=
  open Classical in
  Finset.univ.filter (fun a => (∀ i, a i ≠ 0) ∧ Function.Injective a)

/-- The uniform average `𝔼_{a ∈ A_{p,m}} φ(a)` over evaluation tuples (p.2, p.39: `A_{p,m}` "is
equipped with the uniform distribution").

**Formalization Note.** The average is `(∑_{a ∈ A_{p,m}} φ a) / |A_{p,m}|`; it is `0` when
`A_{p,m}` is empty (`p − 1 < m`). Every statement using it forces `p > m` through its
hypotheses. -/
noncomputable def avgTuples (p m : ℕ) [NeZero p] (φ : (Fin m → ZMod p) → ℝ) : ℝ :=
  (∑ a ∈ evalTuples p m, φ a) / ((evalTuples p m).card : ℝ)

end ShamirLLR


