-- Prove2me | Definitions.Def_WICanon_AIOWF
-- name    : WICanon_AIOWF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:00:47.983789+00:00
-- url     : https://prove2.me/theorems/f372d469-e359-4184-a353-6e5e725da5d7
-- title:
--   Auxiliary-input one-way functions, and their infinitely-often form
-- statement:
--   An efficiently computable family $\{f_a:\{0,1\}^{m(n)}\to\{0,1\}^{m(n)}\}_{a\in\{0,1\}^{\lambda(n)}}$ is an **auxiliary-input one-way function** if for every PPT $\mathcal A$ there is a negligible $\mu$ such that for every $n$ there is some $a\in\{0,1\}^{\lambda(n)}$ with
--
--   $$\Pr_{x\leftarrow\{0,1\}^{m(n)}}\bigl[\mathcal A(a,f_a(x))\in f_a^{-1}(f_a(x))\bigr]\le\mu(n).$$
--
--   It is an **infinitely-often** AI-OWF if for every $\mathcal A$ the above holds for infinitely many $n$. The order of quantifiers is the point: the hard index $a$ may depend on $\mathcal A$ and $n$. With $a$ fixed in advance this would be a standard one-way function, which the paper leaves open.
--
--   **Formalization Note** $\mathcal A$ also receives $1^n$, so its running time is polynomial in $n$ whatever $\lambda(n)+m(n)$ is. The machine evaluating the family is given $1^n$ too; if $\lambda,m$ are both constant the family is trivially invertible, and otherwise $n$ is polynomially readable from the lengths. Success requires a string of length exactly $m(n)$.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Definition 2.5, p.12

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_OWFLocalDesc_Negligible

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity QiOPoQ OWFLocalDesc

/-- An efficiently computable function family on the index set `valid`: one polynomial-time machine
`g` with `f_a^{(n)}(x) = g(1^n, a, x)` for each valid index `a` at parameter `n` and each
`x ∈ {0,1}^{m(n)}`. -/
def EfficientOn (valid : ℕ → Str → Prop) (m : ℕ → ℕ) (f : ℕ → Str → Str → Str) : Prop :=
  ∃ g : Str → Str, PolyTimeComputable g ∧ ∀ n a x, valid n a → x.length = m n →
    g (pair (unary n) (pair a x)) = f n a x

/-- `Pr_{x←{0,1}^{m(n)}}[A(a, f_a(x)) ∈ f_a^{−1}(f_a(x))]` (Arnon, Mazor, Pass, Silbak, *Does Witness
Indistinguishability Require Cryptography?*, STOC 2027 submission manuscript, sha256 3f78ec3d…,
Definition 2.5, eq. (8), p.12). Success means a string of length `m(n)` with the right image.

**Formalization Note.** `A` also receives `1^n`, so its time is polynomial in `n` even when
`λ(n) + m(n)` is small. -/
noncomputable def invProb (m : ℕ → ℕ) (f : ℕ → Str → Str → Str) (A : UPPT) (n : ℕ) (a : Str) : ℝ :=
  avgCoins (m n) fun x =>
    A.expect (pair (unary n) (pair a (f n a x))) fun o =>
      if o.length = m n ∧ f n a o = f n a x then 1 else 0

/-- The shape of Definition 2.5, p.12: an efficiently computable family `{f_a : {0,1}^{m(n)} →
{0,1}^{m(n)}}_{a∈{0,1}^{λ(n)}}` with `λ`, `m` polynomial. -/
def IsLengthPreservingFamily (lam m : Polynomial ℕ) (f : ℕ → Str → Str → Str) : Prop :=
  EfficientOn (fun n a => a.length = lam.eval n) m.eval f ∧
    ∀ n a x, a.length = lam.eval n → x.length = m.eval n → (f n a x).length = m.eval n

/-- **Auxiliary-input one-way functions exist** (Definition 2.5, p.12): for every PPT `A` there is a
negligible `μ` such that for every `n` there is an `a` with inversion probability at most `μ(n)`.

**Formalization Note.** `a` comes after `A` and `n`, and `μ` before `n`. With `a` chosen before `A`,
or absent, this would be standard one-way functions, which the paper leaves open. -/
def AIOWFExist : Prop :=
  ∃ (lam m : Polynomial ℕ) (f : ℕ → Str → Str → Str), IsLengthPreservingFamily lam m f ∧
    ∀ A : UPPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n, ∃ a, a.length = lam.eval n ∧
      invProb m.eval f A n a ≤ μ n

/-- **Infinitely-often auxiliary-input one-way functions exist** (Definition 2.5, p.12): "for every
A the above holds for infinitely many n ∈ N". -/
def IOAIOWFExist : Prop :=
  ∃ (lam m : Polynomial ℕ) (f : ℕ → Str → Str → Str), IsLengthPreservingFamily lam m f ∧
    ∀ A : UPPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n₀, ∃ n ≥ n₀, ∃ a, a.length = lam.eval n ∧
      invProb m.eval f A n a ≤ μ n

end WICanon


