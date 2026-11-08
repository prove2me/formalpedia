-- Prove2me | Definitions.Def_WICanon_DistAIOWF
-- name    : WICanon_DistAIOWF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:23.87477+00:00
-- url     : https://prove2.me/theorems/ae354da1-a65e-4008-9673-617065a0f5b0
-- title:
--   Distributional auxiliary-input one-way functions
-- statement:
--   A family $\{f_a\}$ is a **distributional auxiliary-input one-way function** if there is a constant $c>0$ such that for every PPT $\mathcal A$ and every $n$, some index $a$ has
--
--   $$\mathrm{SD}\bigl((\mathcal A(a,f_a(X)),f_a(X)),(X,f_a(X))\bigr)\ge\frac1{n^c},$$
--
--   with $X$ uniform on $\{0,1\}^{m(n)}$. It is **infinitely-often** distributional if for every $\mathcal A$ this holds for infinitely many $n$.
--
--   **Formalization Note** Three readings. (1) The index set is a parameter `valid`, since Theorem 3.1 and Lemma 3.10 define $f_a$ only for $a=(x,w_0,w_1)$ with both pairs in $\mathcal R$. (2) The codomain is free: Theorem 3.1's family outputs transcript prefixes of varying length, and Theorem 3.7's has codomain $\{0,1\}^{\ell(n)}$. (3) The non-io form is for all sufficiently large $n$: at $n=1$ the printed bound is $\mathrm{SD}\ge 1$, which a finite table defeats for every family, so "for every $n$" would be empty.
-- source:
--   Arnon, Mazor, Pass, Silbak, Does Witness Indistinguishability Require Cryptography?, STOC 2027 submission manuscript (sha256 3f78ec3d…), Definition 2.6, p.12

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_WICanon_Law

set_option autoImplicit false

namespace WICanon

open QAlgorithms.Complexity QiOPoQ

/-- The law of `(A(a, f_a(X)), f_a(X))` for `X ← {0,1}^{m(n)}` (Arnon, Mazor, Pass, Silbak, STOC 2027
submission manuscript, sha256 3f78ec3d…, Definition 2.6, p.12). `A` also receives `1^n`. -/
noncomputable def inverterLaw (m : ℕ → ℕ) (f : ℕ → Str → Str → Str) (A : UPPT) (n : ℕ) (a : Str) :
    Law :=
  bindLaw (coinLaw (m n) id) fun x =>
    let y := f n a x
    let inp := pair (unary n) (pair a y)
    mapLaw (fun o => pair o y) (coinLaw (A.coins.eval inp.length) fun r => A.run (pair inp r))

/-- The law of `(X, f_a(X))` for `X ← {0,1}^{m(n)}` (Definition 2.6, p.12). -/
noncomputable def preimageLaw (m : ℕ → ℕ) (f : ℕ → Str → Str → Str) (n : ℕ) (a : Str) : Law :=
  coinLaw (m n) fun x => pair x (f n a x)

/-- **Distributional auxiliary-input one-way function** (Definition 2.6, p.12): there is a constant
`c > 0` such that for every PPT `A` and every `n` some valid `a` has
`SD((A(a, f_a(X)), f_a(X)), (X, f_a(X))) ≥ 1/n^c`.

**Formalization Note.** (1) Index set: Theorem 3.1 and Lemma 3.10 define `f_a` only for
`a = (x, w_0, w_1)` with both pairs in `R`, so `valid` is a parameter, and "there exists some a" means a
valid one. (2) Codomain: printed `{0,1}^{m(n)}`, but Theorem 3.1's family outputs a transcript prefix of
varying length and Theorem 3.7's has `{0,1}^{ℓ(n)}`, so the codomain is free. (3) "For every n" with
`ε = 1/n^c` fails at `n = 1` for every family, since a finite table in the control of a PPT machine
outputs a preimage for every `a` of that length; the printed form would be empty, and Theorem 2.7's
hypothesis with it. The reading here is "for all sufficiently large n". -/
def IsDistAIOWF (valid : ℕ → Str → Prop) (m : ℕ → ℕ) (f : ℕ → Str → Str → Str) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ A : UPPT, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ a, valid n a ∧
    (n : ℝ) ^ (-c) ≤ SD (inverterLaw m f A n a) (preimageLaw m f n a)

/-- **Infinitely-often distributional auxiliary-input one-way function** (Definition 2.6, p.12): "for
every A the above holds for infinitely many n ∈ N". The constant `c` comes first; the negation, the form
every proof uses, is: for each `c` there is an `A` with `SD < 1/n^c` for all large `n` and all valid `a`. -/
def IsIODistAIOWF (valid : ℕ → Str → Prop) (m : ℕ → ℕ) (f : ℕ → Str → Str → Str) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ A : UPPT, ∀ n₀ : ℕ, ∃ n ≥ n₀, ∃ a, valid n a ∧
    (n : ℝ) ^ (-c) ≤ SD (inverterLaw m f A n a) (preimageLaw m f n a)

end WICanon


