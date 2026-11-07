-- Prove2me | Definitions.Def_QuantumPRC_IsPolyFamily
-- name    : QuantumPRC_IsPolyFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:11.177197+00:00
-- url     : https://prove2.me/theorems/46317965-8ec6-4542-8f99-6ce225e0bd72
-- title:
--   Bit strings, unary codes, efficient polynomial lengths and polynomial-time families
-- statement:
--   Bit strings of length $n$ are $\{0,1\}^n$ (Lean: `Fin n → Bool`, `true` is the bit $1$). The unary string $1^n$ is `unary n`, and `tupleCode` is a fixed self-delimiting, injective code for a tuple of bit strings (every bit doubled, every field closed by $01$).
--
--   1. A length function $f:\mathbb N\to\mathbb N$ is **polynomially bounded** if $f(n)\le n^k+k$ for some $k$.
--   2. $f$ is an **efficient polynomial length** (`EffPoly`) if it is polynomially bounded and $1^\lambda\mapsto 1^{f(\lambda)}$ is computable in polynomial time. The paper's "let $n_{\mathrm L},n_{\mathrm P}$ be polynomials" is read with this notion: every integer-valued polynomial is such a length, and Appendix B (Definition B.10) already uses polynomially bounded functions.
--   3. A family of maps $F_\lambda:\alpha_\lambda\to\beta_\lambda$ is a **deterministic polynomial-time family** (`IsPolyFamily`) if a single polynomial-time Turing machine maps the code of $(1^\lambda, a)$ to the code of $F_\lambda(a)$, for all $\lambda$ and $a$. A **PPT algorithm** is such a family whose last input is a uniformly random coin string of polynomial length.
--
--   These are the conventions for every classical algorithm of the paper (KeyGen, Enc, Dec of PRCs and PRFCs, PRFs, PRPs, GraphSample and Recover).
--
--   **Formalization Note** The machine model is the published `CookPvsNP.PolyTimeComputable` (a one-tape Turing machine halting within $|x|^k+k$ steps).
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), §3.1, p.16 (PPT, A(x; r)); Corollary 7.5, p.42 and §4, p.24 (polynomials); Definition B.10, p.86

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace QuantumPRC

/-- Bit strings of length `n`, `{0,1}^n` (arXiv:2609.38986, §3.1, p.15); also the computational
basis of `n` qubits. `true` is the bit `1`. -/
abbrev Bits (n : ℕ) : Type := Fin n → Bool

/-- A bit string of length `n` written as a list, first bit first. -/
def bits {n : ℕ} (x : Bits n) : List Bool := List.ofFn x

/-- The unary string `1^n`. -/
def unary (n : ℕ) : List Bool := List.replicate n true

/-- A self-delimiting code for a tuple of bit strings: every bit is doubled and every field is
closed by `01`. It is injective, and the tuple is recovered in linear time. -/
def tupleCode (ls : List (List Bool)) : List Bool :=
  ls.flatMap fun l => l.flatMap (fun b => [b, b]) ++ [false, true]

/-- `f` is polynomially bounded: `f n ≤ n^k + k` for some `k`. -/
def PolyBounded (f : ℕ → ℕ) : Prop :=
  ∃ k : ℕ, ∀ n, f n ≤ n ^ k + k

/-- **Efficient polynomial length.** Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…). The paper
writes "Let `nL, nP : ℕ → ℕ` be polynomials" (Corollary 7.5, p.42; §4, p.24; Definitions 3.17–3.24,
6.1). We use: `f` is polynomially bounded and `1^λ ↦ 1^{f(λ)}` is computable in polynomial time.

**Formalization Note.** Every integer-valued polynomial `ℕ → ℕ` has this property, so a statement
over `EffPoly` lengths contains the printed one; Appendix B (Definition B.10, p.86) already uses
"polynomially bounded functions". The machine model is `CookPvsNP.PolyTimeComputable` (one-tape
Turing machine, time `|x|^k + k`). -/
def EffPoly (f : ℕ → ℕ) : Prop :=
  PolyBounded f ∧ CookPvsNP.PolyTimeComputable (fun x : List Bool => unary (f x.length))

/-- **Deterministic polynomial-time family.** `F λ : α λ → β λ` is computed by one polynomial-time
machine that reads `tupleCode (1^λ :: ci λ a)` and writes `co λ (F λ a)`.

This is how every classical algorithm of arXiv:2609.38986 is modelled: a deterministic algorithm
is such a family, and a PPT algorithm is such a family whose last input is a uniformly random coin
string of polynomial length (§3.1, p.16: "`A(x; r)` denotes the output of `A` on input `x` with
internal randomness `r`").

**Formalization Note.** The input codes `ci` are chosen per use and are always injective
(`tupleCode` of `bits`/`unary`/key codes). The security parameter is passed in unary. -/
def IsPolyFamily {α β : ℕ → Type*} (F : ∀ lam, α lam → β lam)
    (ci : ∀ lam, α lam → List (List Bool)) (co : ∀ lam, β lam → List Bool) : Prop :=
  ∃ f : List Bool → List Bool, CookPvsNP.PolyTimeComputable f ∧
    ∀ lam a, f (tupleCode (unary lam :: ci lam a)) = co lam (F lam a)

end QuantumPRC


