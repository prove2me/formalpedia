-- Prove2me | Definitions.Def_MultAddExt_Multiplicative_Hardness
-- name    : MultAddExt_Multiplicative_Hardness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:47:44.871563+00:00
-- url     : https://prove2.me/theorems/ab7dd593-7900-4cbd-996d-09be8e6bf174
-- title:
--   Explicitness, the class E and the nondeterministic hardness assumption H_NP (Assumption 4.10)
-- statement:
--   **Explicitness.** A function $f:\{0,1\}^*\to\{0,1\}^*$ is **polynomial-time computable** if a single deterministic Turing machine (Mathlib's bundled multi-stack machine `Turing.FinTM2`, alphabet $\{0,1\}$) outputs $f(x)$ within $P(|x|)$ steps for a fixed polynomial $P$. A family of functions on $\{0,1\}^n$ is explicit when it is the restriction of one such $f$ to inputs of length $n$; functions of several arguments or parameters receive them through the pairing $\langle u,v\rangle$ (the bits of $u$ doubled, then $01$, then $v$) and parameters $k$ in unary $1^k$.
--
--   **The class E** is $\bigcup_{c} \mathrm{DTIME}(2^{cn})$: $f:\{0,1\}^*\to\{0,1\}$ is in E if some Turing machine decides it within $2^{c(|x|+1)}$ steps for a constant $c$.
--
--   **Assumption 4.10 ($H_{NP}$).** There are $f\in\mathrm E$ and $\beta_{\mathrm{hard}}>0$ such that, for every sufficiently large $\ell$, no nondeterministic circuit of size at most $2^{\beta_{\mathrm{hard}}\ell}$ computes $f$ on all of $\{0,1\}^\ell$:
--   $$\exists f\in \mathrm E,\ \exists \beta_{\mathrm{hard}}>0,\ \exists \ell_0,\ \forall \ell\ge \ell_0,\ \forall C,\ \ \mathrm{size}(C)\le 2^{\beta_{\mathrm{hard}}\ell}\implies \exists x\in\{0,1\}^\ell:\ C(x)\ne f(x).$$
--   When it holds, E is hard for exponential-size nondeterministic circuits. It is the only assumption of the mission's conditional results.
--
--   **Formalization Note** The bound $2^{c(|x|+1)}$ instead of $2^{c|x|}$ gives the same union over $c$, which also absorbs the polynomial overhead between the stack machine and multi-tape machines.
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), §4.2.2, p. 20 (PDF 24), Assumption 4.10; explicitness as used in Theorems 4.41–4.43, pp. 27–28 (PDF 31–32)

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_NondetCircuit

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-! # Explicitness, the class E and the hardness assumption H_NP (Assumption 4.10)

Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, *Multiplicative and Additive Extractors for Low
Entropy Samplable Sources Under Reduced Assumptions*, STOC 2027 submission (manuscript sha256
5ac077d7…), §4.2.2, p. 20 (PDF 24).

Machines are Mathlib's bundled multi-stack Turing machines (`Turing.FinTM2`) over the alphabet
`Bool`, with Mathlib's step count. -/

/-- `f : {0,1}* → {0,1}*` is computable by one deterministic Turing machine in polynomial time. -/
def PolyTimeComputable (f : List Bool → List Bool) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
    (id : List Bool → List Bool) f)

/-- `f ∈ E = ⋃_{c} DTIME(2^{cn})`: some Turing machine decides `f` within `2^{c(|x|+1)}` steps. -/
def InE (f : List Bool → Bool) : Prop :=
  ∃ c : ℕ, ∃ M : Turing.TM2ComputableInTime (id : List Bool → List Bool)
    (fun b : Bool => [b]) f, ∀ ℓ : ℕ, M.time ℓ ≤ 2 ^ (c * (ℓ + 1))

/-- **Assumption 4.10 (H_NP)**: there are `f ∈ E` and `β_hard > 0` such that for every sufficiently
large `ℓ`, no nondeterministic circuit of size at most `2^{β_hard ℓ}` computes `f` on `{0,1}^ℓ`. -/
def HNP : Prop :=
  ∃ f : List Bool → Bool, InE f ∧ ∃ βhard : ℝ, 0 < βhard ∧ ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
    ∀ C : NondetCirc ℓ, (C.size : ℝ) ≤ (2 : ℝ) ^ (βhard * ℓ) →
      ¬ ∀ x : Fin ℓ → Bool, (C.accepts x ↔ f (List.ofFn x) = true)

/-- The unary code `1^k` of a parameter `k`. -/
def unary (k : ℕ) : List Bool := List.replicate k true

/-- The self-delimiting pairing of two strings: the bits of `u` doubled, then `01`, then `v`. It is
injective and decodable in linear time; it is how a machine receives several arguments. -/
def pairEnc (u v : List Bool) : List Bool :=
  u.flatMap (fun b => [b, b]) ++ [false, true] ++ v

end MultAddExt.Multiplicative


