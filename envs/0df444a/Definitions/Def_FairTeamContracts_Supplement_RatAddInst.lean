-- Prove2me | Definitions.Def_FairTeamContracts_Supplement_RatAddInst
-- name    : FairTeamContracts_Supplement_RatAddInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:08:21.3472+00:00
-- url     : https://prove2.me/theorems/6fe6f9c8-cec3-432d-82ee-46c31d7e8e7e
-- title:
--   Rational additive instances and their binary codes (bit model of Theorems 5.1 and 5.2)
-- statement:
--   Theorems 5.1 and 5.2 are about **rational inputs** in the bit model ("Contributions and costs are rational inputs", p.19).
--
--   A **rational additive instance** $I$ consists of a number $n$ of agents, rational singleton contributions $f(i)\in\mathbb Q$ and rational costs $c_i\in\mathbb Q$ for $i\in[n]$. Its success function is the additive extension
--   $$f(S)=\sum_{i\in S}f(i),\qquad S\subseteq[n],$$
--   and $I$ is **admissible** when
--
--   1. $f(i)\ge0$ for every agent $i$;
--   2. $\sum_{i\in[n]}f(i)\le1$;
--   3. $c_i\ge0$ for every agent $i$.
--
--   These are exactly the conditions under which $f$ is a success function of the model (monotone, $f(\emptyset)=0$, values in $[0,1]$) with nonnegative costs.
--
--   Instances and contracts are written over the four-letter alphabet $\{0,1,-,\#\}$. A natural number is written in binary, an integer as an optional minus sign followed by the binary code of its absolute value, and a rational number in lowest terms as numerator$\#$denominator$\#$. An instance is written as the code of $n$, a separator, then for $i=1,\dots,n$ the codes of $f(i)$ and $c_i$. A team contract $(S,\alpha)$ with rational shares is written, for $i=1,\dots,n$, as a membership bit ($1$ iff $i\in S$) followed by the code of $\alpha_i$. Finally $w\#y$ denotes the pair of a string $w$ over another alphabet and a code $y$, as in Cook's checking relations.
--
--   These codes fix what "instance size" and "compute a contract" mean in the bit model.
--
--   **Formalization Note** Agents are `Fin n`. Natural numbers use `Nat.bits` (least significant bit first; $0$ has the empty code). The pair $w\#y$ is a string over `Option (Sym ⊕ CSym)` with `none` as the separator, matching the published `CookPvsNP.checkLang`.
-- source:
--   Chen, Castiglioni, Li, Fair Team Contracts, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2, pp.7–9 (model, additive f) and §5.1, p.19 ("Contributions and costs are rational inputs")

import Mathlib

namespace FairTeamContracts.Supplement

/-- The four-letter alphabet of the bit model used for Theorems 5.1 and 5.2 (Chen, Castiglioni,
Li, *Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §5.1, p.19:
"Contributions and costs are rational inputs"): the binary digits `0` and `1`, a minus sign and a
separator. -/
inductive CSym where
  | b0
  | b1
  | minus
  | sep
  deriving DecidableEq

instance : Fintype CSym where
  elems := {CSym.b0, CSym.b1, CSym.minus, CSym.sep}
  complete := by intro x; cases x <;> simp

instance : Nonempty CSym := ⟨CSym.b0⟩

/-- Binary code of a natural number: its bits, least significant first (`Nat.bits`; `0` has the
empty code). -/
def encNat (m : ℕ) : List CSym :=
  (Nat.bits m).map fun b => if b then CSym.b1 else CSym.b0

/-- Code of an integer: a minus sign if it is negative, then the binary code of its absolute
value. -/
def encInt (z : ℤ) : List CSym :=
  (if z < 0 then [CSym.minus] else []) ++ encNat z.natAbs

/-- Code of a rational number in lowest terms: numerator, separator, denominator, separator. -/
def encRat (q : ℚ) : List CSym :=
  encInt q.num ++ CSym.sep :: encNat q.den ++ [CSym.sep]

/-- A **rational additive instance** of the fair team contract problem (Chen, Castiglioni, Li,
*Fair Team Contracts*, arXiv:2512.19388 (manuscript sha256 b8a12d9b…), §2, pp.7–9, and §5.1,
p.19): a number `n` of agents, the singleton contributions `f(i) = v i ∈ ℚ` and the costs
`cᵢ = c i ∈ ℚ`. The additive success function is `f(S) = ∑_{i ∈ S} f(i)`.

**Formalization Note.** Agents are `Fin n`. Which records are admissible instances is the
predicate `Valid`; the real-valued model of the base mission is `RatAddInst.f`, `RatAddInst.cost`. -/
structure RatAddInst where
  /-- The number of agents. -/
  n : ℕ
  /-- The singleton contributions `f(i)`. -/
  v : Fin n → ℚ
  /-- The costs `cᵢ`. -/
  c : Fin n → ℚ

namespace RatAddInst

/-- An instance is admissible when `f(i) ≥ 0`, `∑ᵢ f(i) ≤ 1` and `cᵢ ≥ 0`: then its additive
extension is a success function (monotone, `f(∅) = 0`, values in `[0, 1]`) and the costs are
nonnegative, as the model of §2 requires. -/
def Valid (I : RatAddInst) : Prop :=
  (∀ i, 0 ≤ I.v i) ∧ ∑ i, I.v i ≤ 1 ∧ ∀ i, 0 ≤ I.c i

/-- The additive success function `f(S) = ∑_{i ∈ S} f(i)` of the instance, as a real set
function. -/
def f (I : RatAddInst) : Finset (Fin I.n) → ℝ :=
  fun S => ∑ i ∈ S, (I.v i : ℝ)

/-- The costs of the instance as real numbers. -/
def cost (I : RatAddInst) : Fin I.n → ℝ :=
  fun i => (I.c i : ℝ)

end RatAddInst

/-- Code of an instance: the binary code of `n`, a separator, then for each agent
`i = 0, …, n − 1` the codes of `f(i)` and of `cᵢ`. -/
def encInst (I : RatAddInst) : List CSym :=
  encNat I.n ++ CSym.sep :: (List.finRange I.n).flatMap fun i => encRat (I.v i) ++ encRat (I.c i)

/-- Code of a team contract `(S, α)` with rational shares: for each agent `i = 0, …, n − 1` a
membership bit (`1` iff `i ∈ S`) followed by the code of `αᵢ`. -/
def encContract {n : ℕ} (S : Finset (Fin n)) (α : Fin n → ℚ) : List CSym :=
  (List.finRange n).flatMap fun i => (if i ∈ S then CSym.b1 else CSym.b0) :: encRat (α i)

/-- The pair `w#y` of a string over `Sym` and a string over `CSym`, over the alphabet
`Option (Sym ⊕ CSym)` (`none` is the separator `#`), as in `CookPvsNP.checkLang`. -/
def pairStr {Sym : Type} (w : List Sym) (y : List CSym) : List (Option (Sym ⊕ CSym)) :=
  w.map (some ∘ Sum.inl) ++ none :: y.map (some ∘ Sum.inr)

end FairTeamContracts.Supplement


