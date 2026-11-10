-- Prove2me | Definitions.Def_DNFSatMQ_Main_Reduction
-- name    : DNFSatMQ_Main_Reduction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:32:14.953023+00:00
-- url     : https://prove2.me/theorems/2e88b163-93f5-4143-a4ef-8028828e6ff6
-- title:
--   The hypothesis (3) of Algorithm 1 and the output law of the sampler Algorithm 2
-- statement:
--   The construction of §4 (p. 11). Let $c_1,\dots,c_m$ be conjunctions on $n$ variables with satisfying sets $C_i$, and $h_1,\dots,h_m$ local hypotheses $\{0,1\}^n \to \{0,1\}$ (indices are $0$-based in Lean).
--
--   **Hypothesis (3).** For $x \in G = \bigcup_i C_i$ let $i(x) = \min\{i : c_i(x) = 1\}$ (`firstIdx`). Then
--   $$h(x) = \begin{cases} h_{i(x)}(x), & x \in G,\\ 0, & x\notin G.\end{cases}$$
--   (`combinedHyp`).
--
--   **Algorithm 2.** Let $W = \sum_i |C_i|$. If $W = 0$ return $\bot$. Otherwise repeat $t$ times: choose $c_i$ with probability $|C_i|/W$ and draw $x \sim U_{C_i}$, and return $x$ if $i = i(x)$ and $h(x) = 1$; after $t$ rejected trials return $\bot$. `algorithm2 c hs t` is the output law on $\{0,1\}^n \cup\{\bot\}$. A trial draws a uniform pair from $\{(i,x) : x \in C_i\}$ (`pairSet`), which has $W$ elements and gives $i$ probability $|C_i|/W$ and then $x$ uniform on $C_i$.
--
--   `numTrials γ ε` is $t = \lceil (2/\gamma)\log(2/\varepsilon)\rceil$ with the natural logarithm, and `errOnConj c h F` is $\Pr_{x\sim U_C}[h(x) \ne f(x)]$ for the target with satisfying set $F$.
--
--   **Formalization Note.** The weighted choice is exact; finding I1 of the mission records that a sampler with finitely many fair coins can only approximate it.
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Algorithms 1 and 2 and the hypothesis (3), p. 11 (PDF 12)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Basic

namespace DNFSatMQ.Main

/-! The hypothesis (3) of Algorithm 1 and the sampling procedure Algorithm 2 (§4, p. 11), for
conjunctions `c₀, …, c_{m-1}` and local hypotheses `h₀, …, h_{m-1}` (indices are `0`-based). -/

/-- `i(x) = min {i : cᵢ(x) = 1}` for `x ∈ G = ⋃ᵢ Cᵢ`, and `none` for `x ∉ G`. -/
def firstIdx {n m : ℕ} (c : Fin m → Conj n) (x : Pt n) : Option (Fin m) :=
  (List.finRange m).find? fun i => decide ((c i).Sat x)

/-- The hypothesis (3): `h(x) = h_{i(x)}(x)` for `x ∈ G`, and `h(x) = 0` for `x ∉ G`. -/
def combinedHyp {n m : ℕ} (c : Fin m → Conj n) (hs : Fin m → Pt n → Bool) (x : Pt n) : Bool :=
  match firstIdx c x with
  | some i => hs i x
  | none => false

/-- The pairs `(i, x)` with `x ∈ Cᵢ`. A uniform pair is exactly "choose `cᵢ` with weight
`|Cᵢ|/W`, then draw `x ∼ U_{Cᵢ}`", and there are `W = Σᵢ |Cᵢ|` of them. -/
def pairSet {n m : ℕ} (c : Fin m → Conj n) : Finset (Fin m × Pt n) :=
  Finset.univ.filter fun p => (c p.1).Sat p.2

/-- The trials of Algorithm 2 (lines 6–10), `j` of them left: draw a uniform pair `(i, x)` and
return `x` if `i = i(x)` and `h(x) = 1`; after `j` rejected trials return `⊥` (`none`). -/
noncomputable def alg2Trials {n m : ℕ} (c : Fin m → Conj n) (hs : Fin m → Pt n → Bool)
    (hW : (pairSet c).Nonempty) : ℕ → PMF (Option (Pt n))
  | 0 => PMF.pure none
  | j + 1 => (PMF.uniformOfFinset (pairSet c) hW).bind fun p =>
      if firstIdx c p.2 = some p.1 ∧ combinedHyp c hs p.2 = true then PMF.pure (some p.2)
      else alg2Trials c hs hW j

/-- **Algorithm 2** (p. 11): the output law `D_h` on `{0,1}ⁿ ∪ {⊥}` of the sampler with `t` trials;
it returns `⊥` at once when `W = 0`. -/
noncomputable def algorithm2 {n m : ℕ} (c : Fin m → Conj n) (hs : Fin m → Pt n → Bool) (t : ℕ) :
    PMF (Option (Pt n)) :=
  if hW : (pairSet c).Nonempty then alg2Trials c hs hW t else PMF.pure none

/-- The number of trials `t = ⌈(2/γ) log(2/ε)⌉` set in Algorithm 1 (natural logarithm). -/
noncomputable def numTrials (γ ε : ℝ) : ℕ := ⌈(2 / γ) * Real.log (2 / ε)⌉₊

/-- The error `Pr_{x∼U_C}[h(x) ≠ f(x)]` of a local hypothesis on the satisfying set of `c`, for the
target with satisfying set `F`. -/
noncomputable def errOnConj {n : ℕ} (c : Conj n) (h : Pt n → Bool) (F : Finset (Pt n)) : ℝ :=
  ((c.cube.filter fun x => h x ≠ decide (x ∈ F)).card : ℝ) / c.cube.card

end DNFSatMQ.Main


