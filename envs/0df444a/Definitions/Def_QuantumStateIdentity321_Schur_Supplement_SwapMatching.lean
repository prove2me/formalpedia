-- Prove2me | Definitions.Def_QuantumStateIdentity321_Schur_Supplement_SwapMatching
-- name    : QuantumStateIdentity321_Schur_Supplement_SwapMatching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:51:01.088607+00:00
-- url     : https://prove2.me/theorems/fbd635f7-d219-4ca5-b594-f1bd715acbc1
-- title:
--   Swap tests, the $k$-fold swap test (Algorithm 1), uniformly random perfect matchings and the random-matching protocol (Algorithm 2)
-- statement:
--   This module defines the objects of §3 of the paper.
--
--   1. An **accept effect** on a finite set $R$ of $d$-dimensional registers is a matrix $A$ on $(\mathbb C^d)^{\otimes R}$ with $0\le A\le I$. If register $x$ holds a fresh copy of $|\psi_{\mathrm{lab}(x)}\rangle$, the input is $\bigotimes_{x\in R}|\psi_{\mathrm{lab}(x)}\rangle$ and the acceptance probability is $\langle\Psi|A|\Psi\rangle$; the number of copies of $|\psi_i\rangle$ consumed is the number of registers labelled $i$. With $R=[n]\times[m]$ this is the published tester model.
--   2. A tester using $m$ copies of each state **solves $\mathrm{QSI}^\varepsilon_n$ with error $\delta$** if it accepts every yes instance with probability at least $1-\delta$ and every no instance with probability at most $\delta$ (Definition 1.1).
--   3. One **swap test** on $\mathbb C^d\otimes\mathbb C^d$ is the measurement $\{\tfrac12(I+\mathrm{SWAP}),\tfrac12(I-\mathrm{SWAP})\}$, the first (symmetric) outcome being $X=1$.
--   4. **Algorithm 1** ($k$-fold swap test, threshold $\tau$) performs $k$ swap tests on $k$ pairs of fresh copies and accepts iff $\hat p=\frac1k\sum_s X^{(s)}\ge\tau$; its accept effect is $\sum_{x\in\{0,1\}^k,\ \hat p(x)\ge\tau}\bigotimes_s\Pi_{x_s}$. The threshold used is $\tau=(7-2\varepsilon+\sqrt\varepsilon)/8$.
--   5. A **perfect matching** of $[N]$ is a fixed-point-free involution; $\ell$ independent uniformly random perfect matchings have the uniform law on $\ell$-tuples.
--   6. **Algorithm 2** with $\ell$ rounds, $k$ copies per edge and threshold $\tau$: if $n$ is odd a register holding an extra copy of $|\psi_1\rangle$ is appended ($N=n+1$, else $N=n$); $\ell$ independent uniform perfect matchings $M_1,\dots,M_\ell$ of $[N]$ are sampled, Algorithm 1 is run on $k$ fresh copies of both endpoints of every edge of every round, and the protocol accepts iff no call rejects. Its accept effect is the uniform average over $(M_1,\dots,M_\ell)$ of the tensor product of the $k$-fold accept effects. The parameters are $\ell=\lceil\log_3(2/\delta)\rceil$, $k=\lceil(8/\gamma^2)\log(n\ell/\delta)\rceil$ with $\gamma=\frac12-\sqrt\varepsilon$, and the soundness-only $k=\lceil(8/\gamma^2)\log(2/\delta)\rceil$ of Theorem 3.4.
--
--   These are the objects in which Lemmas 3.2–3.3 and Theorems 3.4–3.5 are stated.
--
--   **Formalization Note** The swap test is given by its projective measurement; the source's destructive Bell-basis circuit implements exactly this measurement (p.10). Algorithm 2's registers are indexed by (vertex, round, copy); each edge is listed once, from its smaller endpoint, since the swap test is symmetric in its two registers. Logarithms are natural except $\log_3$.
-- source:
--   Shih-Han Hung, Ming-Hsien Tsai, STOC 2027 submission #321 (October 2026), §3.1–3.2, Algorithms 1 and 2 and Definition 1.1, PDF/printed p.2, 10–11, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/321.pdf

import Definitions.Def_QuantumStateIdentity321_Schur_Model

/-!
# Swap tests, the k-fold swap test (Algorithm 1) and the random-matching protocol (Algorithm 2)

Shih-Han Hung, Ming-Hsien Tsai, *Efficient Quantum State Identity Testing*, STOC 2027
submission #321 (October 2026), §3.1–§3.2, pp.9–13 (Algorithms 1 and 2).

Algorithm 2 may use a different number of copies of each input state (an extra block of copies
of `ψ₁` when `n` is odd), so its accept effect acts on an arbitrary finite set of registers `R`,
each labelled by the input state it holds. With `R = Fin n × Fin m` labelled by the first
coordinate this is exactly the published `Tester n m d` / `acceptProb` (checked below).
-/

namespace QuantumStateIdentity321.Schur.Supplement

open Matrix
open scoped ComplexOrder

/-- An accept effect on a finite set `R` of `d`-dimensional registers is *valid* if `0 ≤ A ≤ I`
on `(ℂᵈ)^{⊗R}` (basis `R → Fin d`), i.e. `{A, I − A}` is a two-outcome measurement. -/
def IsValidEffect {d : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (A : Matrix (R → Fin d) (R → Fin d) ℂ) : Prop :=
  A.PosSemidef ∧ (1 - A).PosSemidef

/-- The joint input when register `x : R` holds a fresh copy of `|ψ_{lab x}⟩`: the product
vector `⊗_{x ∈ R} |ψ_{lab x}⟩`, whose amplitude on the basis word `w` is `∏ₓ ψ_{lab x}(w x)`. -/
noncomputable def labelledInput {n d : ℕ} {R : Type} [Fintype R] (lab : R → Fin n)
    (ψ : Fin n → State d) : (R → Fin d) → ℂ :=
  fun w => ∏ x : R, ψ (lab x) (w x)

/-- The acceptance probability `⟨Ψ|A|Ψ⟩` of the accept effect `A` when register `x` holds a copy
of `|ψ_{lab x}⟩`. -/
noncomputable def labelledAcceptProb {n d : ℕ} {R : Type} [Fintype R] [DecidableEq R]
    (A : Matrix (R → Fin d) (R → Fin d) ℂ) (lab : R → Fin n) (ψ : Fin n → State d) : ℝ :=
  (star (labelledInput lab ψ) ⬝ᵥ (A *ᵥ labelledInput lab ψ)).re

/-- The number of registers holding a copy of `|ψᵢ⟩`, i.e. the number of copies of the `i`-th
input state the tester consumes. -/
def copyCount {n : ℕ} {R : Type} [Fintype R] (lab : R → Fin n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun x : R => lab x = i)).card

/-- With `m` copies of every state laid out as in the published model, the labelled input is
the published `copiesVec`, and the labelled acceptance probability of a published tester's effect
is its `acceptProb`. -/
example {n m d : ℕ} (ψ : Fin n → State d) :
    labelledInput (Prod.fst : Fin n × Fin m → Fin n) ψ = copiesVec m ψ := rfl

example {n m d : ℕ} (T : Tester n m d) (ψ : Fin n → State d) :
    labelledAcceptProb T.effect (Prod.fst : Fin n × Fin m → Fin n) ψ = acceptProb T ψ := rfl

/-- Definition 1.1, p.2: a tester using `m` copies of each state *solves* `QSI^ε_n` with error
`δ` if it accepts every yes instance with probability at least `1 − δ` and accepts every no
instance with probability at most `δ` (worst case over unit input vectors). -/
def SolvesQSI {n m d : ℕ} (T : Tester n m d) (ε δ : ℝ) : Prop :=
  (∀ ψ : Fin n → State d, (∀ i, ‖ψ i‖ = 1) → IsYesInstance ε ψ → 1 - δ ≤ acceptProb T ψ) ∧
  (∀ ψ : Fin n → State d, (∀ i, ‖ψ i‖ = 1) → IsNoInstance ε ψ → acceptProb T ψ ≤ δ)

/-! ## The swap test (p.10) -/

/-- The SWAP operator on `ℂᵈ ⊗ ℂᵈ`: `SWAP |a, b⟩ = |b, a⟩`. -/
def swapOp (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun x y => if x = y.swap then 1 else 0

/-- The two outcome projectors of one swap test on registers `(ψ, φ)`: the symmetric outcome
(`true`, `X = 1`) is `½(I + SWAP)` and the antisymmetric outcome (`false`, `X = 0`) is
`½(I − SWAP)`. (p.10: the destructive Bell-basis implementation measures exactly this
projective measurement.) -/
noncomputable def swapOutcome (d : ℕ) (b : Bool) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (1 / 2 : ℂ) • (1 + (if b then (1 : ℂ) else -1) • swapOp d)

/-- The empirical acceptance fraction `p̂ = (1/k) Σₛ X⁽ˢ⁾` of `k` swap-test outcomes (14). -/
noncomputable def empiricalFraction {k : ℕ} (b : Fin k → Bool) : ℝ :=
  ((Finset.univ.filter (fun s : Fin k => b s = true)).card : ℝ) / k

/-- Algorithm 1 (k-fold SWAP test, p.10): the accept effect on `k` pairs of registers, pair `s`
holding the `s`-th copies of `(|ψ⟩, |φ⟩)`. The `k` swap tests are measured independently and the
test accepts iff `p̂ ≥ τ` (it rejects iff `p̂ < τ`). The effect is the sum, over the outcome
strings `b ∈ {0,1}^k` with `p̂(b) ≥ τ`, of `⊗ₛ Π_{b s}`. -/
noncomputable def kFoldAccept (k d : ℕ) (τ : ℝ) :
    Matrix (Fin k → Fin d × Fin d) (Fin k → Fin d × Fin d) ℂ :=
  ∑ b : Fin k → Bool,
    if τ ≤ empiricalFraction b then (fun x y => ∏ s : Fin k, swapOutcome d (b s) (x s) (y s))
    else 0

/-- The registers of two states with `k` copies each, in the published layout
`(state, copy) ∈ Fin 2 × Fin k`, regrouped into the `k` pairs `((0, s), (1, s))`. -/
def pairUp {k d : ℕ} (w : CopyBasis 2 k d) : Fin k → Fin d × Fin d :=
  fun s => (w (0, s), w (1, s))

/-- Algorithm 1 as an effect on the published copy space of `n = 2` states with `k` copies each:
the `s`-th swap test acts on the `s`-th copies of `ψ₁` and `ψ₂`. -/
noncomputable def kFoldEffect (k d : ℕ) (τ : ℝ) : Matrix (CopyBasis 2 k d) (CopyBasis 2 k d) ℂ :=
  fun v w => kFoldAccept k d τ (pairUp v) (pairUp w)

/-- The threshold `τ = (7 − 2ε + √ε)/8` of Algorithm 1 used in Lemma 3.2 and Algorithm 2. -/
noncomputable def swapThreshold (ε : ℝ) : ℝ := (7 - 2 * ε + Real.sqrt ε) / 8

/-! ## Uniformly random perfect matchings (pp.11–12) -/

/-- Perfect matchings of `Fin N`, as fixed-point-free involutions: `m v` is the partner of `v`. -/
def PerfectMatching (N : ℕ) : Type :=
  {m : Equiv.Perm (Fin N) // ∀ v, m v ≠ v ∧ m (m v) = v}

noncomputable instance (N : ℕ) : Fintype (PerfectMatching N) := by
  unfold PerfectMatching; classical exact inferInstance

noncomputable instance (N : ℕ) : DecidableEq (PerfectMatching N) := Classical.decEq _

/-- The probability that `ℓ` independent uniformly random perfect matchings of `Fin N` satisfy an
event `E`: the uniform (product) law on `ℓ`-tuples of perfect matchings. -/
noncomputable def matchingProb (N ℓ : ℕ) (E : (Fin ℓ → PerfectMatching N) → Prop) : ℝ :=
  by classical exact
    ((Finset.univ.filter E).card : ℝ) / (Fintype.card (PerfectMatching N) : ℝ) ^ ℓ

/-! ## Algorithm 2 (random-matching protocol, p.11) -/

/-- The number of matched registers: `N = n` for even `n` and `N = n + 1` for odd `n` (an extra
register holding a copy of `|ψ₁⟩` is appended). -/
def numVertices (n : ℕ) : ℕ := n + n % 2

/-- The input state held by vertex `v` of the matching: vertex `v < n` holds `|ψ_v⟩`, and the
appended vertex `n` (odd `n` only) holds an extra copy of `|ψ₁⟩` (Lean index `0`). -/
def vertexState (n : ℕ) (v : Fin (numVertices n)) : Fin n :=
  if h : v.val < n then ⟨v.val, h⟩ else ⟨0, by have := v.isLt; unfold numVertices at this; omega⟩

/-- Registers of Algorithm 2 with `ℓ` rounds and `k` copies per edge: register `(v, r, s)` is the
`s`-th copy used by vertex `v` in round `r`. Each vertex is in exactly one edge per round, and
each edge consumes `k` fresh copies of both endpoint states. -/
abbrev Alg2Reg (n ℓ k : ℕ) := Fin (numVertices n) × Fin ℓ × Fin k

/-- The state held by a register of Algorithm 2. -/
def alg2Label (n ℓ k : ℕ) : Alg2Reg n ℓ k → Fin n := fun x => vertexState n x.1

/-- Algorithm 2 (p.11) with `ℓ` rounds, `k` copies per edge and threshold `τ`, as an accept
effect: sample `ℓ` independent uniformly random perfect matchings `M₁, …, M_ℓ` of the `N`
vertices; for every round `r` and every edge `{u, M_r u}` run Algorithm 1 with threshold `τ` on
the registers `(u, r, ·)` and `(M_r u, r, ·)`; accept iff no call rejects. Each edge is listed
once, from its smaller endpoint `u < M_r u` (the swap test is symmetric in its two registers).
The effect is the uniform average over `ℓ`-tuples of matchings of the tensor product of the
k-fold accept effects over all rounds and edges. -/
noncomputable def alg2Effect (n d ℓ k : ℕ) (τ : ℝ) :
    Matrix (Alg2Reg n ℓ k → Fin d) (Alg2Reg n ℓ k → Fin d) ℂ :=
  fun x y =>
    ((Fintype.card (PerfectMatching (numVertices n)) : ℂ) ^ ℓ)⁻¹ *
      ∑ M : Fin ℓ → PerfectMatching (numVertices n),
        ∏ r : Fin ℓ, ∏ u ∈ Finset.univ.filter (fun u => u < (M r).val u),
          kFoldAccept k d τ (fun s => (x (u, r, s), x ((M r).val u, r, s)))
            (fun s => (y (u, r, s), y ((M r).val u, r, s)))

/-- Algorithm 2's number of rounds `ℓ = ⌈log₃(2/δ)⌉`. -/
noncomputable def alg2Rounds (δ : ℝ) : ℕ := ⌈Real.logb 3 (2 / δ)⌉₊

/-- Algorithm 2's copies per edge `k = ⌈(8/γ²) · log(nℓ/δ)⌉` with `γ = 1/2 − √ε`. -/
noncomputable def alg2Copies (n : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈8 / (1 / 2 - Real.sqrt ε) ^ 2 * Real.log (n * alg2Rounds δ / δ)⌉₊

/-- The soundness-only copies per edge `k = ⌈(8/γ²) · log(2/δ)⌉` of Theorem 3.4. -/
noncomputable def alg2CopiesSound (ε δ : ℝ) : ℕ :=
  ⌈8 / (1 / 2 - Real.sqrt ε) ^ 2 * Real.log (2 / δ)⌉₊

/-- Sanity check: the two swap-test outcomes add up to the identity. -/
example (d : ℕ) : swapOutcome d true + swapOutcome d false = 1 := by
  unfold swapOutcome
  simp only [if_true, Bool.false_eq_true, if_false, one_smul, neg_smul]
  rw [← smul_add]
  rw [show (1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) + swapOp d + (1 + -swapOp d) = (2 : ℂ) • 1 by
    rw [two_smul]; abel]
  rw [smul_smul]; norm_num

end QuantumStateIdentity321.Schur.Supplement


