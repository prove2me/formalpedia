-- Prove2me | Definitions.Def_AdaptiveSparsify_Checker
-- name    : AdaptiveSparsify_Checker
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:47:19.513806+00:00
-- url     : https://prove2.me/theorems/99ea26ec-00ad-482d-be81-f5dd6dc715ae
-- title:
--   Batched halving sequences and the checker-induced leverage score estimates
-- statement:
--   The decremental process of §5.
--
--   A batched halving sequence of $A=A^{(0)}$ of length $Q$ is a sequence of row sets $H^{(1)},\dots,H^{(Q)}$ such that $A^{(q)}$ arises from $A^{(q-1)}$ by replacing each row of $H^{(q)}$ by half of itself, and for $2\le q\le Q$,
--
--   $$\sum_{i\in H^{(q)}}(a^{(q)}_i)^\top\big((A^{(q)})^\top A^{(q)}+I/\kappa\big)^{-1}a^{(q)}_i\in[0.001,1.2].$$
--
--   The checker of Definition 5.4 maintains estimates $\tilde\tau^{(q)}$ against an adversary choosing $H^{(q)}$ from the history of the estimates. Write $G^{(q)}=(A^{(q)})^\top A^{(q)}+I/\kappa$. In step $q$ it draws rows of $A^{(q)}$ with probabilities proportional to $\tilde\tau^{(q-1)}$ and forms the sparsified Gram matrix $\tilde G^{(q)}$ with $I/\kappa$ added; it draws a fresh Johnson–Lindenstrauss matrix $S$ and sets $Z^{(q)}=S(\tilde G^{(q)})^{-1/2}$; it recomputes $\tilde\tau^{(q)}_i=d/n+10\|Z^{(q)}a^{(q)}_i\|_2^2$ for every halved row. For every $j\ge0$ with $2^j\mid q$ and $\hat q=q-2^j$ it forms
--
--   $$\Delta^{(\hat q,q)}=(1+20\epsilon_{\mathrm{checker}})(\tilde G^{(q)})^{-1}-(1-20\epsilon_{\mathrm{checker}})(\tilde G^{(\hat q)})^{-1},$$
--
--   and it also recomputes every row with $\|S(\Delta^{(\hat q,q)})^{1/2}a^{(q)}_i\|_2^2\ge d/(10n\log n)$.
--
--   **Formalization Note** The process is a deterministic recursion on a pair of tapes, of independent uniform reals for the row draws and of independent $N(0,1)$ reals for $S$, so it is one concrete random object. The sample count, the JL dimension and $\epsilon_{\mathrm{checker}}$ carry constants chosen in the lemmas. $\tilde G^{(0)}$, undefined on the page, is $G^{(0)}$, and the initial estimates are $d/n$ plus an overestimate of the initial leverage (correction C4).
-- source:
--   Liu, Peng, Tang, Weng, Yang, Adaptive Matrix Sparsification with Applications to Empirical Risk Minimization and Computational Geometry (manuscript, sha256 7a66a27b…), Definition 5.2, p.34; Definition 5.4, pp.35–36; Lemma 2.3, p.11

import Mathlib
import Definitions.Def_AdaptiveSparsify_IPM

namespace AdaptiveSparsify

/-!
# Batched halving sequences and the checker-induced estimates

Liu, Peng, Tang, Weng, Yang, *Adaptive Matrix Sparsification …* (manuscript, sha256 7a66a27b…),
Definition 5.2, p.34, and Definition 5.4, pp.35–36, with Lemma 2.3, p.11, for the sampling.

**Formalization Note.**
* The Gram matrix is `G^{(q)} = (A^{(q)})⊤A^{(q)} + I/κ`. Halving a row multiplies it by `1/2`.
* The checker is a deterministic recursion on a pair of tapes, so the process is one concrete random
  object: uniform reals for the row samples of step 1, and `N(0,1)` reals for the JL matrices of
  step 2, addressed by `Nat.pair`. A JL matrix is `m^{-1/2}` times Gaussian entries, the form of
  Lemma 2.1, fresh in each step; the same `S` is used in steps 2 and 4, as printed.
* Sample count and JL dimension are `⌈Cs ϵ⁻² log n Σ τ̃^{(q-1)}⌉` and `⌈Cjl log n⌉`, for constants
  chosen in the lemmas (the page writes `O(ϵ⁻²log n)` and `O(log n)`). `ϵ_checker = 0.001 / (Clem (d
  log(n + d + κ + 2) + 1))`, because `log(n d κ)` vanishes at `n = d = κ = 1` and Lemma 5.3 is stated
  here with an additive constant.
* The set `H^{(q)}` is chosen by the strategy from the history of `τ̃` arrays: the adversary is
  adaptive. A measurable strategy is required for the outer measure bound to mean anything.
* At `q̂ = 0`, step 4(a) refers to `G̃^{(0)}`, undefined on the page since steps start at `q = 1`. It is
  `G^{(0)}` here, the natural reading.
* **Correction C4:** `τ̃^{(0)} = d/n +` the estimate of Lemma 2.4. See the items of Lemma 5.5 and 5.6.
-/

open Matrix

/-- The Gram matrix `A⊤A + I/κ`. -/
noncomputable def gramOf {n d : ℕ} (κ : ℝ) (A : Matrix (Fin n) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Aᵀ * A + κ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- Halve the rows of `H`. -/
noncomputable def halve {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (H : Finset (Fin n)) :
    Matrix (Fin n) (Fin d) ℝ := by
  classical exact fun i => if i ∈ H then (1 / 2 : ℝ) • A i else A i

/-- The matrix sequence `A^{(q)}` of Definition 5.2. -/
noncomputable def halvedSeq {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (H : ℕ → Finset (Fin n)) :
    ℕ → Matrix (Fin n) (Fin d) ℝ
  | 0 => A
  | q + 1 => halve (halvedSeq A H q) (H (q + 1))

/-- `H^{(1)}, …, H^{(Q)}` is a batched halving sequence of `A` of length `Q` (Definition 5.2): for all
`2 ≤ q ≤ Q`, the leverage of `H^{(q)}` against `G^{(q)}` lies in `[0.001, 1.2]`. -/
def IsBatchedHalving {n d : ℕ} (κ : ℝ) (A : Matrix (Fin n) (Fin d) ℝ) (H : ℕ → Finset (Fin n))
    (Q : ℕ) : Prop :=
  ∀ q, 2 ≤ q → q ≤ Q →
    (0.001 : ℝ) ≤ ∑ i ∈ H q,
      leverage (gramOf κ (halvedSeq A H q)) (halvedSeq A H q i) ∧
    ∑ i ∈ H q, leverage (gramOf κ (halvedSeq A H q)) (halvedSeq A H q i) ≤ (1.2 : ℝ)

/-- An adaptive halving strategy: from the history of `τ̃` arrays, the next set of rows. -/
abbrev HalvingStrategy (n : ℕ) := List (Fin n → ℝ) → Finset (Fin n)

/-- A halving strategy is measurable in the history. -/
def HalvingStrategy.Measurable {n : ℕ} (σ : HalvingStrategy n) : Prop :=
  ∀ (j : ℕ) (H₀ : Finset (Fin n)),
    MeasurableSet {h : Fin j → Fin n → ℝ | σ (List.ofFn h) = H₀}

/-- The sampled matrix `Ã` of Lemma 2.3, p.11: row `l` is `(p_{i_l} T)^{-1/2} a_{i_l}`. -/
noncomputable def sampledMatrix {n d T : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (p : Fin n → ℝ)
    (idx : Fin T → Fin n) : Matrix (Fin T) (Fin d) ℝ :=
  Matrix.of fun l k => Real.sqrt (p (idx l) * T)⁻¹ * A (idx l) k

/-- The constants of the checker: `Clem` of `ϵ_checker`, the sampling constant, the JL constant. -/
structure CheckerConstants where
  Clem : ℝ
  Cs : ℝ
  Cjl : ℝ

/-- `ϵ_checker` (Definition 5.4, step 1). -/
noncomputable def epsChecker (C : CheckerConstants) (n d : ℕ) (κ : ℝ) : ℝ :=
  0.001 / (C.Clem * ((d : ℝ) * Real.log ((n : ℝ) + d + κ + 2) + 1))

/-- The state of the checker after step `q`: the current matrix `A^{(q)}`, the estimates `τ̃^{(q)}`, the
sparsified Gram matrices `G̃^{(q')}` indexed by `q'`, and the history of estimates. -/
structure CheckerState (n d : ℕ) where
  A : Matrix (Fin n) (Fin d) ℝ
  τ : Fin n → ℝ
  Gt : ℕ → Matrix (Fin d) (Fin d) ℝ
  hist : List (Fin n → ℝ)

/-- The pair of tapes of the checker. -/
abbrev CheckerTape := (ℕ → unitInterval) × (ℕ → ℝ)

/-- The law of the pair of tapes: independent uniform reals and independent `N(0,1)` reals. -/
noncomputable def checkerTape : MeasureTheory.Measure CheckerTape :=
  (MeasureTheory.Measure.infinitePi fun _ : ℕ => MeasureTheory.volume).prod tape

/-- The JL matrix `S` of step `q` of dimension `mJL × d`: `m^{-1/2}` times fresh Gaussian entries. -/
noncomputable def jlMatrix (d mJL q : ℕ) (ω : CheckerTape) : Matrix (Fin mJL) (Fin d) ℝ :=
  Matrix.of fun r k =>
    Real.sqrt (mJL : ℝ)⁻¹ * ω.2 (Nat.pair q (Nat.pair (r : ℕ) (k : ℕ)))

/-- The sparsified Gram matrix of step 1, from `T` draws with probabilities proportional to `τ`:
`∑_l (p_{i_l} T)⁻¹ a_{i_l} a_{i_l}⊤ + I/κ`. -/
noncomputable def sparsifiedGram {n d : ℕ} (i₀ : Fin n) (κ : ℝ) (T q : ℕ)
    (A : Matrix (Fin n) (Fin d) ℝ) (τ : Fin n → ℝ) (ω : CheckerTape) :
    Matrix (Fin d) (Fin d) ℝ :=
  let p : Fin n → ℝ := fun i => τ i / ∑ i', τ i'
  (∑ l : Fin T,
    let i := drawIndex i₀ p ((ω.1 (Nat.pair q (l : ℕ)) : unitInterval) : ℝ)
    (p i * T)⁻¹ • Matrix.vecMulVec (A i) (A i)) + κ⁻¹ • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- `∆^{(q̂,q)} = (1 + 20ϵ)(G̃^{(q)})⁻¹ - (1 - 20ϵ)(G̃^{(q̂)})⁻¹` of step 4(a). -/
noncomputable def deltaMat {d : ℕ} (ϵ : ℝ) (Gq Gqh : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (1 + 20 * ϵ) • Gq⁻¹ - (1 - 20 * ϵ) • Gqh⁻¹

/-- Step `q + 1` of Definition 5.4 from the state after step `q`, for the set `H` chosen by the
adversary. -/
noncomputable def checkerStep {n d : ℕ} (C : CheckerConstants) (i₀ : Fin n) (κ : ℝ) (q : ℕ)
    (H : Finset (Fin n)) (ω : CheckerTape) (st : CheckerState n d) : CheckerState n d := by
  classical exact
    let q' := q + 1
    let ϵ := epsChecker C n d κ
    let A' := halve st.A H
    let T := ⌈C.Cs * (ϵ⁻¹) ^ 2 * Real.log n * ∑ i, st.τ i⌉₊
    let Gq := sparsifiedGram i₀ κ T q' A' st.τ ω
    let mJL := ⌈C.Cjl * Real.log n⌉₊
    let S := jlMatrix d mJL q' ω
    let Z := S * matInvSqrt Gq
    let est : Fin n → ℝ := fun i => (d : ℝ) / n + 10 * (eNorm (Z *ᵥ A' i)) ^ 2
    let Gt' := Function.update st.Gt q' Gq
    let large : Fin n → Prop := fun i =>
      ∃ j ∈ Finset.range (Nat.log 2 q' + 1), 2 ^ j ∣ q' ∧
        (d : ℝ) / (10 * n * Real.log n) ≤
          (eNorm ((S * matSqrt (deltaMat ϵ Gq (Gt' (q' - 2 ^ j)))) *ᵥ A' i)) ^ 2
    let τ' : Fin n → ℝ := fun i => if i ∈ H ∨ large i then est i else st.τ i
    { A := A', τ := τ', Gt := Gt', hist := st.hist ++ [τ'] }

/-- The state of the checker after step `q`, from `τ̃^{(0)} = τ0`, with `G̃^{(0)} = G^{(0)}`. The adversary
sees the history of estimates, including `τ̃^{(0)}`. -/
noncomputable def checkerRun {n d : ℕ} (C : CheckerConstants) (i₀ : Fin n) (κ : ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) (τ0 : Fin n → ℝ) (σ : HalvingStrategy n) (ω : CheckerTape) :
    ℕ → CheckerState n d
  | 0 => { A := A, τ := τ0, Gt := fun _ => gramOf κ A, hist := [τ0] }
  | q + 1 =>
    let st := checkerRun C i₀ κ A τ0 σ ω q
    checkerStep C i₀ κ q (σ st.hist) ω st

/-- The sets played by the adversary on tape `ω`: `H^{(q)}` for `q ≥ 1`. -/
noncomputable def playedSets {n d : ℕ} (C : CheckerConstants) (i₀ : Fin n) (κ : ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) (τ0 : Fin n → ℝ) (σ : HalvingStrategy n) (ω : CheckerTape)
    (q : ℕ) : Finset (Fin n) :=
  σ (checkerRun C i₀ κ A τ0 σ ω (q - 1)).hist

/-- The hypothesis on the initial estimates of Lemmas 5.5 and 5.6 (correction C4): `τ̃^{(0)}_i` is
`d/n` plus an overestimate of the leverage against `G^{(0)}`, the estimates of Lemma 2.4. -/
def InitialEstimates {n d : ℕ} (κ : ℝ) (A : Matrix (Fin n) (Fin d) ℝ) (τ0 : Fin n → ℝ) : Prop :=
  ∀ i, (d : ℝ) / n + leverage (gramOf κ A) (A i) ≤ τ0 i

end AdaptiveSparsify


