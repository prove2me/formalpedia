-- Prove2me | Definitions.Def_CNFLearnMQ_extendSubclause
-- name    : CNFLearnMQ_extendSubclause
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:32.12274+00:00
-- url     : https://prove2.me/theorems/f63f29f2-f8b7-4b42-9c2e-f4058b1a6813
-- title:
--   ExtendSubclause$(s,Y)$ (Algorithm 4) and its acceptance kernel
-- statement:
--   Given a rejected candidate $s=(S,\sigma_S)$ and the sample pool $Y$, ExtendSubclause takes the first $N_{\mathrm{ext}}$ pool samples $Z_1,\dots,Z_{N_{\mathrm{ext}}}$ violating $s$, runs LearnCore$(Z_i,\zeta)$ on each to get families $\widehat{\mathcal R}_{Z_i}$, and considers every signed core $b=(B,\tau_B)\in\bigcup_i\mathcal C(\widehat{\mathcal R}_{Z_i})$ with $B\cap S=\emptyset$ and $|B|+|S|\le k$. Its empirical frequency is
--   $$\widehat q_s(b)=\frac1{N_{\mathrm{ext}}}\sum_{i=1}^{N_{\mathrm{ext}}}\mathbf 1\big[b\in\mathcal C(\widehat{\mathcal R}_{Z_i})\big],$$
--   and the extension $s\cup b$ is accepted when $\widehat q_s(b)\ge \big((k-|S|)\binom{k-|S|}{|B|}\big)^{-1}$.
--
--   The module defines the join $s\cup b$, the selected samples, the candidate cores, their counts and frequencies, the considered cores, the acceptance kernel `acceptExtensions` (used by Lemma 5.7), the record of a call, and the program.
--
--   Charges: $|Y|(|S|+1)$ for selecting the violating samples, and $(\sum_i|\widehat{\mathcal R}_{Z_i}|)^2(k+1)+N_{\mathrm{ext}}$ for the frequencies and tests.
--
--   **Formalization Note** If fewer than $N_{\mathrm{ext}}$ samples violate $s$ (impossible after a rejection, p.26) the available ones are used, with the denominator $N_{\mathrm{ext}}$ kept.
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), §5.3, pp.25–26; Algorithm 4, p.27

import Mathlib
import Definitions.Def_CNFLearnMQ_learnCore

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant OProg

variable {n : ℕ}

/-- The extension `s ∪ b` of a subclause `s` by a subclause `b` (Feng, Yu, Zhang, STOC 2027
submission (manuscript sha256 519ee6d4…), p.26: "the extension `s ∪ b` joins the subclauses `s` and
`b`"): the literals of `s`, and those of `b` on variables outside `vbl(s)`. (Extensions are only
formed for `vbl(b) ∩ vbl(s) = ∅`.) -/
def joinClause (s b : Clause n) : Clause n := fun v => (s v).or (b v)

/-- The first `N` assignments of the list `Y` that violate `s` (Algorithm 4 line 1, p.27; eq. (13),
p.35), in the order of `Y`. -/
noncomputable def firstViolating (Y : List (Assignment n)) (s : Clause n) (N : ℕ) : List (Assignment n) :=
  by classical exact (Y.filter fun Z => decide (Violates s Z)).take N

/-- `⋃ᵢ C(R̂_{Zᵢ})`: all signed cores induced by the families `Rs` of the samples `Zs`
(Algorithm 4 line 4). -/
def candidateCores (Zs : List (Assignment n)) (Rs : List (Finset (Finset (Fin n)))) :
    Finset (Clause n) :=
  ((Zs.zip Rs).map fun p => inducedFamily p.1 p.2).foldr (· ∪ ·) ∅

/-- The number of `i` with `b ∈ C(R̂_{Zᵢ})`. -/
def coreCount (Zs : List (Assignment n)) (Rs : List (Finset (Finset (Fin n)))) (b : Clause n) : ℕ :=
  ((Zs.zip Rs).filter fun p => decide (b ∈ inducedFamily p.1 p.2)).length

/-- The empirical core frequency `q̂_s(b) = Σᵢ 1[b ∈ C(R̂_{Zᵢ})]/N` (Algorithm 4 line 6, with
`N = N_ext`). -/
noncomputable def qhatCore (N : ℕ) (Zs : List (Assignment n)) (Rs : List (Finset (Finset (Fin n))))
    (b : Clause n) : ℝ :=
  (coreCount Zs Rs b : ℝ) / N

/-- The signed cores considered in ExtendSubclause(s, Y) (Algorithm 4 lines 4–5): those recovered
cores `b = (B, τ_B)` with `B ∩ S = ∅` and `|B| + |S| ≤ k`. -/
def considered (k : ℕ) (s : Clause n) (Zs : List (Assignment n))
    (Rs : List (Finset (Finset (Fin n)))) : Finset (Clause n) :=
  (candidateCores Zs Rs).filter fun b => Disjoint (support b) (support s) ∧ width b + width s ≤ k

/-- Lines 3–9 of Algorithm 4: the accepted extensions `A_s = {s ∪ b}` over the considered signed
cores `b` with `q̂_s(b) ≥ ((k − |S|)·binom(k − |S|, |B|))^{−1}`, where the frequencies are computed
with denominator `N`. -/
noncomputable def acceptExtensions (k N : ℕ) (s : Clause n) (Zs : List (Assignment n))
    (Rs : List (Finset (Finset (Fin n)))) : Finset (Clause n) :=
  ((considered k s Zs Rs).filter fun b =>
    (((k - width s) * (k - width s).choose (width b) : ℕ) : ℝ)⁻¹ ≤ qhatCore N Zs Rs b).image
    (joinClause s)

/-- The record of one call to ExtendSubclause: the input subclause `s`, the selected samples
`Z_1, …, Z_{N_ext}`, the recovered core families `R̂_{Zᵢ}`, and the accepted extensions `A_s`. -/
structure ExtCall (n : ℕ) where
  s : Clause n
  Zs : List (Assignment n)
  Rs : List (Finset (Finset (Fin n)))
  accepted : Finset (Clause n)

/-- ExtendSubclause(s, Y) (Algorithm 4, p.27) with parameters `d, k` (and `n, t, ε, δ`, which fix
`N_ext` and `ζ`) and membership-query access to `Φ`. It returns the record of the call; the
accepted extensions are its `accepted` field.

Charges: `|Y|·(|S| + 1)` for selecting the first `N_ext` violating samples (line 1);
`(Σᵢ|R̂_{Zᵢ}|)²·(k + 1) + N_ext` for the core frequencies and acceptance tests of lines 4–8 (each
candidate is compared with every recovered core, each comparison reading `k + 1` words).

**Formalization Note** If fewer than `N_ext` pool samples violate `s` (impossible after a rejection,
p.26) the samples that exist are used; the frequencies keep the denominator `N_ext`. -/
noncomputable def extendSubclause (n k d : ℕ) (t ε δ : ℝ) (s : Clause n)
    (Y : List (Assignment n)) : OProg n (ExtCall n) := do
  let N := Next n k d δ
  charge (Y.length * (width s + 1))
  let Zs := firstViolating Y s N
  let Rs ← Zs.mapM fun Z => learnCore n k d Z (zeta n k d t ε δ)
  let tot := (Rs.map Finset.card).sum
  charge (tot * tot * (k + 1) + N)
  return ⟨s, Zs, Rs, acceptExtensions k N s Zs Rs⟩

end CNFLearnMQ


