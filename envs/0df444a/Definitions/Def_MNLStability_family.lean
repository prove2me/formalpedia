-- Prove2me | Definitions.Def_MNLStability_family
-- name    : MNLStability_family
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:13.659512+00:00
-- url     : https://prove2.me/theorems/b71684a7-7310-464e-a826-b92ca32acbfd
-- title:
--   Program 1: the universal family of §4
-- statement:
--   `family r ord C ε` builds the list of candidate step vectors for a set $I$ of products listed by `ord` by non-increasing price.
--
--   1. If $I$ is empty or $\varepsilon\ge1$, return $[0]$. If $nC\le1$, return $0$ and the vectors with one unit of one product of $I$.
--   2. Set $e=\varepsilon/3$, $J=\lceil\log C/\log(1+e)\rceil$, and let $H(1)>\dots>H(L)=0$ be the set $\{0,C\}\cup\{\lceil(1+e)^j\rceil\le C: 0\le j\le J\}$ in decreasing order.
--   3. Output $0$ and, for every subset $\Lambda$ of the levels, every $a\in\{0,\dots,J\}$, every $\mu\in\mathbb N^{|\Lambda|}$ with $\sum\mu\le\lfloor2L/e\rfloor$, and every non-increasing $\nu\in\mathbb Z^{|\Lambda|}$ with values in $[\lfloor\log_{1+e}(e/(nL))\rfloor,J+1]$: with $\tilde R=(1+e)^ar_1$ ($r_1$ the largest price of $I$), $\tilde R_\lambda=\mu_\lambda(e/L)\tilde R$ and $\tilde E_\lambda=(1+e)^{\nu_\lambda}$, compute the lengths $\tilde m$ for the thresholds $\tilde R_\lambda/\tilde E_\lambda$ and emit $\tilde V^{\mathrm{step}}$ (nothing if the lengths do not exist).
--
--   The program reads only the prices of $I$, $C$, $n$ and $\varepsilon$: no weight and no law of $M$.
--
--   **Formalization Note** The paper normalizes $\tilde R$ and $\tilde E_\ell$ by a guessed estimate $\tilde\varphi$ of the probability $\varphi$ of Claim 1. The candidate depends on them only through $\tilde R_\ell/\tilde E_\ell$, so this program enumerates the same grids divided by $\varphi$ and guesses no $\tilde\varphi$; the guessing grids are those of guessing steps 1–3 (pp.20–21) at accuracy $e=\varepsilon/3$, because Lemma 9 loses $3e$. Each enumeration is a counted loop, and each straight-line block is charged its operation count at its site.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §4.3–4.4, pp.20–22; Theorem 3, p.18; §4.6, pp.24–25

import Mathlib
import Definitions.Def_MNLStability_Prog
import Definitions.Def_MNLStability_greedyLengths

namespace MNLStability

variable {n : ℕ}

/-- The levels `H(1) > H(2) > ⋯ > H(L) = 0` of a `(1 + e)`-spaced subset of `[C]` with `0` added
(SSRN:3498325, §4.2, p.19): `0`, `C`, and `⌈(1 + e)^j⌉` for `0 ≤ j ≤ J` when it is at most `C`,
sorted by decreasing value. -/
noncomputable def levelList (e : ℝ) (C J : ℕ) : List ℕ :=
  ((insert 0 (insert C (((List.range (J + 1)).map fun j => ⌈(1 + e) ^ j⌉₊).filter
    (· ≤ C)).toFinset)).sort (· ≤ ·)).reverse

/-- One candidate of the enumeration (§4.3–4.4, pp.20–22) for the guess `(Λ, a, μ, ν)`:
`R̃ = (1 + e)^a · r₁`, `R̃_λ = μ_λ · (e/L) · R̃`, `Ẽ_λ = (1 + e)^{ν_λ}`; the lengths `m̃` are the
greedy minimal indices of p.22 for the thresholds `R̃_λ/Ẽ_λ` along the prices `rs` of `ord`, and the
candidate is `Ṽ^step`. A guess for which the minimal indices do not exist emits nothing. Costs:
`|ν_λ| + 6` per threshold (the power by repeated multiplication) plus the length of the list
appended to, `2(|rs| + |Λ| + 1)` for the greedy
scan, `2(n + |ord| + 1)` to write `Ṽ^step`, `1` to append it. -/
noncomputable def emitCandidate (ord : List (Fin n)) (rs : List ℝ) (e : ℝ) (L : ℕ) (Rt : ℝ)
    (Λ : List ℕ) (μ : List ℕ) (ν : List ℤ) (acc : List (Fin n → ℕ)) :
    Prog (List (Fin n → ℕ)) := do
  let taus ← foldP (μ.zip ν) (fun ts p => opn (ts.length + p.2.natAbs + 6)
    (ts ++ [(p.1 : ℝ) * (e / L) * Rt / (1 + e) ^ p.2])) []
  let ks ← opn (2 * (rs.length + taus.length + 1)) (greedyLengths rs taus)
  match ks with
  | none => pure acc
  | some ks => do
    let V ← opn (2 * (n + ord.length + 1)) (stepVec ord Λ ks)
    opn 1 (V :: acc)

/-- **Program 1: the universal family** of SSRN:3498325, §4 (Theorem 3, p.18; the guessing procedure
§4.3, pp.20–21; the reconstruction §4.4, p.22), for the set `I` of products listed in `ord` by
non-increasing price.

1. If `I` is empty or `1 ≤ ε`, return `[0]`. If `n·C ≤ 1`, return `0` and the vectors with one unit
   of one product of `I`.
2. `e = ε/3`; `J = ⌈log C / log(1 + e)⌉`; `H(1) > ⋯ > H(L) = 0` is `levelList e C J`.
3. Output `0` and, for every sublist `Λ` of the levels, every `a ∈ {0, …, J}`, every `μ ∈ ℕ^{|Λ|}` with
   `Σ μ ≤ ⌊2L/e⌋`, and every non-increasing `ν ∈ ℤ^{|Λ|}` with values in
   `[⌊log(e/(nL))/log(1 + e)⌋, J + 1]`, the candidate `emitCandidate` with `r₁` the price of the first
   product of `ord`.

The program reads the prices `r` of `ord`, `C`, `n` and `ε`, and nothing else: no weight and no law
of `M`.

**Formalization Note.** The paper normalizes `R̃` and `Ẽ_ℓ` by an estimate `φ̃` of the probability
`φ` of Claim 1; the candidate depends on them only through `R̃_ℓ/Ẽ_ℓ`, so the program enumerates the
same grid divided by `φ`, and no estimate of `φ` is guessed. -/
noncomputable def family (r : Fin n → ℝ) (ord : List (Fin n)) (C : ℕ) (ε : ℝ) :
    Prog (List (Fin n → ℕ)) := do
  let stop ← opn 2 (decide (ord = [] ∨ 1 ≤ ε))
  if stop then pure [0]
  else do
    let tiny ← opn 2 (decide (n * C ≤ 1))
    if tiny then opn (2 * (n + 1) * (ord.length + 1)) (0 :: ord.map fun i => Pi.single i 1)
    else do
      let e ← opn 1 (ε / 3)
      let J ← opn 5 ⌈Real.log C / Real.log (1 + e)⌉₊
      let Hl ← opn (6 * (J + 3)) (levelList e C J)
      let L ← opn 1 Hl.length
      let r1 ← opn 2 ((ord.head?.map r).getD 0)
      let rs ← foldP ord (fun rs i => opn (rs.length + 2) (rs ++ [r i])) []
      let B ← opn 4 ⌊2 * (L : ℝ) / e⌋₊
      let lo ← opn 8 ⌊Real.log (e / (n * L)) / Real.log (1 + e)⌋
      let hi ← opn 1 ((J : ℤ) + 1)
      foldSubsets Hl (fun acc Λ =>
        foldP (List.range (J + 1)) (fun acc a => do
          let Rt ← opn (a + 2) ((1 + e) ^ a * r1)
          foldComps Λ.length B (fun acc μ =>
            foldNoninc Λ.length lo hi (fun acc ν =>
              emitCandidate ord rs e L Rt Λ μ ν acc) acc) acc) acc) [0]

end MNLStability


