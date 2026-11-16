-- Prove2me | Definitions.Def_SteinerAPX_Supplement_TimedNetworkScheme
-- name    : SteinerAPX_Supplement_TimedNetworkScheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:12:16.49322+00:00
-- url     : https://prove2.me/theorems/bb4d8c27-8c75-4fa9-b4d4-72c909d6ad1a
-- title:
--   $(1+\varepsilon)$-approximation schemes in $\mathbb R^d$ running in time $2^{C\varepsilon^{-\gamma(d-1)}}\cdot\mathrm{poly}$
-- statement:
--   Fix a dimension $d$ and a real $\gamma$. A **TimedNetworkScheme$(d,\gamma)$** is one Turing machine $M$ with finite alphabets together with constants $C \in \mathbb R$ and $p \in \mathbb N$ such that for every rational $\varepsilon$ with $0<\varepsilon<1$ and every set of $n \ge 2$ distinct rational points in $\mathbb R^d$, $M$, started on the binary code of the pair $(\varepsilon, t)$, outputs the code of a list of rational segments in $\mathbb R^d$ whose union is connected, contains every terminal and has total length at most $(1+\varepsilon)\,\mathrm{OPT}$, within
--   $$\left\lceil 2^{\,C\,(1/\varepsilon)^{\gamma(d-1)}} \cdot (\ell+2)^p \right\rceil$$
--   steps, where $\ell$ is the length of the input code. A **TimedValueScheme$(d,\gamma)$** is the same with output a rational $v$ such that $\mathrm{OPT} \le v \le (1+\varepsilon)\,\mathrm{OPT}$.
--
--   These are the algorithms "running in time $2^{O(\varepsilon^{-\gamma(d-1)})}\,\mathrm{poly}(n)$" that Theorem 3 rules out under weak ETH.
--
--   **Formalization Note** $\varepsilon$ is part of the input, and $M$, $C$, $p$ are fixed before $\varepsilon$ and the instance. The polynomial factor is taken in the input length $\ell$, which is at least $n$, so the budget is at least the source's; a constant factor and an additive constant in the exponent are absorbed by $(\ell+2)^p$. Inputs are coded with the published `ratBits` and `rawTerminalsBits`; time is counted with `HMBinPacking.OutputsWithin`.
-- source:
--   Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…3fcfa9), Theorem 3, p.2 (PDF p.4); proof, §6.2, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_SteinerAPX_Network
import Definitions.Def_SteinerAPX_RawTerminals

set_option autoImplicit false

namespace SteinerAPX.Supplement

open OAI.BinPackingGap OAI.BinPackingGames.Foundations.Complexity

/-- The binary code of an input `(ε, t)` of an approximation scheme: the rational accuracy `ε`,
then the raw terminal set `t` (published `ratBits`, `rawTerminalsBits`, `pairBits`). -/
def schemeInputBits : ℚ × RawTerminals → List Bool :=
  BinaryEncoding.pairBits ratBits rawTerminalsBits

/-- The step budget `⌈2^{C · (1/ε)^{γ(d−1)}} · (ℓ + 2)^p⌉` of a scheme on an input of length `ℓ`
with accuracy `ε`. -/
noncomputable def schemeBudget (d : ℕ) (γ C : ℝ) (p : ℕ) (ε : ℚ) (ℓ : ℕ) : ℕ :=
  ⌈(2 : ℝ) ^ (C * (1 / (ε : ℝ)) ^ (γ * ((d : ℝ) - 1))) * ((ℓ : ℝ) + 2) ^ p⌉₊

/-- **A `(1+ε)`-approximation algorithm for Euclidean Steiner Tree in `ℝ^d` running in time
`2^{O(ε^{−γ(d−1)})} poly(n)` (network output).** S. Bartlmae, *Inapproximability of Euclidean
Steiner Tree*, STOC 2027 submission (manuscript sha256 6f78a9ea…), Theorem 3, p.2 (PDF p.4):
"admits no (1 + ε)-approximation algorithm running in time 2^{O(ε^{−γ(d−1)})} poly(n)"; proof,
§6.2, p.25 (PDF p.27): "Choose ε = (a/(4c_d)) m^{1/(1−d)} …".

One machine `M` with finite stack alphabets and constants `C`, `p` such that for every rational
`ε` with `0 < ε < 1` and every valid set `t` of `n ≥ 2` distinct rational points in `ℝ^d`, `M`
started on the code of `(ε, t)` outputs the code of a raw network `N` whose endpoints lie in `ℝ^d`,
which spans the terminals and has length at most `(1 + ε) · OPT`, within
`⌈2^{C · (1/ε)^{γ(d−1)}} · (ℓ + 2)^p⌉` steps, `ℓ` the length of the input code.

**Formalization Note** `ε` is part of the input and `M`, `C`, `p` are fixed before `ε` and the
instance (the proof runs the scheme with an `ε` computed from the instance). `ε^{−γ(d−1)}` is
`(1/ε)^{γ(d−1)}` with a real exponent (`Real.rpow`). `poly(n)` is taken in the input length `ℓ`,
which is at least the number of terminals, so more algorithms meet the bound; a constant factor and
an additive constant in the exponent are absorbed by `(ℓ + 2)^p` because `ℓ + 2 ≥ 2`. `C` is any
real (a negative `C` only shrinks the budget). Correctness is required only for `ε < 1` and
`n ≥ 2`, which again admits more algorithms. -/
structure TimedNetworkScheme (d : ℕ) (γ : ℝ) where
  machine : Turing.TM2ComputableAux Bool Bool
  finiteAlphabets : RevRedSAT.FiniteAlphabets machine
  C : ℝ
  p : ℕ
  guarantee : ∀ (ε : ℚ) (t : RawTerminals), 0 < ε → ε < 1 → t.Valid → 2 ≤ t.n → t.k = d →
    ∃ N : RawNetwork, N.ValidIn t.k ∧ Spans t.terminals (N.toNetwork t.k) ∧
      len (N.toNetwork t.k) ≤ (1 + (ε : ℝ)) * opt t.terminals ∧
      HMBinPacking.OutputsWithin machine (schemeInputBits (ε, t)) (rawNetworkBits N)
        (schemeBudget d γ C p ε (schemeInputBits (ε, t)).length)

/-- **A `(1+ε)`-approximation algorithm for the optimal value in `ℝ^d` running in time
`2^{O(ε^{−γ(d−1)})} poly(n)`.** Same source and conventions as `TimedNetworkScheme`; the machine
outputs the code (`ratBits`) of a rational `v` with `OPT ≤ v ≤ (1 + ε) · OPT`. -/
structure TimedValueScheme (d : ℕ) (γ : ℝ) where
  machine : Turing.TM2ComputableAux Bool Bool
  finiteAlphabets : RevRedSAT.FiniteAlphabets machine
  C : ℝ
  p : ℕ
  guarantee : ∀ (ε : ℚ) (t : RawTerminals), 0 < ε → ε < 1 → t.Valid → 2 ≤ t.n → t.k = d →
    ∃ v : ℚ, opt t.terminals ≤ (v : ℝ) ∧ (v : ℝ) ≤ (1 + (ε : ℝ)) * opt t.terminals ∧
      HMBinPacking.OutputsWithin machine (schemeInputBits (ε, t)) (ratBits v)
        (schemeBudget d γ C p ε (schemeInputBits (ε, t)).length)

end SteinerAPX.Supplement


